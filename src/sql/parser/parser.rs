//! Production parser entry point.
//!
//! `Parser::parse` lexes the input, then calls the Verus-verified
//! `verified_control::parse_control_at` directly on the token vector. The legacy
//! handcrafted recursive-descent parser in this file is `#[cfg(test)]`-only and
//! serves purely as a differential oracle against the verified core; it is not
//! compiled into the shipped binary. `Parser::parse` also applies a cheap
//! `MAX_NESTING_DEPTH` pre-check (`check_nesting_depth`) to reject
//! pathologically deep input before the recursive verified expression parser
//! can overflow the stack.
//!
//! Limit: this module is unverified glue — it is NOT in `VERIFY_MODULES`. The
//! verified guarantees live in the modules it calls; the lexing and dispatch
//! here are plain Rust.

#[cfg(test)]
use std::ops::Add;

#[cfg(test)]
use super::stream::PeekStream;
#[cfg(test)]
use super::stream::TokenStream;
use super::{Keyword, Token, ast, verified_control};
#[cfg(test)]
use super::{float_trust, verified_integer};
use crate::errinput;
use crate::error::Result;
#[cfg(test)]
use crate::sql::types::DataType;

/// The SQL parser takes tokens from the lexer and parses the SQL syntax into an
/// Abstract Syntax Tree (AST).
///
/// The AST represents the syntactic structure of a SQL query (e.g. the SELECT
/// and FROM clauses, values, arithmetic expressions, etc.). However, it only
/// ensures the syntax is well-formed, and does not know whether e.g. a given
/// table or column exists or which kind of join to use -- that is the job of
/// the planner.
pub struct Parser;

/// The parser implementation, generic over its streaming token source.
///
/// This is the legacy handcrafted recursive-descent parser, retained only as a
/// `cfg(test)` differential oracle against the verified parser. Production code
/// never constructs it (see `Parser::parse`), so it is compiled out of
/// non-test builds — if any production path referenced it, the build would fail.
#[cfg(test)]
struct StreamingParser<S> {
    stream: S,
}

/// Robustness bound on expression nesting depth accepted by the parser.
///
/// The verified expression parser is recursive-descent, so deeply nested input
/// would overflow the stack and abort the process. This bound is a cheap O(n)
/// pre-check that rejects such input with a clean error instead of recursing.
///
/// The bound is set from measurement, not guesswork, and the measurement is of
/// the *worst input this guard admits*, not of each construct in isolation --
/// `check_nesting_depth` counts combined depth, so a staircase that interleaves
/// prefix operators with parentheses is admitted only to a fraction of 64. On
/// the default 2 MiB thread stack (`server.rs`, which spawns sessions via
/// `thread::scope` with no `stack_size` override), bisecting thread stack size
/// against the deepest admitted instance of every shape gives:
///
/// | shape                              | admitted | debug    | release |
/// |------------------------------------|----------|----------|---------|
/// | precedence ladder into a call      | 32       | 1101 KiB | 255 KiB |
/// | precedence ladder into parens      | 32       |  998 KiB | 231 KiB |
/// | `NOT 1 = (` staircase              | 64       |  896 KiB | 179 KiB |
/// | nested parentheses                 | 64       |  541 KiB |  87 KiB |
/// | `(1^` staircase                    | 32       |  462 KiB |  95 KiB |
/// | prefix `-` / `^` chain             | 64       |  207 KiB |  56 KiB |
/// | prefix-into-paren staircase        |  9       |  227 KiB |  55 KiB |
/// | function arguments                 | 63       |  151 KiB |  43 KiB |
///
/// The worst rows are shapes the guard counts *loosely*. It counts what nests
/// without bound (parens, prefix runs, `^` chains, call arguments) and ignores
/// the bounded extra: an infix operator whose precedence is strictly higher than
/// the enclosing one opens one more `parse_expression_at` frame for its right
/// operand, and there are only nine precedence levels, so a "ladder"
/// `1 OR 1 AND NOT 1 = 1 < 1 + 1 * 1 ^ f(` costs about eleven frames for the
/// two units the guard charges it. That is a constant factor, not a hole, and
/// the measured worst case is what the bound is judged against: 1101 KiB is
/// 54% of the stack in a debug build, a ~1.9x margin in the worst
/// configuration, and 12% in release, ~8x. Frames would have to grow by nearly
/// 2x in a debug build before the bound stopped holding.
/// `precedence_ladder_at_the_bound_fits_the_session_stack` pins the worst row
/// on a real 2 MiB thread.
///
/// An earlier bound of 256 was unsafe: it was calibrated against an 8 MiB main
/// thread (the "~937" figure in the history), and parses run on spawned threads
/// with 2 MiB. 64 is still far above any legitimate query -- nothing real nests
/// 64 parens, chains 64 unary minuses, or calls a function with 64 arguments --
/// so this changes behaviour only for pathological input, which no real query,
/// goldenscript, differential case, or corpus input reaches.
const MAX_NESTING_DEPTH: usize = 64;

/// One open parenthesis level in the `check_nesting_depth` scan (index 0 is the
/// statement level, which is never popped). Each field is a bucket of live
/// parser frames, released at a different point.
struct NestLevel {
    /// Prefix operators that were still awaiting their operand when this level
    /// opened. The parser parses the parenthesised operand *underneath* them,
    /// so they stay live until this level closes.
    prefix_held: usize,
    /// Function-call argument frames: `parse_fn_args_ne_exec` recurses per
    /// argument, and those frames live until the call's `)`.
    args: usize,
    /// `^` frames at this level. `^` is the one right-associative operator, so
    /// its right operand is parsed at the same precedence and nests for the
    /// whole chain; the chain completes at any lower-precedence operator, at a
    /// comma, or at `)`.
    carets: usize,
    /// Whether this paren opened a function call. Only a call's commas recurse.
    is_call: bool,
}

impl NestLevel {
    fn frames(&self) -> usize {
        self.prefix_held + self.args + self.carets
    }
}

/// Keywords after which a bare *name* follows rather than an expression. An
/// identifier in one of these positions is a table name, so a `(` after it
/// opens a DDL/DML column list -- parsed by a loop -- not a call.
fn introduces_name(token: &Token) -> bool {
    matches!(
        token,
        Token::Keyword(
            Keyword::Table | Keyword::Into | Keyword::From | Keyword::Join | Keyword::Update
        )
    )
}

/// Whether this token, appearing where an *operator* is expected, ends any `^`
/// chain open at the current level.
///
/// `^` is the highest-precedence infix operator, so in operator position every
/// operator listed here binds less tightly and terminates the chain, as does
/// any keyword -- a keyword in operator position is either a lower-precedence
/// infix operator (`AND`, `IS`, `LIKE`) or a clause boundary (`FROM`,
/// `WHERE`), and both end the expression the chain belongs to.
///
/// The `expect_operand` test is load-bearing, not a tidiness check. Where an
/// operand may start, these same tokens are not infix operators at all and the
/// chain recurses straight through them: `-`/`+` are *prefix* operators at
/// precedence 10 against `^`'s 8 (`verified_precedence.rs:72-78`, `:45-63`),
/// `*` is `Expression::All`, and `TRUE`/`FALSE`/`NULL`/`INFINITY`/`NAN` are
/// literal atoms. Clearing there let `2^-2^-2...` interleave a cleared counter
/// with unbounded real recursion and abort the process.
///
/// The list is an allowlist, and deliberately conservative: a token is in it
/// only if it provably cannot continue an operand. `.` is the reason this is
/// not simply "any token in operator position" -- `a.b` continues the operand
/// with the `^` frames still live underneath it. Erring towards not clearing
/// over-counts, which only rejects deeper input; clearing while the frames are
/// live under-counts and lets the parser overflow the stack.
fn closes_caret_chain(token: &Token, expect_operand: bool) -> bool {
    !expect_operand
        && matches!(
            token,
            Token::Keyword(_)
                | Token::Equal
                | Token::NotEqual
                | Token::GreaterThan
                | Token::GreaterThanOrEqual
                | Token::LessThan
                | Token::LessThanOrEqual
                | Token::LessOrGreaterThan
                | Token::Plus
                | Token::Minus
                | Token::Asterisk
                | Token::Slash
                | Token::Percent
        )
}

/// Rejects input whose parse would recurse deeper than `MAX_NESTING_DEPTH`.
///
/// This mirrors the recursion of `verified_precedence::parse_expression_at`,
/// which descends on exactly four things, each measured here:
///
/// * `(` -- a parenthesised subexpression or a call's argument list;
/// * a *prefix* `-`/`+`/`NOT` -- these stack while they await their operand.
///   They unwind once it arrives, but the operand may itself be a parenthesised
///   group or a call, which the parser descends into *underneath* them, so the
///   pending run is carried into that level rather than discarded;
/// * `^` -- the one right-associative operator, whose right operand is parsed
///   at the same precedence and so nests for the whole chain. Left-associative
///   operators are folded by `sparse_infix_loop` and do NOT recurse;
/// * a comma **inside a function call** -- `parse_fn_args_ne_exec` recurses per
///   argument.
///
/// Counting more than this would reject legitimate bulk input. Statement-level
/// lists (SELECT items, VALUES rows), row literals, and DDL/DML column lists
/// (`CREATE TABLE t (...)`, `INSERT INTO t (...)`) are all parsed by loops at
/// zero stack cost and must keep parsing however wide they get.
fn check_nesting_depth(tokens: &[Token]) -> Result<()> {
    let mut levels = vec![NestLevel { prefix_held: 0, args: 0, carets: 0, is_call: false }];
    // Frames held by every open level, maintained incrementally.
    let mut held_total: usize = 0;
    // Prefix operators at the current level still awaiting their operand.
    let mut prefix_run: usize = 0;
    // True where an operand may start, which is what distinguishes a prefix
    // `-`/`+` from an infix one.
    let mut expect_operand = true;
    // An identifier may be a call head, which is only settled by the NEXT
    // token, so its pending prefix run is released one token late.
    let mut ident_pending = false;
    let mut after_name_kw = false;

    for token in tokens {
        // An identifier that was not followed by `(` was a plain operand, so
        // the prefix operators awaiting it have now unwound.
        if ident_pending && !matches!(token, Token::OpenParen) {
            prefix_run = 0;
        }
        let call_head = ident_pending;
        ident_pending = false;

        if closes_caret_chain(token, expect_operand) {
            let level = levels.last_mut().expect("levels is non-empty");
            held_total -= level.carets;
            level.carets = 0;
        }

        match token {
            Token::OpenParen => {
                // The pending prefix frames stay live while the parser descends
                // into this group, so they are carried in and released at `)`.
                levels.push(NestLevel {
                    prefix_held: prefix_run,
                    args: 0,
                    carets: 0,
                    is_call: call_head,
                });
                held_total += prefix_run;
                prefix_run = 0;
                expect_operand = true;
            }
            Token::CloseParen => {
                if levels.len() > 1 {
                    let level = levels.pop().expect("levels is non-empty");
                    held_total -= level.frames();
                }
                prefix_run = 0;
                expect_operand = false;
            }
            Token::Comma => {
                let level = levels.last_mut().expect("levels is non-empty");
                held_total -= level.carets;
                level.carets = 0;
                if level.is_call {
                    level.args += 1;
                    held_total += 1;
                }
                prefix_run = 0;
                expect_operand = true;
            }
            Token::Minus | Token::Plus if expect_operand => prefix_run += 1,
            Token::Caret => {
                let level = levels.last_mut().expect("levels is non-empty");
                level.carets += 1;
                held_total += 1;
                expect_operand = true;
            }
            Token::Keyword(Keyword::Not) => {
                prefix_run += 1;
                expect_operand = true;
            }
            Token::Ident(_) if expect_operand => {
                if after_name_kw {
                    // A table name. A `(` after it opens a DDL/DML column
                    // list, which is parsed by a loop, not a call.
                    prefix_run = 0;
                } else {
                    // Settled on the next token: `(` makes this a call head.
                    ident_pending = true;
                }
                expect_operand = false;
            }
            Token::Number(_)
            | Token::String(_)
            | Token::Asterisk
            | Token::Keyword(Keyword::True | Keyword::False | Keyword::Null)
            | Token::Keyword(Keyword::Infinity | Keyword::NaN)
                if expect_operand =>
            {
                prefix_run = 0;
                expect_operand = false;
            }
            _ => {
                prefix_run = 0;
                expect_operand = true;
            }
        }

        after_name_kw = introduces_name(token);

        if levels.len() - 1 + held_total + prefix_run > MAX_NESTING_DEPTH {
            return errinput!("expression nesting too deep");
        }
    }
    Ok(())
}

impl Parser {
    /// Parses the input string into a SQL statement AST. The entire string must
    /// be parsed as a single statement, ending with an optional semicolon.
    ///
    /// Production parsing goes directly through the verified parser
    /// (`verified_control::parse_control_at`); it never touches the legacy
    /// recursive-descent `StreamingParser`, which is a `cfg(test)`-only
    /// differential oracle.
    pub fn parse(statement: &str) -> Result<ast::Statement> {
        let tokens: Vec<Token> = super::tokenize(statement)?;

        // Robustness guard: reject pathologically deep nesting up front, so the
        // recursive verified parser cannot overflow the stack and abort the
        // process. This is an O(n) scan over the token stream.
        check_nesting_depth(&tokens)?;

        let (opt, consumed, perr) = verified_control::parse_control_at(&tokens, 0);
        match opt {
            Some(statement) => {
                // Skip an optional trailing semicolon, then reject any leftover
                // tokens with the same error the legacy parser produced.
                let mut pos = consumed;
                if tokens.get(pos) == Some(&Token::Semicolon) {
                    pos += 1;
                }
                if let Some(token) = tokens.get(pos) {
                    return errinput!("unexpected token {token}");
                }
                Ok(statement)
            }
            None => Err(perr
                .expect("the verified parser always reports an error on rejection")
                .render()),
        }
    }

    #[cfg(test)]
    pub(crate) fn parse_legacy(statement: &str) -> Result<ast::Statement> {
        let mut parser = StreamingParser::new(TokenStream::new(statement));
        let statement = parser.parse_statement()?;
        parser.skip(Token::Semicolon);
        if let Some(token) = parser.stream.next()? {
            return errinput!("unexpected token {token}");
        }
        Ok(statement)
    }

    /// Parse the input string into a SQL expression AST. The entire string must
    /// be parsed as a single expression. Only used in tests.
    #[cfg(test)]
    pub fn parse_expr(expr: &str) -> Result<ast::Expression> {
        let tokens: Vec<Token> = super::tokenize(expr)?;
        check_nesting_depth(&tokens)?;
        let (opt, perr) = super::verified_precedence::parse_expression_full(&tokens);
        match opt {
            Some(expression) => Ok(expression),
            None => Err(perr
                .expect("the verified parser always reports an error on rejection")
                .render()),
        }
    }

    #[cfg(test)]
    pub(crate) fn parse_expr_legacy(expr: &str) -> Result<ast::Expression> {
        let mut parser = StreamingParser::new(TokenStream::new(expr));
        let expression = parser.parse_expression()?;
        if let Some(token) = parser.stream.next()? {
            return errinput!("unexpected token {token}");
        }
        Ok(expression)
    }
}

#[cfg(test)]
impl<S: PeekStream> StreamingParser<S> {
    /// Creates a parser over a streaming token source.
    fn new(stream: S) -> Self {
        Self { stream }
    }

    /// Fetches the next lexer token, or errors if none is found.
    fn next(&mut self) -> Result<Token> {
        self.stream.next()?.ok_or_else(|| errinput!("unexpected end of input"))
    }

    /// Returns the next identifier, or errors if not found.
    fn next_ident(&mut self) -> Result<String> {
        match self.next()? {
            Token::Ident(ident) => Ok(ident),
            token => errinput!("expected identifier, got {token}"),
        }
    }

    /// Returns the next lexer token if it satisfies the predicate.
    fn next_if(&mut self, predicate: impl Fn(&Token) -> bool) -> Option<Token> {
        self.peek().ok()?.filter(|t| predicate(t))?;
        self.next().ok()
    }

    /// Passes the next lexer token through the closure, consuming it if the
    /// closure returns Some. Returns the result of the closure.
    fn next_if_map<T>(&mut self, f: impl Fn(&Token) -> Option<T>) -> Option<T> {
        self.peek().ok()?.map(f)?.inspect(|_| drop(self.next()))
    }

    /// Returns the next keyword if there is one.
    fn next_if_keyword(&mut self) -> Option<Keyword> {
        self.next_if_map(|token| match token {
            Token::Keyword(keyword) => Some(*keyword),
            _ => None,
        })
    }

    /// Consumes the next lexer token if it is the given token, returning true.
    fn next_is(&mut self, token: Token) -> bool {
        self.next_if(|t| t == &token).is_some()
    }

    /// Consumes the next lexer token if it's the expected token, or errors.
    fn expect(&mut self, expect: Token) -> Result<()> {
        let token = self.next()?;
        if token != expect {
            return errinput!("expected token {expect}, found {token}");
        }
        Ok(())
    }

    /// Consumes the next lexer token if it is the given token. Equivalent to
    /// next_is(), but expresses intent better.
    fn skip(&mut self, token: Token) {
        self.next_is(token);
    }

    /// Peeks the next lexer token if any, but transposes it for convenience.
    fn peek(&mut self) -> Result<Option<&Token>> {
        self.stream.peek()
    }

    /// Parses a SQL statement.
    fn parse_statement(&mut self) -> Result<ast::Statement> {
        let Some(token) = self.peek()? else {
            return errinput!("unexpected end of input");
        };
        match token {
            Token::Keyword(Keyword::Begin) => self.parse_begin(),
            Token::Keyword(Keyword::Commit) => self.parse_commit(),
            Token::Keyword(Keyword::Rollback) => self.parse_rollback(),
            Token::Keyword(Keyword::Explain) => self.parse_explain(),

            Token::Keyword(Keyword::Create) => self.parse_create_table(),
            Token::Keyword(Keyword::Drop) => self.parse_drop_table(),

            Token::Keyword(Keyword::Delete) => self.parse_delete(),
            Token::Keyword(Keyword::Insert) => self.parse_insert(),
            Token::Keyword(Keyword::Select) => self.parse_select(),
            Token::Keyword(Keyword::Update) => self.parse_update(),

            token => errinput!("unexpected token {token}"),
        }
    }

    /// Parses a BEGIN statement.
    fn parse_begin(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Begin.into())?;
        self.skip(Keyword::Transaction.into());

        let mut read_only = false;
        if self.next_is(Keyword::Read.into()) {
            match self.next()? {
                Token::Keyword(Keyword::Only) => read_only = true,
                Token::Keyword(Keyword::Write) => {}
                token => return errinput!("unexpected token {token}"),
            }
        }

        let mut as_of = None;
        if self.next_is(Keyword::As.into()) {
            self.expect(Keyword::Of.into())?;
            self.expect(Keyword::System.into())?;
            self.expect(Keyword::Time.into())?;
            match self.next()? {
                Token::Number(n) => match verified_integer::parse_u64(&n) {
                    Some(version) => as_of = Some(version),
                    None => {
                        return errinput!("invalid system time {}", String::from_utf8_lossy(&n));
                    }
                },
                token => return errinput!("unexpected token {token}, wanted number"),
            }
        }
        Ok(ast::Statement::Begin { read_only, as_of })
    }

    /// Parses a COMMIT statement.
    fn parse_commit(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Commit.into())?;
        Ok(ast::Statement::Commit)
    }

    /// Parses a ROLLBACK statement.
    fn parse_rollback(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Rollback.into())?;
        Ok(ast::Statement::Rollback)
    }

    /// Parses an EXPLAIN statement.
    fn parse_explain(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Explain.into())?;
        if self.next_is(Keyword::Explain.into()) {
            return errinput!("cannot nest EXPLAIN statements");
        }
        Ok(ast::Statement::Explain(Box::new(self.parse_statement()?)))
    }

    /// Parses a CREATE TABLE statement.
    fn parse_create_table(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Create.into())?;
        self.expect(Keyword::Table.into())?;
        let name = self.next_ident()?;
        self.expect(Token::OpenParen)?;
        let mut columns = Vec::new();
        loop {
            columns.push(self.parse_create_table_column()?);
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        self.expect(Token::CloseParen)?;
        Ok(ast::Statement::CreateTable { name, columns })
    }

    /// Parses a CREATE TABLE column definition.
    fn parse_create_table_column(&mut self) -> Result<ast::Column> {
        let name = self.next_ident()?;
        let datatype = match self.next()? {
            Token::Keyword(Keyword::Bool | Keyword::Boolean) => DataType::Boolean,
            Token::Keyword(Keyword::Float | Keyword::Double) => DataType::Float,
            Token::Keyword(Keyword::Int | Keyword::Integer) => DataType::Integer,
            Token::Keyword(Keyword::String | Keyword::Text | Keyword::Varchar) => DataType::String,
            token => return errinput!("unexpected token {token}"),
        };
        let mut column = ast::Column {
            name,
            datatype,
            primary_key: false,
            nullable: None,
            default: None,
            unique: false,
            index: false,
            references: None,
        };
        while let Some(keyword) = self.next_if_keyword() {
            match keyword {
                Keyword::Primary => {
                    self.expect(Keyword::Key.into())?;
                    column.primary_key = true;
                }
                Keyword::Null => {
                    if column.nullable.is_some() {
                        return errinput!("nullability already set for column {}", column.name);
                    }
                    column.nullable = Some(true)
                }
                Keyword::Not => {
                    self.expect(Keyword::Null.into())?;
                    if column.nullable.is_some() {
                        return errinput!("nullability already set for column {}", column.name);
                    }
                    column.nullable = Some(false)
                }
                Keyword::Default => column.default = Some(self.parse_expression()?),
                Keyword::Unique => column.unique = true,
                Keyword::Index => column.index = true,
                Keyword::References => column.references = Some(self.next_ident()?),
                keyword => return errinput!("unexpected keyword {keyword}"),
            }
        }
        Ok(column)
    }

    /// Parses a DROP TABLE statement.
    fn parse_drop_table(&mut self) -> Result<ast::Statement> {
        self.expect(Token::Keyword(Keyword::Drop))?;
        self.expect(Token::Keyword(Keyword::Table))?;
        let mut if_exists = false;
        if self.next_is(Keyword::If.into()) {
            self.expect(Token::Keyword(Keyword::Exists))?;
            if_exists = true;
        }
        let name = self.next_ident()?;
        Ok(ast::Statement::DropTable { name, if_exists })
    }

    /// Parses a DELETE statement.
    fn parse_delete(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Delete.into())?;
        self.expect(Keyword::From.into())?;
        let table = self.next_ident()?;
        Ok(ast::Statement::Delete { table, where_clause: self.parse_where_clause()? })
    }

    /// Parses an INSERT statement.
    fn parse_insert(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Insert.into())?;
        self.expect(Keyword::Into.into())?;
        let table = self.next_ident()?;

        let mut columns = None;
        if self.next_is(Token::OpenParen) {
            let columns = columns.insert(Vec::new());
            loop {
                columns.push(self.next_ident()?);
                if !self.next_is(Token::Comma) {
                    break;
                }
            }
            self.expect(Token::CloseParen)?;
        }

        self.expect(Keyword::Values.into())?;

        let mut values = Vec::new();
        loop {
            let mut row = Vec::new();
            self.expect(Token::OpenParen)?;
            loop {
                row.push(self.parse_expression()?);
                if !self.next_is(Token::Comma) {
                    break;
                }
            }
            self.expect(Token::CloseParen)?;
            values.push(row);
            if !self.next_is(Token::Comma) {
                break;
            }
        }

        Ok(ast::Statement::Insert { table, columns, values })
    }

    /// Parses an UPDATE statement.
    fn parse_update(&mut self) -> Result<ast::Statement> {
        self.expect(Keyword::Update.into())?;
        let table = self.next_ident()?;
        self.expect(Keyword::Set.into())?;
        let mut set = std::collections::BTreeMap::new();
        loop {
            let column = self.next_ident()?;
            self.expect(Token::Equal)?;
            let expr = (!self.next_is(Keyword::Default.into()))
                .then(|| self.parse_expression())
                .transpose()?;
            if set.contains_key(&column) {
                return errinput!("column {column} set multiple times");
            }
            set.insert(column, expr);
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        Ok(ast::Statement::Update {
            table,
            set,
            order: ast::AssignOrder::placeholder(),
            where_clause: self.parse_where_clause()?,
        })
    }

    /// Parses a SELECT statement.
    fn parse_select(&mut self) -> Result<ast::Statement> {
        Ok(ast::Statement::Select {
            select: self.parse_select_clause()?,
            from: self.parse_from_clause()?,
            where_clause: self.parse_where_clause()?,
            group_by: self.parse_group_by_clause()?,
            having: self.parse_having_clause()?,
            order_by: self.parse_order_by_clause()?,
            limit: self.parse_limit_clause()?,
            offset: self.parse_offset_clause()?,
        })
    }

    /// Parses a SELECT clause, if present.
    fn parse_select_clause(&mut self) -> Result<Vec<(ast::Expression, Option<String>)>> {
        if !self.next_is(Keyword::Select.into()) {
            return Ok(Vec::new());
        }
        let mut select = Vec::new();
        loop {
            let expr = self.parse_expression()?;
            let mut alias = None;
            if self.next_is(Keyword::As.into()) || matches!(self.peek()?, Some(Token::Ident(_))) {
                if expr == ast::Expression::All {
                    return errinput!("can't alias *");
                }
                alias = Some(self.next_ident()?);
            }
            select.push((expr, alias));
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        Ok(select)
    }

    /// Parses a FROM clause, if present.
    fn parse_from_clause(&mut self) -> Result<Vec<ast::From>> {
        if !self.next_is(Keyword::From.into()) {
            return Ok(Vec::new());
        }
        let mut from = Vec::new();
        loop {
            let mut from_item = self.parse_from_table()?;
            while let Some(join_type) = self.parse_from_join()? {
                let left = Box::new(from_item);
                let right = Box::new(self.parse_from_table()?);
                let mut predicate = None;
                if join_type != ast::JoinType::Cross {
                    self.expect(Keyword::On.into())?;
                    predicate = Some(self.parse_expression()?)
                }
                from_item = ast::From::Join { left, right, join_type, predicate };
            }
            from.push(from_item);
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        Ok(from)
    }

    // Parses a FROM table.
    fn parse_from_table(&mut self) -> Result<ast::From> {
        let name = self.next_ident()?;
        let mut alias = None;
        if self.next_is(Keyword::As.into()) || matches!(self.peek()?, Some(Token::Ident(_))) {
            alias = Some(self.next_ident()?)
        };
        Ok(ast::From::Table { name, alias })
    }

    // Parses a FROM JOIN type, if present.
    fn parse_from_join(&mut self) -> Result<Option<ast::JoinType>> {
        if self.next_is(Keyword::Join.into()) {
            return Ok(Some(ast::JoinType::Inner));
        }
        if self.next_is(Keyword::Cross.into()) {
            self.expect(Keyword::Join.into())?;
            return Ok(Some(ast::JoinType::Cross));
        }
        if self.next_is(Keyword::Inner.into()) {
            self.expect(Keyword::Join.into())?;
            return Ok(Some(ast::JoinType::Inner));
        }
        if self.next_is(Keyword::Left.into()) {
            self.skip(Keyword::Outer.into());
            self.expect(Keyword::Join.into())?;
            return Ok(Some(ast::JoinType::Left));
        }
        if self.next_is(Keyword::Right.into()) {
            self.skip(Keyword::Outer.into());
            self.expect(Keyword::Join.into())?;
            return Ok(Some(ast::JoinType::Right));
        }
        Ok(None)
    }

    /// Parses a WHERE clause, if present.
    fn parse_where_clause(&mut self) -> Result<Option<ast::Expression>> {
        if !self.next_is(Keyword::Where.into()) {
            return Ok(None);
        }
        Ok(Some(self.parse_expression()?))
    }

    /// Parses a GROUP BY clause, if present.
    fn parse_group_by_clause(&mut self) -> Result<Vec<ast::Expression>> {
        if !self.next_is(Keyword::Group.into()) {
            return Ok(Vec::new());
        }
        let mut group_by = Vec::new();
        self.expect(Keyword::By.into())?;
        loop {
            group_by.push(self.parse_expression()?);
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        Ok(group_by)
    }

    /// Parses a HAVING clause, if present.
    fn parse_having_clause(&mut self) -> Result<Option<ast::Expression>> {
        if !self.next_is(Keyword::Having.into()) {
            return Ok(None);
        }
        Ok(Some(self.parse_expression()?))
    }

    /// Parses an ORDER BY clause, if present.
    fn parse_order_by_clause(&mut self) -> Result<Vec<(ast::Expression, ast::Direction)>> {
        if !self.next_is(Keyword::Order.into()) {
            return Ok(Vec::new());
        }
        let mut order_by = Vec::new();
        self.expect(Keyword::By.into())?;
        loop {
            let expr = self.parse_expression()?;
            let order = self
                .next_if_map(|token| match token {
                    Token::Keyword(Keyword::Asc) => Some(ast::Direction::Ascending),
                    Token::Keyword(Keyword::Desc) => Some(ast::Direction::Descending),
                    _ => None,
                })
                .unwrap_or_default();
            order_by.push((expr, order));
            if !self.next_is(Token::Comma) {
                break;
            }
        }
        Ok(order_by)
    }

    /// Parses a LIMIT clause, if present.
    fn parse_limit_clause(&mut self) -> Result<Option<ast::Expression>> {
        if !self.next_is(Keyword::Limit.into()) {
            return Ok(None);
        }
        Ok(Some(self.parse_expression()?))
    }

    /// Parses an OFFSET clause, if present.
    fn parse_offset_clause(&mut self) -> Result<Option<ast::Expression>> {
        if !self.next_is(Keyword::Offset.into()) {
            return Ok(None);
        }
        Ok(Some(self.parse_expression()?))
    }

    /// Parses an expression using the precedence climbing algorithm. See:
    ///
    /// <https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method>
    /// <https://eli.thegreenplace.net/2012/08/02/parsing-expressions-by-precedence-climbing>
    ///
    /// Expressions are made up of two main entities:
    ///
    /// * Atoms: values, variables, functions, and parenthesized expressions.
    /// * Operators: performs operations on atoms and sub-expressions.
    ///   * Prefix operators: e.g. `-a` or `NOT a`.
    ///   * Infix operators: e.g. `a + b`  or `a AND b`.
    ///   * Postfix operators: e.g. `a!` or `a IS NULL`.
    ///
    /// During parsing, we have to respect the mathematical precedence and
    /// associativity of operators. Consider e.g.:
    ///
    /// 2 ^ 3 ^ 2 - 4 * 3
    ///
    /// By the rules of precedence and associativity, this expression should
    /// be interpreted as:
    ///
    /// (2 ^ (3 ^ 2)) - (4 * 3)
    ///
    /// Specifically, the exponentiation operator ^ is right-associative, so it
    /// should be 2 ^ (3 ^ 2) = 512, not (2 ^ 3) ^ 2 = 64. Similarly,
    /// exponentiation and multiplication have higher precedence than
    /// subtraction, so it should be (2 ^ 3 ^ 2) - (4 * 3) = 500, not
    /// 2 ^ 3 ^ (2 - 4) * 3 = -3.24.
    ///
    /// To use precedence climbing, we first need to specify the relative
    /// precedence of operators as a number, where 1 is the lowest precedence:
    ///
    /// * 1: OR
    /// * 2: AND
    /// * 3: NOT
    /// * 4: =, !=, LIKE, IS
    /// * 5: <, <=, >, >=
    /// * 6: +, -
    /// * 7: *, /, %
    /// * 8: ^
    /// * 9: !
    /// * 10: +, - (prefix)
    ///
    /// We also have to specify the associativity of operators:
    ///
    /// * Right-associative: ^ and all prefix operators.
    /// * Left-associative: all other operators.
    ///
    /// Left-associative operators get a +1 to their precedence, so that they
    /// bind tighter to their left operand than right-associative operators.
    ///
    /// The precedence climbing algorithm works by recursively parsing the
    /// left-hand side of an expression (including any prefix operators), any
    /// infix operators and recursive right-hand side expressions, and finally
    /// any postfix operators.
    ///
    /// The grouping is determined by where the right-hand side recursion
    /// terminates. The algorithm will greedily consume as many operators as
    /// possible, but only as long as their precedence is greater than or equal
    /// to the precedence of the previous operator (hence the name "climbing").
    /// When we find an operator with lower precedence, we return the current
    /// expression up the recursion stack and resume parsing the operator at a
    /// lower precedence.
    ///
    /// The precedence levels for the previous example are as follows:
    ///
    ///     -----          Precedence 9: ^ right-associativity
    /// ---------          Precedence 9: ^
    ///             -----  Precedence 7: *
    /// -----------------  Precedence 6: -
    /// 2 ^ 3 ^ 2 - 4 * 3
    ///
    /// Let's walk through the recursive parsing of this expression:
    ///
    /// parse_expression_at(prec=0)
    ///   lhs = parse_expression_atom() = 2
    ///   op = parse_infix_operator(prec=0) = ^ (prec=9)
    ///   rhs = parse_expression_at(prec=9)
    ///     lhs = parse_expression_atom() = 3
    ///     op = parse_infix_operator(prec=9) = ^ (prec=9)
    ///     rhs = parse_expression_at(prec=9)
    ///       lhs = parse_expression_atom() = 2
    ///       op = parse_infix_operator(prec=9) = None (reject - at prec=6)
    ///       return lhs = 2
    ///     lhs = (lhs op rhs) = (3 ^ 2)
    ///     op = parse_infix_operator(prec=9) = None (reject - at prec=6)
    ///     return lhs = (3 ^ 2)
    ///   lhs = (lhs op rhs) = (2 ^ (3 ^ 2))
    ///   op = parse_infix_operator(prec=0) = - (prec=6)
    ///   rhs = parse_expression_at(prec=6)
    ///     lhs = parse_expression_atom() = 4
    ///     op = parse_infix_operator(prec=6) = * (prec=7)
    ///     rhs = parse_expression_at(prec=7)
    ///       lhs = parse_expression_atom() = 3
    ///       op = parse_infix_operator(prec=7) = None (end of expression)
    ///       return lhs = 3
    ///     lhs = (lhs op rhs) = (4 * 3)
    ///     op = parse_infix_operator(prec=6) = None (end of expression)
    ///     return lhs = (4 * 3)
    ///   lhs = (lhs op rhs) = ((2 ^ (3 ^ 2)) - (4 * 3))
    ///   op = parse_infix_operator(prec=0) = None (end of expression)
    ///   return lhs = ((2 ^ (3 ^ 2)) - (4 * 3))
    fn parse_expression(&mut self) -> Result<ast::Expression> {
        self.parse_expression_at(0)
    }

    /// Parses an expression at the given minimum precedence.
    fn parse_expression_at(&mut self, min_precedence: Precedence) -> Result<ast::Expression> {
        // If the left-hand side is a prefix operator, recursively parse it and
        // its operand. Otherwise, parse the left-hand side as an atom.
        let mut lhs = if let Some(prefix) = self.parse_prefix_operator_at(min_precedence) {
            let next_precedence = prefix.precedence() + prefix.associativity();
            let rhs = self.parse_expression_at(next_precedence)?;
            prefix.into_expression(rhs)
        } else {
            self.parse_expression_atom()?
        };

        // Apply any postfix operators to the left-hand side.
        while let Some(postfix) = self.parse_postfix_operator_at(min_precedence)? {
            lhs = postfix.into_expression(lhs)
        }

        // Repeatedly apply any infix operators to the left-hand side as long as
        // their precedence is greater than or equal to the current minimum
        // precedence (i.e. that of the upstack operator).
        //
        // The right-hand side expression parsing will recursively apply any
        // infix operators at or above this operator's precedence to the
        // right-hand side.
        while let Some(infix) = self.parse_infix_operator_at(min_precedence) {
            let next_precedence = infix.precedence() + infix.associativity();
            let rhs = self.parse_expression_at(next_precedence)?;
            lhs = infix.into_expression(lhs, rhs);
        }

        // Apply any postfix operators after the binary operator. Consider e.g.
        // 1 + NULL IS NULL.
        while let Some(postfix) = self.parse_postfix_operator_at(min_precedence)? {
            lhs = postfix.into_expression(lhs)
        }

        Ok(lhs)
    }

    /// Parses an expression atom. This is either:
    ///
    /// * A literal value.
    /// * A column name.
    /// * A function call.
    /// * A parenthesized expression.
    fn parse_expression_atom(&mut self) -> Result<ast::Expression> {
        Ok(match self.next()? {
            // All columns.
            Token::Asterisk => ast::Expression::All,

            // Literal value.
            Token::Number(n) if n.iter().all(u8::is_ascii_digit) => {
                match verified_integer::parse_i64(&n) {
                    Some(value) => ast::Literal::Integer(value).into(),
                    None => {
                        return errinput!("number too large to fit in target type");
                    }
                }
            }
            Token::Number(n) => match float_trust::parse_f64(&n) {
                Some(value) => ast::Literal::Float(value).into(),
                None => {
                    return errinput!("invalid float literal {}", String::from_utf8_lossy(&n));
                }
            },
            Token::String(s) => ast::Literal::String(s).into(),
            Token::Keyword(Keyword::True) => ast::Literal::Boolean(true).into(),
            Token::Keyword(Keyword::False) => ast::Literal::Boolean(false).into(),
            Token::Keyword(Keyword::Infinity) => ast::Literal::Float(f64::INFINITY).into(),
            Token::Keyword(Keyword::NaN) => {
                ast::Literal::Float(float_trust::canonical_nan()).into()
            }
            Token::Keyword(Keyword::Null) => ast::Literal::Null.into(),

            // Function call.
            Token::Ident(name) if self.next_is(Token::OpenParen) => {
                let mut args = Vec::new();
                while !self.next_is(Token::CloseParen) {
                    if !args.is_empty() {
                        self.expect(Token::Comma)?;
                    }
                    args.push(self.parse_expression()?);
                }
                ast::Expression::Function(name, args)
            }

            // Column name, either qualified as table.column or unqualified.
            Token::Ident(table) if self.next_is(Token::Period) => {
                ast::Expression::Column(Some(table), self.next_ident()?)
            }
            Token::Ident(column) => ast::Expression::Column(None, column),

            // Parenthesized expression.
            Token::OpenParen => {
                let expr = self.parse_expression()?;
                self.expect(Token::CloseParen)?;
                expr
            }

            token => return errinput!("expected expression atom, found {token}"),
        })
    }

    /// Parses a prefix operator, if there is one and its precedence is at least
    /// min_precedence.
    fn parse_prefix_operator_at(&mut self, min_precedence: Precedence) -> Option<PrefixOperator> {
        self.next_if_map(|token| {
            let operator = match token {
                Token::Keyword(Keyword::Not) => PrefixOperator::Not,
                Token::Minus => PrefixOperator::Minus,
                Token::Plus => PrefixOperator::Plus,
                _ => return None,
            };
            Some(operator).filter(|op| op.precedence() >= min_precedence)
        })
    }

    /// Parses an infix operator, if there is one and its precedence is at least
    /// min_precedence.
    fn parse_infix_operator_at(&mut self, min_precedence: Precedence) -> Option<InfixOperator> {
        self.next_if_map(|token| {
            let operator = match token {
                Token::Asterisk => InfixOperator::Multiply,
                Token::Caret => InfixOperator::Exponentiate,
                Token::Equal => InfixOperator::Equal,
                Token::GreaterThan => InfixOperator::GreaterThan,
                Token::GreaterThanOrEqual => InfixOperator::GreaterThanOrEqual,
                Token::Keyword(Keyword::And) => InfixOperator::And,
                Token::Keyword(Keyword::Like) => InfixOperator::Like,
                Token::Keyword(Keyword::Or) => InfixOperator::Or,
                Token::LessOrGreaterThan => InfixOperator::NotEqual,
                Token::LessThan => InfixOperator::LessThan,
                Token::LessThanOrEqual => InfixOperator::LessThanOrEqual,
                Token::Minus => InfixOperator::Subtract,
                Token::NotEqual => InfixOperator::NotEqual,
                Token::Percent => InfixOperator::Remainder,
                Token::Plus => InfixOperator::Add,
                Token::Slash => InfixOperator::Divide,
                _ => return None,
            };
            Some(operator).filter(|op| op.precedence() >= min_precedence)
        })
    }

    /// Parses a postfix operator, if there is one and its precedence is at
    /// least min_precedence.
    fn parse_postfix_operator_at(
        &mut self,
        min_precedence: Precedence,
    ) -> Result<Option<PostfixOperator>> {
        // Handle IS (NOT) NULL/NAN separately, since it's multiple tokens.
        if self.peek()? == Some(&Token::Keyword(Keyword::Is)) {
            // We can't consume tokens unless the precedence is satisfied, so we
            // assume IS NULL (they all have the same precedence).
            if PostfixOperator::Is(ast::Literal::Null).precedence() < min_precedence {
                return Ok(None);
            }
            self.expect(Keyword::Is.into())?;
            let not = self.next_is(Keyword::Not.into());
            let value = match self.next()? {
                Token::Keyword(Keyword::NaN) => ast::Literal::Float(float_trust::canonical_nan()),
                Token::Keyword(Keyword::Null) => ast::Literal::Null,
                token => return errinput!("unexpected token {token}"),
            };
            let operator = match not {
                false => PostfixOperator::Is(value),
                true => PostfixOperator::IsNot(value),
            };
            return Ok(Some(operator));
        }

        Ok(self.next_if_map(|token| {
            let operator = match token {
                Token::Exclamation => PostfixOperator::Factorial,
                _ => return None,
            };
            Some(operator).filter(|op| op.precedence() >= min_precedence)
        }))
    }
}

/// Operator precedence.
#[cfg(test)]
type Precedence = u8;

/// Operator associativity.
#[cfg(test)]
enum Associativity {
    Left,
    Right,
}

#[cfg(test)]
impl Add<Associativity> for Precedence {
    type Output = Self;

    fn add(self, rhs: Associativity) -> Self {
        // Left-associative operators have increased precedence, so they bind
        // tighter to their left-hand side.
        self + match rhs {
            Associativity::Left => 1,
            Associativity::Right => 0,
        }
    }
}

/// Prefix operators.
#[cfg(test)]
enum PrefixOperator {
    Minus, // -a
    Not,   // NOT a
    Plus,  // +a
}

#[cfg(test)]
impl PrefixOperator {
    /// The operator precedence.
    fn precedence(&self) -> Precedence {
        match self {
            Self::Not => 3,
            Self::Minus | Self::Plus => 10,
        }
    }

    // The operator associativity. Prefix operators are right-associative by
    // definition.
    fn associativity(&self) -> Associativity {
        Associativity::Right
    }

    /// Builds an AST expression for the operator.
    fn into_expression(self, rhs: ast::Expression) -> ast::Expression {
        let rhs = Box::new(rhs);
        match self {
            Self::Plus => ast::Operator::Identity(rhs).into(),
            Self::Minus => ast::Operator::Negate(rhs).into(),
            Self::Not => ast::Operator::Not(rhs).into(),
        }
    }
}

/// Infix operators.
#[cfg(test)]
enum InfixOperator {
    Add,                // a + b
    And,                // a AND b
    Divide,             // a / b
    Equal,              // a = b
    Exponentiate,       // a ^ b
    GreaterThan,        // a > b
    GreaterThanOrEqual, // a >= b
    LessThan,           // a < b
    LessThanOrEqual,    // a <= b
    Like,               // a LIKE b
    Multiply,           // a * b
    NotEqual,           // a != b
    Or,                 // a OR b
    Remainder,          // a % b
    Subtract,           // a - b
}

#[cfg(test)]
impl InfixOperator {
    /// The operator precedence.
    ///
    /// Mostly follows Postgres, except IS and LIKE having same precedence as =.
    /// This is similar to SQLite and MySQL.
    fn precedence(&self) -> Precedence {
        match self {
            Self::Or => 1,
            Self::And => 2,
            // Self::Not => 3
            Self::Equal | Self::NotEqual | Self::Like => 4, // also Self::Is
            Self::GreaterThan
            | Self::GreaterThanOrEqual
            | Self::LessThan
            | Self::LessThanOrEqual => 5,
            Self::Add | Self::Subtract => 6,
            Self::Multiply | Self::Divide | Self::Remainder => 7,
            Self::Exponentiate => 8,
        }
    }

    /// The operator associativity.
    fn associativity(&self) -> Associativity {
        match self {
            Self::Exponentiate => Associativity::Right,
            _ => Associativity::Left,
        }
    }

    /// Builds an AST expression for the infix operator.
    fn into_expression(self, lhs: ast::Expression, rhs: ast::Expression) -> ast::Expression {
        let (lhs, rhs) = (Box::new(lhs), Box::new(rhs));
        match self {
            Self::Add => ast::Operator::Add(lhs, rhs).into(),
            Self::And => ast::Operator::And(lhs, rhs).into(),
            Self::Divide => ast::Operator::Divide(lhs, rhs).into(),
            Self::Equal => ast::Operator::Equal(lhs, rhs).into(),
            Self::Exponentiate => ast::Operator::Exponentiate(lhs, rhs).into(),
            Self::GreaterThan => ast::Operator::GreaterThan(lhs, rhs).into(),
            Self::GreaterThanOrEqual => ast::Operator::GreaterThanOrEqual(lhs, rhs).into(),
            Self::LessThan => ast::Operator::LessThan(lhs, rhs).into(),
            Self::LessThanOrEqual => ast::Operator::LessThanOrEqual(lhs, rhs).into(),
            Self::Like => ast::Operator::Like(lhs, rhs).into(),
            Self::Multiply => ast::Operator::Multiply(lhs, rhs).into(),
            Self::NotEqual => ast::Operator::NotEqual(lhs, rhs).into(),
            Self::Or => ast::Operator::Or(lhs, rhs).into(),
            Self::Remainder => ast::Operator::Remainder(lhs, rhs).into(),
            Self::Subtract => ast::Operator::Subtract(lhs, rhs).into(),
        }
    }
}

/// Postfix operators.
#[cfg(test)]
enum PostfixOperator {
    Factorial,           // a!
    Is(ast::Literal),    // a IS NULL | NAN
    IsNot(ast::Literal), // a IS NOT NULL | NAN
}

#[cfg(test)]
impl PostfixOperator {
    // The operator precedence.
    fn precedence(&self) -> Precedence {
        match self {
            Self::Is(_) | Self::IsNot(_) => 4,
            Self::Factorial => 9,
        }
    }

    /// Builds an AST expression for the operator.
    fn into_expression(self, lhs: ast::Expression) -> ast::Expression {
        let lhs = Box::new(lhs);
        match self {
            Self::Factorial => ast::Operator::Factorial(lhs).into(),
            Self::Is(v) => ast::Operator::Is(lhs, v).into(),
            Self::IsNot(v) => ast::Operator::Not(ast::Operator::Is(lhs, v).into()).into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Parser;

    /// Pathologically deep parenthesis nesting is rejected with a clean error
    /// instead of overflowing the stack and aborting the process.
    #[test]
    fn deep_nesting_is_rejected_not_crashed() {
        let depth = 300;
        let mut sql = String::from("SELECT ");
        sql.push_str(&"(".repeat(depth));
        sql.push('1');
        sql.push_str(&")".repeat(depth));

        let result = Parser::parse(&sql);
        assert!(result.is_err(), "deeply nested input should be rejected, got {result:?}");
        assert!(
            result.unwrap_err().to_string().contains("nesting too deep"),
            "should report a nesting-depth error",
        );
    }

    /// A normal query with modest parenthesis nesting still parses.
    #[test]
    fn modest_nesting_still_parses() {
        Parser::parse("SELECT ((1 + 2) * (3 - 4))").expect("modest nesting should parse");
        Parser::parse("SELECT 1 WHERE (((1 = 1)))").expect("modest nesting should parse");
    }
}

#[cfg(test)]
mod nesting_depth_tests {
    use super::*;

    /// Every construct on which `parse_expression_at` recurses must be rejected
    /// with a clean error rather than overflowing the stack.
    ///
    /// Regression for a confirmed remote, pre-auth process kill: before the
    /// guard modelled them, each of these aborted the process. The paren case
    /// was guarded; the other four were not.
    #[test]
    fn deep_recursive_constructs_are_rejected_cleanly() {
        let n = 5_000;
        for sql in [
            format!("SELECT {}1{}", "(".repeat(n), ")".repeat(n)), // nested parens
            format!("SELECT {}1", "-".repeat(n)),                  // prefix minus
            format!("SELECT {}TRUE", "NOT ".repeat(n)),            // prefix NOT
            format!("SELECT 1{}", "^1".repeat(n)),                 // right-assoc chain
            format!("SELECT f(1{})", ",1".repeat(n)),              // function arguments
        ] {
            let err = Parser::parse(&sql).expect_err("should reject, not crash").to_string();
            assert!(err.contains("nesting too deep"), "wrong error for {:.32}: {err}", sql);
        }
    }

    /// The guard must not catch input the parser handles iteratively. Each of
    /// these is a flat construct parsed by a loop, so it costs no stack and
    /// must keep parsing however long it gets.
    #[test]
    fn bulk_iterative_constructs_still_parse() {
        let n = 5_000;
        for sql in [
            format!("SELECT 1{}", "+1".repeat(n)),     // left-assoc chain
            format!("SELECT 1{}", ",1".repeat(n)),     // SELECT list
            format!("SELECT -1{}", ",-1".repeat(n)),   // one prefix op per item
            format!("SELECT 1^1{}", ",1^1".repeat(n)), // one ^ per item
            format!("INSERT INTO t VALUES (1){}", ",(1)".repeat(n)), // rows
            format!("INSERT INTO t VALUES (1{})", ",1".repeat(n)), // row literal
        ] {
            assert!(Parser::parse(&sql).is_ok(), "should parse: {:.32}", sql);
        }
    }

    /// The worst input the guard admits must parse on the stack the server
    /// actually gives a session (2 MiB, `server.rs`). A strictly rising
    /// precedence chain opens one recursive right-operand frame per step, which
    /// the guard does not count -- there are only nine levels, so it is a
    /// bounded constant, not a hole -- and repeating the whole ladder into a call
    /// is the most stack-hungry shape per counted unit. Bisected: 1101 KiB in
    /// debug, 255 KiB in release, per the `MAX_NESTING_DEPTH` table. This runs
    /// the deepest admitted instance on a real 2 MiB thread, so a frame-size
    /// growth that closed the margin would fail here (by abort) rather than in
    /// production.
    #[test]
    fn precedence_ladder_at_the_bound_fits_the_session_stack() {
        // Each repetition charges the guard 2 units (the `^` and the paren).
        let n = MAX_NESTING_DEPTH / 2;
        let ladder = "1 OR 1 AND NOT 1 = 1 < 1 + 1 * 1 ^ f(".repeat(n);
        let sql = format!("SELECT {ladder}1{}", ")".repeat(n));
        let one_more =
            format!("SELECT {ladder}1 OR 1 AND NOT 1 = 1 < 1 + 1 * 1 ^ f(1{}", ")".repeat(n + 1));
        let handle = std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(move || {
                Parser::parse(&sql).expect("deepest admitted ladder should parse");
                let err = Parser::parse(&one_more).expect_err("one past the bound").to_string();
                assert!(err.contains("nesting too deep"), "wrong error: {err}");
            })
            .expect("spawn");
        handle.join().expect("ladder overflowed a 2 MiB stack");
    }

    /// The guard must measure *combined* depth, not each construct in
    /// isolation. Prefix frames stay live while the parser descends into a
    /// parenthesised operand or a call underneath them, so interleaving the two
    /// multiplies real depth. A staircase -- `n` prefix ops, `(`, `n-1` prefix
    /// ops, `(`, ... -- reached ~2080 live prefix frames while an earlier
    /// version of this guard never saw its running maximum exceed the bound,
    /// and aborted the process in a debug build.
    #[test]
    fn interleaved_prefix_and_parens_are_rejected() {
        for (open, close, lead) in [("(", ")", "-"), ("(", ")", "NOT "), ("f(", ")", "-")] {
            let mut sql = String::from("SELECT ");
            let mut depth = 0;
            for run in (1..=64).rev() {
                sql.push_str(&lead.repeat(run));
                sql.push_str(open);
                depth += 1;
            }
            sql.push('1');
            sql.push_str(&close.repeat(depth));
            let err = Parser::parse(&sql).expect_err("staircase should be rejected").to_string();
            assert!(err.contains("nesting too deep"), "staircase admitted: {err}");
        }
    }

    /// A `^` chain whose counter is cleared by an interleaved token, while the
    /// parser keeps recursing through it.
    ///
    /// Regression for a remote, pre-auth process abort in a *release* build:
    /// `closes_caret_chain` cleared the live `^`-frame count on `-`, `+`, `*`
    /// and on every keyword regardless of position. In operand position none of
    /// those ends a chain -- `-`/`+` are prefix operators that bind tighter
    /// than `^`, `*` is `Expression::All`, and `TRUE`/`NULL` are literal atoms
    /// -- so the counter was zeroed every other token while real depth grew
    /// once per `^`. `SELECT 2` + `^-2` x3000, about 9 KB, aborted the process.
    #[test]
    fn interrupted_caret_chains_are_rejected() {
        let n = 5_000;
        for sql in [
            format!("SELECT 2{}", "^-2".repeat(n)),        // prefix minus
            format!("SELECT 2{}", "^+2".repeat(n)),        // prefix plus
            format!("SELECT 2{}", "^*".repeat(n)),         // Expression::All
            format!("SELECT 2{}", "^NULL ".repeat(n)),     // literal atom
            format!("SELECT 2{}", "^TRUE ".repeat(n)),     // literal atom
            format!("SELECT 2{}", "^NOT TRUE ".repeat(n)), // prefix keyword
            format!("SELECT 2{}", "^-*".repeat(n)),        // prefix then All
        ] {
            let err = Parser::parse(&sql).expect_err("should reject, not crash").to_string();
            assert!(err.contains("nesting too deep"), "chain admitted for {:.32}: {err}", sql);
        }
    }

    /// The position test that fixes the case above must not make the guard
    /// reject ordinary SQL: a `^` chain really is complete at a lower-precedence
    /// infix operator or a clause keyword, so those still release its frames
    /// however many times a statement repeats them.
    #[test]
    fn caret_chains_closed_by_operators_and_clauses_still_parse() {
        let n = 1_000;
        for sql in [
            format!("SELECT 2^2{}", "+2^2".repeat(n)), // lower-precedence infix
            format!("SELECT 2^2{}", "*2^2".repeat(n)), // infix asterisk
            format!("SELECT 1 WHERE 2^2 = 4{}", " AND 2^2 = 4".repeat(n)), // keywords
            format!("SELECT 2{}", "^-2".repeat(MAX_NESTING_DEPTH / 2)), // under the bound
        ] {
            assert!(Parser::parse(&sql).is_ok(), "should parse: {:.48}", sql);
        }
    }

    /// Wide DDL/DML column lists are parsed by loops (`verified_control`), not
    /// by the recursive argument parser, so they must not be counted. The
    /// identifier before the paren is a table name, not a call head.
    #[test]
    fn wide_ddl_and_dml_column_lists_still_parse() {
        let cols = (0..500).map(|i| format!("c{i}")).collect::<Vec<_>>().join(",");
        let defs = (0..500).map(|i| format!("c{i} INT")).collect::<Vec<_>>().join(",");
        let vals = (0..500).map(|_| "1").collect::<Vec<_>>().join(",");
        for sql in
            [format!("CREATE TABLE t ({defs})"), format!("INSERT INTO t ({cols}) VALUES ({vals})")]
        {
            assert!(Parser::parse(&sql).is_ok(), "should parse: {:.48}", sql);
        }
    }

    /// The bound is inclusive, and input just under it still parses -- a guard
    /// that rejected everything would pass the test above vacuously.
    #[test]
    fn depth_at_the_bound_parses_and_past_it_does_not() {
        let at = MAX_NESTING_DEPTH;
        let over = MAX_NESTING_DEPTH + 1;
        assert!(Parser::parse(&format!("SELECT {}1", "-".repeat(at))).is_ok());
        assert!(Parser::parse(&format!("SELECT {}1", "-".repeat(over))).is_err());
        assert!(Parser::parse(&format!("SELECT {}1{}", "(".repeat(at), ")".repeat(at))).is_ok());
        assert!(
            Parser::parse(&format!("SELECT {}1{}", "(".repeat(over), ")".repeat(over))).is_err()
        );
    }
}
