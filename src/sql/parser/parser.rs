use super::stream::{BufferedTokenStream, PeekStream};
#[cfg(test)]
use super::verified_precedence;
use super::{Token, ast, verified_control};
use crate::errinput;
use crate::error::Result;

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
struct StreamingParser<S> {
    stream: S,
}

impl Parser {
    /// Parses the input string into a SQL statement AST. The entire string must
    /// be parsed as a single statement, ending with an optional semicolon.
    pub fn parse(statement: &str) -> Result<ast::Statement> {
        // The input is lexed up front into a buffered token vector, and the
        // Verus-verified concrete parser runs at the cursor. The whole grammar —
        // every statement kind, every clause, every expression — is verified;
        // there is no recursive-descent fallback.
        let mut parser = StreamingParser::new(BufferedTokenStream::new(statement)?);
        let statement = parser.parse_statement()?;
        parser.skip(Token::Semicolon);
        if let Some(token) = parser.stream.next()? {
            return errinput!("unexpected token {token}");
        }
        Ok(statement)
    }

    /// Parse the input string into a SQL expression AST. The entire string must
    /// be parsed as a single expression. Only used in tests.
    ///
    /// Fully cut over to the Verus-verified precedence parser
    /// ([`verified_precedence::parse_expression_full`], proven to invert the
    /// canonical printer): it produces both the AST and, on rejection, the
    /// structured `ParseError` rendered to the production error string. No legacy
    /// fallback.
    #[cfg(test)]
    pub fn parse_expr(expr: &str) -> Result<ast::Expression> {
        let tokens: Vec<Token> = super::Lexer::new(expr).collect::<Result<_>>()?;
        let (opt, perr) = super::verified_precedence::parse_expression_full(&tokens);
        match opt {
            Some(expression) => Ok(expression),
            None => Err(perr
                .expect("the verified parser always reports an error on rejection")
                .render()),
        }
    }

    /// Parses a canonical token sequence as one complete expression, via the
    /// verified precedence parser. Used by the printer's roundtrip tests.
    #[cfg(test)]
    pub(crate) fn parse_expr_tokens(tokens: &[Token]) -> Result<ast::Expression> {
        let tokens = tokens.to_vec();
        let (expression, err) = verified_precedence::parse_expression_full(&tokens);
        match expression {
            Some(expression) => Ok(expression),
            None => {
                Err(err.expect("the verified parser always reports an error on rejection").render())
            }
        }
    }

    /// Parses a canonical token sequence as one complete statement, via the
    /// verified statement parser. Used by the printer's roundtrip tests.
    #[cfg(test)]
    pub(crate) fn parse_statement_tokens(tokens: &[Token]) -> Result<ast::Statement> {
        let tokens = tokens.to_vec();
        let (statement, consumed, err) = verified_control::parse_control_at(&tokens, 0);
        let statement = match statement {
            Some(statement) => statement,
            None => {
                return Err(err
                    .expect("the verified parser always reports an error on rejection")
                    .render());
            }
        };
        // Skip an optional trailing semicolon, then reject any leftover token.
        let mut end = consumed;
        if end < tokens.len() && tokens[end] == Token::Semicolon {
            end += 1;
        }
        if end < tokens.len() {
            return errinput!("unexpected token {}", tokens[end]);
        }
        Ok(statement)
    }
}

impl<S: PeekStream> StreamingParser<S> {
    /// Creates a parser over a streaming token source.
    fn new(stream: S) -> Self {
        Self { stream }
    }

    /// Fetches the next lexer token, or errors if none is found.
    fn next(&mut self) -> Result<Token> {
        self.stream.next()?.ok_or_else(|| errinput!("unexpected end of input"))
    }

    /// Returns the next lexer token if it satisfies the predicate.
    fn next_if(&mut self, predicate: impl Fn(&Token) -> bool) -> Option<Token> {
        self.peek().ok()?.filter(|t| predicate(t))?;
        self.next().ok()
    }

    /// Consumes the next lexer token if it is the given token, returning true.
    fn next_is(&mut self, token: Token) -> bool {
        self.next_if(|t| t == &token).is_some()
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

    /// Parses a SQL statement with the Verus-verified concrete statement parser,
    /// which handles every kind and produces the rejection error itself (rendered
    /// from its structured `ParseError`). The parser always runs over a buffered
    /// token stream in production.
    fn parse_statement(&mut self) -> Result<ast::Statement> {
        let (opt, consumed, perr) = {
            let (tokens, pos) =
                self.stream.buffer().expect("the parser always runs over a buffered token stream");
            verified_control::parse_control_at(tokens, pos)
        };
        match opt {
            Some(statement) => {
                self.stream.set_pos(consumed);
                Ok(statement)
            }
            None => Err(perr
                .expect("the verified parser always reports an error on rejection")
                .render()),
        }
    }
}
