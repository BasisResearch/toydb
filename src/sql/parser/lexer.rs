use std::fmt::Display;

use vstd::prelude::*;

use crate::errinput;
use crate::error::Result;

use super::unicode_trust;

verus! {

/// A lexical token.
///
/// These carry owned String clones rather than &str references into the
/// original input string, because the lexer may need to modify the string (e.g.
/// to parse escaped quotes in strings, lowercase identifiers, etc). We could
/// use `Cow<str>` to avoid this in the common case, but we'll end up using
/// owned strings in the final parsed AST anyway to avoid propagating these
/// lifetimes throughout the entire SQL execution engine, so we keep it simple.
#[derive(Debug, PartialEq)]
pub enum Token {
    /// A numeric string, with digits, decimal points, and/or exponents. Leading
    /// signs (e.g. -) are separate tokens.
    Number(Vec<u8>),
    /// A Unicode string, with quotes stripped and escape sequences resolved.
    String(String),
    /// An identifier, with any quotes stripped. Lowercased if not quoted.
    Ident(String),
    /// A SQL keyword.
    Keyword(Keyword),
    Period,             // .
    Equal,              // =
    NotEqual,           // !=
    GreaterThan,        // >
    GreaterThanOrEqual, // >=
    LessThan,           // <
    LessThanOrEqual,    // <=
    LessOrGreaterThan,  // <>
    Plus,               // +
    Minus,              // -
    Asterisk,           // *
    Slash,              // /
    Caret,              // ^
    Percent,            // %
    Exclamation,        // !
    Question,           // ?
    Comma,              // ,
    Semicolon,          // ;
    OpenParen,          // (
    CloseParen,         // )
}

} // verus!

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(match self {
            Self::Number(n) => return write!(f, "{}", String::from_utf8_lossy(n)),
            Self::String(s) => s,
            Self::Ident(s) => s,
            Self::Keyword(k) => return k.fmt(f),
            Self::Period => ".",
            Self::Equal => "=",
            Self::NotEqual => "!=",
            Self::GreaterThan => ">",
            Self::GreaterThanOrEqual => ">=",
            Self::LessThan => "<",
            Self::LessThanOrEqual => "<=",
            Self::LessOrGreaterThan => "<>",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Asterisk => "*",
            Self::Slash => "/",
            Self::Caret => "^",
            Self::Percent => "%",
            Self::Exclamation => "!",
            Self::Question => "?",
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::OpenParen => "(",
            Self::CloseParen => ")",
        })
    }
}

impl From<Keyword> for Token {
    fn from(keyword: Keyword) -> Self {
        Self::Keyword(keyword)
    }
}

verus! {

/// Reserved SQL keywords.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Keyword {
    And,
    As,
    Asc,
    Begin,
    Bool,
    Boolean,
    By,
    Commit,
    Create,
    Cross,
    Default,
    Delete,
    Desc,
    Double,
    Drop,
    Exists,
    Explain,
    False,
    Float,
    From,
    Group,
    Having,
    If,
    Index,
    Infinity,
    Inner,
    Insert,
    Int,
    Integer,
    Into,
    Is,
    Join,
    Key,
    Left,
    Like,
    Limit,
    NaN,
    Not,
    Null,
    Of,
    Offset,
    On,
    Only,
    Or,
    Order,
    Outer,
    Primary,
    Read,
    References,
    Right,
    Rollback,
    Select,
    Set,
    String,
    System,
    Table,
    Text,
    Time,
    Transaction,
    True,
    Unique,
    Update,
    Values,
    Varchar,
    Where,
    Write,
}

} // verus!

impl Clone for Token {
    fn clone(&self) -> Self {
        match self {
            Self::Number(value) => Self::Number(value.clone()),
            Self::String(value) => Self::String(value.clone()),
            Self::Ident(value) => Self::Ident(value.clone()),
            Self::Keyword(value) => Self::Keyword(*value),
            Self::Period => Self::Period,
            Self::Equal => Self::Equal,
            Self::NotEqual => Self::NotEqual,
            Self::GreaterThan => Self::GreaterThan,
            Self::GreaterThanOrEqual => Self::GreaterThanOrEqual,
            Self::LessThan => Self::LessThan,
            Self::LessThanOrEqual => Self::LessThanOrEqual,
            Self::LessOrGreaterThan => Self::LessOrGreaterThan,
            Self::Plus => Self::Plus,
            Self::Minus => Self::Minus,
            Self::Asterisk => Self::Asterisk,
            Self::Slash => Self::Slash,
            Self::Caret => Self::Caret,
            Self::Percent => Self::Percent,
            Self::Exclamation => Self::Exclamation,
            Self::Question => Self::Question,
            Self::Comma => Self::Comma,
            Self::Semicolon => Self::Semicolon,
            Self::OpenParen => Self::OpenParen,
            Self::CloseParen => Self::CloseParen,
        }
    }
}

verus! {

/// Scans the numeric token beginning at `start` with an explicit byte cursor.
#[allow(clippy::manual_range_contains)]
fn scan_number_bytes(input: &[u8], start: usize) -> (r: (Vec<u8>, usize))
    requires
        start < input@.len(),
        48u8 <= input@[start as int] <= 57u8,
    ensures
        start < r.1 <= input@.len(),
        r.0@ == input@.subrange(start as int, r.1 as int),
{
    let mut pos = start;
    let mut number = Vec::new();

    while pos < input.len() && 48u8 <= input[pos] && input[pos] <= 57u8
        invariant
            start <= pos <= input@.len(),
            number@ == input@.subrange(start as int, pos as int),
        decreases input.len() - pos,
    {
        number.push(input[pos]);
        pos += 1;
    }

    if pos < input.len() && input[pos] == b'.' {
        number.push(b'.');
        pos += 1;
        while pos < input.len() && 48u8 <= input[pos] && input[pos] <= 57u8
            invariant
                start < pos <= input@.len(),
                number@ == input@.subrange(start as int, pos as int),
            decreases input.len() - pos,
        {
            number.push(input[pos]);
            pos += 1;
        }
    }

    if pos < input.len() && (input[pos] == b'e' || input[pos] == b'E') {
        number.push(input[pos]);
        pos += 1;
        if pos < input.len() && (input[pos] == b'+' || input[pos] == b'-') {
            number.push(input[pos]);
            pos += 1;
        }
        while pos < input.len() && 48u8 <= input[pos] && input[pos] <= 57u8
            invariant
                start < pos <= input@.len(),
                number@ == input@.subrange(start as int, pos as int),
            decreases input.len() - pos,
        {
            number.push(input[pos]);
            pos += 1;
        }
    }

    (number, pos)
}

} // verus!

impl TryFrom<&str> for Keyword {
    // Use a cheap static error string. This just indicates it's not a keyword.
    type Error = &'static str;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        // Only compare lowercase, which is enforced by the lexer. This avoids
        // allocating a string to change the case. Assert this.
        debug_assert!(value.chars().all(|c| !c.is_uppercase()), "keyword must be lowercase");
        Ok(match value {
            "as" => Self::As,
            "asc" => Self::Asc,
            "and" => Self::And,
            "begin" => Self::Begin,
            "bool" => Self::Bool,
            "boolean" => Self::Boolean,
            "by" => Self::By,
            "commit" => Self::Commit,
            "create" => Self::Create,
            "cross" => Self::Cross,
            "default" => Self::Default,
            "delete" => Self::Delete,
            "desc" => Self::Desc,
            "double" => Self::Double,
            "drop" => Self::Drop,
            "exists" => Self::Exists,
            "explain" => Self::Explain,
            "false" => Self::False,
            "float" => Self::Float,
            "from" => Self::From,
            "group" => Self::Group,
            "having" => Self::Having,
            "if" => Self::If,
            "index" => Self::Index,
            "infinity" => Self::Infinity,
            "inner" => Self::Inner,
            "insert" => Self::Insert,
            "int" => Self::Int,
            "integer" => Self::Integer,
            "into" => Self::Into,
            "is" => Self::Is,
            "join" => Self::Join,
            "key" => Self::Key,
            "left" => Self::Left,
            "like" => Self::Like,
            "limit" => Self::Limit,
            "nan" => Self::NaN,
            "not" => Self::Not,
            "null" => Self::Null,
            "of" => Self::Of,
            "offset" => Self::Offset,
            "on" => Self::On,
            "only" => Self::Only,
            "or" => Self::Or,
            "order" => Self::Order,
            "outer" => Self::Outer,
            "primary" => Self::Primary,
            "read" => Self::Read,
            "references" => Self::References,
            "right" => Self::Right,
            "rollback" => Self::Rollback,
            "select" => Self::Select,
            "set" => Self::Set,
            "string" => Self::String,
            "system" => Self::System,
            "table" => Self::Table,
            "text" => Self::Text,
            "time" => Self::Time,
            "transaction" => Self::Transaction,
            "true" => Self::True,
            "unique" => Self::Unique,
            "update" => Self::Update,
            "values" => Self::Values,
            "varchar" => Self::Varchar,
            "where" => Self::Where,
            "write" => Self::Write,
            _ => return Err("not a keyword"),
        })
    }
}

impl Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // Display keywords as uppercase.
        f.write_str(match self {
            Self::As => "AS",
            Self::Asc => "ASC",
            Self::And => "AND",
            Self::Begin => "BEGIN",
            Self::Bool => "BOOL",
            Self::Boolean => "BOOLEAN",
            Self::By => "BY",
            Self::Commit => "COMMIT",
            Self::Create => "CREATE",
            Self::Cross => "CROSS",
            Self::Default => "DEFAULT",
            Self::Delete => "DELETE",
            Self::Desc => "DESC",
            Self::Double => "DOUBLE",
            Self::Drop => "DROP",
            Self::Exists => "EXISTS",
            Self::Explain => "EXPLAIN",
            Self::False => "FALSE",
            Self::Float => "FLOAT",
            Self::From => "FROM",
            Self::Group => "GROUP",
            Self::Having => "HAVING",
            Self::If => "IF",
            Self::Index => "INDEX",
            Self::Infinity => "INFINITY",
            Self::Inner => "INNER",
            Self::Insert => "INSERT",
            Self::Int => "INT",
            Self::Integer => "INTEGER",
            Self::Into => "INTO",
            Self::Is => "IS",
            Self::Join => "JOIN",
            Self::Key => "KEY",
            Self::Left => "LEFT",
            Self::Like => "LIKE",
            Self::Limit => "LIMIT",
            Self::NaN => "NAN",
            Self::Not => "NOT",
            Self::Null => "NULL",
            Self::Of => "OF",
            Self::Offset => "OFFSET",
            Self::On => "ON",
            Self::Only => "ONLY",
            Self::Outer => "OUTER",
            Self::Or => "OR",
            Self::Order => "ORDER",
            Self::Primary => "PRIMARY",
            Self::Read => "READ",
            Self::References => "REFERENCES",
            Self::Right => "RIGHT",
            Self::Rollback => "ROLLBACK",
            Self::Select => "SELECT",
            Self::Set => "SET",
            Self::String => "STRING",
            Self::System => "SYSTEM",
            Self::Table => "TABLE",
            Self::Text => "TEXT",
            Self::Time => "TIME",
            Self::Transaction => "TRANSACTION",
            Self::True => "TRUE",
            Self::Unique => "UNIQUE",
            Self::Update => "UPDATE",
            Self::Values => "VALUES",
            Self::Varchar => "VARCHAR",
            Self::Where => "WHERE",
            Self::Write => "WRITE",
        })
    }
}

/// The lexer (lexical analyzer) preprocesses raw SQL strings into a sequence of
/// lexical tokens (e.g. keyword, number, string, etc), which are passed on to
/// the SQL parser. In doing so, it strips away basic syntactic noise such as
/// whitespace, case, and quotes, and performs initial symbol validation.
pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

/// The lexer is used as a token iterator.
impl Iterator for Lexer<'_> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Result<Token>> {
        match self.scan() {
            Ok(Some(token)) => Some(Ok(token)),
            // If there's any remaining chars, the lexer didn't recognize them.
            Ok(None) => self.peek().map(|c| errinput!("unexpected character {c}")),
            Err(err) => Some(Err(err)),
        }
    }
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given string.
    pub fn new(input: &'a str) -> Lexer<'a> {
        Lexer { input, pos: 0 }
    }

    /// Returns the next character without consuming it.
    fn peek(&self) -> Option<char> {
        self.input.get(self.pos..)?.chars().next()
    }

    /// Returns and consumes the next character.
    fn next_char(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    /// Returns the next character if it satisfies the predicate.
    fn next_if(&mut self, predicate: impl Fn(char) -> bool) -> Option<char> {
        self.peek().filter(|&c| predicate(c))?;
        self.next_char()
    }

    /// Returns true if the next character is the given character, consuming it.
    fn next_is(&mut self, c: char) -> bool {
        self.next_if(|n| n == c).is_some()
    }

    /// Scans the next token, if any.
    fn scan(&mut self) -> Result<Option<Token>> {
        // Ignore whitespace.
        self.skip_whitespace();
        let Some(c) = self.peek() else {
            return Ok(None);
        };
        // The first character tells us the token kind. Scan it accordingly.
        match c {
            '\'' => self.scan_string(),
            '"' => self.scan_ident_quoted(),
            '0'..='9' => Ok(self.scan_number()),
            c if unicode_trust::is_alphabetic(c) => Ok(self.scan_ident_or_keyword()),
            _ => Ok(self.scan_symbol()),
        }
    }

    /// Scans the next identifier or keyword, if any. It's converted to
    /// lowercase, by SQL convention.
    fn scan_ident_or_keyword(&mut self) -> Option<Token> {
        // The first character must be alphabetic. The rest can be numeric.
        let first = self.next_if(unicode_trust::is_alphabetic)?;
        let mut name: String = unicode_trust::lowercase(first).into_iter().collect();
        while let Some(c) = self.next_if(|c| unicode_trust::is_alphanumeric(c) || c == '_') {
            name.extend(unicode_trust::lowercase(c))
        }
        // Check if the identifier matches a keyword.
        if let Ok(keyword) = Keyword::try_from(name.as_str()) {
            return Some(Token::Keyword(keyword));
        }
        Some(Token::Ident(name))
    }

    /// Scans the next quoted identifier, if any. Case is preserved.
    fn scan_ident_quoted(&mut self) -> Result<Option<Token>> {
        if !self.next_is('"') {
            return Ok(None);
        }
        let mut ident = String::new();
        loop {
            match self.next_char() {
                // "" is the escape sequence for ".
                Some('"') if self.next_is('"') => ident.push('"'),
                Some('"') => break,
                Some(c) => ident.push(c),
                None => return errinput!("unexpected end of quoted identifier"),
            }
        }
        Ok(Some(Token::Ident(ident)))
    }

    /// Scans the next number, if any.
    fn scan_number(&mut self) -> Option<Token> {
        let start = self.pos;
        let first = *self.input.as_bytes().get(start)?;
        if !first.is_ascii_digit() {
            return None;
        }
        let (number, end) = scan_number_bytes(self.input.as_bytes(), start);
        self.pos = end;
        Some(Token::Number(number))
    }

    /// Scans the next quoted string literal, if any.
    fn scan_string(&mut self) -> Result<Option<Token>> {
        if !self.next_is('\'') {
            return Ok(None);
        }
        let mut string = String::new();
        loop {
            match self.next_char() {
                // '' is the escape sequence for '.
                Some('\'') if self.next_is('\'') => string.push('\''),
                Some('\'') => break,
                Some(c) => string.push(c),
                None => return errinput!("unexpected end of string literal"),
            }
        }
        Ok(Some(Token::String(string)))
    }

    /// Scans the next symbol token, if any.
    ///
    /// Routes through the verified `scan_symbol_bytes` (a sound single-implementation
    /// cutover, like `scan_number_bytes`): symbols are ASCII and UTF-8 is
    /// self-synchronising, so byte-level scanning matches the former char-level
    /// behaviour exactly. Two-character operators (`!=`, `<=`, `>=`, `<>`) are
    /// handled inside the verified scanner via maximal munch.
    fn scan_symbol(&mut self) -> Option<Token> {
        let (token, next_pos) =
            super::verified_lexer::scan_symbol_bytes(self.input.as_bytes(), self.pos);
        self.pos = next_pos;
        token
    }

    /// Skips any whitespace.
    fn skip_whitespace(&mut self) {
        while self.next_if(|c| c.is_whitespace()).is_some() {}
    }
}

/// Returns true if the entire given string is a single valid identifier.
pub fn is_ident(ident: &str) -> bool {
    let mut lexer = Lexer::new(ident);
    let Some(Ok(Token::Ident(_))) = lexer.next() else {
        return false;
    };
    lexer.next().is_none() // if further tokens, it's not a lone identifier
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Error;

    #[test]
    fn cursor_peek_and_next_advance_by_utf8_bytes() {
        let mut lexer = Lexer::new("  é + α");

        assert_eq!(lexer.pos, 0);
        assert_eq!(lexer.peek(), Some(' '));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("é".into()))));
        assert_eq!(lexer.pos, 4);
        assert_eq!(lexer.peek(), Some(' '));
        assert_eq!(lexer.next(), Some(Ok(Token::Plus)));
        assert_eq!(lexer.pos, 6);
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("α".into()))));
        assert_eq!(lexer.pos, "  é + α".len());
        assert_eq!(lexer.peek(), None);
    }

    #[test]
    fn unicode_identifiers_and_string_payloads_are_preserved() {
        let tokens: Vec<_> =
            Lexer::new("ÄBC \"MiXeD\" 'café''s'").collect::<Result<Vec<_>>>().unwrap();

        assert_eq!(
            tokens,
            vec![
                Token::Ident("äbc".into()),
                Token::Ident("MiXeD".into()),
                Token::String("café's".into()),
            ]
        );
    }

    #[test]
    fn numeric_scanner_preserves_the_consumed_ascii_slice() {
        let tokens = Lexer::new("12 3.5 6e-7 8E+9").collect::<Result<Vec<_>>>().unwrap();

        assert_eq!(
            tokens,
            vec![
                Token::Number(b"12".to_vec()),
                Token::Number(b"3.5".to_vec()),
                Token::Number(b"6e-7".to_vec()),
                Token::Number(b"8E+9".to_vec()),
            ]
        );
    }

    #[test]
    fn invalid_character_is_reported_without_advancing_cursor() {
        let mut lexer = Lexer::new("$");

        assert_eq!(lexer.next(), Some(Err(Error::InvalidInput("unexpected character $".into()))));
        assert_eq!(lexer.pos, 0);
        assert_eq!(lexer.peek(), Some('$'));
    }

    #[test]
    fn unterminated_payloads_are_errors() {
        assert_eq!(
            Lexer::new("'unterminated").next(),
            Some(Err(Error::InvalidInput("unexpected end of string literal".into())))
        );
        assert_eq!(
            Lexer::new("\"unterminated").next(),
            Some(Err(Error::InvalidInput("unexpected end of quoted identifier".into())))
        );
    }
}
