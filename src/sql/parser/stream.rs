//! Streaming token lookahead for the SQL parser.

use super::{Lexer, Token};
use crate::error::Result;

/// A token source with one-token lookahead.
pub(crate) trait PeekStream {
    /// Returns the next token without consuming it.
    fn peek(&mut self) -> Result<Option<&Token>>;

    /// Returns and consumes the next token.
    fn next(&mut self) -> Result<Option<Token>>;

    /// The whole token vector and the current position, enabling the
    /// position-based Verus-verified parser to run at the cursor.
    fn buffer(&self) -> Option<(&Vec<Token>, usize)>;

    /// Repositions the cursor (paired with [`buffer`]).
    fn set_pos(&mut self, pos: usize);
}

/// A fully-buffered token source: the input is lexed up front into a vector, and
/// the cursor is an index. This backs the production parser's cutover to the
/// verified expression parser, which needs random access to the token vector.
pub(crate) struct BufferedTokenStream {
    tokens: Vec<Token>,
    pos: usize,
}

impl BufferedTokenStream {
    /// Lexes `input` fully into a buffered stream.
    pub(crate) fn new(input: &str) -> Result<Self> {
        let tokens: Vec<Token> = Lexer::new(input).collect::<Result<_>>()?;
        Ok(Self { tokens, pos: 0 })
    }
}

impl PeekStream for BufferedTokenStream {
    fn peek(&mut self) -> Result<Option<&Token>> {
        Ok(self.tokens.get(self.pos))
    }

    fn next(&mut self) -> Result<Option<Token>> {
        let token = self.tokens.get(self.pos).cloned();
        if token.is_some() {
            self.pos += 1;
        }
        Ok(token)
    }

    fn buffer(&self) -> Option<(&Vec<Token>, usize)> {
        Some((&self.tokens, self.pos))
    }

    fn set_pos(&mut self, pos: usize) {
        self.pos = pos;
    }
}

#[cfg(test)]
mod tests {
    use super::{BufferedTokenStream, PeekStream};
    use crate::sql::parser::Token;

    #[test]
    fn peek_preserves_the_next_token() {
        let mut stream = BufferedTokenStream::new("foo + 1").unwrap();

        assert_eq!(stream.peek().unwrap(), Some(&Token::Ident("foo".into())));
        assert_eq!(stream.peek().unwrap(), Some(&Token::Ident("foo".into())));
        assert_eq!(stream.next().unwrap(), Some(Token::Ident("foo".into())));
        assert_eq!(stream.next().unwrap(), Some(Token::Plus));
    }

    #[test]
    fn end_of_input_is_stable() {
        let mut stream = BufferedTokenStream::new("").unwrap();

        assert_eq!(stream.peek().unwrap(), None);
        assert_eq!(stream.next().unwrap(), None);
        assert_eq!(stream.peek().unwrap(), None);
    }

    #[test]
    fn lexer_errors_surface_at_construction() {
        // A buffered stream lexes eagerly, so an invalid token fails up front.
        assert!(BufferedTokenStream::new("@").is_err());
    }
}
