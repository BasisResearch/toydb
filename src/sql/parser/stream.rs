//! Streaming token lookahead for the SQL parser.

use super::{Lexer, Token};
use crate::error::Result;

/// A token source with one-token lookahead.
pub(crate) trait PeekStream {
    /// Returns the next token without consuming it.
    fn peek(&mut self) -> Result<Option<&Token>>;

    /// Returns and consumes the next token.
    fn next(&mut self) -> Result<Option<Token>>;

    fn buffer(&self) -> Option<(&Vec<Token>, usize)> {
        None
    }

    fn set_pos(&mut self, _pos: usize) {}
}

pub(crate) struct BufferedTokenStream {
    tokens: Vec<Token>,
    pos: usize,
}

impl BufferedTokenStream {
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

/// A streaming lexer with a single cached token.
///
/// # Invariants
///
/// - `lookahead` contains at most one token or lexer error.
/// - Peeking never advances past the cached item.
#[cfg(test)]
pub(crate) struct TokenStream<'a> {
    lexer: Lexer<'a>,
    lookahead: Option<Result<Option<Token>>>,
}

#[cfg(test)]
impl<'a> TokenStream<'a> {
    /// Creates a token stream over `input`.
    pub(crate) fn new(input: &'a str) -> Self {
        Self { lexer: Lexer::new(input), lookahead: None }
    }

    fn read_next(&mut self) -> Result<Option<Token>> {
        self.lexer.next().transpose()
    }
}

#[cfg(test)]
impl PeekStream for TokenStream<'_> {
    fn peek(&mut self) -> Result<Option<&Token>> {
        if self.lookahead.is_none() {
            self.lookahead = Some(self.read_next());
        }
        match self.lookahead.as_ref().expect("lookahead was initialized") {
            Ok(token) => Ok(token.as_ref()),
            Err(error) => Err(error.clone()),
        }
    }

    fn next(&mut self) -> Result<Option<Token>> {
        match self.lookahead.take() {
            Some(result) => result,
            None => self.read_next(),
        }
    }
}

/// A borrowed token stream used to test the token-level parser contract.
#[cfg(test)]
pub(crate) struct SliceTokenStream<'a> {
    tokens: &'a [Token],
    pos: usize,
}

#[cfg(test)]
impl<'a> SliceTokenStream<'a> {
    pub(crate) fn new(tokens: &'a [Token]) -> Self {
        Self { tokens, pos: 0 }
    }
}

#[cfg(test)]
impl PeekStream for SliceTokenStream<'_> {
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
}

#[cfg(test)]
mod tests {
    use super::{PeekStream, TokenStream};
    use crate::sql::parser::Token;

    #[test]
    fn peek_preserves_the_next_token() {
        let mut stream = TokenStream::new("foo + 1");

        assert_eq!(stream.peek().unwrap(), Some(&Token::Ident("foo".into())));
        assert_eq!(stream.peek().unwrap(), Some(&Token::Ident("foo".into())));
        assert_eq!(stream.next().unwrap(), Some(Token::Ident("foo".into())));
        assert_eq!(stream.next().unwrap(), Some(Token::Plus));
    }

    #[test]
    fn end_of_input_is_stable() {
        let mut stream = TokenStream::new("");

        assert_eq!(stream.peek().unwrap(), None);
        assert_eq!(stream.next().unwrap(), None);
        assert_eq!(stream.peek().unwrap(), None);
    }

    #[test]
    fn peek_preserves_lexer_errors() {
        let mut stream = TokenStream::new("@");

        let first = stream.peek().unwrap_err();
        assert_eq!(stream.peek().unwrap_err(), first);
        assert_eq!(stream.next().unwrap_err(), first);
    }
}
