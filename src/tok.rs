//! Token Data Structure

use std::fmt;

#[derive(Clone, Copy)]
pub struct Token<'a> {
    pub line: u32,
    pub col: u32,
    pub text: &'a str,
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}>", self.text.escape_default().collect::<String>())
    }
}

impl<'a> fmt::Debug for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}>", self.text.escape_default().collect::<String>())
    }
}

impl<'a> Token<'a> {
    pub fn new(line: u32, col: u32, text: &'a str) -> Token<'a> {
        Token { line, col, text }
    }

    pub fn inner_str(&self) -> Option<Token> {
        if self.text.starts_with('"') && self.text.ends_with('"') {
            Some(Token::new(self.line, self.col, &self.text[1..self.text.len()-1]))
        } else {
            None
        }
    }
}
