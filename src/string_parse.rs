//! String parser

use crate::perr::*;
use crate::tok::*;

pub fn string_parse(tok: &Token) -> PResult<String> {
    let mut out = String::new();
    let mut it = tok.text.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            let c = it.next().ok_or(
                mperr!(tok, "Trailing escape character not allowed."))?;
            match c {
                '"' => out.push('"'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                '\\' => out.push('\\'),
                'z' => out.push('ζ'),
                'Z' => out.push('Ζ'),
                'x' => out.push('ξ'),
                'X' => out.push('Ξ'),
                'l' => out.push('λ'),
                'L' => out.push('Λ'),
                'F' => out.push('🔥'),
                '🐙' => out.push_str("Ph'nglui mglw'nafh Cthulhu R'lyeh wgah'nagl fhtagn"),
                '🚀' => out.push_str("ＳＥＥ　ＹＯＵ　ＳＰＡＣＥ　ＣＯＷＢＯＹ . . ."),
                _ => { out.push('\\'); out.push(c); }
            }
        } else {
            out.push(c);
        }
    }
    Ok(out)
}
