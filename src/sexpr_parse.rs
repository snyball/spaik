//! S-Expression Parser

use crate::perr::*;
use crate::tok::*;
use crate::ast::*;
use crate::error::Source;
use crate::r8vm::R8VM;
use crate::sym_db::SymDB;
use std::io;
use fnv::FnvHashMap;

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

/**
 * Find pairs of delimiters inside a token array.
 *
 * # Arguments
 *
 * - `pairs` : List of pairs, e.g [("(", ")"), ("[", "]"), ("{", "}")]
 * - `toks` : Token array.
 *
 * # Returns
 *
 * A hashmap `map`, where `map[idx]` contains the position of the closing
 * delimiter that closes the opening delimiter at `idx`
 *
 * # Time complexity
 *
 * O(n⋅m), where n is the number of tokens and m is the number of pairs.
*/
pub fn find_pairs(pairs: &[(&str, &str)], toks: &[Token]) -> PResult<FnvHashMap<u32, u32>>
{
    let mut st = vec![];
    let mut map = FnvHashMap::default();

    for (i, tok) in toks.iter().enumerate() {
        for (open, close) in pairs.iter() {
            if tok.text == *open {
                st.push((*open, i as u32));
            } else if tok.text == *close {
                let (delim, j) = st.pop()
                                   .ok_or_else(|| {
                                       mperr!(tok, "Trailing delimiter '{}'", *close)
                                   })?;
                if delim != *open {
                    return Err(mperr!(tok,
                                      "Closing delimiter '{}' does not match opening delimiter '{}'",
                                      *close, delim));
                }
                map.insert(j, i as u32);
            }
        }
    }

    if let Some((delim, i)) = st.pop() {
        return Err(mperr!(toks[i as usize], "Unclosed delimiter `{}`", delim))
    }

    Ok(map)
}

fn sexpr_modifier(tok: &str) -> Option<&'static str> {
    Some(match tok {
        "'" => "quote",
        "#" => "sys::hash",
        "#'" => "sys::closurize",
        "`" => "sys::quasi",
        "," => "sys::unquote",
        "@" => "sys::deref",
        ",@" => "sys::usplice",
        "¬" => "not",
        _ => return None,
    })
}

pub struct Parser<'b, 'c> {
    pairs: FnvHashMap<u32, u32>,
    toks: Vec<Token<'b>>,
    vm: &'c mut R8VM,
}

impl Parser<'_, '_> {
    pub fn parse(vm: &mut R8VM, text: &str) -> PResult<Value> {
        lazy_static! {
            static ref TREE: Fragment = standard_lisp_tok_tree();
        }
        let pairs = [("(", ")"), ("{", "}"), ("[", "]")];
        let toks = tokenize(text, &TREE)?;

        let len = toks.len();
        let pairs_lookup = find_pairs(&pairs, &toks)?;
        let mut parser = Parser {
            pairs: pairs_lookup,
            toks,
            vm
        };
        parser.parse_rec((0, len))
    }

    fn parse_rec(&mut self, range: (usize, usize)) -> PResult<Value> {
        let mut li: Vec<Value> = Vec::new();
        // Modifiers are sexprs that wrap other sexprs, i.e (quote ), (QUASI ),
        // or (QUASI (quote )).
        let mut mods = None;
        // Push a sexpr/atom, applying modifiers
        let mut push = |sub: Value, mods: &mut Option<Value>| {
            li.push(match mods.take() {
                Some(mut x) => {
                    x.pushdown(Box::new(sub));
                    x
                },
                None => sub,
            })
        };
        // Add a modifier to the next sexpr/atom
        macro_rules! modifier {($src:expr, $sub:expr) => {
            if let Some(ref mut x) = mods {
                x.pushdown(Box::new($sub))
            } else {
                mods = Some($sub)
            }
        }}
        let (beg, end) = range;
        let mut it = beg..end;
        while let Some(i) = it.next() {
            let Token { line, col, text } = self.toks[i];
            let mut inner = || {
                let j = self.pairs[&(i as u32)] as usize;
                (&mut it).take(j - i).for_each(drop);
                (i+1, j)
            };
            match &text[..] {
                "(" => {
                    let range = inner();
                    push(self.parse_rec(range)?, &mut mods)
                },
                _ => {
                    if let Some(m) = sexpr_modifier(text) {
                        let symdb: &mut dyn SymDB = &mut self.vm.mem;
                        let sym = Value::from_sym(symdb.put(m).into(),
                                                  Source::new(line, col));
                        let tail = Value::new_tail(Box::new(sym));
                        modifier!(src.clone(), tail);
                    } else {
                        push(Value::from_token(self.vm, &self.toks[i])?, &mut mods);
                    }
                }
            }
        }
        // Expressions like "(...) ``", or "(... |x y z|) (...)" are errors as there are
        // leftover modifiers that have not been applied to anything.
        if let Some(x) = mods {
            perr!(
                (0, 0),
                "Ends within object, do you have trailing (quasi)quotes? ({})",
                x
            );
        }
        Ok(li.into())
    }
}

#[derive(Hash, PartialEq, Eq)]
pub struct Fragment {
    end: bool,
    c: char,
    choices: Vec<Fragment>
}

/**
 * The result of an advancement on a token fragment tree.
 *
 * - `Advance`: The next node to follow.
 * - `Valid`: Means that the tree cannot progress using the given
 *            branch-character, *but* the current node is an end-node
 *            so it represents a valid operator. The character given
 *            to advance() when `Valid` is returned is *not* a part of
 *            the operator.
 * - `Invalid`: The input does not match any token in the tree, this means that
 *              you should backtrack.
*/
enum AdvanceResult<'a> {
    Advance(&'a Fragment),
    Valid,
    Invalid
}

/**
 * A fragment is a part of a operator/token lookup tree. To get a feel for how
 * it works, use the print_dot method on `standard_lisp_tok_tree()` with either
 * `&mut io::stdout()` or a file handle, then run the following command on your
 * generated file:
 *
 *    dot -Tsvg print_dot_output.dot > tree.svg
 *
 * Then open that svg file in your favorite browser (or Emacs) to see the
 * structure.
*/
impl Fragment {
    pub fn root() -> Fragment {
        Fragment { c: 'ɛ',
                   choices: Vec::new(),
                   end: false }
    }

    pub fn insert(&mut self, text: &str) {
        if text.is_empty() {
            self.end = true;
        } else if let Some(sub) = self.find_mut(text) {
            sub.insert(&text[1..]);
        } else {
            self.choices.push(Fragment { c: text.chars().next().unwrap(),
                                         choices: Default::default(),
                                         end: false });
            self.choices.last_mut()
                        .unwrap()
                        .insert(&text[1..])
        }
    }

    fn find_mut(&mut self, text: &str) -> Option<&mut Fragment> {
        self.choices
            .iter_mut()
            .find(|Fragment { c, .. }| text.starts_with(*c))
    }

    pub fn is_valid(&self) -> bool {
        self.end
    }

    /**
     * Advance forward to the next node in the tree, see the documentation for
     * AdvanceResult for more information.
     *
     * # Arguments
     *
     * - `nc` : Which character to branch on.
     */
    fn advance(&self, nc: char) -> AdvanceResult<'_> {
        use AdvanceResult::*;
        self.choices.iter()
                    .find(|Fragment { c, .. }| *c == nc)
                    .map(Advance)
                    .or_else(|| if self.end {
                        Some(Valid)
                    } else {
                        None
                    }).unwrap_or(Invalid)
    }

    /**
     * Print out the token fragment tree in the GraphViz dot [1] format.
     *
     * [1]: https://www.graphviz.org/documentation/
     *
     * # Arguments
     *
     * - `stream` : Output.
     */
    pub fn print_dot(&self, stream: &mut dyn io::Write) -> io::Result<()> {
        let mut cnt = 0;
        let mut roots = vec![(cnt, self)];
        writeln!(stream, "digraph tokens {{")?;
        writeln!(stream, r#"    end [label="end", shape=box, style=filled]"#)?;
        while let Some((id, root)) = roots.pop() {
            writeln!(stream, "    N{} [label={:?}];", id,
                   &[root.c].iter().collect::<String>())?;
            if root.end {
                writeln!(stream, "    N{} -> end;", id)?;
            }
            for sub in root.choices.iter() {
                cnt += 1;
                writeln!(stream, "    N{} -> N{};", id, cnt)?;
                roots.push((cnt, sub));
            }
        }
        writeln!(stream, "}}")
    }
}

#[derive(Default, Clone, Copy)]
struct TokRange {
    beg: usize,
    end: usize
}

impl TokRange {
    #[inline]
    pub fn new(beg: usize, end: usize) -> TokRange {
        TokRange { beg, end }
    }

    #[inline]
    pub fn on(beg: usize, c: char) -> TokRange {
        TokRange::new(beg, beg + c.len_utf8())
    }

    #[inline]
    pub fn at(beg: usize) -> TokRange {
        TokRange { beg, end: beg }
    }

    #[inline]
    pub fn advance(&mut self, c: char) {
        self.end += c.len_utf8();
    }

    #[inline]
    pub fn into_tok<'a>(&self, line: u32, col: u32, src: &'a str) -> Token<'a> {
        Token { line, col, text: &src[self.beg..self.end] }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.beg == self.end
    }

    #[inline]
    pub fn join(&self, o: &TokRange) -> TokRange {
        TokRange { beg: self.beg, end: o.end }
    }
}

enum TokState {
    Churn { acc: TokRange,
            start: LineTracker },
    InLineComment,
    InString { acc: TokRange,
               start: LineTracker,
               had_escape: bool },
    Done,
}

#[derive(Default, Clone, Copy)]
struct LineTracker {
    line: u32,
    col: u32
}

impl LineTracker {
    #[inline]
    pub fn step(&mut self, c: char) {
        if c == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
    }

    #[inline]
    pub fn get(&self) -> (u32, u32) {
        (self.line, self.col)
    }
}

pub fn standard_lisp_tok_tree() -> Fragment {
    const TOKS: &[&str] = &[",", ",@", "`", "(", ")", "#'", "#", "'"];
    let mut tree = Fragment::root();
    for tok in TOKS {
        tree.insert(tok);
    }
    tree
}

/// TODO: Change all of `acc` to `span`
pub fn tokenize<'a>(text: &'a str, frags: &Fragment) -> PResult<Vec<Token<'a>>> {
    use TokState::*;
    const COMMENT_CHAR: char = ';';
    const QUOTE_CHAR: char = '"';
    const ESCAPE_CHAR: char = '\\';
    let mut toks = vec![];
    let mut line_info = LineTracker::default();
    let mut state = TokState::Churn { acc: TokRange::at(0),
                                      start: line_info };
    let mut add_tok = |start: &LineTracker, acc: &TokRange| if !acc.is_empty() {
        let (line, col) = start.get();
        toks.push(acc.into_tok(line, col, text));
    };

    let mut it = text.char_indices().peekable();
    while let Some((i, c)) = it.next() {
        let next_range = move || TokRange::at(i + c.len_utf8());
        let churn = move || Churn { acc: next_range(),
                                    start: line_info };
        line_info.step(c);
        match state {
            InString { ref mut acc, ref mut had_escape, start } => {
                acc.advance(c);
                if *had_escape {
                    *had_escape = false;
                } else if c == ESCAPE_CHAR {
                    *had_escape = true;
                } else if c == QUOTE_CHAR {
                    add_tok(&start, acc);
                    state = churn();
                }
            }
            InLineComment if c == '\n' => state = churn(),
            InLineComment => (),
            Churn { acc, start } if c == COMMENT_CHAR => {
                add_tok(&start, &acc);
                state = InLineComment;
            }
            Churn { acc, start } if c == QUOTE_CHAR => {
                add_tok(&start, &acc);
                state = InString { acc: TokRange::on(i, c),
                                   had_escape: false,
                                   start: line_info };
            }
            Churn { ref mut acc, ref mut start } if c.is_whitespace() => {
                add_tok(start, acc);
                // Skip remaining whitespace
                *acc = loop {
                    match it.peek() {
                        Some((_, nc)) if nc.is_whitespace() => line_info.step(*nc),
                        Some((j, _)) => break TokRange::at(*j),
                        // Since we're at the end, we can set acc to *any* empty
                        // TokRange.
                        None => break TokRange::at(0),
                    }
                    it.next().unwrap();
                };
                *start = line_info;
            }
            Churn { ref mut acc, ref start } => match frags.advance(c) {
                AdvanceResult::Invalid => acc.advance(c),
                AdvanceResult::Valid => unreachable!(),
                // We've spotted what could possibly be the start of an
                // operator, we do 1-lookahead until either finding a valid
                // operator sequence, or ending with an invalid one.
                AdvanceResult::Advance(mut frag) => {
                    let op_start = line_info;
                    let mut op_span = TokRange::on(i, c);
                    state = loop {
                        if let Some((j, nc)) = it.peek() {
                            match frag.advance(*nc) {
                                AdvanceResult::Valid => {
                                    add_tok(start, acc);
                                    add_tok(&op_start, &op_span);
                                    break Churn { acc: TokRange::at(*j),
                                                  start: *start };
                                }
                                // Say `-->` is an operator, and you type
                                // thi--ng, when we reach `n` the token can no
                                // longer be `-->`, so we continue with symbol
                                // parsing.
                                AdvanceResult::Invalid =>
                                    break Churn { acc: acc.join(&op_span),
                                                  start: *start },
                                AdvanceResult::Advance(next) => {
                                    op_span.advance(c);
                                    frag = next
                                },
                            }
                            line_info.step(*nc);
                            it.next().unwrap();
                        } else if frag.is_valid() {
                            // Given `-->` is an operator, the input ended with
                            // something like `this-->`, which will be
                            // interpreted as [(this), (-->)]
                            add_tok(&start, &acc);
                            add_tok(&op_start, &op_span);
                            break Done
                        } else {
                            // Given `-->` is an operator, the input ended with
                            // something like `this--`, which will be a symbol.
                            add_tok(&start, &acc.join(&op_span));
                            break Done
                        }
                    }
                }
            }
            // The Done state is only reached when Churn has exhausted input.
            Done => unreachable!(),
        }
    }

    match state {
        InString { start, .. } =>
            perr!(start.get(), "Unterminated string"),
        Churn { acc, start } =>
            add_tok(&start, &acc),
        _ => ()
    }

    Ok(toks)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_test() {
        let text = "(progn `(loop (if (= x y) (break)) ((set x (+ x 1)))) (map #'print '(1e2 2e-2 3)))";
        let mut vm = R8VM::new();
        let res = Parser::parse(&mut vm, text).unwrap();
        println!("{}", res.to_string(&vm.mem));
    }

    #[test]
    fn tok_tree() {
        let toks = &[",", ",@", "`", "(", ")", "#'", "#", "'"];
        let mut tree = Fragment::root();
        for tok in toks {
            tree.insert(tok);
        }
        dbg!(tokenize("`(a,b`\"wasd\"#'w',@c);; wasd\nasd", &tree).unwrap());
    }
}
