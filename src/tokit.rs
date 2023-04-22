//! S-Expression Tokenizer

use crate::error::ErrorKind;
use crate::error::LineCol;
use crate::error::Meta;
use crate::tok::*;
use crate::error::Error;
use std::collections::VecDeque;
use std::io;
use std::iter::Peekable;
use std::str::CharIndices;

#[derive(Hash, PartialEq, Eq, Debug, Clone)]
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
                    .or(if self.end {
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
    #[allow(dead_code)]
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

#[derive(Default, Clone, Copy, PartialEq, Eq)]
struct Span {
    beg: usize,
    end: usize
}

impl Span {
    #[inline]
    pub fn new(beg: usize, end: usize) -> Span {
        Span { beg, end }
    }

    #[inline]
    pub fn on(beg: usize, c: char) -> Span {
        Span::new(beg, beg + c.len_utf8())
    }

    #[inline]
    pub fn at(beg: usize) -> Span {
        Span { beg, end: beg }
    }

    #[inline]
    pub fn advance(&mut self, c: char) {
        self.end += c.len_utf8();
    }

    #[inline]
    pub fn make_tok<'a>(&self, line: u32, col: u32, src: &'a str) -> Token<'a> {
        Token { line, col, text: &src[self.beg..self.end] }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.beg == self.end
    }

    #[inline]
    pub fn join(&self, o: &Span) -> Span {
        Span { beg: self.beg, end: o.end }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TokState {
    Churn { span: Span,
            start: LineTracker },
    InLineComment,
    InString { span: Span,
               start: LineTracker,
               had_escape: bool },
    Done,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct LineTracker {
    line: u32,
    col: u32
}

impl Default for LineTracker {
    fn default() -> Self {
        Self { line: 1,
               col: Default::default() }
    }
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

pub struct Toker<'a, 'b> {
    line_tracker: LineTracker,
    state: TokState,
    text: &'a str,
    frags: &'b Fragment,
    it: Peekable<CharIndices<'a>>,
    toks: VecDeque<Token<'a>>,
    err: Option<Error>,
}

impl<'a> Toker<'a, '_> {
    pub fn new<'b>(text: &'a str, frags: &'b Fragment) -> Toker<'a, 'b> {
        let line_tracker = LineTracker::default();
        Toker { line_tracker,
                state: TokState::Churn { span: Span::at(0),
                                         start: line_tracker },
                text,
                frags,
                it: text.char_indices().peekable(),
                toks: Default::default(),
                err: None }
    }

    pub fn check_error(&mut self) -> Result<(), Error> {
        self.err.take().map(Err).unwrap_or(Ok(()))
    }

    fn add_tok(&mut self, start: &LineTracker, span: &Span) {
        if !span.is_empty() {
            let (line, col) = start.get();
            self.toks.push_back(span.make_tok(line, col, self.text));
        }
    }

    pub fn peek(&mut self) -> Option<Token<'a>> {
        self.toks.front().copied().or_else(|| {
            self.advance();
            self.toks.front().copied()
        })
    }

    fn advance(&mut self) {
        use TokState::*;
        const COMMENT_CHAR: char = ';';
        const QUOTE_CHAR: char = '"';
        const ESCAPE_CHAR: char = '\\';

        let num_toks = self.toks.len();
        while num_toks == self.toks.len() {
            let Some((i, c)) = self.it.next() else {
                if self.state == Done { return }
                match self.state {
                    InString { start, .. } =>
                        self.err = Some(
                            Error::new(ErrorKind::UnterminatedString)
                                .amend(Meta::Source(start.into()))
                        ),
                    Churn { span, start } =>
                        self.add_tok(&start, &span),
                    _ => ()
                }
                self.state = Done;
                return;
            };

            let next_range = move || Span::at(i + c.len_utf8());
            let line_tracker = self.line_tracker;
            let churn = move || Churn { span: next_range(),
                                        start: line_tracker };
            self.line_tracker.step(c);

            let mut state = self.state;
            match state {
                InString { ref mut span, ref mut had_escape, start } => {
                    span.advance(c);
                    if *had_escape {
                        *had_escape = false;
                    } else if c == ESCAPE_CHAR {
                        *had_escape = true;
                    } else if c == QUOTE_CHAR {
                        self.add_tok(&start, span);
                        state = churn();
                    }
                }
                InLineComment if c == '\n' => state = churn(),
                InLineComment => (),
                Churn { span, start } if c == COMMENT_CHAR => {
                    self.add_tok(&start, &span);
                    state = InLineComment;
                }
                Churn { span, start } if c == QUOTE_CHAR => {
                    self.add_tok(&start, &span);
                    state = InString { span: Span::on(i, c),
                                       had_escape: false,
                                       start: self.line_tracker };
                }
                Churn { ref mut span, ref mut start } if c.is_whitespace() => {
                    self.add_tok(start, span);
                    // Skip remaining whitespace
                    *span = loop {
                        match self.it.peek() {
                            Some((_, nc)) if nc.is_whitespace() =>
                                self.line_tracker.step(*nc),
                            Some((j, _)) => break Span::at(*j),
                            // Since we're at the end, we can set span to *any* empty
                            // Span.
                            None => break Span::at(0),
                        }
                        self.it.next().unwrap();
                    };
                    *start = self.line_tracker;
                }
                Churn { ref mut span, ref start } => match self.frags.advance(c) {
                    AdvanceResult::Invalid => span.advance(c),
                    AdvanceResult::Valid => unreachable!(),
                    // We've spotted what could possibly be the start of an
                    // operator, we do 1-lookahead until either finding a valid
                    // operator sequence, or ending with an invalid one.
                    AdvanceResult::Advance(mut frag) => {
                        let op_start = self.line_tracker;
                        let mut op_span = Span::on(i, c);
                        state = loop {
                            if let Some((j, nc)) = self.it.peek().copied() {
                                match frag.advance(nc) {
                                    AdvanceResult::Valid => {
                                        self.add_tok(start, span);
                                        self.add_tok(&op_start, &op_span);
                                        break Churn { span: Span::at(j),
                                                      start: *start };
                                    }
                                    // Say `-->` is an operator, and you type
                                    // thi--ng, when we reach `n` the token can no
                                    // longer be `-->`, so we continue with symbol
                                    // parsing.
                                    AdvanceResult::Invalid =>
                                        break Churn { span: span.join(&op_span),
                                                      start: *start },
                                    AdvanceResult::Advance(next) => {
                                        op_span.advance(c);
                                        frag = next
                                    },
                                }
                                self.line_tracker.step(nc);
                                self.it.next().unwrap();
                            } else if frag.is_valid() {
                                // Given `-->` is an operator, the input ended with
                                // something like `this-->`, which will be
                                // interpreted as [(this), (-->)]
                                self.add_tok(start, span);
                                self.add_tok(&op_start, &op_span);
                                break Done
                            } else {
                                // Given `-->` is an operator, the input ended with
                                // something like `this--`, which will be a symbol.
                                self.add_tok(start, &span.join(&op_span));
                                break Done
                            }
                        }
                    }
                }
                // The Done state is only reached when Churn has exhausted input.
                Done => unreachable!(),
            }
            self.state = state;
        }
    }
}

impl Into<LineCol> for LineTracker {
    fn into(self) -> LineCol {
        LineCol { line: self.line, col: self.col }
    }
}

impl<'a, 'b> Iterator for Toker<'a, 'b> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(tok) = self.toks.pop_front() {
            return Some(tok)
        }
        self.advance();
        self.toks.pop_front()
    }
}

/**
 * Remove unneeded whitespace from SPAIK code.
 *
 * # Arguments
 *
 * - `text` : Input SPAIK code
 * - `io` : Output stream to write minified code to.
 *
 */
pub fn minify(text: &str, f: &mut dyn io::Write) -> Result<(), Error> {
    let tok_tree = standard_lisp_tok_tree();
    let mut toker = Toker::new(text, &tok_tree);
    macro_rules! ops {
        () => { "(" | ")" | "," | ",@" | "'" | "`" | "#'" | "#" };
    }
    while let Some(tok) = toker.next() {
        if matches!(tok.text, ops!()) {
            write!(f, "{}", tok.text)?;
            continue;
        }
        match toker.peek().map(|t| t.text) {
            Some(ops!()) | None => write!(f, "{}", tok.text)?,
            Some(_) => write!(f, "{} ", tok.text)?,
        }
    }
    Ok(())
}
