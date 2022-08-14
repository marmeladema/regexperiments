//! Based on Russ Cox's article from https://swtch.com/~rsc/regexp/regexp1.html

use std::fmt;

#[derive(Debug)]
enum RegexAst {
    Catenate(Vec<RegexAst>),
    Alternate(Vec<RegexAst>),
    Char(char),
    Wildcard,
    ZeroPlus(Box<RegexAst>),
    OnePlus(Box<RegexAst>),
    ZeroOne(Box<RegexAst>),
}

impl fmt::Display for RegexAst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Catenate(items) => {
                for item in items {
                    write!(f, "{}", item)?;
                }
                Ok(())
            }
            Self::Alternate(items) => {
                let mut items = items.iter();
                if let Some(item) = items.next() {
                    write!(f, "{}", item)?;
                    for item in items {
                        write!(f, "|{}", item)?;
                    }
                }
                Ok(())
            }
            Self::Char(c) => write!(f, "{}", c),
            Self::Wildcard => write!(f, "."),
            Self::ZeroPlus(node) => {
                if matches!(
                    **node,
                    RegexAst::Catenate { .. } | RegexAst::Alternate { .. }
                ) {
                    write!(f, "({})*", node)
                } else {
                    write!(f, "{}*", node)
                }
            }
            Self::OnePlus(node) => {
                if matches!(
                    **node,
                    RegexAst::Catenate { .. } | RegexAst::Alternate { .. }
                ) {
                    write!(f, "({})+", node)
                } else {
                    write!(f, "{}+", node)
                }
            }
            Self::ZeroOne(node) => {
                if matches!(
                    **node,
                    RegexAst::Catenate { .. } | RegexAst::Alternate { .. }
                ) {
                    write!(f, "({})?", node)
                } else {
                    write!(f, "{}?", node)
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum State {
    Match,
    Split { out: usize, out1: usize },
    Char { c: char, out: usize },
    Wildcard { out: usize },
}

impl State {
    fn next(self) -> usize {
        match self {
            State::Char { out, .. } => out,
            State::Split { out1, .. } => out1,
            _ => unreachable!(),
        }
    }

    fn append(&mut self, next: usize) {
        match self {
            State::Char { out, .. } => {
                *out = next;
            }
            State::Split { out1, .. } => {
                *out1 = next;
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
struct Frag {
    start: usize,
    out: usize,
}

impl Frag {
    fn new(start: usize, out: usize) -> Self {
        Self { start, out }
    }
}

#[derive(Debug)]
enum RegexHirNode {
    Alternate,
    Catenate,
    Char(char),
    RepeatZeroOne,
    RepeatZeroPlus,
    RepeatOnePlus,
    Wildcard,
}

const INVALID_INDEX: usize = usize::MAX;

#[derive(Debug, Default)]
struct RegexBuilder {
    postfix: Vec<RegexHirNode>,
    states: Vec<State>,
    frags: Vec<Frag>,
}

impl RegexBuilder {
    fn node2hir(&mut self, node: &RegexAst) {
        match node {
            RegexAst::Alternate(children) => {
                for (idx, child) in children.iter().enumerate() {
                    self.node2hir(child);
                    if idx > 0 {
                        self.postfix.push(RegexHirNode::Alternate);
                    }
                }
            }
            RegexAst::Catenate(children) => {
                for (idx, child) in children.iter().enumerate() {
                    self.node2hir(child);
                    if idx > 0 {
                        self.postfix.push(RegexHirNode::Catenate);
                    }
                }
            }
            RegexAst::ZeroPlus(child) => {
                self.node2hir(child);
                self.postfix.push(RegexHirNode::RepeatZeroPlus);
            }
            RegexAst::OnePlus(child) => {
                self.node2hir(child);
                self.postfix.push(RegexHirNode::RepeatOnePlus);
            }
            RegexAst::ZeroOne(child) => {
                self.node2hir(child);
                self.postfix.push(RegexHirNode::RepeatZeroOne);
            }
            RegexAst::Char(c) => {
                self.postfix.push(RegexHirNode::Char(*c));
            }
            RegexAst::Wildcard => {
                self.postfix.push(RegexHirNode::Wildcard);
            }
        }
    }

    fn ast2hir(&mut self, root: &RegexAst) -> Option<&[RegexHirNode]> {
        self.postfix.clear();
        self.node2hir(root);
        Some(&self.postfix)
    }

    fn state(&mut self, state: State) -> usize {
        let idx = self.states.len();
        self.states.push(state);
        idx
    }

    fn patch(&mut self, mut list: usize, idx: usize) {
        while let Some(state) = self.states.get_mut(list) {
            list = match state {
                State::Char { out, .. } => {
                    let next = *out;
                    *out = idx;
                    next
                }
                State::Split { out1, .. } => {
                    let next = *out1;
                    *out1 = idx;
                    next
                }
                State::Wildcard { out } => {
                    let next = *out;
                    *out = idx;
                    next
                }
                _ => panic!("Invalid state: {:?}", state),
            };
        }
    }

    fn append(&mut self, list1: usize, list2: usize) -> usize {
        let oldlist1 = list1;
        let len = self.states.len();
        let mut s = &mut self.states[list1];
        let mut next = s.next();
        while next < len {
            s = &mut self.states[next];
            next = s.next();
        }
        s.append(list2);
        oldlist1
    }

    #[inline]
    fn next_frag(&mut self, node: RegexHirNode) -> Frag {
        match node {
            RegexHirNode::Catenate => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                self.patch(e1.out, e2.start);
                Frag::new(e1.start, e2.out)
            }
            RegexHirNode::Alternate => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e1.start,
                    out1: e2.start,
                });
                Frag::new(s, self.append(e1.out, e2.out))
            }
            RegexHirNode::RepeatZeroOne => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                Frag::new(s, self.append(e.out, s))
            }
            RegexHirNode::RepeatZeroPlus => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Frag::new(s, s)
            }
            RegexHirNode::RepeatOnePlus => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Frag::new(e.start, s)
            }
            RegexHirNode::Wildcard => {
                let idx = self.state(State::Wildcard { out: INVALID_INDEX });
                Frag::new(idx, idx)
            }
            RegexHirNode::Char(c) => {
                let idx = self.state(State::Char {
                    c,
                    out: INVALID_INDEX,
                });
                Frag::new(idx, idx)
            }
        }
    }

    pub fn build(&mut self, ast: &RegexAst) -> Option<Regex> {
        self.states.clear();
        self.frags.clear();
        self.ast2hir(ast)?;
        println!("postfix: {:#?}", self.postfix);
        let mut postfix = std::mem::take(&mut self.postfix);
        for node in postfix.drain(..) {
            let frag = self.next_frag(node);
            self.frags.push(frag)
        }
        self.postfix = postfix;
        let e = self.frags.pop().unwrap();
        assert!(self.frags.is_empty());
        let s = self.state(State::Match);
        self.patch(e.out, s);
        Some(Regex {
            states: StateList(self.states.to_vec().into_boxed_slice()),
            start: e.start,
        })
    }
}

struct StateList(Box<[State]>);

impl fmt::Debug for StateList {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_map()
            .entries(self.0.iter().enumerate().map(|(idx, state)| (idx, state)))
            .finish()
    }
}

impl std::ops::Deref for StateList {
    type Target = [State];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
struct Regex {
    states: StateList,
    start: usize,
}

#[derive(Debug, Default)]
struct MatcherMemory {
    lastlist: Vec<usize>,
    clist: Vec<usize>,
    nlist: Vec<usize>,
}

impl MatcherMemory {
    fn matcher<'a>(&'a mut self, regex: &'a Regex) -> Matcher<'a> {
        self.lastlist.clear();
        self.lastlist.resize(regex.states.len(), usize::MAX);
        self.clist.clear();
        self.nlist.clear();

        let mut m = Matcher {
            states: &regex.states,
            lastlist: &mut self.lastlist,
            listid: 0,
            clist: &mut self.clist,
            nlist: &mut self.nlist,
        };

        m.startlist(regex.start);

        m
    }
}

#[derive(Debug)]
struct Matcher<'a> {
    states: &'a [State],
    lastlist: &'a mut [usize],
    listid: usize,
    clist: &'a mut Vec<usize>,
    nlist: &'a mut Vec<usize>,
}

impl<'a> Matcher<'a> {
    /// Compute initial state list.
    #[inline]
    fn startlist(&mut self, start: usize) {
        self.addstate(start);
        std::mem::swap(self.clist, self.nlist);
        self.listid += 1;
    }

    #[inline]
    fn addstate(&mut self, idx: usize) {
        if self.lastlist[idx] == self.listid {
            return;
        }
        self.lastlist[idx] = self.listid;
        if let State::Split { out, out1 } = self.states[idx] {
            self.addstate(out);
            self.addstate(out1);
        }
        self.nlist.push(idx);
    }

    fn step(&mut self, c: char) {
        self.nlist.clear();
        let clist = std::mem::take(self.clist);
        for &idx in &clist {
            match self.states[idx] {
                State::Char { c: c2, out } if c == c2 => {
                    self.addstate(out);
                }
                State::Wildcard { out } => {
                    self.addstate(out);
                }
                _ => {}
            }
        }
        *self.clist = std::mem::replace(self.nlist, clist);
        self.listid += 1;
    }

    fn chunk(&mut self, input: &str) {
        for c in input.chars() {
            self.step(c);
        }
    }

    /// Check whether state list contains a match.
    pub fn ismatch(&self) -> bool {
        for &idx in self.clist.iter() {
            if self.states[idx] == State::Match {
                return true;
            }
        }

        false
    }
}

pub fn main() {}

#[test]
fn test_regex_ast() {
    use crate::*;

    let ast = RegexAst::Catenate(vec![
        RegexAst::ZeroPlus(Box::new(RegexAst::Wildcard)),
        RegexAst::Char('a'),
        RegexAst::Alternate(vec![RegexAst::Char('b'), RegexAst::Char('c')]),
    ]);
    println!("pattern: {}", ast);

    let mut builder = RegexBuilder::default();
    let regex = builder.build(&ast).unwrap();
    println!("regex: {:#?}", regex);

    let mut memory = MatcherMemory::default();

    let input = "ab";
    let mut matcher = memory.matcher(&regex);
    matcher.chunk(input);
    assert!(matcher.ismatch());

    let input = "aab";
    let mut matcher = memory.matcher(&regex);
    matcher.chunk(input);
    assert!(matcher.ismatch());

    let input = "ac";
    let mut matcher = memory.matcher(&regex);
    matcher.chunk(input);
    assert!(matcher.ismatch());

    let input = "aac";
    let mut matcher = memory.matcher(&regex);
    matcher.chunk(input);
    assert!(matcher.ismatch());
}
