//! Based on Russ Cox's article from https://swtch.com/~rsc/regexp/regexp1.html
//! with additional support for counting constraints from https://www.arl.wustl.edu/~pcrowley/a25-becchi.pdf

use std::collections::VecDeque;
use std::fmt;

#[derive(Debug)]
enum RegexAst {
    Catenate(Vec<RegexAst>),
    Alternate(Vec<RegexAst>),
    Repetition { node: Box<RegexAst>, count: usize },
    Char(char),
    Wildcard,
    Star(Box<RegexAst>),
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
            Self::Repetition { node, count } => {
                if matches!(
                    **node,
                    RegexAst::Catenate { .. } | RegexAst::Alternate { .. }
                ) {
                    write!(f, "({}){{{}}}", node, count)
                } else {
                    write!(f, "{}{{{}}}", node, count)
                }
            }
            Self::Char(c) => write!(f, "{}", c),
            Self::Wildcard => write!(f, "."),
            Self::Star(node) => {
                if matches!(
                    **node,
                    RegexAst::Catenate { .. } | RegexAst::Alternate { .. }
                ) {
                    write!(f, "({})*", node)
                } else {
                    write!(f, "{}*", node)
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum State {
    Split {
        out: usize,
        out1: usize,
    },
    Counter {
        counter: usize,
        out: usize,
    },
    Repeat {
        counter: usize,
        out: usize,
        out1: usize,
        count: usize,
    },
    Char {
        char: char,
        out: usize,
    },
    Wildcard {
        out: usize,
    },
    Match,
}

impl State {
    fn next(self) -> usize {
        match self {
            State::Char { out, .. } => out,
            State::Wildcard { out, .. } => out,
            State::Split { out1, .. } => out1,
            State::Counter { out, .. } => out,
            State::Repeat { out1, .. } => out1,
            _ => unreachable!(),
        }
    }

    fn append(&mut self, next: usize) {
        match self {
            State::Char { out, .. } => {
                *out = next;
            }
            State::Wildcard { out, .. } => {
                *out = next;
            }
            State::Split { out1, .. } => {
                *out1 = next;
            }
            State::Counter { out, .. } => {
                *out = next;
            }
            State::Repeat { out1, .. } => {
                *out1 = next;
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
struct Fragment {
    start: usize,
    out: usize,
}

impl Fragment {
    fn new(start: usize, out: usize) -> Self {
        Self { start, out }
    }
}

#[derive(Debug)]
struct Regex {
    states: Box<[State]>,
    start: usize,
    counters: usize,
}

#[derive(Debug, Default)]
struct RegexBuilder {
    states: Vec<State>,
    counters: usize,
}

const INVALID_INDEX: usize = usize::MAX;

impl RegexBuilder {
    fn push(&mut self, state: State) -> usize {
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
                State::Wildcard { out, .. } => {
                    let next = *out;
                    *out = idx;
                    next
                }

                State::Split { out1, .. } => {
                    let next = *out1;
                    *out1 = idx;
                    next
                }
                State::Counter { out, .. } => {
                    let next = *out;
                    *out = idx;
                    next
                }
                State::Repeat { out1, .. } => {
                    let next = *out1;
                    *out1 = idx;
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

    fn next_catenate<'a>(
        &mut self,
        ast: &'a RegexAst,
        mut nodes: impl Iterator<Item = &'a RegexAst>,
    ) -> Fragment {
        if let Some(next) = nodes.next() {
            let e2 = self.next_catenate(next, nodes);
            let e1 = self.next_fragment(ast);
            self.patch(e1.out, e2.start);
            Fragment::new(e1.start, e2.out)
        } else {
            self.next_fragment(ast)
        }
    }

    fn next_alternate<'a>(
        &mut self,
        ast: &'a RegexAst,
        mut nodes: impl Iterator<Item = &'a RegexAst>,
    ) -> Fragment {
        if let Some(next) = nodes.next() {
            let e2 = self.next_alternate(next, nodes);
            let e1 = self.next_fragment(ast);
            let s = self.push(State::Split {
                out: e1.start,
                out1: e2.start,
            });
            Fragment::new(s, self.append(e1.out, e2.out))
        } else {
            self.next_fragment(ast)
        }
    }

    fn next_fragment(&mut self, ast: &RegexAst) -> Fragment {
        match ast {
            RegexAst::Catenate(items) => {
                let mut nodes = items.iter();
                self.next_catenate(nodes.next().unwrap(), nodes)
            }
            RegexAst::Alternate(items) => {
                let mut nodes = items.iter();
                self.next_alternate(nodes.next().unwrap(), nodes)
            }
            RegexAst::Repetition { node, count } => {
                let e = self.next_fragment(node);
                let s = self.push(State::Repeat {
                    counter: self.counters,
                    out: e.start,
                    out1: INVALID_INDEX,
                    count: *count,
                });
                self.patch(e.out, s);
                let k = self.push(State::Counter {
                    counter: self.counters,
                    out: INVALID_INDEX,
                });
                let e1 = Fragment::new(k, k);
                self.counters += 1;
                self.patch(e1.out, s);
                Fragment::new(e1.start, s)
            }
            RegexAst::Char(char) => {
                let idx = self.push(State::Char {
                    char: *char,
                    out: INVALID_INDEX,
                });
                Fragment::new(idx, idx)
            }
            RegexAst::Wildcard => {
                let idx = self.push(State::Wildcard { out: INVALID_INDEX });
                Fragment::new(idx, idx)
            }
            RegexAst::Star(node) => {
                let e = self.next_fragment(node);
                let s = self.push(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Fragment::new(s, s)
            }
        }
    }

    fn build(&mut self, ast: &RegexAst) -> Regex {
        self.states.clear();
        self.counters = 0;
        let e = self.next_fragment(ast);
        let s = self.push(State::Match);
        self.patch(e.out, s);
        Regex {
            states: self.states.to_vec().into_boxed_slice(),
            start: e.start,
            counters: self.counters,
        }
    }
}

#[derive(Debug, Default)]
struct MatcherMemory {
    lastlist: Vec<usize>,
    counters: Vec<Option<Counter>>,
    clist: Vec<usize>,
    nlist: Vec<usize>,
}

impl MatcherMemory {
    fn matcher<'a>(&'a mut self, regex: &'a Regex) -> Matcher<'a> {
        self.lastlist.clear();
        self.lastlist.resize(regex.states.len(), usize::MAX);
        self.counters.clear();
        self.counters.resize(regex.counters, None);
        self.clist.clear();
        self.nlist.clear();

        let mut m = Matcher {
            counters: &mut self.counters,
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

#[derive(Clone, Debug)]
struct Counter {
    value: usize,
    delta: usize,
    deltas: VecDeque<usize>,
}

impl Default for Counter {
    fn default() -> Self {
        Self {
            value: 0,
            delta: 0,
            deltas: VecDeque::default(),
        }
    }
}
#[derive(Debug)]
struct Matcher<'a> {
    counters: &'a mut [Option<Counter>],
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

    fn addcounter(&mut self, idx: usize) {
        println!(
            "ADDING INSTANCE FOR COUNTER {} = {:#?}",
            idx, self.counters[idx]
        );
        if let Some(counter) = self.counters[idx].as_mut() {
            counter.deltas.push_back(counter.delta);
            counter.delta = 0;
        } else {
            self.counters[idx] = Some(Counter::default());
        }
    }

    fn inccounter(&mut self, idx: usize) {
        println!(
            "INCREMENTING VALUE FOR COUNTER {} = {:#?}",
            idx, self.counters[idx]
        );
        let counter = self.counters[idx].as_mut().unwrap();
        counter.value += 1;
        counter.delta += 1;
    }

    fn delcounter(&mut self, idx: usize) {
        println!(
            "DELETING INSTANCE FOR COUNTER {} = {:#?}",
            idx, self.counters[idx]
        );
        let counter = self.counters[idx].as_mut().unwrap();
        assert!(counter.value > 0);
        if let Some(delta) = counter.deltas.pop_front() {
            assert!(delta < counter.value);
            counter.value -= delta;
        } else {
            self.counters[idx] = None;
        }
    }

    #[inline]
    fn addstate(&mut self, idx: usize) {
        println!("[addstate] idx = {}, lastid = {}", idx, self.listid);
        if self.lastlist[idx] == self.listid {
            println!("[addstate] skipping");
            return;
        }
        self.lastlist[idx] = self.listid;
        match self.states[idx] {
            State::Split { out, out1 } => {
                self.addstate(out);
                self.addstate(out1);
            }
            State::Counter { out, counter } => {
                self.addcounter(counter);
                self.lastlist[out] = usize::MAX;
                self.addstate(out);
            }
            State::Repeat {
                out,
                out1,
                count,
                counter,
                ..
            } => {
                self.inccounter(counter);
                self.lastlist[idx] = self.listid;
                let value = self.counters[counter].as_ref().unwrap().value - 1;
                let single = self.counters[counter].as_ref().unwrap().deltas.is_empty();
                println!(
                    "[addstate:repeat] count = {}, value = {}, single = {}",
                    count, value, single
                );
                if value != count || !single {
                    // `value != count` <=> all instances of the counter are different from `count`
                    // `!single` <=> at least one other instance of the counter is different from `count`
                    self.addstate(out);
                }
                if value == count {
                    // The oldest instance of the counter is equal to `start`
                    self.delcounter(counter);
                    self.addstate(out1);
                }
            }
            _ => {}
        }
        self.nlist.push(idx);
    }

    fn step(&mut self, c: char) {
        self.nlist.clear();
        let clist = std::mem::take(self.clist);
        println!(
            "c: {}, list = {:?}, counters = {:#?}",
            c, clist, self.counters
        );
        for &idx in &clist {
            println!("states[{}]: {:?}", idx, self.states[idx]);
            match self.states[idx] {
                State::Char { char: c2, out } if c == c2 => {
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
        println!("[chunk] input = {}", input);
        for c in input.chars() {
            self.step(c);
        }
    }

    /// Check whether state list contains a match.
    pub fn ismatch(&self) -> bool {
        println!("list = {:?}, counters = {:?}", self.clist, self.counters);
        for &idx in self.clist.iter() {
            if matches!(self.states[idx], State::Match) {
                return true;
            }
        }

        false
    }
}

fn main() {
    let mut args = std::env::args();
    args.next().unwrap();
    let input = args.next();

    let mut builder = RegexBuilder::default();

    let ast = RegexAst::Repetition {
        node: Box::new(RegexAst::Alternate(vec![
            RegexAst::Catenate(vec![RegexAst::Char('a')]),
            RegexAst::Catenate(vec![RegexAst::Char('b'), RegexAst::Char('c')]),
        ])),
        count: 1,
    };
    println!("pattern: {}", ast);

    let regex = builder.build(&ast);
    println!("regex: {:#?}", regex);

    let mut memory = MatcherMemory::default();
    let mut matcher = memory.matcher(&regex);

    if let Some(ref input) = input {
        matcher.chunk(&input);
        println!("{}: {}", input, matcher.ismatch());
    }

    let ast = RegexAst::Repetition {
        node: Box::new(ast),
        count: 2,
    };
    println!("pattern: {}", ast);

    let regex = builder.build(&ast);
    println!("regex: {:#?}", regex);

    let mut memory = MatcherMemory::default();
    let mut matcher = memory.matcher(&regex);

    if let Some(ref input) = input {
        matcher.chunk(&input);
        println!("{}: {}", input, matcher.ismatch());
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn test_counting() {
        let ast = RegexAst::Catenate(vec![
            RegexAst::Star(Box::new(RegexAst::Wildcard)),
            RegexAst::Char('a'),
            RegexAst::Repetition {
                node: Box::new(RegexAst::Wildcard),
                count: 3,
            },
            RegexAst::Char('b'),
            RegexAst::Char('c'),
        ]);
        println!("pattern: {}", ast);

        let mut builder = RegexBuilder::default();
        let regex = builder.build(&ast);
        println!("regex: {:#?}", regex);

        let mut memory = MatcherMemory::default();

        let input = "axaybzbc";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(matcher.ismatch());

        let input = "aybzbc";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(matcher.ismatch());
    }

    #[test]
    fn test_nested_counting() {
        use itertools::Itertools;

        let mut builder = RegexBuilder::default();
        let mut memory = MatcherMemory::default();

        let ast = RegexAst::Repetition {
            node: Box::new(RegexAst::Alternate(vec![
                RegexAst::Catenate(vec![RegexAst::Char('a')]),
                RegexAst::Catenate(vec![RegexAst::Char('b'), RegexAst::Char('c')]),
            ])),
            count: 2,
        };
        println!("pattern: {}", ast);

        let regex = builder.build(&ast);
        println!("regex: {:#?}", regex);

        let mut matcher = memory.matcher(&regex);
        matcher.chunk("");
        assert!(!matcher.ismatch());

        let input = "a";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(!matcher.ismatch());

        let input = "bc";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(!matcher.ismatch());

        for v in std::iter::repeat(["a", "bc"])
            .take(2)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            println!("input = {:?}", input);
            let mut matcher = memory.matcher(&regex);
            matcher.chunk(&input);
            assert!(matcher.ismatch());
        }

        for v in std::iter::repeat(["a", "bc"])
            .take(3)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            println!("input = {:?}", input);
            let mut matcher = memory.matcher(&regex);
            matcher.chunk(&input);
            assert!(!matcher.ismatch());
        }

        let ast = RegexAst::Repetition {
            node: Box::new(ast),
            count: 3,
        };
        println!("pattern: {}", ast);

        let regex = builder.build(&ast);
        println!("regex: {:#?}", regex);

        let mut matcher = memory.matcher(&regex);
        matcher.chunk("");
        assert!(!matcher.ismatch());

        for i in 0..6 {
            for v in std::iter::repeat(["a", "bc"])
                .take(i)
                .map(|a| a.into_iter())
                .multi_cartesian_product()
            {
                let input = v.into_iter().collect::<String>();
                println!("input = {:?}", input);
                let mut matcher = memory.matcher(&regex);
                matcher.chunk(&input);
                assert!(!matcher.ismatch());
            }
        }

        for v in std::iter::repeat(["a", "bc"])
            .take(6)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            println!("input = {:?}", input);
            let mut matcher = memory.matcher(&regex);
            matcher.chunk(&input);
            assert!(matcher.ismatch());
        }

        for v in std::iter::repeat(["a", "bc"])
            .take(7)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            println!("input = {:?}", input);
            let mut matcher = memory.matcher(&regex);
            matcher.chunk(&input);
            assert!(!matcher.ismatch());
        }
    }
}
