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

#[derive(Clone, Copy, Debug)]
enum State {
    Split {
        out: usize,
        out1: usize,
    },
    // Creates a new counter instance
    CounterInstance {
        counter: usize,
        out: usize,
    },
    // Increments all instances of a counter
    CounterIncrement {
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
    Noop {
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
            State::CounterInstance { out, .. } => out,
            State::CounterIncrement { out1, .. } => out1,
            State::Noop { out } => out,
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
            State::CounterInstance { out, .. } => {
                *out = next;
            }
            State::CounterIncrement { out1, .. } => {
                *out1 = next;
            }
            State::Noop { out } => *out = next,
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
enum RegexHirNode {
    Alternate,
    Catenate,
    Char(char),
    RepeatZeroOne,
    RepeatZeroPlus,
    RepeatOnePlus,
    Wildcard,
    CounterInstance { counter: usize },
    CounterIncrement { counter: usize, count: usize },
    Noop,
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
    counters: Box<[usize]>,
}

#[derive(Debug, Default)]
struct RegexBuilder {
    postfix: Vec<RegexHirNode>,
    states: Vec<State>,
    frags: Vec<Fragment>,
    counters: Vec<usize>,
}

const INVALID_INDEX: usize = usize::MAX;

impl RegexBuilder {
    fn next_counter(&mut self) -> usize {
        let counter = self.counters.len();
        self.counters.push(counter);
        counter
    }
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
            RegexAst::Repetition { node, count } => {
                if *count > 0 {
                    let counter = self.next_counter();
                    self.node2hir(node);
                    self.postfix.push(RegexHirNode::CounterInstance { counter });
                    self.node2hir(node);
                    self.postfix.push(RegexHirNode::CounterIncrement {
                        counter,
                        count: *count,
                    });
                    self.postfix.push(RegexHirNode::Catenate);
                } else {
                    self.postfix.push(RegexHirNode::Noop);
                }
            }
            RegexAst::Char(c) => {
                self.postfix.push(RegexHirNode::Char(*c));
            }
            RegexAst::Wildcard => {
                self.postfix.push(RegexHirNode::Wildcard);
            }
        }
    }

    fn ast2hir(&mut self, root: &RegexAst) {
        self.postfix.clear();
        self.node2hir(root);
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
                State::CounterInstance { out, .. } => {
                    let next = *out;
                    *out = idx;
                    next
                }
                State::CounterIncrement { out1, .. } => {
                    let next = *out1;
                    *out1 = idx;
                    next
                }
                State::Noop { out, .. } => {
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
    fn next_fragment(&mut self, node: RegexHirNode) -> Fragment {
        match node {
            RegexHirNode::Catenate => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                self.patch(e1.out, e2.start);
                Fragment::new(e1.start, e2.out)
            }
            RegexHirNode::Alternate => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e1.start,
                    out1: e2.start,
                });
                Fragment::new(s, self.append(e1.out, e2.out))
            }
            RegexHirNode::RepeatZeroOne => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                Fragment::new(s, self.append(e.out, s))
            }
            RegexHirNode::RepeatZeroPlus => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Fragment::new(s, s)
            }
            RegexHirNode::RepeatOnePlus => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Fragment::new(e.start, s)
            }
            RegexHirNode::CounterInstance { counter } => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::CounterInstance {
                    counter,
                    out: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Fragment::new(e.start, s)
            }
            RegexHirNode::CounterIncrement { counter, count } => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::CounterIncrement {
                    out: e.start,
                    out1: INVALID_INDEX,
                    count,
                    counter,
                });
                self.patch(e.out, s);
                Fragment::new(s, s)
            }
            RegexHirNode::Wildcard => {
                let idx = self.state(State::Wildcard { out: INVALID_INDEX });
                Fragment::new(idx, idx)
            }
            RegexHirNode::Char(char) => {
                let idx = self.state(State::Char {
                    char,
                    out: INVALID_INDEX,
                });
                Fragment::new(idx, idx)
            }
            RegexHirNode::Noop => {
                let idx = self.state(State::Noop { out: INVALID_INDEX });
                Fragment::new(idx, idx)
            }
        }
    }

    pub fn build(&mut self, ast: &RegexAst) -> Regex {
        self.states.clear();
        self.frags.clear();
        self.ast2hir(ast);
        println!("postfix: {:#?}", self.postfix);
        let mut postfix = std::mem::take(&mut self.postfix);
        for node in postfix.drain(..) {
            let frag = self.next_fragment(node);
            self.frags.push(frag)
        }
        self.postfix = postfix;
        let e = self.frags.pop().unwrap();
        assert!(self.frags.is_empty());
        let s = self.state(State::Match);
        self.patch(e.out, s);
        Regex {
            states: StateList(self.states.to_vec().into_boxed_slice()),
            start: e.start,
            counters: self.counters.to_vec().into_boxed_slice(),
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
        self.counters.resize(regex.counters.len(), None);
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

impl Counter {
    fn push(&mut self) {
        assert!(self.delta > 0);
        self.deltas.push_back(self.delta);
        self.delta = 0;
    }

    fn incr(&mut self) {
        self.value += 1;
        self.delta += 1;
    }

    // Return true is if the counter has no instances left
    // false otherwise.
    fn pop(&mut self) -> bool {
        assert!(self.value > 0);
        if let Some(delta) = self.deltas.pop_front() {
            assert!(delta < self.value);
            self.value -= delta;
            false
        } else {
            true
        }
    }
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
            counter.push();
        } else {
            self.counters[idx] = Some(Counter::default());
        }
    }

    fn inccounter(&mut self, idx: usize) {
        println!(
            "INCREMENTING VALUE FOR COUNTER {} = {:#?}",
            idx, self.counters[idx]
        );
        self.counters[idx].as_mut().unwrap().incr();
    }

    fn delcounter(&mut self, idx: usize) {
        println!(
            "DELETING INSTANCE FOR COUNTER {} = {:#?}",
            idx, self.counters[idx]
        );
        if self.counters[idx].as_mut().unwrap().pop() {
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
            State::CounterInstance { out, counter } => {
                self.addcounter(counter);
                self.addstate(out);
            }
            State::CounterIncrement {
                out,
                out1,
                count,
                counter,
                ..
            } => {
                self.inccounter(counter);
                let value = self.counters[counter].as_ref().unwrap().value;
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
            State::Noop { out } => {
                self.addstate(out);
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
            RegexAst::ZeroPlus(Box::new(RegexAst::Wildcard)),
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
            assert!(matcher.ismatch(), "input = {} should have matched", input);
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

    #[test]
    fn test_empty_counting() {
        use itertools::Itertools;

        let mut builder = RegexBuilder::default();
        let mut memory = MatcherMemory::default();

        let ast = RegexAst::Repetition {
            node: Box::new(RegexAst::Alternate(vec![
                RegexAst::Catenate(vec![RegexAst::Char('a')]),
                RegexAst::Catenate(vec![RegexAst::Char('b'), RegexAst::Char('c')]),
            ])),
            count: 0,
        };
        println!("pattern: {}", ast);

        let regex = builder.build(&ast);
        println!("regex: {:#?}", regex);

        let mut matcher = memory.matcher(&regex);
        matcher.chunk("");
        assert!(matcher.ismatch());

        let input = "a";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(!matcher.ismatch());

        let input = "bc";
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        assert!(!matcher.ismatch());
    }
}
