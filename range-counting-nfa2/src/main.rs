//! Based on Russ Cox's article from https://swtch.com/~rsc/regexp/regexp1.html
//! with additional support for counting constraints from https://www.arl.wustl.edu/~pcrowley/a25-becchi.pdf

use std::collections::VecDeque;
use std::fmt;

#[derive(Debug)]
enum RegexAst {
    Catenate(Vec<RegexAst>),
    Alternate(Vec<RegexAst>),
    Repetition {
        node: Box<RegexAst>,
        min: Option<usize>,
        max: Option<usize>,
    },
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
            Self::Repetition { node, min, max } => {
                let needs_group = matches!(
                    **node,
                    RegexAst::Catenate { .. }
                        | RegexAst::Alternate { .. }
                        | RegexAst::Repetition { .. }
                        | RegexAst::ZeroPlus(_)
                        | RegexAst::OnePlus(_)
                        | RegexAst::ZeroOne(_)
                );
                if needs_group {
                    write!(f, "({})", node)?;
                } else {
                    write!(f, "{}", node)?;
                }
                match (min, max) {
                    (Some(n), Some(m)) if n == m => write!(f, "{{{}}}", n),
                    (None | Some(0), Some(m)) => write!(f, "{{,{}}}", m),
                    (Some(n), None) => write!(f, "{{{},}}", n),
                    (Some(n), Some(m)) => write!(f, "{{{},{}}}", n, m),
                    (None, None) => write!(f, "{{,}}"),
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
        min: usize,
        max: usize,
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

    fn to_dot(
        &self,
        idx: usize,
        states: &[State],
        buffer: &mut impl Write,
        stack: &mut Vec<usize>,
    ) -> Result<(), std::io::Error> {
        match self {
            State::Split { out, out1 } => {
                states[*out].to_dot(idx, states, buffer, stack)?;
                states[*out1].to_dot(idx, states, buffer, stack)
            }
            State::CounterInstance { counter, out } => {
                stack.push(*out);
                writeln!(
                    buffer,
                    "\t{} -> {} [label=\"CounterInstance-{}\"];",
                    idx, out, counter
                )
            }
            State::CounterIncrement {
                counter,
                out,
                out1,
                min,
                max,
            } => {
                stack.push(*out);
                writeln!(
                    buffer,
                    "\t{} -> {} [label=\"Continue-{}{{{},{}}}\"];",
                    idx, out, counter, min, max
                )?;
                stack.push(*out1);
                writeln!(
                    buffer,
                    "\t{} -> {} [label=\"Break-{}{{{},{}}}\"];",
                    idx, out1, counter, min, max
                )
            }
            State::Char { char, out } => {
                stack.push(*out);
                writeln!(buffer, "\t{} -> {} [label=\"{}\"];", idx, out, char)
            }
            State::Wildcard { out } => {
                stack.push(*out);
                writeln!(buffer, "\t{} -> {} [label=\"*\"];", idx, out)
            }
            State::Match => writeln!(buffer, "\t{} [peripheries=2];", idx),
            State::Noop { .. } => todo!(),
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

#[derive(Copy, Clone, Debug)]
enum RegexHirNode {
    Alternate,
    Catenate,
    Char(char),
    RepeatZeroOne,
    RepeatZeroPlus,
    RepeatOnePlus,
    Wildcard,
    CounterInstance {
        counter: usize,
    },
    CounterIncrement {
        counter: usize,
        min: usize,
        max: usize,
    },
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

use std::io::Write;

impl Regex {
    fn to_dot(&self, mut buffer: impl Write) {
        let mut visited = vec![false; self.states.len()];
        writeln!(buffer, "digraph graphname {{").unwrap();
        writeln!(buffer, "\trankdir=LR;").unwrap();
        writeln!(&mut buffer, "\t{} [shape=box];", self.start).unwrap();
        let mut stack = vec![self.start];
        while let Some(idx) = stack.pop() {
            if !visited[idx] {
                writeln!(buffer, "\t// [{}] {:?}", idx, self.states[idx]).unwrap();
                self.states[idx]
                    .to_dot(idx, &self.states, &mut buffer, &mut stack)
                    .unwrap();
                visited[idx] = true;
            }
        }
        writeln!(buffer, "}}").unwrap();
    }
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
            RegexAst::Repetition { node, min, max } => {
                let min = min.unwrap_or(0);
                let max = max.unwrap_or(usize::MAX);
                assert!(min <= max);
                if min > 0 {
                    let counter = self.next_counter();

                    let start = self.postfix.len();
                    self.node2hir(node);
                    let end = self.postfix.len();
                    self.postfix.push(RegexHirNode::CounterInstance { counter });
                    /*self.node2hir(node);*/
                    self.postfix.extend_from_within(start..end);
                    self.postfix
                        .push(RegexHirNode::CounterIncrement { counter, min, max });
                    self.postfix.push(RegexHirNode::Catenate);

                    /*self.node2hir(node);
                    self.postfix.push(RegexHirNode::CounterInstance { counter });
                    self.node2hir(node);
                    self.postfix
                        .push(RegexHirNode::CounterIncrement { counter, min, max });
                    self.postfix.push(RegexHirNode::Catenate);*/
                } else {
                    // self.postfix.push(RegexHirNode::Noop);
                    todo!()
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
            RegexHirNode::CounterIncrement { counter, min, max } => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::CounterIncrement {
                    out: e.start,
                    out1: INVALID_INDEX,
                    min,
                    max,
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
    incremented: bool,
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
        self.incremented = true;
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
            assert_eq!(self.value, self.delta);
            true
        }
    }
}

impl Default for Counter {
    fn default() -> Self {
        Self {
            incremented: false,
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
                counter,
                min,
                max,
            } if self.counters[counter]
                .as_ref()
                .is_some_and(|c| !c.incremented) =>
            {
                self.inccounter(counter);
                let value = self.counters[counter].as_ref().unwrap().value;
                assert!(value > 0);
                assert!(value <= max);
                let is_single = self.counters[counter].as_ref().unwrap().deltas.is_empty();

                // Follow the continue path to add the body's character-consuming
                // states.  Temporarily clear our lastlist mark so we can detect
                // whether the body's epsilon closure reaches back to this
                // CounterIncrement.  The `incremented` flag remains true (from
                // inccounter above), so the recursive addstate will NOT re-process
                // this state — it will just set lastlist[idx] = listid and fall
                // through to `_ => {}`.
                let should_continue = value != max || !is_single;
                let mut is_epsilon_body = false;
                if should_continue {
                    self.lastlist[idx] = self.listid.wrapping_sub(1);
                    println!("[addstate] continue for counter {}", counter);
                    self.addstate(out);
                    // Check if the epsilon closure reached back to us.
                    is_epsilon_body = self.lastlist[idx] == self.listid;
                    // Ensure we're marked as visited regardless.
                    self.lastlist[idx] = self.listid;
                }

                // Evaluate break condition.  For epsilon-matchable bodies, the
                // repetition can freely match empty any number of times, so any
                // counter value from the current up to `max` is reachable.  We
                // check if the range [value, max] intersects [min, max].  For
                // non-epsilon bodies, check all current counter instances.
                let stop = if is_epsilon_body {
                    // [value, max] ∩ [min, max] is non-empty iff value <= max && min <= max
                    // (both of which are invariants), so this is always true when min <= max.
                    min <= max
                } else {
                    let cnt = self.counters[counter].as_ref().unwrap();
                    let mut val = cnt.value;
                    let mut s = val >= min && val <= max;
                    for delta in &cnt.deltas {
                        val -= delta;
                        s = s || (val >= min && val <= max)
                    }
                    s
                };

                if value == max {
                    self.delcounter(counter);
                }

                if stop {
                    println!("[addstate] break for counter {}", counter);
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
        for counter in self.counters.iter_mut().filter_map(|c| c.as_mut()) {
            counter.incremented = false;
        }
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

fn main() {}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Build an anchored regex pattern string from the AST for use with the `regex` crate.
    fn anchored_pattern(ast: &RegexAst) -> String {
        format!("^{}$", ast)
    }

    /// Assert that our NFA matcher and the `regex` crate agree on whether
    /// `input` matches the given AST. Panics with a descriptive message on mismatch.
    fn assert_matches_regex_crate(ast: &RegexAst, input: &str) {
        let pattern = anchored_pattern(ast);
        let re = regex::Regex::new(&pattern).expect("regex crate should parse pattern");
        let expected = re.is_match(input);

        let mut builder = RegexBuilder::default();
        let regex = builder.build(ast);
        let mut memory = MatcherMemory::default();
        let mut matcher = memory.matcher(&regex);
        matcher.chunk(input);
        let actual = matcher.ismatch();

        assert_eq!(
            actual, expected,
            "mismatch for pattern `{}` on input {:?}: our NFA returned {}, regex crate returned {}",
            pattern, input, actual, expected
        );
    }

    fn range_regex() -> RegexAst {
        RegexAst::Repetition {
            node: Box::new(RegexAst::Alternate(vec![
                RegexAst::Catenate(vec![RegexAst::Char('a')]),
                RegexAst::Catenate(vec![RegexAst::Char('b'), RegexAst::Char('c')]),
            ])),
            min: Some(1),
            max: Some(2),
        }
    }

    #[test]
    fn test_counting() {
        let ast = RegexAst::Catenate(vec![
            RegexAst::ZeroPlus(Box::new(RegexAst::Wildcard)),
            RegexAst::Char('a'),
            RegexAst::Repetition {
                node: Box::new(RegexAst::Wildcard),
                min: Some(3),
                max: Some(3),
            },
            RegexAst::Char('b'),
            RegexAst::Char('c'),
        ]);

        assert_matches_regex_crate(&ast, "aybzbc");
        assert_matches_regex_crate(&ast, "axaybzbc");
        assert_matches_regex_crate(&ast, "abc");
        assert_matches_regex_crate(&ast, "");
        assert_matches_regex_crate(&ast, "a123bc");
    }

    #[test]
    fn test_range() {
        use itertools::Itertools;

        let ast = range_regex();

        // Non-matching
        assert_matches_regex_crate(&ast, "");

        // Single repetition
        assert_matches_regex_crate(&ast, "a");
        assert_matches_regex_crate(&ast, "bc");

        // Two repetitions (all combos)
        for v in std::iter::repeat(["a", "bc"])
            .take(2)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            assert_matches_regex_crate(&ast, &input);
        }

        // Three repetitions — should not match (max is 2)
        for v in std::iter::repeat(["a", "bc"])
            .take(3)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            assert_matches_regex_crate(&ast, &input);
        }
    }

    #[test]
    fn test_nested_counting() {
        use itertools::Itertools;

        let ast = RegexAst::Repetition {
            node: Box::new(range_regex()),
            min: Some(2),
            max: Some(3),
        };

        assert_matches_regex_crate(&ast, "");
        assert_matches_regex_crate(&ast, "a");
        assert_matches_regex_crate(&ast, "bc");

        for i in 2..=6 {
            for v in std::iter::repeat(["a", "bc"])
                .take(i)
                .map(|a| a.into_iter())
                .multi_cartesian_product()
            {
                let input = v.into_iter().collect::<String>();
                assert_matches_regex_crate(&ast, &input);
            }
        }

        for v in std::iter::repeat(["a", "bc"])
            .take(7)
            .map(|a| a.into_iter())
            .multi_cartesian_product()
        {
            let input = v.into_iter().collect::<String>();
            assert_matches_regex_crate(&ast, &input);
        }
    }

    #[test]
    fn test_aaaaa() {
        let ast = RegexAst::Repetition {
            node: Box::new(RegexAst::Alternate(vec![
                RegexAst::Char('a'),
                RegexAst::ZeroOne(Box::new(RegexAst::Char('a'))),
            ])),
            min: Some(2),
            max: Some(3),
        };

        assert_matches_regex_crate(&ast, "aaaaa");
        assert_matches_regex_crate(&ast, "");
        assert_matches_regex_crate(&ast, "a");
        assert_matches_regex_crate(&ast, "aa");
        assert_matches_regex_crate(&ast, "aaa");
    }
}
