/// Based on Russ Cox's article from https://swtch.com/~rsc/regexp/regexp1.html
use std::mem::take;

#[derive(Clone, Copy, Debug, Default)]
struct Paren {
    nalt: usize,
    natom: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum State {
    Match,
    Split { out: usize, out1: usize },
    Char { c: char, out: usize },
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

const INVALID_INDEX: usize = usize::MAX;

#[derive(Debug, Default)]
struct Builder {
    paren_stack: Vec<Paren>,
    postfix: String,
    states: Vec<State>,
    frags: Vec<Frag>,
}

impl Builder {
    /// Convert infix regexp pattern to postfix notation.
    /// Insert . as explicit concatenation operator.
    fn infix2postfix(&mut self, pattern: &str) -> Option<&str> {
        self.paren_stack.clear();
        self.postfix.clear();
        let mut paren_curr = Paren::default();

        for c in pattern.chars() {
            match c {
                '(' => {
                    if paren_curr.natom > 1 {
                        paren_curr.natom -= 1;
                        self.postfix.push('.');
                    }
                    self.paren_stack.push(take(&mut paren_curr));
                }
                '|' => {
                    if paren_curr.natom == 0 {
                        return None;
                    }
                    loop {
                        paren_curr.natom -= 1;
                        if paren_curr.natom > 0 {
                            self.postfix.push('.')
                        } else {
                            break;
                        }
                    }
                    paren_curr.nalt += 1;
                }
                ')' => {
                    let paren_last = self.paren_stack.pop()?;
                    if paren_curr.natom == 0 {
                        return None;
                    }
                    loop {
                        paren_curr.natom -= 1;
                        if paren_curr.natom > 0 {
                            self.postfix.push('.');
                        } else {
                            break;
                        }
                    }
                    while paren_curr.nalt > 0 {
                        self.postfix.push('|');
                        paren_curr.nalt -= 1;
                    }
                    paren_curr = paren_last;
                    paren_curr.natom += 1;
                }
                '*' | '+' | '?' => {
                    if paren_curr.natom == 0 {
                        return None;
                    }
                    self.postfix.push(c);
                }
                _ => {
                    if paren_curr.natom > 1 {
                        paren_curr.natom -= 1;
                        self.postfix.push('.');
                    }
                    self.postfix.push(c);
                    paren_curr.natom += 1;
                }
            }
        }
        if !self.paren_stack.is_empty() {
            return None;
        }

        if paren_curr.natom == 0 {
            return None;
        }
        paren_curr.natom -= 1;
        while paren_curr.natom > 0 {
            self.postfix.push('.');
            paren_curr.natom -= 1;
        }
        while paren_curr.nalt > 0 {
            self.postfix.push('|');
            paren_curr.nalt -= 1;
        }
        Some(self.postfix.as_str())
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
    fn next_frag(&mut self, c: char) -> Frag {
        match c {
            '.' => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                self.patch(e1.out, e2.start);
                Frag::new(e1.start, e2.out)
            }
            '|' => {
                let e2 = self.frags.pop().unwrap();
                let e1 = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e1.start,
                    out1: e2.start,
                });
                Frag::new(s, self.append(e1.out, e2.out))
            }
            '?' => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                Frag::new(s, self.append(e.out, s))
            }
            '*' => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Frag::new(s, s)
            }
            '+' => {
                let e = self.frags.pop().unwrap();
                let s = self.state(State::Split {
                    out: e.start,
                    out1: INVALID_INDEX,
                });
                self.patch(e.out, s);
                Frag::new(e.start, s)
            }
            _ => {
                let idx = self.state(State::Char {
                    c,
                    out: INVALID_INDEX,
                });
                Frag::new(idx, idx)
            }
        }
    }

    pub fn build(&mut self, pattern: &str) -> Option<Regex> {
        self.states.clear();
        self.frags.clear();
        self.infix2postfix(pattern)?;
        let postfix = std::mem::take(&mut self.postfix);
        for c in postfix.chars() {
            let frag = self.next_frag(c);
            self.frags.push(frag)
        }
        self.postfix = postfix;
        let e = self.frags.pop().unwrap();
        assert!(self.frags.is_empty());
        let s = self.state(State::Match);
        self.patch(e.out, s);
        Some(Regex {
            states: self.states.to_vec().into_boxed_slice(),
            start: e.start,
        })
    }
}

#[derive(Debug)]
struct Regex {
    states: Box<[State]>,
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

pub fn main() {
    let mut args = std::env::args();
    args.next().unwrap();

    let pattern = if let Some(pattern) = args.next() {
        pattern
    } else {
        println!("./thompson-nfa <pattern> [<input>]");
        std::process::exit(1);
    };

    let mut builder = Builder::default();
    let regex = if let Some(regex) = builder.build(&pattern) {
        regex
    } else {
        eprintln!("Invalid pattern `{}`", pattern);
        std::process::exit(1);
    };

    println!("Regex: {:#?}", regex);

    let mut memory = MatcherMemory::default();
    let mut matcher = memory.matcher(&regex);

    if let Some(input) = args.next() {
        matcher.chunk(&input);
        println!("{}: {}", input, matcher.ismatch());
    }
}
