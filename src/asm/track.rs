//! Where certified loops end up: what the passes do to their labels and to the words they
//! hold at them, noted only while a build makes certificates for the prover. Nothing here
//! changes the code.

use std::cell::RefCell;
use std::collections::HashMap;

use super::Inst;
use crate::word::Word;

/// The stand-in for a loop's counter among the words held at its head.
pub(crate) const COUNTER: u32 = u32::MAX;

/// Where a local is at a loop's head, as codegen and the passes leave it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    /// A memory word not yet placed.
    Mem(u32),
    /// A memory word, placed.
    Word(u64),
    Const(Word),
    /// Read from calldata wherever it is read: the instructions that read it.
    Calldata(Vec<Inst>),
    /// No code reads it.
    Dead,
    /// On the stack, under this many items.
    Stack(usize),
}

/// What a site is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// A loop, whose head is `top`.
    Loop,
    /// A function compiled once, whose entry is `top`.
    Func,
    /// A function's body inlined into a call, from mark `top` to mark `done`.
    Inline,
    /// Where the statements of a guard end in a route's code, at mark `done`, with the
    /// route's index as `line`.
    GuardEnd,
}

/// A loop codegen emitted, a function it compiled once, an inlined copy of one, or the end
/// of a guard's statements.
#[derive(Clone, Debug)]
pub(crate) struct Site {
    pub kind: Kind,
    pub func: String,
    pub line: u32,
    pub col: u32,
    pub top: u32,
    pub done: u32,
    /// The counter is on the stack at the head; else it counts from zero by iterations.
    pub counter: bool,
    /// Each local of the loop's function, by its declaration's place and name: its memory
    /// word before placing, which the held words name, and where it is.
    pub locals: Vec<((u32, u32, String), Option<u32>, Place)>,
}

#[derive(Clone, Default)]
pub(crate) struct Track {
    pub sites: Vec<Site>,
    /// Labels whose jumps go to another now: old to new.
    pub renamed: HashMap<u32, u32>,
    /// What a label has on the stack that a site names: each word, or `COUNTER`, and how
    /// many items are above it.
    pub held: HashMap<u32, Vec<(u32, usize)>>,
    /// Where each label is in the assembled code.
    pub pos: HashMap<u32, usize>,
    /// Where each mark is in the code the passes have: before this instruction.
    pub marks: HashMap<u32, usize>,
    /// Where each mark is in the assembled code.
    pub mark_pcs: HashMap<u32, usize>,
    /// How many passes have carried the marks, so a pass that runs others leaves it to them.
    pub carried: u64,
    /// Why each mark the passes lost was lost, and where the pass runs.
    pub lost: HashMap<u32, String>,
}

thread_local! {
    static TRACK: RefCell<Option<Track>> = const { RefCell::new(None) };
}

pub(crate) fn start() {
    TRACK.with(|t| *t.borrow_mut() = Some(Track::default()));
}

pub(crate) fn take() -> Option<Track> {
    TRACK.with(|t| t.borrow_mut().take())
}

pub(crate) fn put(track: Track) {
    TRACK.with(|t| *t.borrow_mut() = Some(track));
}

pub(crate) fn on() -> bool {
    TRACK.with(|t| t.borrow().is_some())
}

/// The code before a pass, and the words its labels hold, when there are marks to carry.
pub(crate) type Before = Option<(Vec<Inst>, HashMap<u32, Vec<(u32, usize)>>)>;

pub(crate) fn before(code: &[Inst]) -> Before {
    TRACK.with(|t| {
        t.borrow()
            .as_ref()
            .filter(|t| !t.marks.is_empty())
            .map(|t| (code.to_vec(), t.held.clone()))
    })
}

/// Carries the marks from the code `before` a pass to `code`, the code it made.
#[track_caller]
pub(crate) fn carry(before: Before, code: &[Inst]) {
    let caller = std::panic::Location::caller();
    if PASS.with(|p| p.get().is_none()) {
        PASS.with(|p| p.set(Some(caller)));
        carry_from(before, code);
        PASS.with(|p| p.set(None));
    } else {
        carry_from(before, code);
    }
}

fn carry_from(before: Before, code: &[Inst]) {
    if let Some((old, held_old)) = before {
        note(|t| {
            let held_new = t.held.clone();
            super::marks::remap(t, &old, code, &held_old, &held_new);
            t.carried += 1;
        });
    }
}

fn carried() -> u64 {
    TRACK.with(|t| t.borrow().as_ref().map_or(0, |t| t.carried))
}

/// Runs a pass over `code`, carrying the marks along to the code it makes, unless the passes
/// it runs carried them already.
#[track_caller]
pub(crate) fn pass<R, F: FnOnce(&mut Vec<Inst>) -> R>(code: &mut Vec<Inst>, f: F) -> R {
    if !on() {
        return f(code);
    }
    let was = before(code);
    let n = carried();
    let caller = std::panic::Location::caller();
    let out = f(code);
    if carried() == n {
        PASS.with(|p| p.set(Some(caller)));
        carry_from(was, code);
        PASS.with(|p| p.set(None));
    }
    out
}

thread_local! {
    /// Where the pass whose marks are carried runs, for reports of the marks it loses.
    static PASS: std::cell::Cell<Option<&'static std::panic::Location<'static>>> =
        const { std::cell::Cell::new(None) };
}

/// Where the pass whose marks are carried runs.
pub(crate) fn current_pass() -> String {
    PASS.with(|p| p.get().map_or("a pass".to_string(), |l| l.to_string()))
}

/// Takes the marks out of `code`, before the first pass.
pub(crate) fn strip(code: &mut Vec<Inst>) {
    note(|t| super::marks::strip(t, code));
}

/// Notes something, when tracking.
pub(crate) fn note(f: impl FnOnce(&mut Track)) {
    TRACK.with(|t| {
        if let Some(track) = t.borrow_mut().as_mut() {
            f(track);
        }
    });
}

impl Track {
    /// A word held at `label` with `above` items over it: what was at or under that depth
    /// is one deeper. An alias adds no item, only another name for one.
    pub(crate) fn hold(&mut self, label: u32, word: u32, above: usize, alias: bool) {
        let items = self.held.entry(label).or_default();
        if !alias {
            for item in items.iter_mut() {
                if item.1 >= above {
                    item.1 += 1;
                }
            }
        }
        items.retain(|item| item.0 != word);
        items.push((word, above));
    }

    /// The label `label`'s jumps go to now.
    pub(crate) fn follow(&self, mut label: u32) -> u32 {
        for _ in 0..64 {
            match self.renamed.get(&label) {
                Some(&to) if to != label => label = to,
                _ => break,
            }
        }
        label
    }

    /// Where a label ended up, following renames, or a mark.
    pub(crate) fn at(&self, mut label: u32) -> Option<usize> {
        if super::marks::is_mark(label) {
            return self.mark_pcs.get(&label).copied();
        }
        for _ in 0..64 {
            if let Some(&p) = self.pos.get(&label) {
                return Some(p);
            }
            label = *self.renamed.get(&label)?;
        }
        None
    }
}
