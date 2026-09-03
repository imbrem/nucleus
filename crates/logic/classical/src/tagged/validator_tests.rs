//! Differential tests for the packed-arena validator.
//!
//! The oracle below deliberately reimplements the storage predicate with
//! simple vectors and pairwise overlap checks. It does not call the production
//! validator.

use std::collections::HashMap;

use super::{Arena, Checked, Formula, Ref, Sequent, Word, pack};

const RESERVED: usize = 4;
const MAX_CLASS: usize = 29;
const REFCOUNT_MAX: u32 = (1 << 25) - 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Block {
    base: usize,
    class: usize,
}

impl Block {
    fn capacity(self) -> Option<usize> {
        4_usize.checked_shl(self.class.try_into().ok()?)
    }
    fn stop(self) -> Option<usize> {
        self.base.checked_add(self.capacity()?)
    }
    fn fits(self, len: usize) -> bool {
        self.base >= RESERVED
            && self.base.is_multiple_of(4)
            && self.stop().is_some_and(|x| x <= len)
    }
    fn overlaps(self, other: Self) -> bool {
        self.base < other.stop().unwrap_or(0) && other.base < self.stop().unwrap_or(0)
    }
}

struct Oracle<'a> {
    words: &'a [Word],
    free_root: Word,
    roots: &'a [(Ref, Ref)],
}

impl Oracle<'_> {
    fn pointer(word: Word) -> Option<usize> {
        (!word.is_negative() && word.payload() != 0 && word.tag() == 0)
            .then(|| usize::try_from(word.base()).ok())
            .flatten()
    }

    fn live(&self, base: usize) -> Option<Block> {
        let raw = self.words.get(base)?.raw();
        let tag = raw & 3;
        let class = usize::try_from((raw >> 2) & 0x1f).ok()?;
        let rc = raw >> 7;
        if tag >= 3 || class > MAX_CLASS || rc == 0 || rc > REFCOUNT_MAX {
            return None;
        }
        let block = Block { base, class };
        block.fits(self.words.len()).then_some(block)
    }

    fn free_header(&self, base: usize) -> Option<(Block, usize, usize)> {
        if *self.words.get(base)? != Word::ZERO {
            return None;
        }
        let next = Self::pointer(*self.words.get(base + 1)?)?;
        let prev = Self::pointer(*self.words.get(base + 2)?)?;
        let class_word = *self.words.get(base + 3)?;
        if class_word.is_negative() {
            return None;
        }
        let class = usize::try_from(class_word.payload()).ok()?;
        let block = Block { base, class };
        block.fits(self.words.len()).then_some((block, next, prev))
    }

    fn children(&self, block: Block) -> Option<&[Word]> {
        if self.live(block.base)? != block {
            return None;
        }
        let words = self.words.get(block.base + 1..block.stop()?)?;
        let end = words.iter().position(|word| *word == Word::ZERO)?;
        words[end..]
            .iter()
            .all(|word| *word == Word::ZERO)
            .then_some(&words[..end])
    }

    fn ring(&self, head: usize, class: usize, root: Option<usize>) -> Option<Vec<Block>> {
        let mut result = Vec::new();
        let mut current = head;
        loop {
            if result.iter().any(|block: &Block| block.base == current) {
                return None;
            }
            let (block, next, _) = self.free_header(current)?;
            if block.class != class {
                return None;
            }
            if root != Some(current)
                && self
                    .words
                    .get(block.base + 4..block.stop()?)?
                    .iter()
                    .any(|w| *w != Word::ZERO)
            {
                return None;
            }
            let (_, _, next_prev) = self.free_header(next)?;
            if next_prev != current {
                return None;
            }
            result.push(block);
            if next == head {
                return Some(result);
            }
            current = next;
        }
    }

    fn free(&self) -> Option<Vec<Block>> {
        if self.free_root == Word::ZERO {
            return Some(Vec::new());
        }
        let base = Self::pointer(self.free_root)?;
        let (root, _, _) = self.free_header(base)?;
        let mut result = Vec::new();
        for class in 0..root.class {
            let word = *self.words.get(root.base + 4 + class)?;
            if word != Word::ZERO {
                result.extend(self.ring(Self::pointer(word)?, class, None)?);
            }
        }
        if self
            .words
            .get(root.base + 4 + root.class..root.stop()?)?
            .iter()
            .any(|w| *w != Word::ZERO)
        {
            return None;
        }
        result.extend(self.ring(base, root.class, Some(base))?);
        pairwise(&result).then_some(result)
    }

    fn accepts(&self) -> bool {
        if self.words.len() < RESERVED || self.words[..RESERVED].iter().any(|w| *w != Word::ZERO) {
            return false;
        }
        let Some(free) = self.free() else {
            return false;
        };
        let mut live = Vec::new();
        let mut base = RESERVED;
        while base < self.words.len() {
            let block = if self.words[base] == Word::ZERO {
                match self.free_header(base) {
                    Some((b, _, _)) => b,
                    None => return false,
                }
            } else {
                match self.live(base) {
                    Some(b) => b,
                    None => return false,
                }
            };
            if block.base != base {
                return false;
            }
            if self.words[base] == Word::ZERO {
                if !free.contains(&block) {
                    return false;
                }
            } else {
                live.push(block);
            }
            let Some(stop) = block.stop() else {
                return false;
            };
            base = stop;
        }
        if base != self.words.len()
            || !pairwise(&free)
            || !pairwise(&live)
            || free.iter().any(|a| live.iter().any(|b| a.overlaps(*b)))
        {
            return false;
        }

        let mut incoming = HashMap::<usize, u32>::new();
        for reference in self.roots.iter().flat_map(|(a, b)| [a, b]) {
            if !Self::count_ref(*reference, &live, &mut incoming) {
                return false;
            }
        }
        for block in &live {
            let Some(children) = self.children(*block) else {
                return false;
            };
            for word in children {
                let Ok(reference) = Ref::new(*word) else {
                    return false;
                };
                if !Self::count_ref(reference, &live, &mut incoming) {
                    return false;
                }
            }
        }
        for block in &live {
            let stored = self.words[block.base].raw() >> 7;
            if stored < incoming.get(&block.base).copied().unwrap_or(0) {
                return false;
            }
        }
        let mut colors = HashMap::new();
        self.roots
            .iter()
            .flat_map(|(a, b)| [*a, *b])
            .all(|r| self.acyclic(r, &mut colors))
    }

    fn count_ref(reference: Ref, live: &[Block], incoming: &mut HashMap<usize, u32>) -> bool {
        let word = reference.word();
        if word.tag() == 3 {
            return true;
        }
        if word.tag() != 0 {
            return false;
        }
        let Ok(base) = usize::try_from(word.base()) else {
            return false;
        };
        if !live.iter().any(|block| block.base == base) {
            return false;
        }
        let count = incoming.entry(base).or_default();
        let Some(next) = count.checked_add(1) else {
            return false;
        };
        *count = next;
        true
    }

    fn acyclic(&self, reference: Ref, colors: &mut HashMap<usize, u8>) -> bool {
        if reference.word().tag() == 3 {
            return true;
        }
        let Ok(base) = usize::try_from(reference.word().base()) else {
            return false;
        };
        match colors.get(&base) {
            Some(1) => return false,
            Some(2) => return true,
            _ => {}
        }
        let Some(block) = self.live(base) else {
            return false;
        };
        let Some(children) = self.children(block) else {
            return false;
        };
        colors.insert(base, 1);
        for word in children {
            let Ok(child) = Ref::new(*word) else {
                return false;
            };
            if !self.acyclic(child, colors) {
                return false;
            }
        }
        colors.insert(base, 2);
        true
    }
}

fn pairwise(blocks: &[Block]) -> bool {
    blocks
        .iter()
        .enumerate()
        .all(|(i, a)| blocks[i + 1..].iter().all(|b| !a.overlaps(*b)))
}

fn agrees(arena: &Arena) -> bool {
    let (words, free_root, roots) = arena.clone().into_parts();
    let oracle = Oracle {
        words: &words,
        free_root,
        roots: &roots,
    }
    .accepts();
    oracle == Checked::check(arena.clone()).is_ok()
}

fn lit(atom: u32) -> Formula {
    Formula::Literal {
        atom,
        negative: false,
    }
}

fn pointer(base: u32) -> Ref {
    Ref::new(Word::pointer(base, false).unwrap()).unwrap()
}

fn metadata(tag: u32, class: u32, rc: u32) -> Word {
    Word::from_raw((rc << 7) | (class << 2) | tag)
}

fn seeds() -> Vec<Arena> {
    let mut result = Vec::new();
    for sequents in [
        Vec::new(),
        vec![Sequent {
            premise: lit(1),
            conclusion: lit(1),
        }],
        vec![Sequent {
            premise: Formula::And {
                negative: false,
                children: vec![lit(1), lit(2)],
            },
            conclusion: Formula::Or {
                negative: true,
                children: vec![lit(3)],
            },
        }],
    ] {
        result.push(pack(&sequents).unwrap().arena().clone());
    }
    result.push(Arena::new(
        vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            metadata(0, 0, 2),
            Word::literal(1, false).unwrap(),
            Word::ZERO,
            Word::ZERO,
        ],
        Word::ZERO,
        vec![(pointer(4), pointer(4))],
    ));
    result.push(Arena::new(
        vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            metadata(0, 0, REFCOUNT_MAX),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            metadata(1, 0, REFCOUNT_MAX),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
        ],
        Word::ZERO,
        vec![(
            pointer(4),
            Ref::new(Word::literal(1, false).unwrap()).unwrap(),
        )],
    ));
    let p4 = pointer(4).word();
    let p12 = pointer(12).word();
    result.push(Arena::new(
        vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            p4,
            p4,
            Word::natural(1).unwrap(),
            p12,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            p12,
            p12,
            Word::ZERO,
        ],
        p4,
        Vec::new(),
    ));
    result
}

#[test]
fn seed_shapes_agree() {
    assert!(seeds().iter().all(agrees));
}

#[test]
fn every_single_word_corruption_agrees() {
    for seed in seeds() {
        let (words, free, roots) = seed.into_parts();
        for index in 0..words.len() {
            for raw in [
                0,
                1,
                2,
                3,
                4,
                7,
                1 << 7,
                u32::MAX,
                words[index].raw() ^ 1,
                words[index].raw() ^ (1 << 31),
            ] {
                let mut changed = words.clone();
                changed[index] = Word::from_raw(raw);
                assert!(
                    agrees(&Arena::new(changed, free, roots.clone())),
                    "word {index}, raw {raw:#x}"
                );
            }
        }
    }
}

#[test]
fn randomized_corruption_agrees() {
    let mut state = 0x6a09_e667_f3bc_c909_u64;
    for seed in seeds() {
        let (words, free, roots) = seed.into_parts();
        for _ in 0..2_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let mut changed = words.clone();
            if !changed.is_empty() {
                let index = usize::try_from(state).unwrap_or(0) % changed.len();
                changed[index] = Word::from_raw((state >> 32) as u32);
            }
            assert!(agrees(&Arena::new(changed, free, roots.clone())));
        }
    }
}

#[test]
fn truncation_and_extension_agree() {
    for seed in seeds() {
        let (words, free, roots) = seed.into_parts();
        for len in 0..words.len() {
            assert!(agrees(&Arena::new(
                words[..len].to_vec(),
                free,
                roots.clone()
            )));
        }
        let mut extended = words;
        extended.extend([Word::ZERO; 4]);
        assert!(agrees(&Arena::new(extended, free, roots)));
    }
}
