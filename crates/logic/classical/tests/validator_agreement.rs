//! The flat validator accepts exactly what the recursive one accepted.
//!
//! `Checked::check` used to decide two conjuncts by scanning: unique ownership
//! by comparing each newly claimed block against every block claimed so far,
//! and exact coverage by asking, for every address, whether some block
//! contains it. Both are now decided by marking a bitmap. The replacement is
//! only worth anything if it decides the *same* predicate, so this file keeps
//! a faithful transcription of the former algorithm and drives both over
//! hostile input.
//!
//! `reference` is that transcription, written against the arena's public word
//! accessors. It recurses and carries the old fuel counter, so it is limited
//! to shallow arenas -- which is the point of replacing it, and the reason the
//! depth tests live elsewhere.

use covalence_logic_classical::tagged::{Arena, Checked, Formula, Ref, Sequent, Word, pack};

// ---------------------------------------------------------------------------
// The former validator, transcribed.
// ---------------------------------------------------------------------------

mod reference {
    use super::{Arena, Formula, Ref, Sequent, Word};

    const PAYLOAD_WIDTH: u64 = 63;
    const RESERVED_WORDS: usize = 4;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct Block {
        pub base: usize,
        pub size_class: usize,
    }

    impl Block {
        fn capacity(self) -> Option<usize> {
            4_usize.checked_shl(u32::try_from(self.size_class).ok()?)
        }

        fn stop(self) -> Option<usize> {
            self.base.checked_add(self.capacity()?)
        }

        fn fits(self, size: usize) -> bool {
            self.base >= RESERVED_WORDS
                && self.base.is_multiple_of(4)
                && self.stop().is_some_and(|stop| stop <= size)
        }

        fn contains(self, address: usize) -> bool {
            self.stop()
                .is_some_and(|stop| self.base <= address && address < stop)
        }

        fn disjoint(self, other: Self) -> bool {
            self.stop().is_some_and(|stop| stop <= other.base)
                || other.stop().is_some_and(|stop| stop <= self.base)
        }
    }

    #[derive(Clone, Copy)]
    struct Header {
        block: Block,
        next: usize,
        prev: usize,
    }

    enum Nullable {
        Null,
        Address(usize),
    }

    #[derive(Debug)]
    pub struct Decoded {
        pub sequents: Vec<Sequent>,
        pub free: Vec<Block>,
    }

    struct View<'a> {
        words: &'a [Word],
        free_root: Word,
        roots: &'a [(Ref, Ref)],
    }

    fn pointer(word: Word) -> Option<usize> {
        if word.is_negative() || word.payload() == 0 || word.tag() != 0 {
            return None;
        }
        usize::try_from(word.base()).ok()
    }

    fn optional_pointer(word: Word) -> Option<Nullable> {
        if word == Word::ZERO {
            Some(Nullable::Null)
        } else {
            pointer(word).map(Nullable::Address)
        }
    }

    fn natural(word: Word) -> Option<u64> {
        (!word.is_negative()).then(|| word.payload())
    }

    impl View<'_> {
        fn word(&self, index: usize) -> Option<Word> {
            self.words.get(index).copied()
        }

        fn header(&self, base: usize) -> Option<Header> {
            if self.word(base)? != Word::ZERO {
                return None;
            }
            let next = pointer(self.word(base.checked_add(1)?)?)?;
            let prev = pointer(self.word(base.checked_add(2)?)?)?;
            let size_class = usize::try_from(natural(self.word(base.checked_add(3)?)?)?).ok()?;
            if size_class.checked_add(2)? > usize::try_from(PAYLOAD_WIDTH).ok()? {
                return None;
            }
            let block = Block { base, size_class };
            block
                .fits(self.words.len())
                .then_some(Header { block, next, prev })
        }

        fn zero_range(&self, start: usize, count: usize) -> bool {
            start
                .checked_add(count)
                .and_then(|stop| self.words.get(start..stop))
                .is_some_and(|words| words.iter().all(|word| *word == Word::ZERO))
        }

        fn ordinary_node(&self, header: Header) -> bool {
            header
                .block
                .capacity()
                .is_some_and(|capacity| self.zero_range(header.block.base + 4, capacity - 4))
        }

        fn walk_ring(
            &self,
            head: usize,
            expected_class: usize,
            special: Option<usize>,
        ) -> Option<Vec<Block>> {
            let mut current = head;
            let mut visited: Vec<Block> = Vec::new();
            for _ in 0..=self.words.len() {
                if visited.iter().any(|block| block.base == current) {
                    return None;
                }
                let header = self.header(current)?;
                if header.block.size_class != expected_class {
                    return None;
                }
                if special != Some(current) && !self.ordinary_node(header) {
                    return None;
                }
                let next_header = self.header(header.next)?;
                if next_header.prev != current {
                    return None;
                }
                visited.push(header.block);
                if header.next == head {
                    return Some(visited);
                }
                current = header.next;
            }
            None
        }

        fn directory_head(&self, root: Header, size_class: usize) -> Option<Nullable> {
            let address = root.block.base.checked_add(4)?.checked_add(size_class)?;
            optional_pointer(self.word(address)?)
        }

        fn root_padding(&self, root: Header) -> bool {
            root.block.capacity().is_some_and(|capacity| {
                let spare = capacity - 4;
                root.block.size_class <= spare
                    && self.zero_range(
                        root.block.base + 4 + root.block.size_class,
                        spare - root.block.size_class,
                    )
            })
        }

        fn decode_free(&self) -> Option<Vec<Block>> {
            let size = u64::try_from(self.words.len()).ok()?;
            if size > (1_u64 << PAYLOAD_WIDTH) {
                return None;
            }
            let root_base = match optional_pointer(self.free_root)? {
                Nullable::Null => return Some(Vec::new()),
                Nullable::Address(base) => base,
            };
            let root = self.header(root_base)?;
            if !self.root_padding(root) {
                return None;
            }
            let mut blocks = Vec::new();
            for size_class in 0..root.block.size_class {
                if let Nullable::Address(head) = self.directory_head(root, size_class)? {
                    blocks.extend(self.walk_ring(head, size_class, None)?);
                }
            }
            blocks.extend(self.walk_ring(root_base, root.block.size_class, Some(root_base))?);
            pairwise_disjoint(&blocks).then_some(blocks)
        }

        fn live_block(&self, base: u64) -> Option<Block> {
            let base = usize::try_from(base).ok()?;
            let size_class = usize::try_from(natural(self.word(base)?)?).ok()?;
            if size_class.checked_add(2)? > usize::try_from(PAYLOAD_WIDTH).ok()? {
                return None;
            }
            let block = Block { base, size_class };
            block.fits(self.words.len()).then_some(block)
        }

        fn read_live(&self, block: Block) -> Option<Vec<Ref>> {
            if self.live_block(u64::try_from(block.base).ok()?)? != block {
                return None;
            }
            let capacity = block.capacity()?;
            let start = block.base.checked_add(1)?;
            let words = self.words.get(start..start.checked_add(capacity - 1)?)?;
            let terminator = words.iter().position(|word| *word == Word::ZERO)?;
            if !words[terminator..].iter().all(|word| *word == Word::ZERO) {
                return None;
            }
            words[..terminator]
                .iter()
                .copied()
                .map(Ref::new)
                .collect::<Result<Vec<_>, _>>()
                .ok()
        }

        fn decode_ref(
            &self,
            free: &[Block],
            fuel: usize,
            live: &mut Vec<Block>,
            reference: Ref,
        ) -> Option<Formula> {
            let next_fuel = fuel.checked_sub(1)?;
            let word = reference.word();
            if word.tag() == 3 {
                return Some(Formula::Literal {
                    atom: word.base() / 4,
                    negative: word.is_negative(),
                });
            }
            let block = self.live_block(word.base())?;
            if live.iter().chain(free).any(|owned| !block.disjoint(*owned)) {
                return None;
            }
            let children = self.read_live(block)?;
            live.insert(0, block);
            let mut decoded = Vec::with_capacity(children.len());
            for child in children {
                decoded.push(self.decode_ref(free, next_fuel, live, child)?);
            }
            match word.tag() {
                0 => Some(Formula::And {
                    negative: word.is_negative(),
                    children: decoded,
                }),
                1 => Some(Formula::Or {
                    negative: word.is_negative(),
                    children: decoded,
                }),
                2 => Some(Formula::Sat {
                    negative: word.is_negative(),
                    children: decoded,
                }),
                _ => None,
            }
        }

        fn decode_state(&self) -> Option<Decoded> {
            if !self.zero_range(0, RESERVED_WORDS) {
                return None;
            }
            let free = self.decode_free()?;
            let fuel = self.words.len().checked_add(1)?;
            let mut live = Vec::new();
            let mut sequents = Vec::with_capacity(self.roots.len());
            for (premise, conclusion) in self.roots {
                let premise = self.decode_ref(&free, fuel, &mut live, *premise)?;
                let conclusion = self.decode_ref(&free, fuel, &mut live, *conclusion)?;
                sequents.push(Sequent {
                    premise,
                    conclusion,
                });
            }
            if !covers_storage(&live, &free, self.words.len()) {
                return None;
            }
            drop(live);
            Some(Decoded { sequents, free })
        }
    }

    fn pairwise_disjoint(blocks: &[Block]) -> bool {
        blocks.iter().enumerate().all(|(index, block)| {
            blocks[index + 1..]
                .iter()
                .all(|other| block.disjoint(*other))
        })
    }

    fn covers_storage(live: &[Block], free: &[Block], size: usize) -> bool {
        (RESERVED_WORDS..size)
            .all(|address| live.iter().chain(free).any(|block| block.contains(address)))
    }

    /// Validates one arena exactly as the recursive implementation did.
    pub fn check(arena: &Arena) -> Option<Decoded> {
        View {
            words: arena.words(),
            free_root: arena.free_root(),
            roots: arena.roots(),
        }
        .decode_state()
    }
}

// ---------------------------------------------------------------------------
// Shapes and mutation.
// ---------------------------------------------------------------------------

fn literal(atom: u64) -> Formula {
    Formula::Literal {
        atom,
        negative: atom.is_multiple_of(3),
    }
}

fn clause(tag: u64, width: u64) -> Formula {
    Formula::Or {
        negative: false,
        children: (0..width)
            .map(|index| literal(tag * 8 + index + 1))
            .collect(),
    }
}

/// Seed arenas: a matrix projection, a nested table, an empty table, and an
/// arena carrying free blocks so the intrusive rings are exercised too.
fn seeds() -> Vec<Arena> {
    let mut arenas = Vec::new();
    for rows in [0_u64, 1, 3] {
        for width in [1_u64, 2, 4] {
            let sequent = Sequent {
                premise: Formula::And {
                    negative: false,
                    children: (0..rows).map(|row| clause(row, width)).collect(),
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: (0..rows)
                        .map(|row| Formula::And {
                            negative: row % 2 == 1,
                            children: (0..width)
                                .map(|index| literal(row * 8 + index + 1))
                                .collect(),
                        })
                        .collect(),
                },
            };
            arenas.push(pack(&[sequent]).expect("packs").arena().clone());
        }
    }
    arenas.push(
        pack(
            &(0..4)
                .map(|index| Sequent {
                    premise: literal(index + 1),
                    conclusion: Formula::Sat {
                        negative: true,
                        children: vec![literal(index + 2), clause(index, 2)],
                    },
                })
                .collect::<Vec<_>>(),
        )
        .expect("packs")
        .arena()
        .clone(),
    );
    arenas.push(pack(&[]).expect("packs").arena().clone());

    // A canonical arena grown by one trailing free block, and the two-class
    // intrusive directory the runtime's own tests pin.
    let canonical = pack(&[Sequent {
        premise: literal(1),
        conclusion: literal(1),
    }])
    .expect("packs");
    let (mut words, _, roots) = canonical.arena().clone().into_parts();
    let base = u64::try_from(words.len()).expect("fits");
    let free = Word::pointer(base, 0, false).expect("fits");
    words.extend([Word::ZERO, free, free, Word::ZERO]);
    arenas.push(Arena::new(words, free, roots));

    let pointer = |base: u64| Word::pointer(base, 0, false).expect("fits");
    arenas.push(Arena::new(
        vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(4),
            pointer(4),
            Word::natural(1).expect("fits"),
            pointer(12),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(12),
            pointer(12),
            Word::ZERO,
        ],
        pointer(4),
        vec![],
    ));
    arenas
}

/// A deterministic 64-bit generator, so a failure is reproducible from its
/// seed alone.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).expect("bound fits")).expect("fits")
    }
}

/// The nearest four-aligned block base at or below `index`, never null.
fn aligned(index: usize) -> u64 {
    (u64::try_from(index).expect("index fits") / 4).max(1) * 4
}

/// Overwrites a handful of words with values chosen to look plausible: zeros,
/// literals, naturals, aligned pointers and sign flips are what a corrupted or
/// adversarial arena actually contains.
fn mutate(arena: &Arena, rng: &mut Rng) -> Arena {
    let (mut words, mut free_root, mut roots) = arena.clone().into_parts();
    if words.is_empty() {
        return Arena::new(words, free_root, roots);
    }
    for _ in 0..=rng.below(4) {
        let index = rng.below(words.len());
        let length = u64::try_from(words.len()).expect("fits");
        words[index] = match rng.below(7) {
            0 => Word::ZERO,
            1 => Word::natural(rng.next() % 4).expect("small natural fits"),
            2 => Word::literal(rng.next() % 8, rng.next().is_multiple_of(2)).expect("fits"),
            3 => Word::pointer(
                aligned(rng.below(words.len())),
                u8::try_from(rng.below(3)).expect("tag fits"),
                false,
            )
            .expect("pointer fits"),
            4 => Word::pointer((length / 4).max(1) * 4, 0, false).expect("pointer fits"),
            5 => words[index].negated(),
            _ => Word::from_raw(rng.next()),
        };
    }
    if rng.below(4) == 0 && !roots.is_empty() && !words.is_empty() {
        let slot = rng.below(roots.len());
        let candidate = Ref::new(
            Word::pointer(
                aligned(rng.below(words.len())),
                u8::try_from(rng.below(3)).expect("tag fits"),
                false,
            )
            .expect("pointer fits"),
        );
        if let Ok(candidate) = candidate {
            if rng.below(2) == 0 {
                roots[slot].0 = candidate;
            } else {
                roots[slot].1 = candidate;
            }
        }
    }
    if rng.below(8) == 0 {
        let keep = words.len().saturating_sub(1 + rng.below(4));
        words.truncate(keep);
    }
    if rng.below(8) == 0 {
        free_root = Word::ZERO;
    }
    Arena::new(words, free_root, roots)
}

/// Free blocks in the order the validator reports them.
///
/// Live blocks are no longer reported at all: the flat pass recovers them to
/// decide ownership and then forgets them, and nothing in the tree ever read
/// them.
fn free_blocks(checked: &Checked) -> Vec<(usize, usize)> {
    checked
        .free_blocks()
        .iter()
        .map(|block| (block.base(), block.size_class()))
        .collect()
}

fn reference_free_blocks(decoded: &reference::Decoded) -> Vec<(usize, usize)> {
    decoded
        .free
        .iter()
        .map(|block| (block.base, block.size_class))
        .collect()
}

/// Checks one arena both ways and reports whether the flat pass accepted it.
fn agree(arena: &Arena, label: &str) -> bool {
    let flat = Checked::check(arena.clone());
    let recursive = reference::check(arena);
    match (flat, recursive) {
        (Ok(flat), Some(recursive)) => {
            let decoded = flat.decode_sequents().expect("a checked arena decodes");
            assert_eq!(decoded, recursive.sequents, "{label}");
            assert_eq!(
                free_blocks(&flat),
                reference_free_blocks(&recursive),
                "{label}"
            );
            true
        }
        (Err(_), None) => false,
        (flat, recursive) => panic!(
            "{label}: flat accepted {} but the recursive validator accepted {}",
            flat.is_ok(),
            recursive.is_some()
        ),
    }
}

#[test]
fn the_seed_shapes_validate_identically() {
    for (index, arena) in seeds().iter().enumerate() {
        assert!(agree(arena, &format!("seed {index}")), "seed {index}");
    }
}

#[test]
fn every_single_word_corruption_is_judged_identically() {
    // Exhaustive rather than random: every word of a real arena set to each of
    // a fixed panel of hostile values.
    let arena = seeds().swap_remove(4);
    let panel = [
        Word::ZERO,
        Word::natural(0).expect("fits"),
        Word::natural(1).expect("fits"),
        Word::natural(64).expect("fits"),
        Word::literal(1, false).expect("fits"),
        Word::literal(1, true).expect("fits"),
        Word::pointer(4, 0, false).expect("fits"),
        Word::pointer(4, 1, false).expect("fits"),
        Word::pointer(8, 2, true).expect("fits"),
        Word::from_raw(1),
        Word::from_raw(u64::MAX),
    ];
    let mut accepted = 0_usize;
    for index in 0..arena.words().len() {
        for word in panel {
            let (mut words, free_root, roots) = arena.clone().into_parts();
            words[index] = word;
            let candidate = Arena::new(words, free_root, roots);
            if agree(&candidate, &format!("word {index} := {}", word.raw())) {
                accepted += 1;
            }
        }
    }
    // The unmodified word appears in the panel for some positions, so a few
    // mutations must survive; a run where nothing was accepted would mean the
    // agreement above was vacuous.
    assert!(accepted > 0, "no mutation was accepted");
}

#[test]
fn randomized_corruption_is_judged_identically() {
    let seeds = seeds();
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let mut accepted = 0_usize;
    for round in 0..40_000 {
        let arena = &seeds[round % seeds.len()];
        let candidate = mutate(arena, &mut rng);
        if agree(&candidate, &format!("round {round}")) {
            accepted += 1;
        }
    }
    assert!(accepted > 0, "no mutated arena was accepted");
}

#[test]
fn a_truncated_or_extended_word_array_is_judged_identically() {
    // Coverage is the conjunct the bitmap replaced by a running total, and a
    // word array that no tiling can reach is exactly what tests it.
    let arena = seeds().swap_remove(4);
    for extra in 0..8 {
        let (mut words, free_root, roots) = arena.clone().into_parts();
        words.extend(std::iter::repeat_n(Word::ZERO, extra));
        agree(
            &Arena::new(words, free_root, roots),
            &format!("extended by {extra}"),
        );
    }
    for missing in 1..8 {
        let (mut words, free_root, roots) = arena.clone().into_parts();
        let keep = words.len().saturating_sub(missing);
        words.truncate(keep);
        agree(
            &Arena::new(words, free_root, roots),
            &format!("truncated by {missing}"),
        );
    }
}
