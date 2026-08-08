//! BLAKE3 written in the const-evaluable subset of Rust.
//!
//! The [`blake3`](::blake3) crate is vectorized and is not `const`, so every
//! constant derived from a hash had to be computed out of band, checked into
//! the source as hexadecimal, and validated in a test. This module is a
//! transcription of the BLAKE3 reference implementation that uses only `while`
//! loops, integer arithmetic, and slice splitting, so the same derivations can
//! be written where the compiler will perform them.
//!
//! Const evaluation is an interpreter and this code compresses one block at a
//! time, so it is orders of magnitude slower than the runtime implementation.
//! It is meant for the short inputs that appear in constants — context strings
//! and path segments — not for hashing data at run time.
//!
//! Every mode here is checked against the [`blake3`](::blake3) crate in the
//! tests, over inputs that cross block, chunk, and subtree boundaries.

/// The digest and key length in bytes.
const OUT_LEN: usize = 32;

/// The compression-function block length in bytes.
const BLOCK_LEN: usize = 64;

/// The length of a leaf chunk in bytes.
const CHUNK_LEN: usize = 1024;

/// [`CHUNK_LEN`] as an input offset.
const CHUNK_LEN_OFFSET: u64 = 1024;

/// The greatest number of chaining values a stack can hold.
///
/// An input is at most `2^64` bytes, so it has at most `2^54` chunks, and the
/// stack holds one value per one bit of the chunk count.
const MAX_DEPTH: usize = 54;

const CHUNK_START: u32 = 1;
const CHUNK_END: u32 = 2;
const PARENT: u32 = 4;
const ROOT: u32 = 8;
const KEYED_HASH: u32 = 16;
const DERIVE_KEY_CONTEXT: u32 = 32;
const DERIVE_KEY_MATERIAL: u32 = 64;

/// The BLAKE3 initialization vector, shared with SHA-256.
const IV: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

/// The permutation applied to the message words between rounds.
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// The quarter-round mixing function.
const fn g(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(mx);
    state[d] = (state[d] ^ state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(12);
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(my);
    state[d] = (state[d] ^ state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(7);
}

/// Mixes the four columns and then the four diagonals of the state.
const fn round(state: &mut [u32; 16], message: &[u32; 16]) {
    g(state, 0, 4, 8, 12, message[0], message[1]);
    g(state, 1, 5, 9, 13, message[2], message[3]);
    g(state, 2, 6, 10, 14, message[4], message[5]);
    g(state, 3, 7, 11, 15, message[6], message[7]);
    g(state, 0, 5, 10, 15, message[8], message[9]);
    g(state, 1, 6, 11, 12, message[10], message[11]);
    g(state, 2, 7, 8, 13, message[12], message[13]);
    g(state, 3, 4, 9, 14, message[14], message[15]);
}

/// Reorders the message words for the next round.
const fn permute(message: &mut [u32; 16]) {
    let mut permuted = [0; 16];
    let mut index = 0;
    while index < 16 {
        permuted[index] = message[MSG_PERMUTATION[index]];
        index += 1;
    }
    *message = permuted;
}

/// Splits a chunk counter into its low and high words.
#[allow(clippy::cast_possible_truncation)]
const fn counter_words(counter: u64) -> (u32, u32) {
    (counter as u32, (counter >> 32) as u32)
}

/// Narrows a block length, which is at most [`BLOCK_LEN`].
#[allow(clippy::cast_possible_truncation)]
const fn block_word(len: usize) -> u32 {
    debug_assert!(len <= BLOCK_LEN);
    len as u32
}

/// The BLAKE3 compression function.
const fn compress(
    chaining_value: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [u32; 16] {
    let (counter_low, counter_high) = counter_words(counter);
    let mut state = [
        chaining_value[0],
        chaining_value[1],
        chaining_value[2],
        chaining_value[3],
        chaining_value[4],
        chaining_value[5],
        chaining_value[6],
        chaining_value[7],
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        counter_low,
        counter_high,
        block_len,
        flags,
    ];
    let mut message = *block_words;

    let mut index = 0;
    while index < 7 {
        round(&mut state, &message);
        if index < 6 {
            permute(&mut message);
        }
        index += 1;
    }

    let mut index = 0;
    while index < 8 {
        state[index] ^= state[index + 8];
        state[index + 8] ^= chaining_value[index];
        index += 1;
    }
    state
}

/// Truncates a compression output to a chaining value.
const fn first_words(state: &[u32; 16]) -> [u32; 8] {
    [
        state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7],
    ]
}

/// Reads a block as little-endian message words.
const fn block_words(block: &[u8; BLOCK_LEN]) -> [u32; 16] {
    let mut words = [0; 16];
    let mut index = 0;
    while index < 16 {
        words[index] = u32::from_le_bytes([
            block[index * 4],
            block[index * 4 + 1],
            block[index * 4 + 2],
            block[index * 4 + 3],
        ]);
        index += 1;
    }
    words
}

/// Writes eight words as little-endian bytes.
const fn words_bytes(words: &[u32; 8]) -> [u8; OUT_LEN] {
    let mut bytes = [0; OUT_LEN];
    let mut index = 0;
    while index < 8 {
        let word = words[index].to_le_bytes();
        bytes[index * 4] = word[0];
        bytes[index * 4 + 1] = word[1];
        bytes[index * 4 + 2] = word[2];
        bytes[index * 4 + 3] = word[3];
        index += 1;
    }
    bytes
}

/// Reads a 32-byte key as little-endian key words.
const fn key_words(key: &[u8; OUT_LEN]) -> [u32; 8] {
    let mut words = [0; 8];
    let mut index = 0;
    while index < 8 {
        words[index] = u32::from_le_bytes([
            key[index * 4],
            key[index * 4 + 1],
            key[index * 4 + 2],
            key[index * 4 + 3],
        ]);
        index += 1;
    }
    words
}

/// A compression that has not yet been told whether it is a root.
struct Output {
    input_chaining_value: [u32; 8],
    block_words: [u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
}

impl Output {
    /// Compresses this node as an interior node of the tree.
    const fn chaining_value(&self) -> [u32; 8] {
        first_words(&compress(
            &self.input_chaining_value,
            &self.block_words,
            self.counter,
            self.block_len,
            self.flags,
        ))
    }

    /// Compresses this node as the root, taking the first 32 output bytes.
    const fn root_bytes(&self) -> [u8; OUT_LEN] {
        words_bytes(&first_words(&compress(
            &self.input_chaining_value,
            &self.block_words,
            0,
            self.block_len,
            self.flags | ROOT,
        )))
    }
}

/// Builds the parent of two chaining values.
const fn parent_output(left: &[u32; 8], right: &[u32; 8], key: &[u32; 8], flags: u32) -> Output {
    let mut words = [0; 16];
    let mut index = 0;
    while index < 8 {
        words[index] = left[index];
        words[index + 8] = right[index];
        index += 1;
    }
    Output {
        input_chaining_value: *key,
        block_words: words,
        counter: 0,
        block_len: block_word(BLOCK_LEN),
        flags: flags | PARENT,
    }
}

/// Compresses the parent of two chaining values as an interior node.
const fn parent_cv(left: &[u32; 8], right: &[u32; 8], key: &[u32; 8], flags: u32) -> [u32; 8] {
    parent_output(left, right, key, flags).chaining_value()
}

/// One leaf chunk in progress.
struct ChunkState {
    chaining_value: [u32; 8],
    chunk_counter: u64,
    block: [u8; BLOCK_LEN],
    block_len: usize,
    blocks_compressed: usize,
    flags: u32,
}

impl ChunkState {
    const fn new(key: &[u32; 8], chunk_counter: u64, flags: u32) -> Self {
        Self {
            chaining_value: *key,
            chunk_counter,
            block: [0; BLOCK_LEN],
            block_len: 0,
            blocks_compressed: 0,
            flags,
        }
    }

    /// Returns how much of this chunk has been absorbed.
    const fn len(&self) -> usize {
        BLOCK_LEN * self.blocks_compressed + self.block_len
    }

    /// Returns [`CHUNK_START`] while the first block is still current.
    const fn start_flag(&self) -> u32 {
        if self.blocks_compressed == 0 {
            CHUNK_START
        } else {
            0
        }
    }

    /// Absorbs input, which must not overflow the chunk.
    const fn update(&mut self, mut input: &[u8]) {
        while !input.is_empty() {
            if self.block_len == BLOCK_LEN {
                let words = block_words(&self.block);
                self.chaining_value = first_words(&compress(
                    &self.chaining_value,
                    &words,
                    self.chunk_counter,
                    block_word(BLOCK_LEN),
                    self.flags | self.start_flag(),
                ));
                self.blocks_compressed += 1;
                self.block = [0; BLOCK_LEN];
                self.block_len = 0;
            }

            let want = BLOCK_LEN - self.block_len;
            let take = if input.len() < want {
                input.len()
            } else {
                want
            };
            let (head, tail) = input.split_at(take);
            let mut index = 0;
            while index < take {
                self.block[self.block_len + index] = head[index];
                index += 1;
            }
            self.block_len += take;
            input = tail;
        }
    }

    /// Closes the chunk over its final, possibly partial, block.
    const fn output(&self) -> Output {
        Output {
            input_chaining_value: self.chaining_value,
            block_words: block_words(&self.block),
            counter: self.chunk_counter,
            block_len: block_word(self.block_len),
            flags: self.flags | self.start_flag() | CHUNK_END,
        }
    }
}

/// An incremental BLAKE3 tree hasher.
///
/// `start_counter` is the chunk index of the first chunk of the input, which is
/// zero for a whole input and the subtree's offset when hashing a subtree. The
/// stack merges on the count of chunks within this hasher's own subtree, so an
/// offset subtree merges into the same shape it would have inside a whole
/// input.
struct Hasher {
    chunk_state: ChunkState,
    key: [u32; 8],
    start_counter: u64,
    cv_stack: [[u32; 8]; MAX_DEPTH],
    cv_stack_len: usize,
    flags: u32,
}

impl Hasher {
    const fn new(key: [u32; 8], flags: u32, start_counter: u64) -> Self {
        Self {
            chunk_state: ChunkState::new(&key, start_counter, flags),
            key,
            start_counter,
            cv_stack: [[0; 8]; MAX_DEPTH],
            cv_stack_len: 0,
            flags,
        }
    }

    const fn push_stack(&mut self, chaining_value: [u32; 8]) {
        self.cv_stack[self.cv_stack_len] = chaining_value;
        self.cv_stack_len += 1;
    }

    const fn pop_stack(&mut self) -> [u32; 8] {
        self.cv_stack_len -= 1;
        self.cv_stack[self.cv_stack_len]
    }

    /// Merges a finished chunk in, closing every subtree the count completes.
    const fn add_chunk_chaining_value(&mut self, mut chaining_value: [u32; 8], mut chunks: u64) {
        while chunks & 1 == 0 {
            let left = self.pop_stack();
            chaining_value = parent_cv(&left, &chaining_value, &self.key, self.flags);
            chunks >>= 1;
        }
        self.push_stack(chaining_value);
    }

    const fn update(&mut self, mut input: &[u8]) {
        while !input.is_empty() {
            if self.chunk_state.len() == CHUNK_LEN {
                let chaining_value = self.chunk_state.output().chaining_value();
                let counter = self.chunk_state.chunk_counter;
                self.add_chunk_chaining_value(chaining_value, counter - self.start_counter + 1);
                let key = self.key;
                self.chunk_state = ChunkState::new(&key, counter + 1, self.flags);
            }

            let want = CHUNK_LEN - self.chunk_state.len();
            let take = if input.len() < want {
                input.len()
            } else {
                want
            };
            let (head, tail) = input.split_at(take);
            self.chunk_state.update(head);
            input = tail;
        }
    }

    /// Folds the stack into the node covering the whole input.
    const fn output(&self) -> Output {
        let mut output = self.chunk_state.output();
        let mut remaining = self.cv_stack_len;
        while remaining > 0 {
            remaining -= 1;
            let right = output.chaining_value();
            output = parent_output(&self.cv_stack[remaining], &right, &self.key, self.flags);
        }
        output
    }

    const fn finalize(&self) -> [u8; OUT_LEN] {
        self.output().root_bytes()
    }

    const fn finalize_non_root(&self) -> [u8; OUT_LEN] {
        words_bytes(&self.output().chaining_value())
    }
}

/// Hashes `input` with a key and flags already in tree form.
const fn hash_with(key: [u32; 8], flags: u32, input: &[u8]) -> [u8; OUT_LEN] {
    let mut hasher = Hasher::new(key, flags, 0);
    hasher.update(input);
    hasher.finalize()
}

/// Computes the unkeyed BLAKE3 hash of `input`.
pub(crate) const fn hash(input: &[u8]) -> [u8; OUT_LEN] {
    hash_with(IV, 0, input)
}

/// Computes the BLAKE3 hash of `input` under a 32-byte `key`.
pub(crate) const fn keyed_hash(key: &[u8; OUT_LEN], input: &[u8]) -> [u8; OUT_LEN] {
    hash_with(key_words(key), KEYED_HASH, input)
}

/// Hashes a derive-key context string into a context key.
pub(crate) const fn hash_derive_key_context(context: &str) -> [u8; OUT_LEN] {
    hash_with(IV, DERIVE_KEY_CONTEXT, context.as_bytes())
}

/// Hashes key material under an already derived context key.
pub(crate) const fn hash_from_context_key(
    context_key: &[u8; OUT_LEN],
    input: &[u8],
) -> [u8; OUT_LEN] {
    hash_with(key_words(context_key), DERIVE_KEY_MATERIAL, input)
}

/// Derives key material from a context string.
pub(crate) const fn derive_key(context: &str, input: &[u8]) -> [u8; OUT_LEN] {
    hash_from_context_key(&hash_derive_key_context(context), input)
}

/// Returns the greatest number of chunks a subtree at `counter` may cover.
const fn max_subtree_chunks(counter: u64) -> u64 {
    if counter == 0 {
        u64::MAX
    } else {
        1 << counter.trailing_zeros()
    }
}

/// Computes the chaining value of a non-root subtree at `input_offset`.
///
/// # Panics
///
/// Panics for empty input, an offset that is not chunk-aligned, or input too
/// long for a subtree at that offset.
pub(crate) const fn subtree_chaining_value(input_offset: u64, input: &[u8]) -> [u8; OUT_LEN] {
    assert!(!input.is_empty(), "a subtree must not be empty");
    assert!(
        input_offset.is_multiple_of(CHUNK_LEN_OFFSET),
        "a subtree must start on a chunk boundary"
    );
    let counter = input_offset / CHUNK_LEN_OFFSET;
    assert!(
        input.len().div_ceil(CHUNK_LEN) as u64 <= max_subtree_chunks(counter),
        "a subtree must not exceed the greatest subtree at its offset"
    );

    let mut hasher = Hasher::new(IV, 0, counter);
    hasher.update(input);
    hasher.finalize_non_root()
}

/// Merges two chaining values into a non-root parent.
pub(crate) const fn merge_non_root(left: &[u8; OUT_LEN], right: &[u8; OUT_LEN]) -> [u8; OUT_LEN] {
    words_bytes(&parent_cv(&key_words(left), &key_words(right), &IV, 0))
}

/// Merges two chaining values into a root digest.
pub(crate) const fn merge_root(left: &[u8; OUT_LEN], right: &[u8; OUT_LEN]) -> [u8; OUT_LEN] {
    parent_output(&key_words(left), &key_words(right), &IV, 0).root_bytes()
}
