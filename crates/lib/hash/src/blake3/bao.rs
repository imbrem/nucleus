//! Interoperability with the canonical Bao verified-streaming formats.
//!
//! These adapters use the reference `bao` implementation. Decoding treats the
//! encoding and any separately supplied content as untrusted and returns only
//! bytes verified against a caller-provided pure [`Blake3Hash`]. Successfully
//! decoded bytes are authenticated; the input encoding is not asserted to be
//! canonical, because Bao permits equivalent and trailing representations.

use std::{
    io::{self, Cursor, Read},
    ops::Range,
};

use super::Blake3Hash;

/// Encodes all `data` in Bao's canonical combined format.
///
/// The returned root is the ordinary unkeyed BLAKE3 digest of `data`.
#[must_use]
pub fn encode_combined(data: impl AsRef<[u8]>) -> (Vec<u8>, Blake3Hash) {
    let (encoded, root) = ::bao::encode::encode(data);
    (encoded, from_bao(root))
}

/// Validates and decodes a Bao combined encoding.
///
/// # Errors
///
/// Returns an I/O error when the encoding is truncated, malformed, or does
/// not match `root`.
pub fn decode_combined(encoded: impl AsRef<[u8]>, root: Blake3Hash) -> io::Result<Vec<u8>> {
    let expected = to_bao(root);
    let mut reader = ::bao::decode::Decoder::new(encoded.as_ref(), &expected);
    let mut output = Vec::new();
    reader.read_to_end(&mut output)?;
    Ok(output)
}

/// Encodes the Bao tree for `data` in canonical outboard format.
///
/// The outboard contains the little-endian length prefix and parent nodes but
/// not `data`. The returned root is the ordinary unkeyed BLAKE3 digest.
#[must_use]
pub fn encode_outboard(data: impl AsRef<[u8]>) -> (Vec<u8>, Blake3Hash) {
    let (outboard, root) = ::bao::encode::outboard(data);
    (outboard, from_bao(root))
}

/// Validates `data` against a Bao outboard and BLAKE3 root.
///
/// The returned bytes are owned and authenticated. Neither input is trusted.
///
/// # Errors
///
/// Returns an I/O error when the outboard is truncated or malformed, or when
/// `data` does not match `root`.
pub fn decode_outboard(
    data: impl AsRef<[u8]>,
    outboard: impl AsRef<[u8]>,
    root: Blake3Hash,
) -> io::Result<Vec<u8>> {
    let supplied_length = data.as_ref().len();
    let data = Cursor::new(data.as_ref());
    let outboard = Cursor::new(outboard.as_ref());
    let expected = to_bao(root);
    let mut decoder = ::bao::decode::Decoder::new_outboard(data, outboard, &expected);
    let mut output = Vec::new();
    decoder.read_to_end(&mut output)?;
    if output.len() != supplied_length {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "outboard length does not match the supplied content",
        ));
    }
    Ok(output)
}

/// Extracts a canonical Bao slice from a combined encoding.
///
/// Extraction rearranges untrusted encoded bytes but does not authenticate
/// them. Pass the result to [`decode_slice`] with the expected root before use.
///
/// # Errors
///
/// Returns an I/O error for reversed ranges, truncated input, or ranges that
/// cannot be extracted from the encoding.
pub fn extract_slice(combined: impl AsRef<[u8]>, range: Range<u64>) -> io::Result<Vec<u8>> {
    let length = range_length(&range)?;
    let input = Cursor::new(combined.as_ref());
    let mut extractor = ::bao::encode::SliceExtractor::new(input, range.start, length);
    let mut encoded_slice = Vec::new();
    extractor.read_to_end(&mut encoded_slice)?;
    Ok(encoded_slice)
}

/// Extracts a canonical Bao slice from content and its outboard.
///
/// Bao slices always include disclosed content inline; there is no distinct
/// outboard-slice format. Extraction does not authenticate its inputs.
///
/// # Errors
///
/// Returns an I/O error for reversed ranges, truncated input, or ranges that
/// cannot be extracted from the content and outboard.
pub fn extract_slice_outboard(
    data: impl AsRef<[u8]>,
    outboard: impl AsRef<[u8]>,
    range: Range<u64>,
) -> io::Result<Vec<u8>> {
    let length = range_length(&range)?;
    let data = Cursor::new(data.as_ref());
    let outboard = Cursor::new(outboard.as_ref());
    let mut extractor =
        ::bao::encode::SliceExtractor::new_outboard(data, outboard, range.start, length);
    let mut encoded_slice = Vec::new();
    extractor.read_to_end(&mut encoded_slice)?;
    Ok(encoded_slice)
}

/// Validates and decodes one requested byte range from a Bao slice.
///
/// The returned bytes, and only those bytes, are authenticated against `root`.
/// Bao may disclose complete 1 KiB chunks around the request internally; those
/// extra bytes are not returned.
///
/// # Errors
///
/// Returns an I/O error for reversed ranges, a truncated or malformed slice,
/// an out-of-bounds request, or bytes that do not match `root`.
pub fn decode_slice(
    encoded_slice: impl AsRef<[u8]>,
    root: Blake3Hash,
    range: Range<u64>,
) -> io::Result<Vec<u8>> {
    let length = range_length(&range)?;
    let expected = to_bao(root);
    let mut decoder =
        ::bao::decode::SliceDecoder::new(encoded_slice.as_ref(), &expected, range.start, length);
    let capacity = usize::try_from(length)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range is too large"))?;
    let mut output = Vec::new();
    output.try_reserve_exact(capacity).map_err(|_| {
        io::Error::new(
            io::ErrorKind::OutOfMemory,
            "could not reserve the requested Bao slice",
        )
    })?;
    decoder.read_to_end(&mut output)?;
    if output.len() != capacity {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "Bao slice does not cover the complete requested range",
        ));
    }
    Ok(output)
}

fn range_length(range: &Range<u64>) -> io::Result<u64> {
    range.end.checked_sub(range.start).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "range start is greater than its end",
        )
    })
}

fn from_bao(root: ::bao::Hash) -> Blake3Hash {
    Blake3Hash::from_array(*root.as_bytes())
}

fn to_bao(root: Blake3Hash) -> ::bao::Hash {
    ::bao::Hash::from(*root.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input() -> Vec<u8> {
        (0_u16..5_000)
            .map(|index| u8::try_from(index % 251).unwrap())
            .collect()
    }

    #[test]
    fn combined_and_outboard_round_trip_to_the_same_blake3_root() {
        let data = input();
        let expected = Blake3Hash::from_bytes(&data);

        let (combined, combined_root) = encode_combined(&data);
        let (outboard, outboard_root) = encode_outboard(&data);

        assert_eq!(combined_root, expected);
        assert_eq!(outboard_root, expected);
        assert_eq!(
            decode_combined(&combined, expected).expect("decode combined"),
            data
        );
        assert_eq!(
            decode_outboard(&data, &outboard, expected).expect("decode outboard"),
            data
        );
    }

    #[test]
    fn single_chunk_encodings_match_the_canonical_wire_layout() {
        let (combined, root) = encode_combined(b"abc");
        let (outboard, outboard_root) = encode_outboard(b"abc");

        assert_eq!(root, Blake3Hash::from_bytes(b"abc"));
        assert_eq!(outboard_root, root);
        assert_eq!(combined, [3_u64.to_le_bytes().as_slice(), b"abc"].concat());
        assert_eq!(outboard, 3_u64.to_le_bytes());
    }

    #[test]
    fn corrupted_combined_content_outboard_and_roots_are_rejected() {
        let data = input();
        let (mut combined, root) = encode_combined(&data);
        let (mut outboard, _) = encode_outboard(&data);

        let combined_last = combined.len() - 1;
        combined[combined_last] ^= 1;
        assert!(decode_combined(&combined, root).is_err());

        outboard[8] ^= 1;
        assert!(decode_outboard(&data, &outboard, root).is_err());

        let mut corrupt_data = data.clone();
        corrupt_data[2_048] ^= 1;
        let (outboard, _) = encode_outboard(&data);
        assert!(decode_outboard(&corrupt_data, &outboard, root).is_err());

        let (short_outboard, short_root) = encode_outboard(b"prefix");
        assert!(decode_outboard(b"prefix plus suffix", short_outboard, short_root).is_err());

        assert!(
            decode_combined(encode_combined(&data).0, Blake3Hash::from_bytes(b"wrong")).is_err()
        );
    }

    #[test]
    fn combined_and_outboard_extract_the_same_validated_slice() {
        let data = input();
        let range = 777..3_333;
        let (combined, root) = encode_combined(&data);
        let (outboard, _) = encode_outboard(&data);

        let from_combined = extract_slice(&combined, range.clone()).expect("extract combined");
        let from_outboard =
            extract_slice_outboard(&data, &outboard, range.clone()).expect("extract outboard");

        assert_eq!(from_combined, from_outboard);
        let start = usize::try_from(range.start).unwrap();
        let end = usize::try_from(range.end).unwrap();
        assert_eq!(
            decode_slice(&from_combined, root, range.clone()).expect("validate slice"),
            data[start..end]
        );

        let mut corrupt = from_combined;
        let last = corrupt.len() - 1;
        corrupt[last] ^= 1;
        assert!(decode_slice(&corrupt, root, range).is_err());
    }

    #[test]
    fn empty_ranges_are_validated_and_invalid_ranges_are_rejected() {
        let data = input();
        let (combined, root) = encode_combined(&data);
        let encoded_slice = extract_slice(&combined, 1_500..1_500).expect("extract empty range");

        assert_eq!(
            decode_slice(&encoded_slice, root, 1_500..1_500).expect("validate empty range"),
            Vec::<u8>::new()
        );

        let reversed = Range { start: 10, end: 9 };
        assert_eq!(
            extract_slice(&combined, reversed).unwrap_err().kind(),
            io::ErrorKind::InvalidInput
        );

        let beyond = extract_slice(&combined, 6_000..6_001).expect("extract final proof");
        assert!(decode_slice(&beyond, root, 6_000..6_001).is_err());
    }
}
