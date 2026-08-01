use covalence_data_segment::{
    InsertError, KeyedSegmentMap, Segment, SegmentMap, SegmentRange, Translation,
};

fn range(lo: u64, hi: u64) -> SegmentRange {
    SegmentRange::new(lo, hi).unwrap()
}

#[test]
fn ranges_are_nonempty_half_open_geometry() {
    assert_eq!(SegmentRange::new(4, 4).unwrap_err().lo, 4);
    assert!(SegmentRange::new(7, 2).is_err());

    let span = range(4, 9);
    assert_eq!(span.width(), 5);
    assert!(!span.contains(3));
    assert!(span.contains(4));
    assert!(span.contains(8));
    assert!(!span.contains(9));
    assert!(span.overlaps(range(8, 12)));
    assert!(!span.overlaps(range(9, 12)));
}

#[test]
fn insertion_allows_adjacency_and_rejects_every_overlap_shape() {
    let mut map = SegmentMap::new();
    let middle = map.insert(range(10, 20), "middle").unwrap();
    map.insert(range(0, 10), "left").unwrap();
    map.insert(range(20, 30), "right").unwrap();

    for overlap in [
        range(9, 11),
        range(10, 11),
        range(19, 20),
        range(19, 21),
        range(5, 25),
        range(11, 19),
    ] {
        assert!(matches!(
            map.insert(overlap, "bad"),
            Err(InsertError::Overlap { .. })
        ));
    }

    assert_eq!(map.len(), 3);
    assert_eq!(map.get(10).unwrap().id(), middle);
    assert_eq!(map.get(19).unwrap().value(), &"middle");
    assert_eq!(map.get(30), None);
}

#[test]
fn overlap_queries_include_a_predecessor_and_remain_ordered() {
    let mut map = SegmentMap::new();
    for (lo, hi) in [(0, 4), (8, 12), (20, 24), (31, 40)] {
        map.insert(range(lo, hi), lo).unwrap();
    }

    let found = map
        .overlapping(range(2, 33))
        .map(Segment::range)
        .collect::<Vec<_>>();
    assert_eq!(
        found,
        vec![range(0, 4), range(8, 12), range(20, 24), range(31, 40)]
    );
    assert_eq!(map.overlapping(range(12, 20)).count(), 0);
}

#[test]
fn keyed_maps_isolate_geometry_and_allocate_global_ids() {
    let mut map = KeyedSegmentMap::new();
    let alpha = map.insert("alpha", range(0, 10), 1).unwrap();
    let beta = map.insert("beta", range(0, 10), 2).unwrap();

    assert_ne!(alpha, beta);
    assert_eq!(map.get(&"alpha", 5).unwrap().value(), &1);
    assert_eq!(map.get(&"beta", 5).unwrap().value(), &2);
    assert!(map.insert("alpha", range(9, 11), 3).is_err());
    assert_eq!(map.get_id(beta).unwrap().0, &"beta");

    let (key, removed) = map.remove(alpha).unwrap();
    assert_eq!(key, "alpha");
    assert_eq!(removed.range(), range(0, 10));
    assert_eq!(map.get(&"alpha", 5), None);
    assert_eq!(map.len(), 1);
}

#[test]
fn replacement_retires_old_ids_and_splits_all_intersections() {
    let mut map = SegmentMap::new();
    let first = map.insert(range(0, 10), 'a').unwrap();
    let second = map.insert(range(12, 20), 'b').unwrap();

    let surgery = map
        .replace(range(4, 16), 'x', |old, _retained| *old.value())
        .unwrap();
    assert_eq!(
        surgery.removed.iter().map(Segment::id).collect::<Vec<_>>(),
        vec![first, second]
    );
    assert_eq!(map.get_id(first), None);
    assert_eq!(map.get_id(second), None);
    assert_eq!(map.get(3).unwrap().value(), &'a');
    assert_eq!(map.get(4).unwrap().value(), &'x');
    assert_eq!(map.get(15).unwrap().value(), &'x');
    assert_eq!(map.get(16).unwrap().value(), &'b');
    assert_eq!(
        map.overlapping(range(0, 20))
            .map(Segment::range)
            .collect::<Vec<_>>(),
        vec![range(0, 4), range(4, 16), range(16, 20)]
    );
}

#[test]
fn range_removal_preserves_translated_source_offsets() {
    let mut map = SegmentMap::new();
    map.insert(
        range(100, 200),
        Translation {
            source: "source",
            source_lo: 1_000,
        },
    )
    .unwrap();

    map.remove_range(range(125, 175), |old, retained| Translation {
        source: old.value().source,
        source_lo: old.value().source_lo + retained.lo() - old.range().lo(),
    })
    .unwrap();

    let left = map.get(124).unwrap();
    assert_eq!(left.value().translate(left.range(), 124), Some(1_024));
    assert_eq!(map.get(125), None);
    let right = map.get(175).unwrap();
    assert_eq!(right.value().translate(right.range(), 175), Some(1_075));
    assert_eq!(right.value().translate(right.range(), 199), Some(1_099));
}

#[test]
fn deterministic_range_surgery_matches_a_point_model() {
    const WIDTH: usize = 64;
    let mut map = SegmentMap::new();
    let mut model = [None; WIDTH];
    let mut state = 0x243f_6a88_85a3_08d3_u64;

    for step in 0..500_u16 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let lo = usize::try_from(state % WIDTH as u64).unwrap();
        state = state.rotate_left(17);
        let hi = lo + 1 + usize::try_from(state % (WIDTH - lo) as u64).unwrap();
        let selected = range(lo as u64, hi as u64);

        if step % 4 == 0 {
            map.remove_range(selected, |old, _| *old.value()).unwrap();
            model[lo..hi].fill(None);
        } else {
            let value = u8::try_from(step % 251).unwrap();
            map.replace(selected, value, |old, _| *old.value()).unwrap();
            model[lo..hi].fill(Some(value));
        }

        for (point, expected) in model.iter().enumerate() {
            assert_eq!(
                map.get(point as u64).map(|segment| *segment.value()),
                *expected,
                "step {step}, point {point}"
            );
        }
        let segments = map.overlapping(range(0, WIDTH as u64)).collect::<Vec<_>>();
        assert!(
            segments
                .windows(2)
                .all(|pair| pair[0].range().hi() <= pair[1].range().lo())
        );
    }
}
