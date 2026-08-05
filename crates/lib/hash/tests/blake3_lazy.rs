use covalence_lib_hash::{
    Blake3Hash,
    blake3::lazy::{
        BuildError, CHUNK_BYTES, FixedTree, Geometry, GeometryError, ImmutableTree, LazyTree,
        LeafError, LeafIndex, LeafRequest, LeafResult, LeafValue, ReloadError, RootPlan,
        SQLITE_PAGE_BYTES, SupplyError,
    },
};

fn data(length: usize) -> Vec<u8> {
    (0u8..=250).cycle().take(length).collect()
}

fn leaves(geometry: Geometry, bytes: &[u8]) -> Vec<LeafValue> {
    (0..geometry.leaves())
        .map(|index| {
            let begin = usize::try_from(index * geometry.leaf_bytes()).unwrap();
            let end = (begin + usize::try_from(geometry.leaf_bytes()).unwrap()).min(bytes.len());
            LeafValue::from_bytes(geometry, LeafIndex(index), &bytes[begin..end]).unwrap()
        })
        .collect()
}

fn tree(bytes: &[u8], leaf_bytes: u64) -> FixedTree {
    let geometry = Geometry::new(bytes.len() as u64, leaf_bytes).unwrap();
    FixedTree::new(geometry, leaves(geometry, bytes)).unwrap()
}

fn answer(geometry: Geometry, request: LeafRequest, bytes: &[u8]) -> LeafResult {
    let range = request.bytes.clone();
    LeafResult::from_bytes(
        geometry,
        request,
        &bytes[usize::try_from(range.start).unwrap()..usize::try_from(range.end).unwrap()],
    )
    .unwrap()
}

#[test]
fn retained_subtrees_match_reference_blake3_for_irregular_shapes() {
    for leaf_bytes in [CHUNK_BYTES, SQLITE_PAGE_BYTES, 64 * 1024] {
        for length in [
            0, 1, 1_023, 1_024, 1_025, 4_095, 4_096, 4_097, 7_113, 16_385, 65_535, 65_536, 65_537,
            196_731,
        ] {
            let bytes = data(length);
            assert_eq!(
                tree(&bytes, leaf_bytes).root(),
                Blake3Hash::from_bytes(&bytes),
                "leaf_bytes={leaf_bytes}, length={length}"
            );
        }
    }
}

#[test]
fn geometry_rejects_noncanonical_retained_leaf_widths() {
    for leaf_bytes in [0, 1, 1_023, 1_025, 3_072, 6_144] {
        assert_eq!(
            Geometry::new(10_000, leaf_bytes),
            Err(GeometryError::InvalidLeafBytes { leaf_bytes })
        );
    }
}

#[test]
fn eager_sqlite_page_update_matches_one_shot_hash() {
    let mut bytes = data(9 * usize::try_from(SQLITE_PAGE_BYTES).unwrap() + 137);
    let mut tree = tree(&bytes, SQLITE_PAGE_BYTES);

    let page = LeafIndex(4);
    let begin = usize::try_from(page.0 * SQLITE_PAGE_BYTES).unwrap();
    let end = begin + usize::try_from(SQLITE_PAGE_BYTES).unwrap();
    bytes[begin..end].fill(0xa5);
    tree.update(LeafValue::from_bytes(tree.geometry(), page, &bytes[begin..end]).unwrap())
        .unwrap();

    assert_eq!(tree.root(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn eager_updates_cover_single_and_non_power_of_two_trees() {
    for length in [73, 3 * 1_024 + 17, 5 * 4_096 + 9] {
        let mut bytes = data(length);
        let mut tree = tree(&bytes, CHUNK_BYTES);
        let last = LeafIndex(tree.geometry().leaves() - 1);
        let begin = usize::try_from(last.0 * CHUNK_BYTES).unwrap();
        bytes[begin..].fill(0x5c);
        tree.update(LeafValue::from_bytes(tree.geometry(), last, &bytes[begin..]).unwrap())
            .unwrap();
        assert_eq!(tree.root(), Blake3Hash::from_bytes(&bytes));
    }
}

#[test]
fn dirty_list_preserves_order_and_coalesces_duplicate_dirties() {
    let bytes = data(6 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let mut tree = LazyTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    tree.dirty(LeafIndex(3)).unwrap();
    tree.dirty(LeafIndex(1)).unwrap();
    tree.dirty(LeafIndex(3)).unwrap();

    let RootPlan::Fetch(requests) = tree.plan() else {
        panic!("dirty tree should request leaves")
    };
    assert_eq!(
        requests
            .iter()
            .map(|request| request.index)
            .collect::<Vec<_>>(),
        vec![LeafIndex(3), LeafIndex(1)]
    );
    assert_eq!(tree.root(), None);
    assert_eq!(tree.stale_root(), Blake3Hash::from_bytes(&bytes));

    for request in requests {
        tree.supply(answer(geometry, request, &bytes)).unwrap();
    }
    assert_eq!(
        tree.plan(),
        RootPlan::Rebuild(vec![LeafIndex(3), LeafIndex(1)])
    );
    assert_eq!(tree.rebuild().unwrap(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn dirty_byte_range_selects_only_intersecting_sqlite_pages() {
    let bytes = data(8 * 4_096);
    let mut tree = LazyTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    tree.dirty_bytes(4_095..8_193).unwrap();
    let RootPlan::Fetch(requests) = tree.plan() else {
        panic!("range should dirty leaves")
    };
    assert_eq!(
        requests
            .iter()
            .map(|request| request.index)
            .collect::<Vec<_>>(),
        vec![LeafIndex(0), LeafIndex(1), LeafIndex(2)]
    );
}

#[test]
fn failed_external_fetch_leaves_an_exact_retryable_request() {
    let bytes = data(3 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let mut tree = LazyTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    tree.dirty(LeafIndex(2)).unwrap();

    let RootPlan::Fetch(mut requests) = tree.plan() else {
        panic!("leaf should need fetching")
    };
    let failed = requests.pop().unwrap();
    assert_eq!(failed.bytes, 8_192..12_288);

    // An I/O error is owned by the caller. Not supplying a result preserves
    // the same request and does not partially commit a tree update.
    assert_eq!(tree.rebuild().unwrap_err().missing, vec![failed.clone()]);
    assert_eq!(tree.plan(), RootPlan::Fetch(vec![failed.clone()]));
    tree.supply(answer(geometry, failed, &bytes)).unwrap();
    assert_eq!(tree.rebuild().unwrap(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn rebuild_waits_for_every_dirty_leaf_before_committing() {
    let mut bytes = data(4 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let old_root = Blake3Hash::from_bytes(&bytes);
    let mut tree = LazyTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    tree.dirty(LeafIndex(0)).unwrap();
    tree.dirty(LeafIndex(2)).unwrap();
    bytes[..4_096].fill(1);
    bytes[8_192..12_288].fill(2);

    let RootPlan::Fetch(requests) = tree.plan() else {
        panic!("leaves should need fetching")
    };
    tree.supply(answer(geometry, requests[0].clone(), &bytes))
        .unwrap();
    assert_eq!(
        tree.rebuild().unwrap_err().missing,
        vec![requests[1].clone()]
    );
    assert_eq!(tree.stale_root(), old_root);

    tree.supply(answer(geometry, requests[1].clone(), &bytes))
        .unwrap();
    assert_eq!(tree.rebuild().unwrap(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn results_are_bound_to_verifier_selected_ranges_and_dirty_state() {
    let bytes = data(2 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let mut tree = LazyTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    let forged = LeafRequest {
        index: LeafIndex(1),
        bytes: 0..4_096,
    };
    assert!(matches!(
        LeafResult::from_bytes(geometry, forged, &bytes[..4_096]),
        Err(LeafError::WrongRequest { .. })
    ));

    let request = LeafRequest {
        index: LeafIndex(1),
        bytes: 4_096..8_192,
    };
    assert_eq!(
        tree.supply(answer(geometry, request, &bytes)),
        Err(SupplyError::NotDirty(LeafIndex(1)))
    );
}

#[test]
fn values_are_bound_to_absolute_ranges_not_only_index_and_length() {
    // Both values are leaf 1 and exactly 4 KiB long, but their absolute BLAKE3
    // offsets differ because the retained-leaf widths differ.
    let wide = Geometry::new(12_288, 8_192).unwrap();
    let bytes = data(12_288);
    let wrong = LeafValue::from_bytes(wide, LeafIndex(1), &bytes[8_192..12_288]).unwrap();
    let mut target = tree(&bytes[..8_192], 4_096);

    assert_eq!(
        target.update(wrong),
        Err(LeafError::WrongValue {
            index: LeafIndex(1)
        })
    );

    let mut lazy = LazyTree::new(target);
    lazy.dirty(LeafIndex(1)).unwrap();
    let request = match lazy.plan() {
        RootPlan::Fetch(mut requests) => requests.remove(0),
        _ => panic!("leaf should need fetching"),
    };
    assert!(matches!(
        lazy.supply(LeafResult {
            request,
            value: wrong,
        }),
        Err(SupplyError::Leaf(LeafError::WrongValue {
            index: LeafIndex(1)
        }))
    ));
}

#[test]
fn immutable_eviction_retains_digest_and_rejects_changed_reload() {
    let bytes = data(5 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let mut tree = ImmutableTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    tree.evict(LeafIndex(2)).unwrap();

    let requests = tree.reload_plan(7_000..13_000).unwrap();
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].index, LeafIndex(2));
    let mut changed = bytes[8_192..12_288].to_vec();
    changed[17] ^= 0xff;
    let changed_result = LeafResult::from_bytes(geometry, requests[0].clone(), changed).unwrap();
    assert!(matches!(
        tree.accept_reload(changed_result),
        Err(ReloadError::Changed {
            index: LeafIndex(2),
            ..
        })
    ));
    assert_eq!(tree.reload_plan(7_000..13_000).unwrap().len(), 1);

    tree.accept_reload(answer(geometry, requests[0].clone(), &bytes))
        .unwrap();
    assert!(tree.reload_plan(7_000..13_000).unwrap().is_empty());
    assert_eq!(tree.root(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn immutable_state_can_enter_copy_on_write_without_file_bytes() {
    let mut bytes = data(3 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    let immutable = ImmutableTree::new(tree(&bytes, SQLITE_PAGE_BYTES));
    let mut cow = immutable.into_cow();
    cow.dirty(LeafIndex(1)).unwrap();
    bytes[4_096..8_192].fill(0xcc);
    let RootPlan::Fetch(mut requests) = cow.plan() else {
        panic!("COW update should request changed bytes")
    };
    cow.supply(answer(geometry, requests.remove(0), &bytes))
        .unwrap();
    assert_eq!(cow.rebuild().unwrap(), Blake3Hash::from_bytes(bytes));
}

#[test]
fn empty_tree_needs_no_evidence_and_cannot_be_dirtied() {
    let geometry = Geometry::new(0, SQLITE_PAGE_BYTES).unwrap();
    let tree = FixedTree::new(geometry, Vec::new()).unwrap();
    assert_eq!(tree.root(), Blake3Hash::from_bytes([]));
    let mut lazy = LazyTree::new(tree);
    assert_eq!(lazy.plan(), RootPlan::Clean(Blake3Hash::from_bytes([])));
    assert_eq!(
        lazy.dirty(LeafIndex(0)),
        Err(LeafError::OutOfBounds {
            index: LeafIndex(0),
            leaves: 0
        })
    );
}

#[test]
fn build_requires_exact_ordered_leaf_evidence() {
    let bytes = data(2 * 4_096);
    let geometry = Geometry::new(bytes.len() as u64, SQLITE_PAGE_BYTES).unwrap();
    assert_eq!(
        FixedTree::new(geometry, vec![leaves(geometry, &bytes)[0]]).err(),
        Some(BuildError::WrongLeafCount {
            expected: 2,
            actual: 1
        })
    );
    let mut reversed = leaves(geometry, &bytes);
    reversed.reverse();
    assert!(matches!(
        FixedTree::new(geometry, reversed),
        Err(BuildError::Leaf(LeafError::WrongValue { .. }))
    ));
}
