use covalence_logic_hol::{Kernel, Lit};
use covalence_logic_hol_derived::{equality_symmetry, equality_transitivity};

fn positive(reference: covalence_logic_hol::Ref) -> Lit {
    Lit::positive(reference.get())
}

#[test]
fn symmetry_and_transitivity_are_userspace_derivations() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let x = kernel.tm_fv(1, bool_ty).unwrap();
    let y = kernel.tm_fv(2, bool_ty).unwrap();
    let z = kernel.tm_fv(3, bool_ty).unwrap();

    let xy = kernel.eq(bool_ty, x, y).unwrap();
    let yz = kernel.eq(bool_ty, y, z).unwrap();
    let xy_assumption = kernel.identity(positive(xy)).unwrap();
    let yz_assumption = kernel.identity(positive(yz)).unwrap();

    let symmetric = equality_symmetry(&mut kernel, bool_ty, xy_assumption).unwrap();
    assert_eq!((symmetric.left, symmetric.right), (y, x));
    let symmetric_theorem = kernel.thm().get(symmetric.theorem).unwrap();
    assert_eq!(
        symmetric_theorem
            .lhs
            .rows()
            .map(<[Lit]>::to_vec)
            .collect::<Vec<_>>(),
        vec![vec![positive(xy)]]
    );
    assert_eq!(
        symmetric_theorem
            .rhs
            .rows()
            .map(<[Lit]>::to_vec)
            .collect::<Vec<_>>(),
        vec![vec![positive(symmetric.equality)]]
    );

    let transitive =
        equality_transitivity(&mut kernel, bool_ty, xy_assumption, yz_assumption).unwrap();
    assert_eq!((transitive.left, transitive.right), (x, z));
    let transitive_theorem = kernel.thm().get(transitive.theorem).unwrap();
    assert_eq!(
        transitive_theorem
            .lhs
            .rows()
            .map(<[Lit]>::to_vec)
            .collect::<Vec<_>>(),
        vec![vec![positive(yz)], vec![positive(xy)]]
    );
    assert_eq!(
        transitive_theorem
            .rhs
            .rows()
            .map(<[Lit]>::to_vec)
            .collect::<Vec<_>>(),
        vec![vec![positive(transitive.equality)]]
    );
}

#[test]
fn transitivity_rejects_a_mismatched_middle_without_admission() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let x = kernel.tm_fv(1, bool_ty).unwrap();
    let y = kernel.tm_fv(2, bool_ty).unwrap();
    let z = kernel.tm_fv(3, bool_ty).unwrap();
    let xy = kernel.eq(bool_ty, x, y).unwrap();
    let xz = kernel.eq(bool_ty, x, z).unwrap();
    let left = kernel.identity(positive(xy)).unwrap();
    let right = kernel.identity(positive(xz)).unwrap();
    let before = kernel.arena().clone();

    assert!(equality_transitivity(&mut kernel, bool_ty, left, right).is_err());
    assert_eq!(*kernel.arena(), before);
}
