use covalence_logic_hol::{Kernel, Ref};
use covalence_logic_hol_derived::{
    LambdaSeqBinding, LambdaSeqEquationalLaw, LambdaSeqFiniteMonadModel, LambdaSeqInstruction,
    LambdaSeqNamedContext, LambdaSeqNamedTerm, LambdaSeqTerm, lambda_seq_equation,
};

fn identity_monad(
    kernel: &mut Kernel,
    objects: &[Ref],
) -> covalence_logic_hol_derived::LambdaSeqFiniteMonadModel {
    let mut model = LambdaSeqFiniteMonadModel::default();
    for (index, &object) in objects.iter().enumerate() {
        let value = kernel.tm_fv(100 + index as u64, object).unwrap();
        let pure = kernel.lam(value, value).unwrap();
        model.insert_object(object, object, pure);
    }
    for (source_index, &source) in objects.iter().enumerate() {
        for (target_index, &target) in objects.iter().enumerate() {
            let value = kernel
                .tm_fv(
                    200 + (source_index * objects.len() + target_index) as u64,
                    source,
                )
                .unwrap();
            let continuation_ty = kernel.ty_arr(source, target).unwrap();
            let continuation = kernel
                .tm_fv(
                    300 + (source_index * objects.len() + target_index) as u64,
                    continuation_ty,
                )
                .unwrap();
            let applied = kernel.app(continuation, value).unwrap();
            let continuation_lambda = kernel.lam(continuation, applied).unwrap();
            let bind = kernel.lam(value, continuation_lambda).unwrap();
            model.insert_bind(source, target, bind);
        }
    }
    model
}

#[test]
fn named_lowering_typing_and_monadic_denotation_live_in_hol() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let x = kernel.tm_fv(1, bool_ty).unwrap();
    let not_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    let not = kernel.tm_fv(2, not_ty).unwrap();
    let instruction = LambdaSeqInstruction {
        source: bool_ty,
        target: bool_ty,
        denotation: not,
    };
    let mut context = LambdaSeqNamedContext::default();
    context.push(
        10,
        LambdaSeqBinding {
            variable: x,
            ty: bool_ty,
        },
    );
    let named = LambdaSeqNamedTerm::Let(
        Some(11),
        Box::new(LambdaSeqNamedTerm::Var(10)),
        Box::new(LambdaSeqNamedTerm::Op(
            instruction,
            Box::new(LambdaSeqNamedTerm::Var(11)),
        )),
    );

    let lowered = named.lower(&kernel, &context).unwrap();
    assert!(matches!(
        lowered,
        LambdaSeqTerm::Let(_, ref body)
            if matches!(body.as_ref(), LambdaSeqTerm::Op(_, argument)
                if **argument == LambdaSeqTerm::Bound(0))
    ));
    assert_eq!(lowered.type_check(&kernel, &[]).unwrap(), bool_ty);

    let model = identity_monad(&mut kernel, &[bool_ty]);
    let denotation = lowered.denote(&mut kernel, &model).unwrap();
    assert_eq!(denotation.value_type, bool_ty);
    assert_eq!(kernel.classifier(denotation.term).unwrap(), bool_ty);

    let same = lowered.denote(&mut kernel, &model).unwrap();
    let equation = lambda_seq_equation(&mut kernel, bool_ty, denotation, same).unwrap();
    assert_eq!(kernel.classifier(equation.proposition).unwrap(), bool_ty);
    assert!(kernel.thm().live_theorems().next().is_none());

    let eta = LambdaSeqEquationalLaw::let_eta(&kernel, &[], LambdaSeqTerm::Free(x)).unwrap();
    let eta_equation = eta.denote(&mut kernel, bool_ty, &model, &[]).unwrap();
    assert_eq!(
        kernel.classifier(eta_equation.proposition).unwrap(),
        bool_ty
    );

    let beta = LambdaSeqEquationalLaw::let_beta(
        &kernel,
        &[],
        LambdaSeqTerm::Free(x),
        LambdaSeqTerm::Bound(0),
        &|_| true,
    )
    .unwrap();
    assert_eq!(beta.ty, bool_ty);
    assert!(
        LambdaSeqEquationalLaw::let_beta(
            &kernel,
            &[],
            LambdaSeqTerm::Op(instruction, Box::new(LambdaSeqTerm::Free(x))),
            LambdaSeqTerm::Bound(0),
            &|_| false,
        )
        .is_err()
    );
    let bind_op = LambdaSeqEquationalLaw::bind_op(
        &kernel,
        &[],
        instruction,
        LambdaSeqTerm::Free(x),
        LambdaSeqTerm::Bound(0),
    )
    .unwrap();
    assert_eq!(bind_op.ty, bool_ty);
    let bind_let = LambdaSeqEquationalLaw::bind_let(
        &kernel,
        &[],
        LambdaSeqTerm::Free(x),
        LambdaSeqTerm::Bound(0),
        LambdaSeqTerm::Bound(0),
    )
    .unwrap();
    assert_eq!(bind_let.ty, bool_ty);
}

#[test]
fn malformed_monad_dictionary_is_rejected_transactionally() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.tm_fv(1, bool_ty).unwrap();
    let term = LambdaSeqTerm::Free(value);
    let mut model = LambdaSeqFiniteMonadModel::default();
    model.insert_object(bool_ty, bool_ty, value);
    let before = kernel.arena().clone();

    assert!(term.denote(&mut kernel, &model).is_err());
    assert_eq!(*kernel.arena(), before);
}

#[test]
fn subtyping_is_not_a_typing_rule() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let other = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    let value = kernel.tm_fv(1, bool_ty).unwrap();
    let operation_ty = kernel.ty_arr(other, other).unwrap();
    let operation = kernel.tm_fv(2, operation_ty).unwrap();
    let term = LambdaSeqTerm::Op(
        LambdaSeqInstruction {
            source: other,
            target: other,
            denotation: operation,
        },
        Box::new(LambdaSeqTerm::Free(value)),
    );

    assert!(term.type_check(&kernel, &[]).is_err());
}
