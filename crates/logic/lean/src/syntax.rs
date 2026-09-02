//! Typed syntax reconstructed from `lean4export` records.

use covalence_lib_json::Value;

macro_rules! index_type {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub usize);
    };
}

index_type!(
    /// Index into the export's name table.
    NameId
);
index_type!(
    /// Index into the export's universe-level table.
    LevelId
);
index_type!(
    /// Index into the export's expression table.
    ExprId
);

/// One Lean name node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Name {
    /// The implicit name at index zero.
    Anonymous,
    /// A string component following an earlier name.
    Str { prefix: NameId, value: String },
    /// A numeric component following an earlier name.
    Num { prefix: NameId, value: usize },
}

/// One Lean universe-level node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Level {
    /// The implicit universe level at index zero.
    Zero,
    /// Universe successor.
    Succ(LevelId),
    /// Maximum of two universes.
    Max(LevelId, LevelId),
    /// Impredicative maximum of two universes.
    IMax(LevelId, LevelId),
    /// Named universe parameter.
    Param(NameId),
}

/// Binder visibility stored in lambda and dependent-function expressions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// One Lean expression node, retaining table sharing through typed IDs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    BVar(usize),
    Sort(LevelId),
    Const {
        name: NameId,
        universes: Vec<LevelId>,
    },
    App {
        function: ExprId,
        argument: ExprId,
    },
    Lam {
        name: NameId,
        ty: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    },
    Forall {
        name: NameId,
        ty: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    },
    Let {
        name: NameId,
        ty: ExprId,
        value: ExprId,
        body: ExprId,
        nondependent: bool,
    },
    Proj {
        type_name: NameId,
        index: usize,
        structure: ExprId,
    },
    NatLit(String),
    StrLit(String),
    MData {
        expression: ExprId,
        data: Value,
    },
}

/// Lean's reducibility hint on a definition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(usize),
}

/// Safety metadata is input to a lowering backend, never parser policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// Lean's fixed quotient declaration roles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// Fields common to ordinary and generated declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationHeader {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
}

/// One inductive type specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InductiveType {
    pub header: DeclarationHeader,
    pub num_params: usize,
    pub num_indices: usize,
    pub all: Vec<NameId>,
    pub constructors: Vec<NameId>,
    pub num_nested: usize,
    pub is_recursive: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// One constructor specification in an inductive group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constructor {
    pub header: DeclarationHeader,
    pub inductive: NameId,
    pub constructor_index: usize,
    pub num_params: usize,
    pub num_fields: usize,
    pub is_unsafe: bool,
}

/// One recursor computation rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecursorRule {
    pub constructor: NameId,
    pub num_fields: usize,
    pub rhs: ExprId,
}

/// One generated recursor specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Recursor {
    pub header: DeclarationHeader,
    pub all: Vec<NameId>,
    pub num_params: usize,
    pub num_indices: usize,
    pub num_motives: usize,
    pub num_minors: usize,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// One declaration record in source/environment order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Declaration {
    Axiom {
        header: DeclarationHeader,
        is_unsafe: bool,
    },
    Definition {
        header: DeclarationHeader,
        value: ExprId,
        hints: ReducibilityHints,
        safety: DefinitionSafety,
        all: Vec<NameId>,
    },
    Opaque {
        header: DeclarationHeader,
        value: ExprId,
        all: Vec<NameId>,
        is_unsafe: bool,
    },
    Theorem {
        header: DeclarationHeader,
        value: ExprId,
        all: Vec<NameId>,
    },
    Quotient {
        header: DeclarationHeader,
        kind: QuotKind,
    },
    Inductive {
        types: Vec<InductiveType>,
        constructors: Vec<Constructor>,
        recursors: Vec<Recursor>,
    },
}

impl Declaration {
    /// Every name introduced by this declaration record.
    pub fn names(&self) -> impl Iterator<Item = NameId> + '_ {
        let mut names = Vec::new();
        match self {
            Self::Axiom { header, .. }
            | Self::Definition { header, .. }
            | Self::Opaque { header, .. }
            | Self::Theorem { header, .. }
            | Self::Quotient { header, .. } => names.push(header.name),
            Self::Inductive {
                types,
                constructors,
                recursors,
            } => {
                names.extend(types.iter().map(|item| item.header.name));
                names.extend(constructors.iter().map(|item| item.header.name));
                names.extend(recursors.iter().map(|item| item.header.name));
            }
        }
        names.into_iter()
    }
}

/// A source object a backend can associate with one or more HOL objects.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LeanSyntax {
    Name { id: NameId, value: Name },
    Level { id: LevelId, value: Level },
    Expr { id: ExprId, value: Expr },
    Declaration { ordinal: usize, value: Declaration },
}

/// Typed export tables accumulated in streaming order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tables {
    pub names: Vec<Name>,
    pub levels: Vec<Level>,
    pub expressions: Vec<Expr>,
    pub declarations: Vec<Declaration>,
}

impl Default for Tables {
    fn default() -> Self {
        Self {
            names: vec![Name::Anonymous],
            levels: vec![Level::Zero],
            expressions: Vec::new(),
            declarations: Vec::new(),
        }
    }
}

/// One typed record delivered to a lowering backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Record {
    Name(NameId),
    Level(LevelId),
    Expr(ExprId),
    Declaration(usize),
}

impl Record {
    /// Recover the source syntax selected by this record.
    #[must_use]
    pub fn syntax(&self, tables: &Tables) -> LeanSyntax {
        match *self {
            Self::Name(id) => LeanSyntax::Name {
                id,
                value: tables.names[id.0].clone(),
            },
            Self::Level(id) => LeanSyntax::Level {
                id,
                value: tables.levels[id.0].clone(),
            },
            Self::Expr(id) => LeanSyntax::Expr {
                id,
                value: tables.expressions[id.0].clone(),
            },
            Self::Declaration(ordinal) => LeanSyntax::Declaration {
                ordinal,
                value: tables.declarations[ordinal].clone(),
            },
        }
    }
}
