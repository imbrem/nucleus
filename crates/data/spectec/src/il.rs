//! Typed inventory of elaborated `SpecTec` IL declarations.
//!
//! This layer deliberately stops at the declaration boundary. It records every
//! top-level declaration and recursive-group member without assigning meaning
//! to expression bodies. A semantic lowering can therefore be exhaustive over
//! this inventory without making the S-expression reader part of the TCB.

use std::num::NonZeroU32;

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr};
use covalence_lib_error::snafu::Snafu;

use crate::{AstError, Limits, ParsedAst, parse_ast};

/// One-based position of a top-level form in an elaborated IL document.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RootOrdinal(NonZeroU32);

impl RootOrdinal {
    /// Constructs a one-based root position.
    #[must_use]
    pub const fn new(value: u32) -> Option<Self> {
        match NonZeroU32::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    /// Returns the one-based integer position.
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

/// The four declaration forms emitted by the pinned `SpecTec` IL printer.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IlKind {
    /// A `typ` declaration.
    Type,
    /// A `def` declaration.
    Definition,
    /// A `gram` declaration.
    Grammar,
    /// A `rel` declaration.
    Relation,
}

impl IlKind {
    fn from_head(head: &str) -> Option<Self> {
        match head {
            "typ" => Some(Self::Type),
            "def" => Some(Self::Definition),
            "gram" => Some(Self::Grammar),
            "rel" => Some(Self::Relation),
            _ => None,
        }
    }
}

/// Stable structural selector for one declaration in an IL document.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeclarationId {
    root: RootOrdinal,
    member: Option<NonZeroU32>,
}

/// Stable structural selector for a nested `rule` form.
///
/// `path` contains one-based child positions from the selected declaration's
/// outer list to the rule list. Names remain audit metadata rather than part
/// of identity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleId {
    declaration: DeclarationId,
    path: Vec<NonZeroU32>,
}

/// Stable structural selector for a nested `clause` form.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClauseId {
    declaration: DeclarationId,
    path: Vec<NonZeroU32>,
}

impl ClauseId {
    /// Constructs a clause selector from one-based child positions.
    ///
    /// Returns `None` for an empty path or any zero position.
    #[must_use]
    pub fn new(declaration: DeclarationId, path: impl IntoIterator<Item = u32>) -> Option<Self> {
        let path = structural_path(path)?;
        Some(Self { declaration, path })
    }

    /// Returns the containing declaration selector.
    #[must_use]
    pub const fn declaration(&self) -> DeclarationId {
        self.declaration
    }

    /// Returns the one-based expression path within the declaration.
    #[must_use]
    pub fn path(&self) -> impl ExactSizeIterator<Item = u32> + '_ {
        self.path.iter().map(|position| position.get())
    }
}

impl RuleId {
    /// Constructs a rule selector from one-based child positions.
    ///
    /// Returns `None` for an empty path or any zero position.
    #[must_use]
    pub fn new(declaration: DeclarationId, path: impl IntoIterator<Item = u32>) -> Option<Self> {
        let path = structural_path(path)?;
        Some(Self { declaration, path })
    }

    /// Returns the containing declaration selector.
    #[must_use]
    pub const fn declaration(&self) -> DeclarationId {
        self.declaration
    }

    /// Returns the one-based expression path within the declaration.
    #[must_use]
    pub fn path(&self) -> impl ExactSizeIterator<Item = u32> + '_ {
        self.path.iter().map(|position| position.get())
    }
}

/// One nested rule discovered inside an elaborated declaration.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IlRule {
    id: RuleId,
    name: String,
}

/// One nested definition clause in the elaborated document.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IlClause {
    id: ClauseId,
}

/// Parser-independent view of one elaborated IL node.
///
/// Lists expose only their arity. Text-bearing atom variants borrow their
/// decoded spelling; binary literals, addresses, and other atom families stay
/// distinguishable as [`Other`](Self::Other) without leaking parser types into
/// the IL API.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IlNode<'a> {
    /// Proper list with this many children.
    List(usize),
    /// Ordinary identifier.
    Symbol(&'a str),
    /// Decoded quoted text.
    String(&'a str),
    /// Exact numeric spelling.
    Number(&'a str),
    /// Any other recognized atomic family.
    Other,
}

/// Parser-independent cursor into one elaborated IL declaration.
///
/// A cursor is a cheap structural address. It composes without exposing the
/// backing S-expression representation, so semantic schemas can be written in
/// terms of lists and atoms and retain an exact source path for diagnostics.
#[derive(Clone, Debug)]
pub struct IlCursor<'a> {
    expression: &'a Expr,
    declaration: DeclarationId,
    path: Vec<u32>,
}

impl<'a> IlCursor<'a> {
    /// Returns the containing declaration selector.
    #[must_use]
    pub const fn declaration(&self) -> DeclarationId {
        self.declaration
    }

    /// Returns the one-based child path from the declaration root.
    #[must_use]
    pub fn path(&self) -> &[u32] {
        &self.path
    }

    /// Returns this node's parser-independent shape.
    #[must_use]
    pub fn node(&self) -> IlNode<'a> {
        node_view(self.expression)
    }

    /// Resolves a zero-based list child.
    #[must_use]
    pub fn child(&self, index: usize) -> Option<Self> {
        let items = list_items(self.expression)?;
        let arity = items.len();
        if index >= arity {
            return None;
        }
        let position = u32::try_from(index).ok()?.checked_add(1)?;
        let mut path = self.path.clone();
        path.push(position);
        Some(Self {
            expression: &items[index],
            declaration: self.declaration,
            path,
        })
    }

    /// Iterates direct list children in exact source order.
    #[must_use]
    pub fn children(&self) -> IlChildren<'a> {
        let arity = match self.node() {
            IlNode::List(arity) => arity,
            _ => 0,
        };
        IlChildren {
            parent: self.clone(),
            next: 0,
            arity,
        }
    }

    /// Returns the first child when it is an ordinary identifier.
    #[must_use]
    pub fn head(&self) -> Option<&'a str> {
        match self.child(0)?.node() {
            IlNode::Symbol(value) => Some(value),
            _ => None,
        }
    }

    /// Views this list as a symbolic-head schema form.
    #[must_use]
    pub fn form(&self) -> Option<IlForm<'a>> {
        let IlNode::List(arity) = self.node() else {
            return None;
        };
        Some(IlForm {
            cursor: self.clone(),
            head: self.head()?,
            arguments: arity - 1,
        })
    }
}

/// Exact-size iterator over the direct children of an [`IlCursor`].
#[derive(Clone, Debug)]
pub struct IlChildren<'a> {
    parent: IlCursor<'a>,
    next: usize,
    arity: usize,
}

/// A symbolic-head list viewed as one schema form.
///
/// The same head may have different meanings in different IL categories. This
/// view therefore exposes structure without assigning a global interpretation;
/// category-specific decoders compose over its arguments.
#[derive(Clone, Debug)]
pub struct IlForm<'a> {
    cursor: IlCursor<'a>,
    head: &'a str,
    arguments: usize,
}

impl<'a> IlForm<'a> {
    /// Returns the exact symbolic head.
    #[must_use]
    pub const fn head(&self) -> &'a str {
        self.head
    }

    /// Returns the cursor for the complete form.
    #[must_use]
    pub fn cursor(&self) -> &IlCursor<'a> {
        &self.cursor
    }

    /// Returns the number of arguments after the symbolic head.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.arguments
    }

    /// Returns whether the form has no arguments.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Resolves a zero-based argument after the symbolic head.
    #[must_use]
    pub fn argument(&self, index: usize) -> Option<IlCursor<'a>> {
        self.cursor.child(index.checked_add(1)?)
    }

    /// Iterates arguments after the symbolic head in exact source order.
    #[must_use]
    pub fn arguments(&self) -> impl ExactSizeIterator<Item = IlCursor<'a>> + '_ {
        self.cursor.children().skip(1)
    }
}

impl<'a> Iterator for IlChildren<'a> {
    type Item = IlCursor<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.next;
        if index >= self.arity {
            return None;
        }
        self.next += 1;
        self.parent.child(index)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.arity - self.next;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for IlChildren<'_> {}

impl IlClause {
    /// Returns the stable structural selector.
    #[must_use]
    pub const fn id(&self) -> &ClauseId {
        &self.id
    }
}

impl IlRule {
    /// Returns the stable structural selector.
    #[must_use]
    pub const fn id(&self) -> &RuleId {
        &self.id
    }

    /// Returns the exact name emitted by `SpecTec`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl DeclarationId {
    /// Constructs a structural selector.
    ///
    /// A zero root or recursive member is not a valid one-based position.
    #[must_use]
    pub const fn new(root: u32, member: Option<u32>) -> Option<Self> {
        let Some(root) = RootOrdinal::new(root) else {
            return None;
        };
        let member = match member {
            Some(value) => {
                let Some(value) = NonZeroU32::new(value) else {
                    return None;
                };
                Some(value)
            }
            None => None,
        };
        Some(Self { root, member })
    }

    /// Returns the containing top-level root.
    #[must_use]
    pub const fn root(self) -> RootOrdinal {
        self.root
    }

    /// Returns the one-based member position for a recursive group.
    ///
    /// `None` identifies an ordinary, non-recursive top-level declaration.
    #[must_use]
    pub const fn member(self) -> Option<u32> {
        match self.member {
            Some(member) => Some(member.get()),
            None => None,
        }
    }
}

/// Metadata for one direct declaration or recursive-group member.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IlDeclaration {
    id: DeclarationId,
    kind: IlKind,
    name: String,
}

impl IlDeclaration {
    /// Returns the stable structural selector.
    #[must_use]
    pub const fn id(&self) -> DeclarationId {
        self.id
    }

    /// Returns the declaration form.
    #[must_use]
    pub const fn kind(&self) -> IlKind {
        self.kind
    }

    /// Returns the exact name emitted by `SpecTec`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns whether this declaration belongs to a recursive group.
    #[must_use]
    pub const fn is_recursive(&self) -> bool {
        self.id.member.is_some()
    }
}

/// Metadata for one top-level IL form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IlRoot {
    ordinal: RootOrdinal,
    recursive: bool,
    declarations: std::ops::Range<usize>,
}

impl IlRoot {
    /// Returns the one-based source position.
    #[must_use]
    pub const fn ordinal(&self) -> RootOrdinal {
        self.ordinal
    }

    /// Returns whether the top-level form is a `rec` group.
    #[must_use]
    pub const fn is_recursive(&self) -> bool {
        self.recursive
    }
}

/// A bounded IL document whose complete declaration envelope is recognized.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IlDocument {
    parsed: ParsedAst,
    roots: Vec<IlRoot>,
    declarations: Vec<IlDeclaration>,
}

/// Structurally decoded body of one elaborated IL declaration.
#[derive(Clone, Debug)]
pub enum IlDeclarationBody<'a> {
    /// `typ`: parameters followed by family instances.
    Type {
        /// Declaration parameters.
        parameters: Vec<IlBinding<'a>>,
        /// `inst` forms defining the type family.
        instances: Vec<IlTypeInstance<'a>>,
    },
    /// `def`: parameters, result type, and equational clauses.
    Definition {
        /// Declaration parameters.
        parameters: Vec<IlBinding<'a>>,
        /// Declared result type.
        result: IlCursor<'a>,
        /// `clause` forms defining the function.
        clauses: Vec<IlCursor<'a>>,
    },
    /// `gram`: parameters, result type, and productions.
    Grammar {
        /// Declaration parameters.
        parameters: Vec<IlBinding<'a>>,
        /// Synthesized attribute type.
        result: IlCursor<'a>,
        /// `prod` forms defining the grammar.
        productions: Vec<IlCursor<'a>>,
    },
    /// `rel`: notation, argument type, and inference rules.
    Relation {
        /// Exact mixfix notation emitted by `SpecTec`.
        notation: &'a str,
        /// Type of the relation's argument tuple.
        argument: IlCursor<'a>,
        /// `rule` forms defining the relation.
        rules: Vec<IlCursor<'a>>,
    },
}

/// One instantiated branch of a type-family declaration.
#[derive(Clone, Debug)]
pub struct IlTypeInstance<'a> {
    bindings: Vec<IlBinding<'a>>,
    arguments: Vec<IlArgument<'a>>,
    definition: IlTypeDefinition<'a>,
}

impl<'a> IlTypeInstance<'a> {
    /// Returns locally quantified bindings in source order.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns type-family indices selecting this instance.
    #[must_use]
    pub fn arguments(&self) -> &[IlArgument<'a>] {
        &self.arguments
    }

    /// Returns the structural definition of the selected type.
    #[must_use]
    pub const fn definition(&self) -> &IlTypeDefinition<'a> {
        &self.definition
    }
}

/// Structural body of one type-family instance.
#[derive(Clone, Debug)]
pub enum IlTypeDefinition<'a> {
    /// Alias of another IL type.
    Alias(IlType<'a>),
    /// Tagged alternatives.
    Variant(Vec<IlTypeCase<'a>>),
    /// Named record fields.
    Struct(Vec<IlTypeField<'a>>),
}

/// One tagged alternative in a variant type.
#[derive(Clone, Debug)]
pub struct IlTypeCase<'a> {
    name: &'a str,
    bindings: Vec<IlBinding<'a>>,
    payload: IlType<'a>,
    premises: Vec<IlPremise<'a>>,
}

impl<'a> IlTypeCase<'a> {
    /// Returns the exact constructor spelling.
    #[must_use]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// Returns constructor-local bindings in source order.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns the type of the constructor payload.
    #[must_use]
    pub const fn payload(&self) -> &IlType<'a> {
        &self.payload
    }

    /// Returns constructor side conditions in source order.
    #[must_use]
    pub fn premises(&self) -> &[IlPremise<'a>] {
        &self.premises
    }
}

/// One named field in a structural record type.
#[derive(Clone, Debug)]
pub struct IlTypeField<'a> {
    name: &'a str,
    bindings: Vec<IlBinding<'a>>,
    value: IlType<'a>,
    premises: Vec<IlPremise<'a>>,
}

impl<'a> IlTypeField<'a> {
    /// Returns the exact field spelling.
    #[must_use]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// Returns field-local bindings in source order.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns the type of the field value.
    #[must_use]
    pub const fn value(&self) -> &IlType<'a> {
        &self.value
    }

    /// Returns field side conditions in source order.
    #[must_use]
    pub fn premises(&self) -> &[IlPremise<'a>] {
        &self.premises
    }
}

/// One declaration partitioned according to the authoritative IL schema.
#[derive(Clone, Debug)]
pub struct IlDeclarationSchema<'a> {
    declaration: &'a IlDeclaration,
    body: IlDeclarationBody<'a>,
}

/// One type in the generic elaborated-IL schema.
#[derive(Clone, Debug)]
pub enum IlType<'a> {
    /// Named type, possibly instantiated by heterogeneous arguments.
    Named {
        /// Exact type identifier.
        name: &'a str,
        /// Type-family arguments.
        arguments: Vec<IlArgument<'a>>,
    },
    /// Built-in Boolean type.
    Boolean,
    /// Built-in text type.
    Text,
    /// Built-in numeric type spelling such as `nat`, `i32`, or `f64`.
    Numeric(&'a str),
    /// Dependent tuple type.
    Tuple(Vec<IlTypeBinding<'a>>),
    /// Optional, list, nonempty-list, or fixed-length iteration.
    Iterated {
        /// Element type.
        element: Box<IlType<'a>>,
        /// Iteration shape.
        iteration: IlIteration<'a>,
    },
}

/// One heterogeneous argument to a named IL type.
#[derive(Clone, Debug)]
pub enum IlArgument<'a> {
    /// Expression argument.
    Expression(IlExpression<'a>),
    /// Type argument.
    Type(Box<IlType<'a>>),
    /// Definition argument identified by its exact declaration name.
    Definition(&'a str),
    /// Grammar-symbol argument, retained for grammar lowering.
    Grammar(IlCursor<'a>),
}

/// One explicit binder in a declaration body.
#[derive(Clone, Debug)]
pub enum IlBinding<'a> {
    /// Expression variable with its inferred IL type.
    Expression {
        /// Exact variable name.
        name: &'a str,
        /// Inferred type.
        ty: IlType<'a>,
    },
    /// Type variable.
    Type {
        /// Exact type-variable name.
        name: &'a str,
    },
    /// Higher-order definition parameter.
    Definition {
        /// Exact definition-variable name.
        name: &'a str,
        /// Nested declaration parameters.
        parameters: Vec<IlCursor<'a>>,
        /// Result type.
        result: IlType<'a>,
    },
    /// Higher-order grammar parameter.
    Grammar {
        /// Exact grammar-variable name.
        name: &'a str,
        /// Nested declaration parameters.
        parameters: Vec<IlCursor<'a>>,
        /// Synthesized result type.
        result: IlType<'a>,
    },
}

impl<'a> IlBinding<'a> {
    /// Decodes one explicit binding form.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown binding category, malformed name,
    /// malformed nested parameter, or invalid result type.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        decode_binding(cursor)
    }

    /// Returns the exact bound name.
    #[must_use]
    pub const fn name(&self) -> &'a str {
        match self {
            Self::Expression { name, .. }
            | Self::Type { name }
            | Self::Definition { name, .. }
            | Self::Grammar { name, .. } => name,
        }
    }
}

/// One expression-indexed component of an IL tuple type.
#[derive(Clone, Debug)]
pub struct IlTypeBinding<'a> {
    binder: IlCursor<'a>,
    ty: IlType<'a>,
}

impl<'a> IlTypeBinding<'a> {
    /// Returns the binding expression (`_` for an ordinary product field).
    #[must_use]
    pub const fn binder(&self) -> &IlCursor<'a> {
        &self.binder
    }

    /// Returns the component type.
    #[must_use]
    pub const fn ty(&self) -> &IlType<'a> {
        &self.ty
    }
}

/// Iteration shape attached to an IL type, expression, grammar, or premise.
#[derive(Clone, Debug)]
pub enum IlIteration<'a> {
    /// Optional value (`?`).
    Optional,
    /// Possibly empty sequence (`*`).
    List,
    /// Nonempty sequence (`+`).
    NonEmptyList,
    /// Sequence with an expression-defined length and optional index binder.
    Fixed {
        /// Length expression.
        length: IlCursor<'a>,
        /// Optional exact index-binder name.
        binder: Option<&'a str>,
    },
}

impl<'a> IlType<'a> {
    /// Decodes one type using the generic elaborated-IL schema.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown type constructor, malformed type-family
    /// argument, malformed tuple binding, or invalid iteration shape.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        match cursor.node() {
            IlNode::Symbol("bool") => Ok(Self::Boolean),
            IlNode::Symbol("text") => Ok(Self::Text),
            IlNode::Symbol(name) => Ok(Self::Numeric(name)),
            IlNode::List(_) => decode_type_form(cursor),
            _ => Err(schema_error(
                cursor.declaration(),
                cursor.path(),
                "IL type",
                describe(cursor),
            )),
        }
    }
}

/// Contextual constructor of one elaborated IL expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IlExpressionKind {
    /// Variable reference.
    Variable,
    /// Boolean literal.
    Boolean,
    /// Numeric literal.
    Number,
    /// Text literal.
    Text,
    /// Unary operation.
    Unary,
    /// Binary operation.
    Binary,
    /// Comparison.
    Comparison,
    /// Tuple expression.
    Tuple,
    /// Tuple projection.
    Projection,
    /// Variant construction.
    Case,
    /// Variant elimination.
    Uncase,
    /// Optional expression.
    Optional,
    /// Optional-value extraction.
    UnwrapOptional,
    /// Record expression.
    Struct,
    /// Record field selection.
    Dot,
    /// Record composition.
    Compose,
    /// List expression.
    List,
    /// Subtype lift.
    Lift,
    /// Membership expression.
    Membership,
    /// Sequence length.
    Length,
    /// Sequence concatenation.
    Concatenate,
    /// Sequence indexing.
    Index,
    /// Sequence slice.
    Slice,
    /// Functional path update.
    Update,
    /// Functional path extension.
    Extend,
    /// Definition application.
    Call,
    /// Iterated expression.
    Iterate,
    /// Numeric conversion.
    Convert,
    /// Type inclusion.
    Subtype,
}

/// One expression recognized by the generic elaborated-IL schema.
#[derive(Clone, Debug)]
pub struct IlExpression<'a> {
    cursor: IlCursor<'a>,
    kind: IlExpressionKind,
}

impl<'a> IlExpression<'a> {
    /// Decodes one contextual expression constructor.
    ///
    /// Child expressions remain addressable through [`arguments`](Self::arguments),
    /// allowing semantic consumers to recurse according to the constructor.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown expression form or wrong constructor
    /// arity.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        let form = required_form(cursor, "IL expression")?;
        let (kind, arity) = expression_shape(form.head()).ok_or_else(|| {
            schema_error(
                cursor.declaration(),
                cursor.path(),
                "known IL expression constructor",
                describe(cursor),
            )
        })?;
        arity.require(&form)?;
        Ok(Self {
            cursor: cursor.clone(),
            kind,
        })
    }

    /// Returns the contextual expression constructor.
    #[must_use]
    pub const fn kind(&self) -> IlExpressionKind {
        self.kind
    }

    /// Returns the exact structural cursor for this expression.
    #[must_use]
    pub const fn cursor(&self) -> &IlCursor<'a> {
        &self.cursor
    }

    /// Iterates constructor arguments after the symbolic head.
    #[must_use]
    pub fn arguments(&self) -> impl ExactSizeIterator<Item = IlCursor<'a>> + '_ {
        self.cursor.children().skip(1)
    }

    /// Validates this expression and every contextually nested schema node.
    ///
    /// # Errors
    ///
    /// Returns an error at the exact structural path of the first malformed
    /// atom, expression, argument, type, iteration domain, or update path.
    pub fn validate(&self) -> Result<(), IlSchemaError> {
        validate_expression(self)
    }

    /// Returns the direct semantic child expressions in deterministic order.
    ///
    /// Wrapper nodes such as call arguments, record fields, iteration domains,
    /// and update paths are traversed here, so consumers can implement a
    /// generic bottom-up fold without knowing their positional encoding.
    ///
    /// # Errors
    ///
    /// Returns an error at the first malformed node in this expression tree.
    pub fn children(&self) -> Result<Vec<Self>, IlSchemaError> {
        self.validate()?;
        expression_child_cursors(self)?
            .iter()
            .map(Self::decode)
            .collect()
    }
}

/// One relation rule or relation-valued premise.
#[derive(Clone, Debug)]
pub struct IlRuleSchema<'a> {
    cursor: IlCursor<'a>,
    name: &'a str,
    bindings: Vec<IlBinding<'a>>,
    notation: &'a str,
    conclusion: IlExpression<'a>,
    premises: Vec<IlPremise<'a>>,
}

impl<'a> IlRuleSchema<'a> {
    /// Decodes the shared schema used by top-level relation rules and nested
    /// relation premises.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed name, binding, notation, conclusion,
    /// or premise.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        decode_rule_schema(cursor)
    }

    /// Returns the exact rule name.
    #[must_use]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// Returns explicit rule bindings in source order.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns the exact relation notation.
    #[must_use]
    pub const fn notation(&self) -> &'a str {
        self.notation
    }

    /// Returns the rule conclusion expression.
    #[must_use]
    pub const fn conclusion(&self) -> &IlExpression<'a> {
        &self.conclusion
    }

    /// Returns premises in exact source order.
    #[must_use]
    pub fn premises(&self) -> &[IlPremise<'a>] {
        &self.premises
    }

    /// Returns the complete rule cursor.
    #[must_use]
    pub const fn cursor(&self) -> &IlCursor<'a> {
        &self.cursor
    }
}

/// One premise in an elaborated IL rule, clause, production, or type case.
#[derive(Clone, Debug)]
pub enum IlPremise<'a> {
    /// Invocation of another relation.
    Rule(Box<IlRuleSchema<'a>>),
    /// Boolean side condition.
    If(IlExpression<'a>),
    /// Pattern binding `where left = right`.
    Let {
        /// Binding pattern.
        left: IlExpression<'a>,
        /// Bound expression.
        right: IlExpression<'a>,
    },
    /// Fallback clause marker.
    Otherwise,
    /// Iterated premise; its iteration and domains retain structural cursors
    /// for the expression lowerer.
    Iterated {
        /// Repeated premise.
        premise: Box<IlPremise<'a>>,
        /// Iteration shape.
        iteration: IlIteration<'a>,
        /// Domains binding iteration variables.
        domains: Vec<IlDomain<'a>>,
    },
}

/// One named expression domain of an iterated premise.
#[derive(Clone, Debug)]
pub struct IlDomain<'a> {
    name: &'a str,
    expression: IlExpression<'a>,
}

impl<'a> IlDomain<'a> {
    /// Returns the bound domain name.
    #[must_use]
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// Returns the expression producing the domain sequence.
    #[must_use]
    pub const fn expression(&self) -> &IlExpression<'a> {
        &self.expression
    }
}

/// One equational definition clause.
#[derive(Clone, Debug)]
pub struct IlClauseSchema<'a> {
    cursor: IlCursor<'a>,
    bindings: Vec<IlBinding<'a>>,
    arguments: Vec<IlArgument<'a>>,
    result: IlExpression<'a>,
    premises: Vec<IlPremise<'a>>,
}

impl<'a> IlClauseSchema<'a> {
    /// Decodes one `clause` form.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed bindings, arguments, result expression,
    /// or premises.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        decode_clause_schema(cursor)
    }

    /// Returns explicit clause bindings.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns left-hand-side arguments.
    #[must_use]
    pub fn arguments(&self) -> &[IlArgument<'a>] {
        &self.arguments
    }

    /// Returns the right-hand-side expression.
    #[must_use]
    pub const fn result(&self) -> &IlExpression<'a> {
        &self.result
    }

    /// Returns side conditions in source order.
    #[must_use]
    pub fn premises(&self) -> &[IlPremise<'a>] {
        &self.premises
    }

    /// Returns the complete clause cursor.
    #[must_use]
    pub const fn cursor(&self) -> &IlCursor<'a> {
        &self.cursor
    }
}

/// One attribute-grammar production.
#[derive(Clone, Debug)]
pub struct IlProductionSchema<'a> {
    cursor: IlCursor<'a>,
    bindings: Vec<IlBinding<'a>>,
    symbol: IlCursor<'a>,
    result: IlExpression<'a>,
    premises: Vec<IlPremise<'a>>,
}

impl<'a> IlProductionSchema<'a> {
    /// Decodes one `prod` form.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed bindings, a missing grammar symbol,
    /// malformed result expression, or premises.
    pub fn decode(cursor: &IlCursor<'a>) -> Result<Self, IlSchemaError> {
        decode_production_schema(cursor)
    }

    /// Returns explicit production bindings.
    #[must_use]
    pub fn bindings(&self) -> &[IlBinding<'a>] {
        &self.bindings
    }

    /// Returns the grammar-symbol subtree.
    #[must_use]
    pub const fn symbol(&self) -> &IlCursor<'a> {
        &self.symbol
    }

    /// Returns the synthesized result expression.
    #[must_use]
    pub const fn result(&self) -> &IlExpression<'a> {
        &self.result
    }

    /// Returns production side conditions in source order.
    #[must_use]
    pub fn premises(&self) -> &[IlPremise<'a>] {
        &self.premises
    }

    /// Returns the complete production cursor.
    #[must_use]
    pub const fn cursor(&self) -> &IlCursor<'a> {
        &self.cursor
    }
}

#[derive(Clone, Copy)]
enum SchemaArity {
    Exact(usize),
    Between(usize, usize),
    AtLeast(usize),
    Any,
}

impl SchemaArity {
    fn require(self, form: &IlForm<'_>) -> Result<(), IlSchemaError> {
        let valid = match self {
            Self::Exact(value) => form.len() == value,
            Self::Between(minimum, maximum) => (minimum..=maximum).contains(&form.len()),
            Self::AtLeast(minimum) => form.len() >= minimum,
            Self::Any => true,
        };
        if valid {
            Ok(())
        } else {
            Err(schema_error(
                form.cursor().declaration(),
                form.cursor().path(),
                "valid expression constructor arity",
                format!("form {:?} with {} arguments", form.head(), form.len()),
            ))
        }
    }
}

fn expression_shape(head: &str) -> Option<(IlExpressionKind, SchemaArity)> {
    use IlExpressionKind as K;
    use SchemaArity::{Any, AtLeast, Between, Exact};
    Some(match head {
        "var" => (K::Variable, Exact(1)),
        "bool" => (K::Boolean, Exact(1)),
        "num" => (K::Number, Exact(1)),
        "text" => (K::Text, Exact(1)),
        "un" => (K::Unary, Exact(3)),
        "bin" => (K::Binary, Exact(4)),
        "cmp" => (K::Comparison, Exact(4)),
        "tup" => (K::Tuple, Any),
        "proj" => (K::Projection, Exact(2)),
        "case" => (K::Case, Exact(2)),
        "uncase" => (K::Uncase, Exact(2)),
        "opt" => (K::Optional, Between(0, 1)),
        "unopt" => (K::UnwrapOptional, Exact(1)),
        "struct" => (K::Struct, Any),
        "dot" => (K::Dot, Exact(2)),
        "comp" => (K::Compose, Exact(2)),
        "list" => (K::List, Any),
        "lift" => (K::Lift, Exact(1)),
        "mem" => (K::Membership, Exact(2)),
        "len" => (K::Length, Exact(1)),
        "cat" => (K::Concatenate, Exact(2)),
        "idx" => (K::Index, Exact(2)),
        "slice" => (K::Slice, Exact(3)),
        "upd" => (K::Update, Exact(3)),
        "ext" => (K::Extend, Exact(3)),
        "call" => (K::Call, AtLeast(1)),
        "iter" => (K::Iterate, AtLeast(2)),
        "cvt" => (K::Convert, Exact(3)),
        "sub" => (K::Subtype, Exact(3)),
        _ => return None,
    })
}

fn validate_expression(expression: &IlExpression<'_>) -> Result<(), IlSchemaError> {
    use IlExpressionKind as K;
    let form = required_form(expression.cursor(), "decoded expression")?;
    match expression.kind() {
        K::Variable => {
            require_string_argument(&form, 0, "variable identifier")?;
        }
        K::Boolean => {
            let value = require_symbol_argument(&form, 0, "Boolean literal")?;
            if !matches!(value, "true" | "false") {
                return Err(schema_error(
                    form.cursor().declaration(),
                    &child_path(&form, 0),
                    "Boolean literal true or false",
                    format!("symbol {value:?}"),
                ));
            }
        }
        K::Number => validate_number(&required_argument(&form, 0, "numeric literal")?)?,
        K::Text => {
            require_string_argument(&form, 0, "text literal")?;
        }
        K::Unary => {
            require_symbol_argument(&form, 0, "unary operator")?;
            require_symbol_argument(&form, 1, "unary operand type")?;
            validate_expression_argument(&form, 2, "unary operand")?;
        }
        K::Binary | K::Comparison => {
            require_symbol_argument(&form, 0, "binary operator")?;
            require_symbol_argument(&form, 1, "binary operand type")?;
            validate_expression_argument(&form, 2, "left operand")?;
            validate_expression_argument(&form, 3, "right operand")?;
        }
        K::Tuple | K::List => {
            for argument in form.arguments() {
                IlExpression::decode(&argument)?.validate()?;
            }
        }
        K::Projection => {
            validate_expression_argument(&form, 0, "projected expression")?;
            require_number_argument(&form, 1, "tuple projection index")?;
        }
        K::Case => {
            require_string_argument(&form, 0, "variant mixfix operator")?;
            validate_expression_argument(&form, 1, "variant payload")?;
        }
        K::Uncase => {
            validate_expression_argument(&form, 0, "variant expression")?;
            require_string_argument(&form, 1, "variant mixfix operator")?;
        }
        K::Optional => {
            if !form.is_empty() {
                validate_expression_argument(&form, 0, "optional payload")?;
            }
        }
        K::UnwrapOptional | K::Lift | K::Length => {
            validate_expression_argument(&form, 0, "unary expression payload")?;
        }
        K::Struct => {
            for field in form.arguments() {
                validate_expression_field(&field)?;
            }
        }
        K::Dot => {
            validate_expression_argument(&form, 0, "record expression")?;
            require_string_argument(&form, 1, "record field operator")?;
        }
        K::Compose | K::Membership | K::Concatenate | K::Index => {
            validate_expression_argument(&form, 0, "left expression")?;
            validate_expression_argument(&form, 1, "right expression")?;
        }
        K::Slice => {
            for index in 0..3 {
                validate_expression_argument(&form, index, "slice expression")?;
            }
        }
        K::Update | K::Extend => {
            validate_expression_argument(&form, 0, "updated expression")?;
            validate_path(&required_argument(&form, 1, "update path")?)?;
            validate_expression_argument(&form, 2, "update value")?;
        }
        K::Call => {
            validate_call(&form)?;
        }
        K::Iterate => {
            validate_iterated_expression(&form)?;
        }
        K::Convert => {
            require_symbol_argument(&form, 0, "source numeric type")?;
            require_symbol_argument(&form, 1, "target numeric type")?;
            validate_expression_argument(&form, 2, "converted expression")?;
        }
        K::Subtype => {
            IlType::decode(&required_argument(&form, 0, "source inclusion type")?)?;
            IlType::decode(&required_argument(&form, 1, "target inclusion type")?)?;
            validate_expression_argument(&form, 2, "included expression")?;
        }
    }
    Ok(())
}

fn expression_child_cursors<'a>(
    expression: &IlExpression<'a>,
) -> Result<Vec<IlCursor<'a>>, IlSchemaError> {
    use IlExpressionKind as K;
    let form = required_form(expression.cursor(), "decoded expression")?;
    let mut children = Vec::new();
    match expression.kind() {
        K::Variable | K::Boolean | K::Number | K::Text => {}
        K::Unary => push_argument(&mut children, &form, 2, "unary operand")?,
        K::Binary | K::Comparison => {
            push_argument(&mut children, &form, 2, "left operand")?;
            push_argument(&mut children, &form, 3, "right operand")?;
        }
        K::Tuple | K::List | K::Optional => children.extend(form.arguments()),
        K::Projection | K::Uncase | K::UnwrapOptional | K::Dot | K::Lift | K::Length => {
            push_argument(&mut children, &form, 0, "unary expression payload")?;
        }
        K::Case => push_argument(&mut children, &form, 1, "variant payload")?,
        K::Struct => {
            for field in form.arguments() {
                let field_form = required_form(&field, "record expression field")?;
                push_argument(&mut children, &field_form, 1, "record field expression")?;
            }
        }
        K::Compose | K::Membership | K::Concatenate | K::Index => {
            push_argument(&mut children, &form, 0, "left expression")?;
            push_argument(&mut children, &form, 1, "right expression")?;
        }
        K::Slice => {
            for index in 0..3 {
                push_argument(&mut children, &form, index, "slice expression")?;
            }
        }
        K::Update | K::Extend => {
            push_argument(&mut children, &form, 0, "updated expression")?;
            collect_path_expressions(&required_argument(&form, 1, "update path")?, &mut children)?;
            push_argument(&mut children, &form, 2, "update value")?;
        }
        K::Call => {
            for argument in form.arguments().skip(1) {
                if let IlArgument::Expression(payload) = decode_argument(&argument)? {
                    children.push(payload.cursor().clone());
                }
            }
        }
        K::Iterate => {
            push_argument(&mut children, &form, 0, "iterated expression")?;
            let iteration =
                decode_iteration(&required_argument(&form, 1, "expression iteration")?)?;
            if let IlIteration::Fixed { length, .. } = iteration {
                children.push(length);
            }
            for domain in form.arguments().skip(2) {
                let domain_form = required_form(&domain, "iteration domain")?;
                push_argument(&mut children, &domain_form, 1, "domain expression")?;
            }
        }
        K::Convert | K::Subtype => {
            push_argument(&mut children, &form, 2, "converted expression")?;
        }
    }
    Ok(children)
}

fn push_argument<'a>(
    output: &mut Vec<IlCursor<'a>>,
    form: &IlForm<'a>,
    index: usize,
    expected: &'static str,
) -> Result<(), IlSchemaError> {
    output.push(required_argument(form, index, expected)?);
    Ok(())
}

fn collect_path_expressions<'a>(
    cursor: &IlCursor<'a>,
    output: &mut Vec<IlCursor<'a>>,
) -> Result<(), IlSchemaError> {
    if cursor.node() == IlNode::Symbol("root") {
        return Ok(());
    }
    let form = required_form(cursor, "update path")?;
    collect_path_expressions(&required_argument(&form, 0, "parent path")?, output)?;
    match form.head() {
        "idx" => push_argument(output, &form, 1, "path index"),
        "slice" => {
            push_argument(output, &form, 1, "path slice start")?;
            push_argument(output, &form, 2, "path slice length")
        }
        "dot" => Ok(()),
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "path root, idx, slice, or dot",
            describe(cursor),
        )),
    }
}

fn validate_expression_argument(
    form: &IlForm<'_>,
    index: usize,
    expected: &'static str,
) -> Result<(), IlSchemaError> {
    IlExpression::decode(&required_argument(form, index, expected)?)?.validate()
}

fn validate_call(form: &IlForm<'_>) -> Result<(), IlSchemaError> {
    require_string_argument(form, 0, "definition identifier")?;
    for argument in form.arguments().skip(1) {
        validate_il_argument(&decode_argument(&argument)?)?;
    }
    Ok(())
}

fn validate_iterated_expression(form: &IlForm<'_>) -> Result<(), IlSchemaError> {
    validate_expression_argument(form, 0, "iterated expression")?;
    let iteration_cursor = required_argument(form, 1, "expression iteration")?;
    validate_iteration(&decode_iteration(&iteration_cursor)?)?;
    for domain in form.arguments().skip(2) {
        validate_domain(&domain)?;
    }
    Ok(())
}

fn validate_number(cursor: &IlCursor<'_>) -> Result<(), IlSchemaError> {
    let form = required_form(cursor, "numeric literal family")?;
    if !matches!(form.head(), "nat" | "int" | "rat" | "real") {
        return Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "numeric literal family nat, int, rat, or real",
            describe(cursor),
        ));
    }
    require_arity(&form, 1, "numeric literal with one spelling")?;
    match required_argument(&form, 0, "numeric spelling")?.node() {
        IlNode::Number(_) | IlNode::Symbol(_) => Ok(()),
        _ => Err(schema_error(
            cursor.declaration(),
            &child_path(&form, 0),
            "numeric spelling",
            describe(&required_argument(&form, 0, "numeric spelling")?),
        )),
    }
}

fn validate_expression_field(cursor: &IlCursor<'_>) -> Result<(), IlSchemaError> {
    let form = required_form(cursor, "record expression field")?;
    require_head(&form, "field")?;
    require_arity(&form, 2, "record field with operator and expression")?;
    require_string_argument(&form, 0, "record field operator")?;
    validate_expression_argument(&form, 1, "record field expression")
}

fn validate_path(cursor: &IlCursor<'_>) -> Result<(), IlSchemaError> {
    if cursor.node() == IlNode::Symbol("root") {
        return Ok(());
    }
    let form = required_form(cursor, "update path")?;
    match form.head() {
        "idx" => {
            require_arity(&form, 2, "indexed path")?;
            validate_path(&required_argument(&form, 0, "parent path")?)?;
            validate_expression_argument(&form, 1, "path index")
        }
        "slice" => {
            require_arity(&form, 3, "sliced path")?;
            validate_path(&required_argument(&form, 0, "parent path")?)?;
            validate_expression_argument(&form, 1, "path slice start")?;
            validate_expression_argument(&form, 2, "path slice length")
        }
        "dot" => {
            require_arity(&form, 2, "record-field path")?;
            validate_path(&required_argument(&form, 0, "parent path")?)?;
            require_string_argument(&form, 1, "path field operator")?;
            Ok(())
        }
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "path root, idx, slice, or dot",
            describe(cursor),
        )),
    }
}

fn validate_il_argument(argument: &IlArgument<'_>) -> Result<(), IlSchemaError> {
    match argument {
        IlArgument::Expression(expression) => expression.validate(),
        IlArgument::Type(_) | IlArgument::Definition(_) | IlArgument::Grammar(_) => Ok(()),
    }
}

fn validate_iteration(iteration: &IlIteration<'_>) -> Result<(), IlSchemaError> {
    if let IlIteration::Fixed { length, .. } = iteration {
        IlExpression::decode(length)?.validate()?;
    }
    Ok(())
}

fn require_string_argument<'a>(
    form: &IlForm<'a>,
    index: usize,
    expected: &'static str,
) -> Result<&'a str, IlSchemaError> {
    required_string(
        form.argument(index),
        form.cursor().declaration(),
        &child_path(form, index),
        expected,
    )
}

fn require_symbol_argument<'a>(
    form: &IlForm<'a>,
    index: usize,
    expected: &'static str,
) -> Result<&'a str, IlSchemaError> {
    let cursor = required_argument(form, index, expected)?;
    match cursor.node() {
        IlNode::Symbol(value) => Ok(value),
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            expected,
            describe(&cursor),
        )),
    }
}

fn require_number_argument<'a>(
    form: &IlForm<'a>,
    index: usize,
    expected: &'static str,
) -> Result<&'a str, IlSchemaError> {
    let cursor = required_argument(form, index, expected)?;
    match cursor.node() {
        IlNode::Number(value) => Ok(value),
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            expected,
            describe(&cursor),
        )),
    }
}

fn decode_rule_schema<'a>(cursor: &IlCursor<'a>) -> Result<IlRuleSchema<'a>, IlSchemaError> {
    let form = required_form(cursor, "relation rule")?;
    require_head(&form, "rule")?;
    require_min_arity(&form, 3, "rule name, notation, and conclusion")?;
    let name = required_string(
        form.argument(0),
        cursor.declaration(),
        &child_path(&form, 0),
        "rule name",
    )?;
    let fields = form.arguments().skip(1).collect::<Vec<_>>();
    let notation_index = fields
        .iter()
        .position(|field| matches!(field.node(), IlNode::String(_)))
        .ok_or_else(|| {
            schema_error(
                cursor.declaration(),
                cursor.path(),
                "rule notation after explicit bindings",
                "missing".to_owned(),
            )
        })?;
    let (bindings, tail) = fields.split_at(notation_index);
    require_bindings(bindings)?;
    let bindings = bindings
        .iter()
        .map(decode_binding)
        .collect::<Result<Vec<_>, _>>()?;
    let notation_cursor = tail.first().ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "rule notation",
            "missing".to_owned(),
        )
    })?;
    let IlNode::String(notation) = notation_cursor.node() else {
        return Err(schema_error(
            cursor.declaration(),
            notation_cursor.path(),
            "rule notation",
            describe(notation_cursor),
        ));
    };
    let conclusion_cursor = tail.get(1).ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "rule conclusion",
            "missing".to_owned(),
        )
    })?;
    let conclusion = IlExpression::decode(conclusion_cursor)?;
    conclusion.validate()?;
    let premises = tail
        .iter()
        .skip(2)
        .map(decode_premise)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(IlRuleSchema {
        cursor: cursor.clone(),
        name,
        bindings,
        notation,
        conclusion,
        premises,
    })
}

fn decode_clause_schema<'a>(cursor: &IlCursor<'a>) -> Result<IlClauseSchema<'a>, IlSchemaError> {
    let form = required_form(cursor, "definition clause")?;
    require_head(&form, "clause")?;
    require_min_arity(&form, 1, "clause result expression")?;
    let fields = form.arguments().collect::<Vec<_>>();
    let binding_count = fields.iter().take_while(|field| is_binding(field)).count();
    let (bindings, tail) = fields.split_at(binding_count);
    require_bindings(bindings)?;
    let bindings = bindings
        .iter()
        .map(decode_binding)
        .collect::<Result<Vec<_>, _>>()?;
    let argument_count = tail
        .iter()
        .take_while(|field| is_argument_wrapper(field))
        .count();
    let (argument_cursors, tail) = tail.split_at(argument_count);
    let arguments = argument_cursors
        .iter()
        .map(decode_argument)
        .collect::<Result<Vec<_>, _>>()?;
    for argument in &arguments {
        validate_il_argument(argument)?;
    }
    let result_cursor = tail.first().ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "clause result expression",
            "missing".to_owned(),
        )
    })?;
    let result = IlExpression::decode(result_cursor)?;
    result.validate()?;
    let premises = tail
        .iter()
        .skip(1)
        .map(decode_premise)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(IlClauseSchema {
        cursor: cursor.clone(),
        bindings,
        arguments,
        result,
        premises,
    })
}

fn decode_production_schema<'a>(
    cursor: &IlCursor<'a>,
) -> Result<IlProductionSchema<'a>, IlSchemaError> {
    let form = required_form(cursor, "grammar production")?;
    require_head(&form, "prod")?;
    require_min_arity(&form, 2, "production symbol and result expression")?;
    let fields = form.arguments().collect::<Vec<_>>();
    let binding_count = fields.iter().take_while(|field| is_binding(field)).count();
    let (bindings, tail) = fields.split_at(binding_count);
    require_bindings(bindings)?;
    let bindings = bindings
        .iter()
        .map(decode_binding)
        .collect::<Result<Vec<_>, _>>()?;
    let symbol = tail.first().cloned().ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "production grammar symbol",
            "missing".to_owned(),
        )
    })?;
    let result_cursor = tail.get(1).ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "production result expression",
            "missing".to_owned(),
        )
    })?;
    let result = IlExpression::decode(result_cursor)?;
    result.validate()?;
    let premises = tail
        .iter()
        .skip(2)
        .map(decode_premise)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(IlProductionSchema {
        cursor: cursor.clone(),
        bindings,
        symbol,
        result,
        premises,
    })
}

fn is_binding(cursor: &IlCursor<'_>) -> bool {
    let Some(form) = cursor.form() else {
        return false;
    };
    let first_is_name = matches!(
        form.argument(0).map(|value| value.node()),
        Some(IlNode::String(_))
    );
    match form.head() {
        "exp" => form.len() == 2 && first_is_name,
        "typ" => form.len() == 1 && first_is_name,
        "def" | "gram" => form.len() >= 2 && first_is_name,
        _ => false,
    }
}

fn is_argument_wrapper(cursor: &IlCursor<'_>) -> bool {
    let Some(form) = cursor.form() else {
        return false;
    };
    matches!(form.head(), "exp" | "typ" | "def" | "gram") && form.len() == 1
}

fn decode_premise<'a>(cursor: &IlCursor<'a>) -> Result<IlPremise<'a>, IlSchemaError> {
    if cursor.node() == IlNode::Symbol("else") {
        return Ok(IlPremise::Otherwise);
    }
    let form = required_form(cursor, "rule premise")?;
    match form.head() {
        "rule" => Ok(IlPremise::Rule(Box::new(decode_rule_schema(cursor)?))),
        "if" => {
            require_arity(&form, 1, "if premise with one expression")?;
            let expression =
                IlExpression::decode(&required_argument(&form, 0, "if-premise expression")?)?;
            expression.validate()?;
            Ok(IlPremise::If(expression))
        }
        "let" => {
            require_arity(&form, 2, "let premise with pattern and expression")?;
            let left = IlExpression::decode(&required_argument(&form, 0, "let pattern")?)?;
            let right = IlExpression::decode(&required_argument(&form, 1, "let expression")?)?;
            left.validate()?;
            right.validate()?;
            Ok(IlPremise::Let { left, right })
        }
        "iter" => {
            require_min_arity(&form, 2, "iterated premise with iteration shape")?;
            let premise = Box::new(decode_premise(&required_argument(
                &form,
                0,
                "iterated premise",
            )?)?);
            let iteration_cursor = required_argument(&form, 1, "premise iteration")?;
            let iteration = decode_iteration(&iteration_cursor)?;
            validate_iteration(&iteration)?;
            let domains = form
                .arguments()
                .skip(2)
                .map(|cursor| decode_domain(&cursor))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(IlPremise::Iterated {
                premise,
                iteration,
                domains,
            })
        }
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "premise rule, if, let, else, or iter",
            describe(cursor),
        )),
    }
}

fn decode_domain<'a>(cursor: &IlCursor<'a>) -> Result<IlDomain<'a>, IlSchemaError> {
    let form = required_form(cursor, "iteration domain")?;
    require_head(&form, "dom")?;
    require_arity(&form, 2, "domain with identifier and expression")?;
    let name = required_string(
        form.argument(0),
        cursor.declaration(),
        &child_path(&form, 0),
        "domain identifier",
    )?;
    let expression = IlExpression::decode(&required_argument(&form, 1, "domain expression")?)?;
    expression.validate()?;
    Ok(IlDomain { name, expression })
}

fn validate_domain(cursor: &IlCursor<'_>) -> Result<(), IlSchemaError> {
    decode_domain(cursor).map(|_| ())
}

fn require_bindings(bindings: &[IlCursor<'_>]) -> Result<(), IlSchemaError> {
    for binding in bindings {
        match binding.head() {
            Some("exp" | "typ" | "def" | "gram") => {}
            _ => {
                return Err(schema_error(
                    binding.declaration(),
                    binding.path(),
                    "binding form exp, typ, def, or gram",
                    describe(binding),
                ));
            }
        }
    }
    Ok(())
}

fn required_argument<'a>(
    form: &IlForm<'a>,
    index: usize,
    expected: &'static str,
) -> Result<IlCursor<'a>, IlSchemaError> {
    form.argument(index).ok_or_else(|| {
        schema_error(
            form.cursor().declaration(),
            form.cursor().path(),
            expected,
            "missing".to_owned(),
        )
    })
}

impl<'a> IlDeclarationSchema<'a> {
    /// Returns the stable declaration metadata.
    #[must_use]
    pub const fn declaration(&self) -> &'a IlDeclaration {
        self.declaration
    }

    /// Returns the structurally decoded declaration body.
    #[must_use]
    pub const fn body(&self) -> &IlDeclarationBody<'a> {
        &self.body
    }
}

impl IlDocument {
    /// Parses an elaborated IL document and inventories every root.
    ///
    /// # Errors
    ///
    /// Returns an error for S-expression failures and resource limits, or when
    /// any top-level form is not one of `typ`, `def`, `gram`, `rel`, or `rec`.
    /// Recursive groups must be nonempty and contain only named declarations.
    pub fn parse(bytes: &[u8], limits: Limits) -> Result<Self, IlError> {
        let parsed = parse_ast(bytes, limits).map_err(|source| IlError::Ast { source })?;
        Self::from_parsed(parsed)
    }

    /// Recognizes the declaration envelope of an already parsed document.
    ///
    /// # Errors
    ///
    /// Returns an error if a root or recursive member has an unsupported shape.
    pub fn from_parsed(parsed: ParsedAst) -> Result<Self, IlError> {
        let root_count = parsed.document.expressions().len();
        let mut roots = Vec::with_capacity(root_count);
        let mut declarations = Vec::with_capacity(root_count);
        for (root_index, expression) in parsed.document.expressions().iter().enumerate() {
            let ordinal = root_ordinal(root_index)?;
            let items = list_items(expression).ok_or(IlError::RootAtom { ordinal })?;
            let head = symbol(items.first()).ok_or(IlError::MissingHead { ordinal })?;
            let start = declarations.len();
            if head == "rec" {
                if items.len() == 1 {
                    return Err(IlError::EmptyRecursiveGroup { ordinal });
                }
                for (member_index, member) in items[1..].iter().enumerate() {
                    declarations.push(declaration(
                        member,
                        DeclarationId {
                            root: ordinal,
                            member: Some(member_ordinal(ordinal, member_index)?),
                        },
                    )?);
                }
                roots.push(IlRoot {
                    ordinal,
                    recursive: true,
                    declarations: start..declarations.len(),
                });
            } else {
                declarations.push(declaration(
                    expression,
                    DeclarationId {
                        root: ordinal,
                        member: None,
                    },
                )?);
                roots.push(IlRoot {
                    ordinal,
                    recursive: false,
                    declarations: start..declarations.len(),
                });
            }
        }
        Ok(Self {
            parsed,
            roots,
            declarations,
        })
    }

    /// Borrows the complete bounded S-expression document and its metrics.
    #[must_use]
    pub const fn parsed(&self) -> &ParsedAst {
        &self.parsed
    }

    /// Returns all top-level roots in source order.
    #[must_use]
    pub fn roots(&self) -> &[IlRoot] {
        &self.roots
    }

    /// Returns all declarations in source order, flattening recursive groups.
    #[must_use]
    pub fn declarations(&self) -> &[IlDeclaration] {
        &self.declarations
    }

    /// Returns the declarations belonging to one root.
    #[must_use]
    pub fn root_declarations(&self, root: &IlRoot) -> &[IlDeclaration] {
        &self.declarations[root.declarations.clone()]
    }

    /// Returns the exact S-expression selected by a declaration ID.
    #[must_use]
    pub fn expression(&self, id: DeclarationId) -> Option<&Expr> {
        let root_index = usize::try_from(id.root.get()).ok()?.checked_sub(1)?;
        let root = self.parsed.document.expressions().get(root_index)?;
        match id.member {
            None => Some(root),
            Some(member) => {
                let items = list_items(root)?;
                let member_index = usize::try_from(member.get()).ok()?;
                items.get(member_index)
            }
        }
    }

    /// Returns a parser-independent cursor at one declaration root.
    #[must_use]
    pub fn cursor(&self, id: DeclarationId) -> Option<IlCursor<'_>> {
        let expression = self.expression(id)?;
        Some(IlCursor {
            expression,
            declaration: id,
            path: Vec::new(),
        })
    }

    /// Decodes one declaration using the generic elaborated-IL schema.
    ///
    /// This validates structural roles only; it does not assign Wasm meaning
    /// or trust source names as selectors.
    ///
    /// # Errors
    ///
    /// Returns an error when the declaration head, name, required fields, or
    /// repeated instance/clause/production/rule forms do not match its
    /// inventoried [`IlKind`].
    pub fn schema(
        &self,
        id: DeclarationId,
    ) -> Result<Option<IlDeclarationSchema<'_>>, IlSchemaError> {
        let Some(declaration) = self.declarations.iter().find(|item| item.id == id) else {
            return Ok(None);
        };
        let Some(cursor) = self.cursor(id) else {
            return Err(schema_error(
                id,
                &[],
                "inventoried declaration expression",
                "missing".to_owned(),
            ));
        };
        let form = required_form(&cursor, "declaration form")?;
        let expected_head = schema_head(declaration.kind);
        require_head(&form, expected_head)?;
        let name = required_string(form.argument(0), id, &[2], "quoted declaration name")?;
        if name != declaration.name {
            return Err(schema_error(
                id,
                &[2],
                "inventoried declaration name",
                format!("string {name:?}"),
            ));
        }
        let body = match declaration.kind {
            IlKind::Type => decode_type(&form)?,
            IlKind::Definition => decode_function(&form, "clause")?,
            IlKind::Grammar => decode_grammar(&form)?,
            IlKind::Relation => decode_relation(&form)?,
        };
        Ok(Some(IlDeclarationSchema { declaration, body }))
    }

    /// Views one node selected by a declaration and a one-based child path.
    ///
    /// An empty path selects the declaration itself. This structural API is
    /// independent of names and source spans, and does not expose the backing
    /// S-expression representation.
    #[must_use]
    pub fn node(&self, id: DeclarationId, path: &[u32]) -> Option<IlNode<'_>> {
        let mut expression = self.expression(id)?;
        for &position in path {
            let index = usize::try_from(position).ok()?.checked_sub(1)?;
            expression = list_items(expression)?.get(index)?;
        }
        Some(node_view(expression))
    }

    /// Inventories every nested `rule` form in deterministic tree order.
    ///
    /// Rule identity is the declaration selector plus a one-based expression
    /// path. This includes premise rules nested inside outer rules, avoiding
    /// source-name assumptions and silent omission of deeper forms.
    /// # Errors
    ///
    /// Returns an error when a `rule` form lacks its required quoted name.
    pub fn rules(&self, id: DeclarationId) -> Result<Option<Vec<IlRule>>, IlError> {
        let Some(expression) = self.expression(id) else {
            return Ok(None);
        };
        let mut rules = Vec::new();
        collect_rules(expression, id, &mut Vec::new(), &mut rules)?;
        Ok(Some(rules))
    }

    /// Resolves an exact structural rule selector.
    #[must_use]
    pub fn rule(&self, id: &RuleId) -> Option<&Expr> {
        let mut expression = self.expression(id.declaration)?;
        for position in &id.path {
            let items = list_items(expression)?;
            let index = usize::try_from(position.get()).ok()?.checked_sub(1)?;
            expression = items.get(index)?;
        }
        (symbol(list_items(expression)?.first()) == Some("rule")).then_some(expression)
    }

    /// Resolves a parser-independent cursor for an exact rule selector.
    #[must_use]
    pub fn rule_cursor(&self, id: &RuleId) -> Option<IlCursor<'_>> {
        let expression = self.rule(id)?;
        Some(IlCursor {
            expression,
            declaration: id.declaration,
            path: id.path().collect(),
        })
    }

    /// Inventories every nested `clause` form in deterministic tree order.
    #[must_use]
    pub fn clauses(&self, id: DeclarationId) -> Option<Vec<IlClause>> {
        let expression = self.expression(id)?;
        let mut clauses = Vec::new();
        collect_clauses(expression, id, &mut Vec::new(), &mut clauses);
        Some(clauses)
    }

    /// Resolves an exact structural clause selector.
    #[must_use]
    pub fn clause(&self, id: &ClauseId) -> Option<&Expr> {
        let expression = resolve_path(self.expression(id.declaration)?, &id.path)?;
        (symbol(list_items(expression)?.first()) == Some("clause")).then_some(expression)
    }

    /// Resolves a parser-independent cursor for an exact clause selector.
    #[must_use]
    pub fn clause_cursor(&self, id: &ClauseId) -> Option<IlCursor<'_>> {
        let expression = self.clause(id)?;
        Some(IlCursor {
            expression,
            declaration: id.declaration,
            path: id.path().collect(),
        })
    }
}

/// Why an elaborated S-expression is not a recognized IL declaration envelope.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum IlError {
    /// Bounded S-expression parsing failed.
    #[snafu(display("could not read SpecTec IL: {source}"))]
    Ast {
        /// Underlying syntax or resource error.
        source: AstError,
    },
    /// The document has more roots than the stable selector can represent.
    #[snafu(display("SpecTec IL root count exceeds u32"))]
    TooManyRoots,
    /// A top-level form was unexpectedly atomic.
    #[snafu(display("SpecTec IL root {} is not a list", ordinal.get()))]
    RootAtom {
        /// One-based root position.
        ordinal: RootOrdinal,
    },
    /// A root list was empty or did not begin with a symbol.
    #[snafu(display("SpecTec IL root {} has no symbolic head", ordinal.get()))]
    MissingHead {
        /// One-based root position.
        ordinal: RootOrdinal,
    },
    /// A root used an unsupported top-level form.
    #[snafu(display("SpecTec IL root {} has unsupported form {head:?}", id.root().get()))]
    UnsupportedForm {
        /// Declaration selector.
        id: DeclarationId,
        /// Unrecognized head symbol.
        head: String,
    },
    /// A recursive group contained no declarations.
    #[snafu(display("SpecTec IL recursive root {} is empty", ordinal.get()))]
    EmptyRecursiveGroup {
        /// One-based root position.
        ordinal: RootOrdinal,
    },
    /// A declaration omitted its quoted name.
    #[snafu(display("SpecTec IL declaration at root {} has no quoted name", id.root().get()))]
    MissingName {
        /// Declaration selector.
        id: DeclarationId,
    },
    /// A nested rule omitted its quoted name.
    #[snafu(display("SpecTec rule at {id:?} path {path:?} has no quoted name"))]
    MissingRuleName {
        /// Containing declaration selector.
        id: DeclarationId,
        /// One-based expression path within the declaration.
        path: Vec<u32>,
    },
}

/// Why an inventoried declaration does not match the elaborated-IL schema.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum IlSchemaError {
    /// A node did not have its required structural role.
    #[snafu(display(
        "SpecTec IL declaration at root {} has {actual} at path {path:?}; expected {expected}",
        id.root().get()
    ))]
    Shape {
        /// Stable containing declaration.
        id: DeclarationId,
        /// One-based path to the rejected node.
        path: Vec<u32>,
        /// Required schema role.
        expected: &'static str,
        /// Observed parser-independent shape.
        actual: String,
    },
}

fn decode_type_form<'a>(cursor: &IlCursor<'a>) -> Result<IlType<'a>, IlSchemaError> {
    let form = required_form(cursor, "type form")?;
    match form.head() {
        "var" => {
            require_min_arity(&form, 1, "named type with identifier")?;
            let name = required_string(
                form.argument(0),
                cursor.declaration(),
                &child_path(&form, 0),
                "type identifier",
            )?;
            let arguments = form
                .arguments()
                .skip(1)
                .map(|argument| decode_argument(&argument))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(IlType::Named { name, arguments })
        }
        "tup" => Ok(IlType::Tuple(
            form.arguments()
                .map(|binding| decode_type_binding(&binding))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        "iter" => {
            require_arity(&form, 2, "iterated type with element and iteration")?;
            let element_cursor = form.argument(0).ok_or_else(|| {
                schema_error(
                    cursor.declaration(),
                    cursor.path(),
                    "iteration element type",
                    "missing".to_owned(),
                )
            })?;
            let iteration_cursor = form.argument(1).ok_or_else(|| {
                schema_error(
                    cursor.declaration(),
                    cursor.path(),
                    "iteration shape",
                    "missing".to_owned(),
                )
            })?;
            Ok(IlType::Iterated {
                element: Box::new(IlType::decode(&element_cursor)?),
                iteration: decode_iteration(&iteration_cursor)?,
            })
        }
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "type form var, tup, or iter",
            describe(cursor),
        )),
    }
}

fn decode_argument<'a>(cursor: &IlCursor<'a>) -> Result<IlArgument<'a>, IlSchemaError> {
    let form = required_form(cursor, "type-family argument")?;
    require_arity(&form, 1, "single-payload type-family argument")?;
    let payload = form.argument(0).ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "type-family argument payload",
            "missing".to_owned(),
        )
    })?;
    match form.head() {
        "exp" => {
            let expression = IlExpression::decode(&payload)?;
            expression.validate()?;
            Ok(IlArgument::Expression(expression))
        }
        "typ" => Ok(IlArgument::Type(Box::new(IlType::decode(&payload)?))),
        "def" => Ok(IlArgument::Definition(required_string(
            Some(payload),
            cursor.declaration(),
            &child_path(&form, 0),
            "definition identifier",
        )?)),
        "gram" => Ok(IlArgument::Grammar(payload)),
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "argument form exp, typ, def, or gram",
            describe(cursor),
        )),
    }
}

fn decode_binding<'a>(cursor: &IlCursor<'a>) -> Result<IlBinding<'a>, IlSchemaError> {
    let form = required_form(cursor, "explicit binding")?;
    let name = required_string(
        form.argument(0),
        cursor.declaration(),
        &child_path(&form, 0),
        "binding identifier",
    )?;
    match form.head() {
        "exp" => {
            require_arity(&form, 2, "expression binding with name and type")?;
            let ty = IlType::decode(&required_argument(&form, 1, "expression binding type")?)?;
            Ok(IlBinding::Expression { name, ty })
        }
        "typ" => {
            require_arity(&form, 1, "type binding with name")?;
            Ok(IlBinding::Type { name })
        }
        "def" | "gram" => {
            require_min_arity(&form, 2, "higher-order binding with result type")?;
            let tail = form.arguments().skip(1).collect::<Vec<_>>();
            let Some((result, parameters)) = tail.split_last() else {
                return Err(schema_error(
                    cursor.declaration(),
                    cursor.path(),
                    "higher-order binding result type",
                    "missing".to_owned(),
                ));
            };
            require_parameters(parameters)?;
            let result = IlType::decode(result)?;
            if form.head() == "def" {
                Ok(IlBinding::Definition {
                    name,
                    parameters: parameters.to_vec(),
                    result,
                })
            } else {
                Ok(IlBinding::Grammar {
                    name,
                    parameters: parameters.to_vec(),
                    result,
                })
            }
        }
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "binding form exp, typ, def, or gram",
            describe(cursor),
        )),
    }
}

fn decode_type_binding<'a>(cursor: &IlCursor<'a>) -> Result<IlTypeBinding<'a>, IlSchemaError> {
    let form = required_form(cursor, "tuple type binding")?;
    require_head(&form, "bind")?;
    require_arity(&form, 2, "tuple binding with expression and type")?;
    let binder = form.argument(0).ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "tuple binding expression",
            "missing".to_owned(),
        )
    })?;
    let ty_cursor = form.argument(1).ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            "tuple binding type",
            "missing".to_owned(),
        )
    })?;
    Ok(IlTypeBinding {
        binder,
        ty: IlType::decode(&ty_cursor)?,
    })
}

fn decode_iteration<'a>(cursor: &IlCursor<'a>) -> Result<IlIteration<'a>, IlSchemaError> {
    match cursor.node() {
        IlNode::Symbol("opt") => Ok(IlIteration::Optional),
        IlNode::Symbol("list") => Ok(IlIteration::List),
        IlNode::Symbol("list1") => Ok(IlIteration::NonEmptyList),
        IlNode::List(_) => {
            let form = required_form(cursor, "fixed-length iteration")?;
            require_head(&form, "listn")?;
            if !(1..=2).contains(&form.len()) {
                return Err(schema_error(
                    cursor.declaration(),
                    cursor.path(),
                    "listn with length and optional binder",
                    format!("form with {} arguments", form.len()),
                ));
            }
            let length = form.argument(0).ok_or_else(|| {
                schema_error(
                    cursor.declaration(),
                    cursor.path(),
                    "fixed iteration length",
                    "missing".to_owned(),
                )
            })?;
            let binder = form
                .argument(1)
                .map(|binder| {
                    required_string(
                        Some(binder),
                        cursor.declaration(),
                        &child_path(&form, 1),
                        "fixed iteration binder",
                    )
                })
                .transpose()?;
            Ok(IlIteration::Fixed { length, binder })
        }
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "iteration opt, list, list1, or listn",
            describe(cursor),
        )),
    }
}

fn require_arity(
    form: &IlForm<'_>,
    arity: usize,
    expected: &'static str,
) -> Result<(), IlSchemaError> {
    if form.len() == arity {
        Ok(())
    } else {
        Err(schema_error(
            form.cursor().declaration(),
            form.cursor().path(),
            expected,
            format!("form {:?} with {} arguments", form.head(), form.len()),
        ))
    }
}

fn require_min_arity(
    form: &IlForm<'_>,
    minimum: usize,
    expected: &'static str,
) -> Result<(), IlSchemaError> {
    if form.len() >= minimum {
        Ok(())
    } else {
        Err(schema_error(
            form.cursor().declaration(),
            form.cursor().path(),
            expected,
            format!("form {:?} with {} arguments", form.head(), form.len()),
        ))
    }
}

fn decode_type<'a>(form: &IlForm<'a>) -> Result<IlDeclarationBody<'a>, IlSchemaError> {
    let id = form.cursor().declaration();
    let fields = form.arguments().skip(1).collect::<Vec<_>>();
    let first_instance = fields
        .iter()
        .position(|field| field.head() == Some("inst"))
        .unwrap_or(fields.len());
    let (parameters, instances) = fields.split_at(first_instance);
    let parameters = decode_bindings(parameters)?;
    require_repeated(instances, "inst", "type-family instance")?;
    if instances.is_empty() {
        return Err(schema_error(
            id,
            form.cursor().path(),
            "at least one type-family instance",
            "none".to_owned(),
        ));
    }
    Ok(IlDeclarationBody::Type {
        parameters,
        instances: instances
            .iter()
            .map(decode_type_instance)
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn decode_function<'a>(
    form: &IlForm<'a>,
    repeated_head: &'static str,
) -> Result<IlDeclarationBody<'a>, IlSchemaError> {
    let (parameters, result, repeated) = signature_and_repeated(form, repeated_head)?;
    Ok(IlDeclarationBody::Definition {
        parameters,
        result,
        clauses: repeated,
    })
}

fn decode_grammar<'a>(form: &IlForm<'a>) -> Result<IlDeclarationBody<'a>, IlSchemaError> {
    let (parameters, result, productions) = signature_and_repeated(form, "prod")?;
    Ok(IlDeclarationBody::Grammar {
        parameters,
        result,
        productions,
    })
}

fn decode_relation<'a>(form: &IlForm<'a>) -> Result<IlDeclarationBody<'a>, IlSchemaError> {
    let id = form.cursor().declaration();
    if form.len() < 3 {
        return Err(schema_error(
            id,
            form.cursor().path(),
            "relation name, notation, and argument type",
            format!("{} arguments", form.len()),
        ));
    }
    let notation_cursor = form.argument(1);
    let notation = required_string(
        notation_cursor.clone(),
        id,
        &child_path(form, 1),
        "notation",
    )?;
    let argument = form.argument(2).ok_or_else(|| {
        schema_error(
            id,
            form.cursor().path(),
            "relation argument type",
            "missing".to_owned(),
        )
    })?;
    let rules = form.arguments().skip(3).collect::<Vec<_>>();
    require_repeated(&rules, "rule", "relation rule")?;
    Ok(IlDeclarationBody::Relation {
        notation,
        argument,
        rules,
    })
}

fn signature_and_repeated<'a>(
    form: &IlForm<'a>,
    repeated_head: &'static str,
) -> Result<(Vec<IlBinding<'a>>, IlCursor<'a>, Vec<IlCursor<'a>>), IlSchemaError> {
    let id = form.cursor().declaration();
    let fields = form.arguments().skip(1).collect::<Vec<_>>();
    let first_repeated = fields
        .iter()
        .position(|field| field.head() == Some(repeated_head))
        .unwrap_or(fields.len());
    let (signature, repeated) = fields.split_at(first_repeated);
    let Some((result, parameters)) = signature.split_last() else {
        return Err(schema_error(
            id,
            form.cursor().path(),
            "declaration result type",
            "missing".to_owned(),
        ));
    };
    let parameters = decode_bindings(parameters)?;
    require_repeated(repeated, repeated_head, repeated_head)?;
    Ok((parameters, result.clone(), repeated.to_vec()))
}

fn decode_bindings<'a>(values: &[IlCursor<'a>]) -> Result<Vec<IlBinding<'a>>, IlSchemaError> {
    require_parameters(values)?;
    values.iter().map(decode_binding).collect()
}

fn decode_type_instance<'a>(cursor: &IlCursor<'a>) -> Result<IlTypeInstance<'a>, IlSchemaError> {
    let form = required_form(cursor, "type-family instance")?;
    require_head(&form, "inst")?;
    require_min_arity(&form, 1, "instance definition")?;
    let fields = form.arguments().collect::<Vec<_>>();
    let binding_count = fields.iter().take_while(|field| is_binding(field)).count();
    let (bindings, tail) = fields.split_at(binding_count);
    let argument_count = tail
        .iter()
        .take_while(|field| is_argument_wrapper(field))
        .count();
    let (arguments, definition) = tail.split_at(argument_count);
    let [definition] = definition else {
        return Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "one alias, variant, or struct instance definition",
            format!("{} trailing forms", definition.len()),
        ));
    };
    Ok(IlTypeInstance {
        bindings: decode_bindings(bindings)?,
        arguments: arguments
            .iter()
            .map(decode_argument)
            .collect::<Result<Vec<_>, _>>()?,
        definition: decode_type_definition(definition)?,
    })
}

fn decode_type_definition<'a>(
    cursor: &IlCursor<'a>,
) -> Result<IlTypeDefinition<'a>, IlSchemaError> {
    let form = required_form(cursor, "type instance definition")?;
    match form.head() {
        "alias" => {
            require_arity(&form, 1, "alias with one type")?;
            Ok(IlTypeDefinition::Alias(IlType::decode(
                &required_argument(&form, 0, "alias type")?,
            )?))
        }
        "variant" => Ok(IlTypeDefinition::Variant(
            form.arguments()
                .map(|case| decode_type_case(&case))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        "struct" => Ok(IlTypeDefinition::Struct(
            form.arguments()
                .map(|field| decode_type_field(&field))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "alias, variant, or struct instance definition",
            describe(cursor),
        )),
    }
}

fn decode_type_case<'a>(cursor: &IlCursor<'a>) -> Result<IlTypeCase<'a>, IlSchemaError> {
    let (name, bindings, value, premises) = decode_type_member(cursor, "case")?;
    Ok(IlTypeCase {
        name,
        bindings,
        payload: value,
        premises,
    })
}

fn decode_type_field<'a>(cursor: &IlCursor<'a>) -> Result<IlTypeField<'a>, IlSchemaError> {
    let (name, bindings, value, premises) = decode_type_member(cursor, "field")?;
    Ok(IlTypeField {
        name,
        bindings,
        value,
        premises,
    })
}

type TypeMember<'a> = (&'a str, Vec<IlBinding<'a>>, IlType<'a>, Vec<IlPremise<'a>>);

fn decode_type_member<'a>(
    cursor: &IlCursor<'a>,
    head: &'static str,
) -> Result<TypeMember<'a>, IlSchemaError> {
    let form = required_form(cursor, "type member")?;
    require_head(&form, head)?;
    require_min_arity(&form, 2, "type member name and value")?;
    let name = required_string(
        form.argument(0),
        cursor.declaration(),
        &child_path(&form, 0),
        "type member name",
    )?;
    let fields = form.arguments().skip(1).collect::<Vec<_>>();
    let binding_count = fields.iter().take_while(|field| is_binding(field)).count();
    let (bindings, tail) = fields.split_at(binding_count);
    let Some((value, premises)) = tail.split_first() else {
        return Err(schema_error(
            cursor.declaration(),
            cursor.path(),
            "type member value type",
            "missing".to_owned(),
        ));
    };
    let value = IlType::decode(value)?;
    let premises = premises
        .iter()
        .map(decode_premise)
        .collect::<Result<Vec<_>, _>>()?;
    Ok((name, decode_bindings(bindings)?, value, premises))
}

fn require_parameters(parameters: &[IlCursor<'_>]) -> Result<(), IlSchemaError> {
    for parameter in parameters {
        match parameter.head() {
            Some("exp" | "typ" | "def" | "gram") => {}
            _ => {
                return Err(schema_error(
                    parameter.declaration(),
                    parameter.path(),
                    "parameter form exp, typ, def, or gram",
                    describe(parameter),
                ));
            }
        }
    }
    Ok(())
}

fn require_repeated(
    values: &[IlCursor<'_>],
    head: &'static str,
    expected: &'static str,
) -> Result<(), IlSchemaError> {
    for value in values {
        if value.head() != Some(head) {
            return Err(schema_error(
                value.declaration(),
                value.path(),
                expected,
                describe(value),
            ));
        }
    }
    Ok(())
}

fn required_form<'a>(
    cursor: &IlCursor<'a>,
    expected: &'static str,
) -> Result<IlForm<'a>, IlSchemaError> {
    cursor.form().ok_or_else(|| {
        schema_error(
            cursor.declaration(),
            cursor.path(),
            expected,
            describe(cursor),
        )
    })
}

fn require_head(form: &IlForm<'_>, expected: &'static str) -> Result<(), IlSchemaError> {
    if form.head() == expected {
        return Ok(());
    }
    Err(schema_error(
        form.cursor().declaration(),
        form.cursor().path(),
        expected,
        format!("form {:?}", form.head()),
    ))
}

fn required_string<'a>(
    cursor: Option<IlCursor<'a>>,
    id: DeclarationId,
    path: &[u32],
    expected: &'static str,
) -> Result<&'a str, IlSchemaError> {
    let Some(cursor) = cursor else {
        return Err(schema_error(id, path, expected, "missing".to_owned()));
    };
    match cursor.node() {
        IlNode::String(value) => Ok(value),
        _ => Err(schema_error(id, cursor.path(), expected, describe(&cursor))),
    }
}

fn child_path(form: &IlForm<'_>, argument: usize) -> Vec<u32> {
    let mut path = form.cursor().path().to_vec();
    if let Some(position) = u32::try_from(argument).ok().and_then(|n| n.checked_add(2)) {
        path.push(position);
    }
    path
}

fn schema_error(
    id: DeclarationId,
    path: &[u32],
    expected: &'static str,
    actual: String,
) -> IlSchemaError {
    IlSchemaError::Shape {
        id,
        path: path.to_vec(),
        expected,
        actual,
    }
}

fn describe(cursor: &IlCursor<'_>) -> String {
    match cursor.node() {
        IlNode::List(arity) => match cursor.head() {
            Some(head) => format!("form {head:?} with {} arguments", arity - 1),
            None => format!("headless list of arity {arity}"),
        },
        IlNode::Symbol(value) => format!("symbol {value:?}"),
        IlNode::String(value) => format!("string {value:?}"),
        IlNode::Number(value) => format!("number {value:?}"),
        IlNode::Other => "unsupported atom".to_owned(),
    }
}

const fn schema_head(kind: IlKind) -> &'static str {
    match kind {
        IlKind::Type => "typ",
        IlKind::Definition => "def",
        IlKind::Grammar => "gram",
        IlKind::Relation => "rel",
    }
}

fn root_ordinal(index: usize) -> Result<RootOrdinal, IlError> {
    let one_based = index.checked_add(1).ok_or(IlError::TooManyRoots)?;
    let value = u32::try_from(one_based).map_err(|_| IlError::TooManyRoots)?;
    Ok(RootOrdinal(
        NonZeroU32::new(value).expect("one-based root ordinal is nonzero"),
    ))
}

fn member_ordinal(root: RootOrdinal, index: usize) -> Result<NonZeroU32, IlError> {
    let one_based = index.checked_add(1).ok_or(IlError::TooManyRoots)?;
    let value = u32::try_from(one_based).map_err(|_| IlError::TooManyRoots)?;
    NonZeroU32::new(value).ok_or(IlError::MissingHead { ordinal: root })
}

fn declaration(expression: &Expr, id: DeclarationId) -> Result<IlDeclaration, IlError> {
    let items = list_items(expression).ok_or(IlError::MissingHead { ordinal: id.root })?;
    let head = symbol(items.first()).ok_or(IlError::MissingHead { ordinal: id.root })?;
    let kind = IlKind::from_head(head).ok_or_else(|| IlError::UnsupportedForm {
        id,
        head: head.to_owned(),
    })?;
    let name = string(items.get(1)).ok_or(IlError::MissingName { id })?;
    Ok(IlDeclaration {
        id,
        kind,
        name: name.to_owned(),
    })
}

fn list_items(expression: &Expr) -> Option<&[Expr]> {
    match expression.node() {
        ExprKind::List(node) => Some(SpannedRepr::list_items(node)),
        ExprKind::Atom(_) => None,
    }
}

fn node_view(expression: &Expr) -> IlNode<'_> {
    match expression.node() {
        ExprKind::List(node) => IlNode::List(SpannedRepr::list_items(node).len()),
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Symbol(value) => IlNode::Symbol(value),
            Atom::String(value) => IlNode::String(value),
            Atom::Number(value) => IlNode::Number(value),
            Atom::Bytes(_) | Atom::Keyword(_) | Atom::Directive(_) | Atom::O256(_) => IlNode::Other,
        },
    }
}

fn symbol(expression: Option<&Expr>) -> Option<&str> {
    let ExprKind::Atom(node) = expression?.node() else {
        return None;
    };
    match SpannedRepr::atom(node) {
        Atom::Symbol(value) => Some(value),
        _ => None,
    }
}

fn string(expression: Option<&Expr>) -> Option<&str> {
    let ExprKind::Atom(node) = expression?.node() else {
        return None;
    };
    match SpannedRepr::atom(node) {
        Atom::String(value) => Some(value),
        _ => None,
    }
}

fn collect_rules(
    expression: &Expr,
    declaration: DeclarationId,
    path: &mut Vec<NonZeroU32>,
    rules: &mut Vec<IlRule>,
) -> Result<(), IlError> {
    let Some(items) = list_items(expression) else {
        return Ok(());
    };
    if symbol(items.first()) == Some("rule") {
        let name = string(items.get(1)).ok_or_else(|| IlError::MissingRuleName {
            id: declaration,
            path: path.iter().map(|position| position.get()).collect(),
        })?;
        rules.push(IlRule {
            id: RuleId {
                declaration,
                path: path.clone(),
            },
            name: name.to_owned(),
        });
    }
    for (index, child) in items.iter().enumerate() {
        let Ok(position) = u32::try_from(index + 1) else {
            return Ok(());
        };
        let Some(position) = NonZeroU32::new(position) else {
            return Ok(());
        };
        path.push(position);
        collect_rules(child, declaration, path, rules)?;
        path.pop();
    }
    Ok(())
}

fn collect_clauses(
    expression: &Expr,
    declaration: DeclarationId,
    path: &mut Vec<NonZeroU32>,
    clauses: &mut Vec<IlClause>,
) {
    let Some(items) = list_items(expression) else {
        return;
    };
    if symbol(items.first()) == Some("clause") {
        clauses.push(IlClause {
            id: ClauseId {
                declaration,
                path: path.clone(),
            },
        });
    }
    for (index, child) in items.iter().enumerate() {
        let Some(position) = u32::try_from(index + 1).ok().and_then(NonZeroU32::new) else {
            return;
        };
        path.push(position);
        collect_clauses(child, declaration, path, clauses);
        path.pop();
    }
}

fn structural_path(path: impl IntoIterator<Item = u32>) -> Option<Vec<NonZeroU32>> {
    let path = path
        .into_iter()
        .map(NonZeroU32::new)
        .collect::<Option<Vec<_>>>()?;
    (!path.is_empty()).then_some(path)
}

fn resolve_path<'a>(mut expression: &'a Expr, path: &[NonZeroU32]) -> Option<&'a Expr> {
    for position in path {
        let items = list_items(expression)?;
        let index = usize::try_from(position.get()).ok()?.checked_sub(1)?;
        expression = items.get(index)?;
    }
    Some(expression)
}
