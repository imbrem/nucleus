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
}

/// Exact-size iterator over the direct children of an [`IlCursor`].
#[derive(Clone, Debug)]
pub struct IlChildren<'a> {
    parent: IlCursor<'a>,
    next: usize,
    arity: usize,
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
