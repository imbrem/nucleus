//! Binary decision diagrams for userspace reasoning.
//!
//! [`Diagram`] is general syntax: it may be unordered, redundant, or repeat a
//! variable along a path. [`Bdd`] is a reduced ordered handle canonical within
//! one [`Manager`]. This crate is an optimization and conversion tool, not part
//! of a trusted kernel boundary.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_logic_sat::cnf::{Clause, Formula, Literal};

static NEXT_MANAGER: AtomicU64 = AtomicU64::new(1);

/// A positive propositional variable number, ordered numerically.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable(u64);

impl Variable {
    /// Constructs a variable compatible with Covalence's signed CNF literals.
    ///
    /// # Errors
    ///
    /// Rejects zero and values greater than `i64::MAX`.
    pub const fn new(value: u64) -> Result<Self, BddError> {
        if value == 0 || value > i64::MAX as u64 {
            Err(BddError::InvalidVariable(value))
        } else {
            Ok(Self(value))
        }
    }

    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// An error at a BDD API boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BddError {
    InvalidVariable(u64),
    VariableExhausted,
    ManagerMismatch,
    MissingVariable(Variable),
}

impl fmt::Display for BddError {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVariable(variable) => {
                write!(
                    output,
                    "BDD variable must be in 1..=i64::MAX, found {variable}"
                )
            }
            Self::VariableExhausted => {
                output.write_str("no fresh CNF variable remains below i64::MAX")
            }
            Self::ManagerMismatch => output.write_str("BDD values belong to different managers"),
            Self::MissingVariable(variable) => {
                write!(
                    output,
                    "assignment has no value for variable {}",
                    variable.get()
                )
            }
        }
    }
}

impl Error for BddError {}

/// A general, potentially non-canonical binary decision DAG.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagram(Arc<DiagramNode>);

#[derive(Debug, Eq, PartialEq)]
enum DiagramNode {
    False,
    True,
    Branch {
        variable: Variable,
        low: Diagram,
        high: Diagram,
    },
}

impl Diagram {
    #[must_use]
    pub fn constant(value: bool) -> Self {
        Self(Arc::new(if value {
            DiagramNode::True
        } else {
            DiagramNode::False
        }))
    }

    #[must_use]
    pub fn branch(variable: Variable, low: Self, high: Self) -> Self {
        Self(Arc::new(DiagramNode::Branch {
            variable,
            low,
            high,
        }))
    }

    #[must_use]
    pub fn kind(&self) -> DiagramKind<'_> {
        match self.0.as_ref() {
            DiagramNode::False => DiagramKind::Constant(false),
            DiagramNode::True => DiagramKind::Constant(true),
            DiagramNode::Branch {
                variable,
                low,
                high,
            } => DiagramKind::Branch {
                variable: *variable,
                low,
                high,
            },
        }
    }

    /// Evaluates this syntax without requiring it to be ordered or reduced.
    ///
    /// # Errors
    ///
    /// Returns the first variable absent from `assignment`.
    pub fn evaluate(
        &self,
        mut assignment: impl FnMut(Variable) -> Option<bool>,
    ) -> Result<bool, BddError> {
        let mut current = self;
        loop {
            match current.kind() {
                DiagramKind::Constant(value) => return Ok(value),
                DiagramKind::Branch {
                    variable,
                    low,
                    high,
                } => {
                    current = if assignment(variable).ok_or(BddError::MissingVariable(variable))? {
                        high
                    } else {
                        low
                    };
                }
            }
        }
    }
}

/// A borrowed view of one general decision node.
#[derive(Clone, Copy, Debug)]
pub enum DiagramKind<'a> {
    Constant(bool),
    Branch {
        variable: Variable,
        low: &'a Diagram,
        high: &'a Diagram,
    },
}

/// A canonical BDD handle. It is meaningful only with its originating manager.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bdd {
    manager: u64,
    node: u32,
}

/// A linear-size CNF encoding and the fresh variables it introduces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CnfEncoding {
    formula: Formula,
    introduced: Box<[Variable]>,
}

impl CnfEncoding {
    #[must_use]
    pub fn formula(&self) -> &Formula {
        &self.formula
    }

    #[must_use]
    pub fn introduced_variables(&self) -> &[Variable] {
        &self.introduced
    }
}

#[derive(Clone, Copy)]
enum CnfAtom {
    Constant(bool),
    Literal(i64),
}

impl CnfAtom {
    const fn not(self) -> Self {
        match self {
            Self::Constant(value) => Self::Constant(!value),
            Self::Literal(literal) => Self::Literal(-literal),
        }
    }
}

fn push_cnf_clause(clauses: &mut Vec<Clause>, atoms: impl IntoIterator<Item = CnfAtom>) {
    let mut literals = BTreeSet::new();
    for atom in atoms {
        match atom {
            CnfAtom::Constant(true) => return,
            CnfAtom::Constant(false) => {}
            CnfAtom::Literal(literal) => {
                if literals.contains(&-literal) {
                    return;
                }
                literals.insert(literal);
            }
        }
    }
    clauses.push(Clause::new(literals.into_iter().map(|literal| {
        Literal::new(literal).expect("CNF atoms are nonzero and negatable")
    })));
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Node {
    variable: Variable,
    low: u32,
    high: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum BinaryOp {
    And,
    Or,
    Xor,
}

/// Owns the unique table and variable order for canonical BDDs.
pub struct Manager {
    id: u64,
    nodes: Vec<Option<Node>>,
    unique: HashMap<Node, u32>,
}

impl Default for Manager {
    fn default() -> Self {
        Self::new()
    }
}

impl Manager {
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: NEXT_MANAGER.fetch_add(1, Ordering::Relaxed),
            nodes: vec![None, None],
            unique: HashMap::new(),
        }
    }

    #[must_use]
    pub const fn constant(&self, value: bool) -> Bdd {
        self.handle(if value { 1 } else { 0 })
    }

    #[must_use]
    pub fn variable(&mut self, variable: Variable) -> Bdd {
        let low = self.constant(false);
        let high = self.constant(true);
        self.make(variable, low.node, high.node)
    }

    /// Reduces arbitrary decision syntax into this manager's canonical order.
    pub fn reduce(&mut self, diagram: &Diagram) -> Bdd {
        fn visit(manager: &mut Manager, diagram: &Diagram, cache: &mut HashMap<usize, Bdd>) -> Bdd {
            let identity = Arc::as_ptr(&diagram.0) as usize;
            if let Some(&result) = cache.get(&identity) {
                return result;
            }
            let result = match diagram.kind() {
                DiagramKind::Constant(value) => manager.constant(value),
                DiagramKind::Branch {
                    variable,
                    low,
                    high,
                } => {
                    let low = visit(manager, low, cache);
                    let high = visit(manager, high, cache);
                    let test = manager.variable(variable);
                    manager.if_then_else(test, high, low).expect("one manager")
                }
            };
            cache.insert(identity, result);
            result
        }

        visit(self, diagram, &mut HashMap::new())
    }

    /// Expands a canonical handle into shared general syntax.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn to_diagram(&self, root: Bdd) -> Result<Diagram, BddError> {
        fn visit(manager: &Manager, node: u32, cache: &mut HashMap<u32, Diagram>) -> Diagram {
            if let Some(value) = cache.get(&node) {
                return value.clone();
            }
            let value = match manager.node(node) {
                None => Diagram::constant(node == 1),
                Some(node) => Diagram::branch(
                    node.variable,
                    visit(manager, node.low, cache),
                    visit(manager, node.high, cache),
                ),
            };
            cache.insert(node, value.clone());
            value
        }
        self.check(root)?;
        Ok(visit(self, root.node, &mut HashMap::new()))
    }

    /// Complements a canonical BDD.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn not(&mut self, value: Bdd) -> Result<Bdd, BddError> {
        fn visit(manager: &mut Manager, node: u32, cache: &mut HashMap<u32, u32>) -> u32 {
            if node < 2 {
                return 1 - node;
            }
            if let Some(&result) = cache.get(&node) {
                return result;
            }
            let current = manager.node(node).expect("nonterminal");
            let low = visit(manager, current.low, cache);
            let high = visit(manager, current.high, cache);
            let result = manager.make(current.variable, low, high).node;
            cache.insert(node, result);
            result
        }
        self.check(value)?;
        let node = visit(self, value.node, &mut HashMap::new());
        Ok(self.handle(node))
    }

    /// Conjoins two canonical BDDs.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn and(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.apply(BinaryOp::And, left, right)
    }

    /// Disjoins two canonical BDDs.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn or(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.apply(BinaryOp::Or, left, right)
    }

    /// Computes exclusive disjunction.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn xor(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.apply(BinaryOp::Xor, left, right)
    }

    /// Computes Boolean implication.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn implication(&mut self, premise: Bdd, conclusion: Bdd) -> Result<Bdd, BddError> {
        let premise = self.not(premise)?;
        self.or(premise, conclusion)
    }

    /// Computes Boolean equivalence.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn equivalence(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        let different = self.xor(left, right)?;
        self.not(different)
    }

    /// Existentially quantifies one variable.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn exists(&mut self, variable: Variable, value: Bdd) -> Result<Bdd, BddError> {
        fn visit(
            manager: &mut Manager,
            variable: Variable,
            node: u32,
            cache: &mut HashMap<u32, u32>,
        ) -> Result<u32, BddError> {
            let Some(current) = manager.node(node) else {
                return Ok(node);
            };
            if current.variable > variable {
                return Ok(node);
            }
            if let Some(&result) = cache.get(&node) {
                return Ok(result);
            }
            let result = if current.variable == variable {
                manager
                    .or(manager.handle(current.low), manager.handle(current.high))?
                    .node
            } else {
                let low = visit(manager, variable, current.low, cache)?;
                let high = visit(manager, variable, current.high, cache)?;
                manager.make(current.variable, low, high).node
            };
            cache.insert(node, result);
            Ok(result)
        }
        self.check(value)?;
        let node = visit(self, variable, value.node, &mut HashMap::new())?;
        Ok(self.handle(node))
    }

    /// Selects between two BDDs with a BDD condition.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn if_then_else(
        &mut self,
        condition: Bdd,
        then_value: Bdd,
        else_value: Bdd,
    ) -> Result<Bdd, BddError> {
        let positive = self.and(condition, then_value)?;
        let negative_condition = self.not(condition)?;
        let negative = self.and(negative_condition, else_value)?;
        self.or(positive, negative)
    }

    /// Builds the conjunction of a CNF formula.
    ///
    /// # Errors
    ///
    /// Reserved for manager consistency failures.
    pub fn from_cnf(&mut self, formula: &Formula) -> Result<Bdd, BddError> {
        let mut result = self.constant(true);
        for clause in formula.clauses() {
            let mut disjunction = self.constant(false);
            for literal in clause.literals() {
                let variable = Variable(literal.variable());
                let mut value = self.variable(variable);
                if literal.get() < 0 {
                    value = self.not(value)?;
                }
                disjunction = self.or(disjunction, value)?;
            }
            result = self.and(result, disjunction)?;
        }
        Ok(result)
    }

    /// Produces a linear-size Tseitin CNF encoding of `root`.
    ///
    /// One fresh variable names each reachable internal BDD node. The returned
    /// formula is equivalent to `root` after existentially quantifying the
    /// returned `introduced_variables`.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager or exhaustion of the CNF variable
    /// namespace.
    ///
    /// # Panics
    ///
    /// Panics only if this manager's private node table is internally corrupt.
    pub fn to_cnf(&self, root: Bdd) -> Result<CnfEncoding, BddError> {
        self.check(root)?;
        let original = self.variables(root)?;
        let mut next = original
            .last()
            .map_or(1, |variable| variable.get().saturating_add(1));

        let mut order = Vec::new();
        let mut pending = vec![(root.node, false)];
        let mut visited = HashSet::new();
        while let Some((node, expanded)) = pending.pop() {
            if node < 2 {
                continue;
            }
            if expanded {
                order.push(node);
            } else if visited.insert(node) {
                let current = self.node(node).expect("internal node");
                pending.push((node, true));
                pending.push((current.high, false));
                pending.push((current.low, false));
            }
        }

        let mut auxiliaries = HashMap::new();
        let mut introduced = Vec::with_capacity(order.len());
        for &node in &order {
            let variable = Variable::new(next).map_err(|_| BddError::VariableExhausted)?;
            auxiliaries.insert(node, variable);
            introduced.push(variable);
            next = next.checked_add(1).ok_or(BddError::VariableExhausted)?;
        }

        let atom = |node: u32| {
            if node < 2 {
                CnfAtom::Constant(node == 1)
            } else {
                let variable = auxiliaries[&node];
                CnfAtom::Literal(i64::try_from(variable.get()).expect("bounded variable"))
            }
        };
        let mut clauses = Vec::new();
        for &node in &order {
            let current = self.node(node).expect("internal node");
            let output = atom(node);
            let test =
                CnfAtom::Literal(i64::try_from(current.variable.get()).expect("bounded variable"));
            let low = atom(current.low);
            let high = atom(current.high);
            push_cnf_clause(&mut clauses, [output.not(), test.not(), high]);
            push_cnf_clause(&mut clauses, [output.not(), test, low]);
            push_cnf_clause(&mut clauses, [output, test.not(), high.not()]);
            push_cnf_clause(&mut clauses, [output, test, low.not()]);
        }
        push_cnf_clause(&mut clauses, [atom(root.node)]);
        Ok(CnfEncoding {
            formula: Formula::new(clauses),
            introduced: introduced.into_boxed_slice(),
        })
    }

    /// Evaluates a canonical BDD.
    ///
    /// # Errors
    ///
    /// Rejects a foreign handle or a missing assignment.
    pub fn evaluate(
        &self,
        root: Bdd,
        mut assignment: impl FnMut(Variable) -> Option<bool>,
    ) -> Result<bool, BddError> {
        self.check(root)?;
        let mut node = root.node;
        loop {
            let Some(current) = self.node(node) else {
                return Ok(node == 1);
            };
            node = if assignment(current.variable)
                .ok_or(BddError::MissingVariable(current.variable))?
            {
                current.high
            } else {
                current.low
            };
        }
    }

    /// Returns the variables reachable from a canonical root.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn variables(&self, root: Bdd) -> Result<BTreeSet<Variable>, BddError> {
        self.check(root)?;
        let mut variables = BTreeSet::new();
        let mut pending = vec![root.node];
        let mut visited = HashSet::new();
        while let Some(node) = pending.pop() {
            if !visited.insert(node) {
                continue;
            }
            if let Some(node) = self.node(node) {
                variables.insert(node.variable);
                pending.extend([node.low, node.high]);
            }
        }
        Ok(variables)
    }

    /// Counts distinct reachable nodes, including reached terminals.
    ///
    /// # Errors
    ///
    /// Rejects a handle from another manager.
    pub fn node_count(&self, root: Bdd) -> Result<usize, BddError> {
        self.check(root)?;
        let mut pending = vec![root.node];
        let mut visited = HashSet::new();
        while let Some(node) = pending.pop() {
            if !visited.insert(node) {
                continue;
            }
            if let Some(node) = self.node(node) {
                pending.extend([node.low, node.high]);
            }
        }
        Ok(visited.len())
    }

    #[must_use]
    pub const fn is_false(&self, value: Bdd) -> bool {
        value.manager == self.id && value.node == 0
    }

    #[must_use]
    pub const fn is_true(&self, value: Bdd) -> bool {
        value.manager == self.id && value.node == 1
    }

    const fn handle(&self, node: u32) -> Bdd {
        Bdd {
            manager: self.id,
            node,
        }
    }

    fn check(&self, value: Bdd) -> Result<(), BddError> {
        if value.manager == self.id {
            Ok(())
        } else {
            Err(BddError::ManagerMismatch)
        }
    }

    fn node(&self, node: u32) -> Option<Node> {
        self.nodes[node as usize]
    }

    fn make(&mut self, variable: Variable, low: u32, high: u32) -> Bdd {
        if low == high {
            return self.handle(low);
        }
        let node = Node {
            variable,
            low,
            high,
        };
        if let Some(&existing) = self.unique.get(&node) {
            return self.handle(existing);
        }
        let index = u32::try_from(self.nodes.len()).expect("BDD manager exceeded u32 nodes");
        self.nodes.push(Some(node));
        self.unique.insert(node, index);
        self.handle(index)
    }

    fn apply(&mut self, op: BinaryOp, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        fn visit(
            manager: &mut Manager,
            op: BinaryOp,
            mut left: u32,
            mut right: u32,
            cache: &mut HashMap<(BinaryOp, u32, u32), u32>,
        ) -> u32 {
            if left > right {
                std::mem::swap(&mut left, &mut right);
            }
            if left < 2 && right < 2 {
                let left = left == 1;
                let right = right == 1;
                return u32::from(match op {
                    BinaryOp::And => left && right,
                    BinaryOp::Or => left || right,
                    BinaryOp::Xor => left ^ right,
                });
            }
            if let Some(&result) = cache.get(&(op, left, right)) {
                return result;
            }
            let left_node = manager.node(left);
            let right_node = manager.node(right);
            let variable = match (left_node, right_node) {
                (Some(left), Some(right)) => left.variable.min(right.variable),
                (Some(left), None) => left.variable,
                (None, Some(right)) => right.variable,
                (None, None) => unreachable!(),
            };
            let (left_low, left_high) = match left_node {
                Some(node) if node.variable == variable => (node.low, node.high),
                _ => (left, left),
            };
            let (right_low, right_high) = match right_node {
                Some(node) if node.variable == variable => (node.low, node.high),
                _ => (right, right),
            };
            let low = visit(manager, op, left_low, right_low, cache);
            let high = visit(manager, op, left_high, right_high, cache);
            let result = manager.make(variable, low, high).node;
            cache.insert((op, left, right), result);
            result
        }
        self.check(left)?;
        self.check(right)?;
        let node = visit(self, op, left.node, right.node, &mut HashMap::new());
        Ok(self.handle(node))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduction_orders_and_removes_redundant_syntax() {
        let x = Variable::new(1).unwrap();
        let y = Variable::new(2).unwrap();
        let syntax = Diagram::branch(
            y,
            Diagram::branch(x, Diagram::constant(false), Diagram::constant(true)),
            Diagram::branch(x, Diagram::constant(false), Diagram::constant(true)),
        );
        let mut manager = Manager::new();
        assert_eq!(manager.reduce(&syntax), manager.variable(x));
    }

    #[test]
    fn boolean_operations_are_canonical_and_evaluate() {
        let mut manager = Manager::new();
        let x = manager.variable(Variable::new(1).unwrap());
        let y = manager.variable(Variable::new(2).unwrap());
        let xy = manager.and(x, y).unwrap();
        assert_eq!(manager.and(y, x).unwrap(), xy);
        assert!(
            !manager
                .evaluate(xy, |variable| Some(variable == Variable::new(1).unwrap()))
                .unwrap()
        );
        assert!(manager.evaluate(xy, |_| Some(true)).unwrap());
    }

    #[test]
    fn cnf_round_trips_by_semantics() {
        let formula = Formula::from_signed([[1, -2], [2, 3]]).unwrap();
        let mut manager = Manager::new();
        let root = manager.from_cnf(&formula).unwrap();
        let encoding = manager.to_cnf(root).unwrap();
        assert!(encoding.formula().len() <= 4 * encoding.introduced_variables().len() + 1);
        let mut rebuilt = manager.from_cnf(encoding.formula()).unwrap();
        for &variable in encoding.introduced_variables() {
            rebuilt = manager.exists(variable, rebuilt).unwrap();
        }
        assert_eq!(root, rebuilt);
    }

    #[test]
    fn managers_cannot_mix_handles() {
        let left = Manager::new();
        let mut right = Manager::new();
        assert_eq!(
            right.not(left.constant(true)),
            Err(BddError::ManagerMismatch)
        );
    }
}
