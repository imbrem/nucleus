//! The Metamath frame / database model.
//!
//! A [`Database`] is a flat, source-order list of [`Statement`]s plus a symbol
//! table classifying every symbol as a constant or a variable. Assertions
//! (`$a` axioms, `$p` theorems) carry their **mandatory [`Frame`]**: the
//! `$f`/`$e` hypotheses they depend on (in database order) and the `$d`
//! distinct-variable conditions that constrain how they may be applied.
//!
//! Building a database tracks an active scope stack (`${ ... $}`): floating
//! hypotheses, essential hypotheses, variable declarations, and `$d`
//! restrictions are scoped, while `$c`/`$a`/`$p` are global.

use std::collections::hash_map::Entry;

use fnv::{FnvHashMap, FnvHashSet};

use crate::error::MmError;
use crate::expr::Expr;

/// A floating hypothesis (`$f`): a variable's typecode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FloatHyp {
    pub label: String,
    /// The typecode constant (e.g. `wff`, `term`, `class`).
    pub typecode: String,
    /// The variable being typed (e.g. `ph`, `t`).
    pub var: String,
}

/// An essential hypothesis (`$e`): a full logical premise as an [`Expr`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    pub label: String,
    pub expr: Expr,
}

/// The mandatory frame of an assertion: the hypotheses it consumes and the
/// distinct-variable conditions it imposes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Frame {
    /// Mandatory `$f` hypotheses, in database order. These are the variables
    /// the assertion is parameterised over (its "type signature").
    pub floats: Vec<FloatHyp>,
    /// Mandatory `$e` hypotheses, in database order.
    pub essentials: Vec<Hypothesis>,
    /// Mandatory `$d` conditions as unordered variable pairs.
    pub disjoints: Vec<(String, String)>,
}

impl Frame {
    /// The mandatory hypotheses in RPN-application order: all `$f` first
    /// (database order), then all `$e` (database order). This is the order in
    /// which they are popped off the proof stack.
    pub fn mandatory_count(&self) -> usize {
        self.floats.len() + self.essentials.len()
    }
}

/// A `$p` theorem's proof, in either of Metamath's two encodings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    /// A *normal* (uncompressed) proof: a reverse-Polish sequence of labels.
    Normal(Vec<String>),
    /// A *compressed* proof: a parenthesised label block plus a letter block
    /// (the `A`–`T` / `U`–`Y` base-20/5 integer scheme with `Z` save markers).
    /// The decoder lives in [`crate::verify`].
    Compressed {
        /// The labels referenced by the letter block (between `(` and `)`).
        labels: Vec<String>,
        /// The raw letter block (concatenated, whitespace already stripped).
        letters: Vec<u8>,
    },
}

/// Classification of a declared symbol: `$c` constant or `$v` variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    Constant,
    Variable,
}

/// An assertion: an axiom (`$a`) or a theorem (`$p`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    pub label: String,
    /// The asserted conclusion (typecode + body).
    pub conclusion: Expr,
    /// The mandatory frame.
    pub frame: Frame,
    /// `Some(proof)` for a `$p` theorem, `None` for a `$a` axiom.
    pub proof: Option<Proof>,
    /// The **full** set of `$d` pairs active in this assertion's scope, over
    /// *all* variables (not filtered to the mandatory frame). This is the set a
    /// `$p` theorem's proof checks generated distinct-variable obligations
    /// against: it includes `$d` pairs that mention dummy / working variables
    /// used only inside the proof.
    ///
    /// `frame.disjoints` (the mandatory-filtered subset) is what propagates when
    /// *this* assertion is later applied; `scope_disjoints` is what is *checked*
    /// while proving it. For `$a` axioms the distinction is irrelevant (no
    /// proof), but the field is still the full active set.
    pub scope_disjoints: Vec<(String, String)>,
}

/// A top-level statement, in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// `$c` constant declaration.
    Constant(Vec<String>),
    /// `$v` variable declaration.
    Variable(Vec<String>),
    /// `$f` floating hypothesis.
    Float(FloatHyp),
    /// `$e` essential hypothesis.
    Essential(Hypothesis),
    /// `$d` distinct-variable restriction (the full symbol list).
    Disjoint(Vec<String>),
    /// `$a` / `$p` assertion.
    Assert(Assertion),
}

/// One lexical scope (`${ ... $}`).
#[derive(Debug, Clone, Default)]
struct Scope {
    floats: Vec<FloatHyp>,
    essentials: Vec<Hypothesis>,
    /// Active `$d` pairs (already expanded pairwise).
    disjoints: Vec<(String, String)>,
}

/// A parsed Metamath database.
#[derive(Debug, Clone)]
pub struct Database {
    /// Symbol classification: name → `true` if a variable, `false` if a
    /// constant.
    symbols: FnvHashMap<String, bool>,
    /// All statements in source order.
    statements: Vec<Statement>,
    /// label → index into `statements` (only labelled statements).
    labels: FnvHashMap<String, usize>,
    /// Active scope stack; index 0 is the global scope.
    scopes: Vec<Scope>,
}

impl Default for Database {
    fn default() -> Self {
        Self::new()
    }
}

impl Database {
    pub fn new() -> Self {
        Self {
            symbols: FnvHashMap::default(),
            statements: Vec::new(),
            labels: FnvHashMap::default(),
            scopes: vec![Scope::default()],
        }
    }

    // --- queries -----------------------------------------------------------

    /// Whether `name` is a declared variable.
    pub fn is_variable(&self, name: &str) -> bool {
        self.symbols.get(name).copied().unwrap_or(false)
    }

    /// Whether `name` is a declared symbol (constant or variable).
    pub fn is_symbol(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    /// All statements in source order.
    pub fn statements(&self) -> &[Statement] {
        &self.statements
    }

    /// All declared symbols and their classifications.
    pub fn symbols(&self) -> impl Iterator<Item = (&str, SymbolKind)> {
        self.symbols.iter().map(|(name, variable)| {
            (
                name.as_str(),
                if *variable {
                    SymbolKind::Variable
                } else {
                    SymbolKind::Constant
                },
            )
        })
    }

    /// Look up a labelled statement.
    pub fn statement_by_label(&self, label: &str) -> Option<&Statement> {
        self.labels.get(label).map(|&i| &self.statements[i])
    }

    /// Iterate over all assertions (`$a`/`$p`) in source order.
    pub fn assertions(&self) -> impl Iterator<Item = &Assertion> {
        self.statements.iter().filter_map(|s| match s {
            Statement::Assert(a) => Some(a),
            _ => None,
        })
    }

    // --- construction (the database-building API; used by a reader/parser) --

    pub fn declare_constants(&mut self, names: Vec<String>) -> Result<(), MmError> {
        for n in &names {
            if self.symbols.insert(n.clone(), false).is_some() {
                return Err(MmError::Parse(format!("symbol `{n}` re-declared")));
            }
        }
        self.statements.push(Statement::Constant(names));
        Ok(())
    }

    pub fn declare_variables(&mut self, names: Vec<String>) -> Result<(), MmError> {
        for n in &names {
            // A variable may be re-declared in a disjoint scope; we keep it
            // simple and allow re-declaration as a variable.
            match self.symbols.get(n) {
                Some(false) => {
                    return Err(MmError::Parse(format!(
                        "symbol `{n}` declared as both constant and variable"
                    )));
                }
                _ => {
                    self.symbols.insert(n.clone(), true);
                }
            }
        }
        self.statements.push(Statement::Variable(names));
        Ok(())
    }

    fn register_label(&mut self, label: &str, idx: usize) -> Result<(), MmError> {
        // `entry` hashes the label once; the `contains_key` + `insert` pair
        // hashed it twice for every labelled statement in the database.
        match self.labels.entry(label.to_string()) {
            Entry::Occupied(entry) => Err(MmError::DuplicateLabel(entry.key().clone())),
            Entry::Vacant(entry) => {
                entry.insert(idx);
                Ok(())
            }
        }
    }

    pub fn add_float(&mut self, hyp: FloatHyp) -> Result<(), MmError> {
        if !self.is_symbol(&hyp.typecode) {
            return Err(MmError::UnknownSymbol {
                label: hyp.label.clone(),
                symbol: hyp.typecode.clone(),
            });
        }
        if !self.is_variable(&hyp.var) {
            return Err(MmError::Parse(format!(
                "`{}`: `{}` is not a declared variable",
                hyp.label, hyp.var
            )));
        }
        let idx = self.statements.len();
        self.register_label(&hyp.label, idx)?;
        self.scopes.last_mut().unwrap().floats.push(hyp.clone());
        self.statements.push(Statement::Float(hyp));
        Ok(())
    }

    pub fn add_essential(&mut self, hyp: Hypothesis) -> Result<(), MmError> {
        let idx = self.statements.len();
        self.register_label(&hyp.label, idx)?;
        self.scopes.last_mut().unwrap().essentials.push(hyp.clone());
        self.statements.push(Statement::Essential(hyp));
        Ok(())
    }

    pub fn add_disjoint(&mut self, vars: Vec<String>) -> Result<(), MmError> {
        for v in &vars {
            if !self.is_variable(v) {
                return Err(MmError::Parse(format!("`{v}` in $d is not a variable")));
            }
        }
        // Expand into pairwise restrictions in the current scope.
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if vars[i] == vars[j] {
                    return Err(MmError::Parse(format!(
                        "$d lists `{}` twice (a variable is never distinct from itself)",
                        vars[i]
                    )));
                }
                self.scopes
                    .last_mut()
                    .unwrap()
                    .disjoints
                    .push((vars[i].clone(), vars[j].clone()));
            }
        }
        self.statements.push(Statement::Disjoint(vars));
        Ok(())
    }

    /// Add an assertion (`$a` or `$p`), computing its mandatory frame from the
    /// active scope stack.
    pub fn add_assertion(
        &mut self,
        label: String,
        conclusion: Expr,
        proof: Option<Proof>,
    ) -> Result<(), MmError> {
        let frame = self.build_frame(&conclusion, &label)?;
        // The full in-scope `$d` set (all variables, unfiltered) — what a proof
        // checks its generated obligations against.
        let scope_disjoints: Vec<(String, String)> = self
            .scopes
            .iter()
            .flat_map(|s| s.disjoints.iter())
            .cloned()
            .collect();
        let idx = self.statements.len();
        self.register_label(&label, idx)?;
        self.statements.push(Statement::Assert(Assertion {
            label,
            conclusion,
            frame,
            proof,
            scope_disjoints,
        }));
        Ok(())
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    pub fn pop_scope(&mut self) -> Result<(), MmError> {
        if self.scopes.len() <= 1 {
            return Err(MmError::Parse("unmatched `$}`".into()));
        }
        self.scopes.pop();
        Ok(())
    }

    pub fn finish(self) -> Result<Self, MmError> {
        if self.scopes.len() != 1 {
            return Err(MmError::Parse("unclosed `${` at end of input".into()));
        }
        Ok(self)
    }

    /// Rename every **symbol** of the database through `f`, leaving labels,
    /// proofs, and structure untouched. The result is an *isomorphic copy*
    /// under the symbol map:
    /// substitution, frame computation, and `$d` checking all commute with a
    /// symbol renaming, so every proof that verifies against `self` verifies
    /// verbatim against the renamed database and vice versa — provided `f` is
    /// **injective on the declared symbols** and preserves kind (constant vs
    /// variable). Both are checked; a collision is an error.
    ///
    /// This is a whole-database primitive for experiments with equivalent
    /// symbol presentations.
    pub fn map_symbols(&self, f: &dyn Fn(&str) -> String) -> Result<Database, MmError> {
        let rename_expr = |e: &Expr| {
            Expr::new(
                f(e.typecode()),
                e.body().iter().map(|s| f(s).into()).collect(),
            )
        };
        let rename_float = |h: &FloatHyp| FloatHyp {
            label: h.label.clone(),
            typecode: f(&h.typecode),
            var: f(&h.var),
        };
        let rename_ess = |h: &Hypothesis| Hypothesis {
            label: h.label.clone(),
            expr: rename_expr(&h.expr),
        };
        let rename_pairs = |ps: &[(String, String)]| -> Vec<(String, String)> {
            ps.iter().map(|(a, b)| (f(a), f(b))).collect()
        };
        let rename_frame = |fr: &Frame| Frame {
            floats: fr.floats.iter().map(rename_float).collect(),
            essentials: fr.essentials.iter().map(rename_ess).collect(),
            disjoints: rename_pairs(&fr.disjoints),
        };

        // Symbols map: check injectivity + kind consistency. The walk is sorted
        // by source symbol because `self.symbols` is a hash map: iterating it
        // directly visits symbols in table-layout order, so which of several
        // colliding pairs gets reported is arbitrary and shifts whenever an
        // unrelated symbol is declared. Sorting pins the diagnostic to the
        // lexicographically first collision, which stays put as `f` is
        // debugged.
        let mut sources: Vec<(&str, bool)> = self
            .symbols
            .iter()
            .map(|(name, is_var)| (name.as_str(), *is_var))
            .collect();
        sources.sort_unstable();

        let kind = |is_var: bool| if is_var { "variable" } else { "constant" };
        // renamed → (kind, the source symbol that claimed it), so a collision
        // can name *both* sides rather than just the image they share.
        let mut claimed: FnvHashMap<String, (bool, &str)> = FnvHashMap::default();
        for (name, is_var) in sources {
            match claimed.entry(f(name)) {
                Entry::Occupied(entry) => {
                    let renamed = entry.key();
                    let (prev_var, prev) = *entry.get();
                    return Err(MmError::Parse(if prev_var != is_var {
                        format!(
                            "symbol renaming collides on `{renamed}`: `{prev}` is a {} and `{name}` is a {}",
                            kind(prev_var),
                            kind(is_var)
                        )
                    } else {
                        format!(
                            "symbol renaming is not injective: `{prev}` and `{name}` both map to `{renamed}`"
                        )
                    }));
                }
                Entry::Vacant(entry) => {
                    entry.insert((is_var, name));
                }
            }
        }
        // Drop the provenance now that every rename has been checked.
        let symbols: FnvHashMap<String, bool> = claimed
            .into_iter()
            .map(|(renamed, (is_var, _))| (renamed, is_var))
            .collect();

        let statements = self
            .statements
            .iter()
            .map(|s| match s {
                Statement::Constant(ns) => Statement::Constant(ns.iter().map(|n| f(n)).collect()),
                Statement::Variable(ns) => Statement::Variable(ns.iter().map(|n| f(n)).collect()),
                Statement::Float(h) => Statement::Float(rename_float(h)),
                Statement::Essential(h) => Statement::Essential(rename_ess(h)),
                Statement::Disjoint(vs) => Statement::Disjoint(vs.iter().map(|v| f(v)).collect()),
                Statement::Assert(a) => Statement::Assert(Assertion {
                    label: a.label.clone(),
                    conclusion: rename_expr(&a.conclusion),
                    frame: rename_frame(&a.frame),
                    proof: a.proof.clone(),
                    scope_disjoints: rename_pairs(&a.scope_disjoints),
                }),
            })
            .collect();

        let scopes = self
            .scopes
            .iter()
            .map(|sc| Scope {
                floats: sc.floats.iter().map(rename_float).collect(),
                essentials: sc.essentials.iter().map(rename_ess).collect(),
                disjoints: rename_pairs(&sc.disjoints),
            })
            .collect();

        Ok(Database {
            symbols,
            statements,
            labels: self.labels.clone(),
            scopes,
        })
    }

    /// Render this database to canonical `.mm` source (see [`crate::emit`]).
    /// The result re-parses to a structurally-equivalent database (same symbols
    /// and assertion statements/frames), normalising scope structure.
    pub fn to_mm_string(&self) -> String {
        crate::emit::to_mm_string(self)
    }

    // --- frame computation -------------------------------------------------

    /// Compute the mandatory frame for an assertion with the given conclusion.
    ///
    /// Per the Metamath spec, the mandatory variables are those appearing in
    /// the conclusion or in any active `$e` hypothesis. The mandatory `$f`
    /// hypotheses are the active floats for exactly those variables, in
    /// database order. The mandatory `$e` are all active essentials. The
    /// mandatory `$d` are the active disjoint pairs whose *both* variables are
    /// mandatory.
    fn build_frame(&self, conclusion: &Expr, label: &str) -> Result<Frame, MmError> {
        // Active hypotheses, outermost scope first (= database order).
        let active_floats: Vec<&FloatHyp> =
            self.scopes.iter().flat_map(|s| s.floats.iter()).collect();
        let active_essentials: Vec<&Hypothesis> = self
            .scopes
            .iter()
            .flat_map(|s| s.essentials.iter())
            .collect();
        let active_disjoints: Vec<&(String, String)> = self
            .scopes
            .iter()
            .flat_map(|s| s.disjoints.iter())
            .collect();

        // Mandatory variable set: from the conclusion and from active $e. The
        // `Vec` fixes first-occurrence order — the order the "missing `$f`"
        // diagnostic below reports in — while the set answers membership, which
        // as a `Vec::contains` scan was quadratic in the mandatory-variable
        // count. Both borrow the name from the symbol table, so neither
        // allocates per symbol *occurrence*.
        let mut mandatory_vars: Vec<&str> = Vec::new();
        let mut mandatory: FnvHashSet<&str> = FnvHashSet::default();
        let mut push_var = |name: &str| {
            if let Some((declared, is_variable)) = self.symbols.get_key_value(name) {
                if *is_variable && mandatory.insert(declared.as_str()) {
                    mandatory_vars.push(declared.as_str());
                }
            }
        };
        self.collect_vars(conclusion, label, &mut push_var)?;
        for h in &active_essentials {
            self.collect_vars(&h.expr, &h.label, &mut push_var)?;
        }

        // Mandatory $f: active floats whose variable is mandatory, in order.
        let floats: Vec<FloatHyp> = active_floats
            .iter()
            .filter(|f| mandatory.contains(f.var.as_str()))
            .map(|f| (*f).clone())
            .collect();

        // Every mandatory variable must have a floating hypothesis.
        let typed: FnvHashSet<&str> = floats.iter().map(|f| f.var.as_str()).collect();
        for v in &mandatory_vars {
            if !typed.contains(v) {
                return Err(MmError::MalformedExpr {
                    label: label.to_string(),
                    message: format!("variable `{v}` has no active floating hypothesis (`$f`)"),
                });
            }
        }

        let essentials: Vec<Hypothesis> = active_essentials.into_iter().cloned().collect();

        let disjoints: Vec<(String, String)> = active_disjoints
            .iter()
            .filter(|(a, b)| mandatory.contains(a.as_str()) && mandatory.contains(b.as_str()))
            .map(|(a, b)| ((*a).clone(), (*b).clone()))
            .collect();

        Ok(Frame {
            floats,
            essentials,
            disjoints,
        })
    }

    /// Invoke `f` on every symbol of `expr`, validating that each is a declared
    /// symbol.
    fn collect_vars(
        &self,
        expr: &Expr,
        label: &str,
        f: &mut impl FnMut(&str),
    ) -> Result<(), MmError> {
        let syms = crate::expr::expr_symbols(expr).ok_or_else(|| MmError::MalformedExpr {
            label: label.to_string(),
            message: "expression contains a non-symbol element".into(),
        })?;
        for s in syms {
            if !self.is_symbol(s) {
                return Err(MmError::UnknownSymbol {
                    label: label.to_string(),
                    symbol: s.to_string(),
                });
            }
            f(s);
        }
        Ok(())
    }
}

/// The construction API a `.mm` reader drives, abstracted over the backend.
///
/// The in-memory [`Database`] implements this trait directly (its mutators are
/// the canonical implementation). A future HOL-backed sink can implement the
/// same trait, constructing kernel theorems as declarations stream through it,
/// without the reader knowing which backend it is feeding. The method set
/// mirrors `Database`'s own construction methods.
pub trait DatabaseSink {
    /// Declare one or more `$c` constants or `$v` variables.
    fn declare(&mut self, kind: SymbolKind, names: &[&str]) -> Result<(), MmError>;
    /// Open a `${ ... $}` scope.
    fn push_scope(&mut self);
    /// Close a `${ ... $}` scope.
    fn pop_scope(&mut self) -> Result<(), MmError>;
    /// Add a `$f` floating hypothesis `label $f typecode var`.
    fn add_float(&mut self, label: &str, typecode: &str, var: &str) -> Result<(), MmError>;
    /// Add a `$e` essential hypothesis `label $e <expr>`.
    fn add_essential(&mut self, label: &str, expr: Expr) -> Result<(), MmError>;
    /// Add a `$d` distinct-variable restriction over `vars`.
    fn add_disjoint(&mut self, vars: &[&str]) -> Result<(), MmError>;
    /// Add a `$a` axiom (`proof = None`) or `$p` theorem (`proof = Some(_)`).
    fn add_assertion(
        &mut self,
        label: &str,
        conclusion: Expr,
        proof: Option<Proof>,
    ) -> Result<(), MmError>;
}

impl DatabaseSink for Database {
    fn declare(&mut self, kind: SymbolKind, names: &[&str]) -> Result<(), MmError> {
        let names: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        match kind {
            SymbolKind::Constant => self.declare_constants(names),
            SymbolKind::Variable => self.declare_variables(names),
        }
    }

    fn push_scope(&mut self) {
        Database::push_scope(self);
    }

    fn pop_scope(&mut self) -> Result<(), MmError> {
        Database::pop_scope(self)
    }

    fn add_float(&mut self, label: &str, typecode: &str, var: &str) -> Result<(), MmError> {
        Database::add_float(
            self,
            FloatHyp {
                label: label.to_string(),
                typecode: typecode.to_string(),
                var: var.to_string(),
            },
        )
    }

    fn add_essential(&mut self, label: &str, expr: Expr) -> Result<(), MmError> {
        Database::add_essential(
            self,
            Hypothesis {
                label: label.to_string(),
                expr,
            },
        )
    }

    fn add_disjoint(&mut self, vars: &[&str]) -> Result<(), MmError> {
        Database::add_disjoint(self, vars.iter().map(|s| s.to_string()).collect())
    }

    fn add_assertion(
        &mut self,
        label: &str,
        conclusion: Expr,
        proof: Option<Proof>,
    ) -> Result<(), MmError> {
        Database::add_assertion(self, label.to_string(), conclusion, proof)
    }
}
