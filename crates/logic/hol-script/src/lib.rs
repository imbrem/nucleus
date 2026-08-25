//! An untrusted S-expression front end for checked HOL definitions.
//!
//! Parsing, scope resolution, and elaboration in this module carry no proof
//! authority. The compiler can only call public [`Kernel`] constructors; a bug
//! therefore produces rejected input or a different well-typed arena, never an
//! unchecked row. The returned symbol table is likewise external metadata.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_parse::winnow::{
    Parser,
    combinator::{alt, repeat},
    token::take_while,
};
use covalence_logic_hol::{Kernel, KernelError, Ref};

/// A checked kernel and the public roots named by its source module.
#[derive(Debug)]
pub struct CompiledTheory {
    kernel: Kernel,
    definitions: BTreeMap<String, Ref>,
    symbols: BTreeMap<String, Ref>,
}

impl CompiledTheory {
    /// Borrows the checked kernel produced by elaboration.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Resolves one public symbol.
    ///
    /// A definition is stored under its declared name. Its scoped type
    /// parameters use qualified names such as `IsCoprod/'a`, making an open
    /// schema's substitution inputs recoverable without putting names in the
    /// arena itself.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols.get(name).copied()
    }

    /// Iterates public definitions in lexical order.
    #[must_use]
    pub fn definitions(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.definitions
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Iterates the complete external name-to-reference dictionary.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.symbols
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Splits the checked kernel from its untrusted name index.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, BTreeMap<String, Ref>) {
        (self.kernel, self.symbols)
    }
}

/// A rejected theory source module.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TheoryError {
    /// The S-expression reader rejected the byte stream.
    #[snafu(display("could not read theory source: {message}"))]
    Read {
        /// Reader diagnostic.
        message: String,
    },
    /// A form does not have the grammar required in its position.
    #[snafu(display("invalid theory form: {message}"))]
    Invalid {
        /// Grammar diagnostic.
        message: String,
    },
    /// A name is not available in the current lexical scope.
    #[snafu(display("unknown theory name {name:?}"))]
    Unknown {
        /// Unresolved name.
        name: String,
    },
    /// A public definition repeats an earlier name.
    #[snafu(display("duplicate theory definition {name:?}"))]
    DuplicateDefinition {
        /// Repeated public name.
        name: String,
    },
    /// A parameter or binder repeats a name in its own binding group.
    #[snafu(display("duplicate theory binder {name:?}"))]
    DuplicateBinder {
        /// Repeated lexical name.
        name: String,
    },
    /// Checked construction rejected the elaborated syntax.
    #[snafu(display("checked theory construction failed: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

impl From<KernelError> for TheoryError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SExpr<'a> {
    Atom(&'a str),
    List(Vec<Self>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Token<'a> {
    Open,
    Close,
    Atom(&'a str),
}

/// Compiles a module of open, checked definition schemata.
///
/// The initial grammar is intentionally small:
///
/// ```text
/// declaration := (define name ('type-parameter ...) term)
/// type        := bool | 'type-parameter | (-> type type)
/// term        := true | false | name | (term term ...)
///              | (not term) | (and term term) | (or term term)
///              | (imp term term) | (= term term)
///              | (exists name type term) | (forall name type term)
///              | (ty.exists 'name term) | (ty.forall 'name term)
/// ```
///
/// Type parameters are scoped free type variables, not implicit assertions.
/// Thus `(define P ('a) body)` names the open schema `body['a]`; it does not
/// silently assert `∀type 'a. body`. Term and type quantifiers provide explicit
/// binding when that is intended.
///
/// # Errors
///
/// Returns an error for malformed or excessively nested S-expressions,
/// duplicate or unresolved names, an expression used in the wrong syntactic
/// position, or any term rejected by the checked kernel constructors.
pub fn compile_theory(source: &str) -> Result<CompiledTheory, TheoryError> {
    let forms = read(source)?;
    let mut compiler = Compiler::new()?;
    for form in &forms {
        compiler.declaration(form)?;
    }
    Ok(CompiledTheory {
        kernel: compiler.kernel,
        definitions: compiler.definitions,
        symbols: compiler.symbols,
    })
}

fn read(input: &str) -> Result<Vec<SExpr<'_>>, TheoryError> {
    const MAX_DEPTH: usize = 256;

    let mut rest = input;
    let tokens: Vec<Token<'_>> =
        repeat(0.., token)
            .parse_next(&mut rest)
            .map_err(|error| TheoryError::Read {
                message: error.to_string(),
            })?;
    trivia(&mut rest);
    if !rest.is_empty() {
        return Err(TheoryError::Read {
            message: format!("unexpected input at {rest:?}"),
        });
    }

    let mut roots = Vec::new();
    let mut stack: Vec<Vec<SExpr<'_>>> = Vec::new();
    for item in tokens {
        match item {
            Token::Open => {
                if stack.len() == MAX_DEPTH {
                    return Err(TheoryError::Read {
                        message: format!("nesting exceeds {MAX_DEPTH}"),
                    });
                }
                stack.push(Vec::new());
            }
            Token::Close => {
                let list = stack.pop().ok_or_else(|| TheoryError::Read {
                    message: "unexpected )".to_owned(),
                })?;
                push_expr(&mut roots, &mut stack, SExpr::List(list));
            }
            Token::Atom(atom) => push_expr(&mut roots, &mut stack, SExpr::Atom(atom)),
        }
    }
    if stack.is_empty() {
        Ok(roots)
    } else {
        Err(TheoryError::Read {
            message: "unterminated list".to_owned(),
        })
    }
}

fn push_expr<'a>(roots: &mut Vec<SExpr<'a>>, stack: &mut [Vec<SExpr<'a>>], value: SExpr<'a>) {
    match stack.last_mut() {
        Some(parent) => parent.push(value),
        None => roots.push(value),
    }
}

fn token<'a>(input: &mut &'a str) -> covalence_lib_parse::winnow::ModalResult<Token<'a>> {
    trivia(input);
    alt((
        '('.value(Token::Open),
        ')'.value(Token::Close),
        take_while(1.., |character: char| {
            !character.is_whitespace() && !matches!(character, '(' | ')')
        })
        .map(Token::Atom),
    ))
    .parse_next(input)
}

fn trivia(input: &mut &str) {
    loop {
        *input = input.trim_start_matches(char::is_whitespace);
        let Some(comment) = input.strip_prefix(';') else {
            return;
        };
        *input = comment
            .find('\n')
            .map_or("", |newline| &comment[newline + 1..]);
    }
}

struct Compiler {
    kernel: Kernel,
    star: Ref,
    bool_ty: Ref,
    definitions: BTreeMap<String, Ref>,
    symbols: BTreeMap<String, Ref>,
    arrows: BTreeMap<(Ref, Ref), Ref>,
    next_name: u64,
}

impl Compiler {
    fn new() -> Result<Self, TheoryError> {
        let mut kernel = Kernel::new();
        let star = kernel.star()?;
        let bool_ty = kernel.bool_ty(star)?;
        Ok(Self {
            kernel,
            star,
            bool_ty,
            definitions: BTreeMap::new(),
            symbols: BTreeMap::new(),
            arrows: BTreeMap::new(),
            next_name: 0,
        })
    }

    fn declaration(&mut self, form: &SExpr<'_>) -> Result<(), TheoryError> {
        let items = list(form, "a define form")?;
        if items.len() != 4 || atom(&items[0])? != "define" {
            return invalid("expected (define name ('type ...) term)");
        }
        let name = atom(&items[1])?;
        if name.contains('/') {
            return invalid("definition names cannot contain /");
        }
        if self.definitions.contains_key(name) {
            return Err(TheoryError::DuplicateDefinition {
                name: name.to_owned(),
            });
        }

        let mut types = BTreeMap::new();
        for parameter in list(&items[2], "a type-parameter list")? {
            let parameter = atom(parameter)?;
            if !parameter.starts_with('\'') || parameter.len() == 1 || parameter.contains('/') {
                return invalid("type parameters must begin with ' and cannot contain /");
            }
            if types.contains_key(parameter) {
                return Err(TheoryError::DuplicateBinder {
                    name: parameter.to_owned(),
                });
            }
            let numeric_name = self.name();
            let reference = self.kernel.ty_fv(numeric_name, self.star)?;
            types.insert(parameter.to_owned(), reference);
        }

        let root = self.term(&items[3], &types, &BTreeMap::new())?;
        self.definitions.insert(name.to_owned(), root);
        self.symbols.insert(name.to_owned(), root);
        for (parameter, reference) in types {
            self.symbols
                .insert(format!("{name}/{parameter}"), reference);
        }
        Ok(())
    }

    fn ty(
        &mut self,
        expression: &SExpr<'_>,
        types: &BTreeMap<String, Ref>,
    ) -> Result<Ref, TheoryError> {
        match expression {
            SExpr::Atom("bool") => Ok(self.bool_ty),
            SExpr::Atom(name) => types
                .get(*name)
                .copied()
                .ok_or_else(|| TheoryError::Unknown {
                    name: (*name).to_owned(),
                }),
            SExpr::List(items)
                if items.len() == 3 && matches!(items.first(), Some(SExpr::Atom("->"))) =>
            {
                let domain = self.ty(&items[1], types)?;
                let codomain = self.ty(&items[2], types)?;
                self.arrow(domain, codomain)
            }
            SExpr::List(_) => invalid("expected a type"),
        }
    }

    fn term(
        &mut self,
        expression: &SExpr<'_>,
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
    ) -> Result<Ref, TheoryError> {
        match expression {
            SExpr::Atom("true") => Ok(self.kernel.bool(self.bool_ty, true)?),
            SExpr::Atom("false") => Ok(self.kernel.bool(self.bool_ty, false)?),
            SExpr::Atom(name) => terms
                .get(*name)
                .or_else(|| self.definitions.get(*name))
                .copied()
                .ok_or_else(|| TheoryError::Unknown {
                    name: (*name).to_owned(),
                }),
            SExpr::List(items) => self.application(items, types, terms),
        }
    }

    fn application(
        &mut self,
        items: &[SExpr<'_>],
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
    ) -> Result<Ref, TheoryError> {
        let Some(head) = items.first() else {
            return invalid("the empty list is not a term");
        };
        if let SExpr::Atom(operator) = head {
            match *operator {
                "not" => return self.unary(items, types, terms, Self::not),
                "and" => return self.binary(items, types, terms, Self::and),
                "or" => return self.binary(items, types, terms, Self::or),
                "imp" => return self.binary(items, types, terms, Self::imp),
                "=" => return self.binary(items, types, terms, Self::equal),
                "exists" => return self.quantifier(items, types, terms, false),
                "forall" => return self.quantifier(items, types, terms, true),
                "ty.exists" => return self.type_quantifier(items, types, terms, false),
                "ty.forall" => return self.type_quantifier(items, types, terms, true),
                "->" | "define" => return invalid("type syntax appears in term position"),
                _ => {}
            }
        }

        let mut function = self.term(head, types, terms)?;
        for argument in &items[1..] {
            let argument = self.term(argument, types, terms)?;
            function = self.kernel.app(function, argument)?;
        }
        Ok(function)
    }

    fn unary(
        &mut self,
        items: &[SExpr<'_>],
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
        operation: fn(&mut Self, Ref) -> Result<Ref, TheoryError>,
    ) -> Result<Ref, TheoryError> {
        if items.len() != 2 {
            return invalid("unary operator expects one argument");
        }
        let value = self.term(&items[1], types, terms)?;
        operation(self, value)
    }

    fn binary(
        &mut self,
        items: &[SExpr<'_>],
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
        operation: fn(&mut Self, Ref, Ref) -> Result<Ref, TheoryError>,
    ) -> Result<Ref, TheoryError> {
        if items.len() != 3 {
            return invalid("binary operator expects two arguments");
        }
        let left = self.term(&items[1], types, terms)?;
        let right = self.term(&items[2], types, terms)?;
        operation(self, left, right)
    }

    fn quantifier(
        &mut self,
        items: &[SExpr<'_>],
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
        universal: bool,
    ) -> Result<Ref, TheoryError> {
        if items.len() != 4 {
            return invalid("term quantifier expects a name, type, and body");
        }
        let name = atom(&items[1])?;
        if terms.contains_key(name) {
            return Err(TheoryError::DuplicateBinder {
                name: name.to_owned(),
            });
        }
        let ty = self.ty(&items[2], types)?;
        let numeric_name = self.name();
        let binder = self.kernel.tm_fv(numeric_name, ty)?;
        let mut nested = terms.clone();
        nested.insert(name.to_owned(), binder);
        let body = self.term(&items[3], types, &nested)?;
        if universal {
            Ok(self.kernel.forall_tm(self.bool_ty, binder, body)?)
        } else {
            Ok(self.kernel.exists_tm(binder, body)?)
        }
    }

    fn type_quantifier(
        &mut self,
        items: &[SExpr<'_>],
        types: &BTreeMap<String, Ref>,
        terms: &BTreeMap<String, Ref>,
        universal: bool,
    ) -> Result<Ref, TheoryError> {
        if items.len() != 3 {
            return invalid("type quantifier expects a name and body");
        }
        let name = atom(&items[1])?;
        if !name.starts_with('\'') || name.len() == 1 {
            return invalid("type binders must begin with '");
        }
        if types.contains_key(name) {
            return Err(TheoryError::DuplicateBinder {
                name: name.to_owned(),
            });
        }
        let numeric_name = self.name();
        let binder = self.kernel.ty_fv(numeric_name, self.star)?;
        let mut nested = types.clone();
        nested.insert(name.to_owned(), binder);
        let body = self.term(&items[2], &nested, terms)?;
        if universal {
            Ok(self.kernel.ty_forall(numeric_name, body)?)
        } else {
            Ok(self.kernel.ty_exists(numeric_name, body)?)
        }
    }

    fn not(&mut self, value: Ref) -> Result<Ref, TheoryError> {
        Ok(self.kernel.not_tm(self.bool_ty, value)?)
    }

    fn and(&mut self, left: Ref, right: Ref) -> Result<Ref, TheoryError> {
        let binder = self.logical_binder()?;
        Ok(self.kernel.and_tm(self.bool_ty, binder, left, right)?)
    }

    fn or(&mut self, left: Ref, right: Ref) -> Result<Ref, TheoryError> {
        let binder = self.logical_binder()?;
        Ok(self.kernel.or_tm(self.bool_ty, binder, left, right)?)
    }

    fn imp(&mut self, left: Ref, right: Ref) -> Result<Ref, TheoryError> {
        let binder = self.logical_binder()?;
        Ok(self.kernel.imp_tm(self.bool_ty, binder, left, right)?)
    }

    fn equal(&mut self, left: Ref, right: Ref) -> Result<Ref, TheoryError> {
        Ok(self.kernel.eq(self.bool_ty, left, right)?)
    }

    fn logical_binder(&mut self) -> Result<Ref, TheoryError> {
        let unary = self.arrow(self.bool_ty, self.bool_ty)?;
        let binary = self.arrow(self.bool_ty, unary)?;
        let numeric_name = self.name();
        Ok(self.kernel.tm_fv(numeric_name, binary)?)
    }

    fn arrow(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, TheoryError> {
        if let Some(reference) = self.arrows.get(&(domain, codomain)) {
            return Ok(*reference);
        }
        let reference = self.kernel.ty_arr(domain, codomain)?;
        self.arrows.insert((domain, codomain), reference);
        Ok(reference)
    }

    fn name(&mut self) -> u64 {
        let name = self.next_name;
        self.next_name = self
            .next_name
            .checked_add(1)
            .expect("a finite arena cannot exhaust u64 binder names");
        name
    }
}

fn list<'a>(expression: &'a SExpr<'_>, expected: &str) -> Result<&'a [SExpr<'a>], TheoryError> {
    match expression {
        SExpr::List(items) => Ok(items),
        SExpr::Atom(_) => invalid(format!("expected {expected}")),
    }
}

fn atom<'a>(expression: &'a SExpr<'_>) -> Result<&'a str, TheoryError> {
    match expression {
        SExpr::Atom(value) => Ok(value),
        SExpr::List(_) => invalid("expected a name"),
    }
}

fn invalid<T>(message: impl Into<String>) -> Result<T, TheoryError> {
    Err(TheoryError::Invalid {
        message: message.into(),
    })
}
