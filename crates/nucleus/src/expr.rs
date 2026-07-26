use covalence_data_sexpr::{
    SNode, SView,
    sax::{EventWriter, ToEvents, write_view},
};
use covalence_data_symbol::Symbol;
use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use covalence_neutron::BOOL_SORT_V0;
use snafu::Snafu;

/// A stable substrate sort recognized by this Nucleus build.
pub trait Sort {
    /// Stable semantic identity of the sort.
    const ID: O256;
}

/// Typed expression syntax over a finite input context.
pub trait Expr: SView {
    /// Inputs required to evaluate the expression.
    type Context;
    /// Result sort.
    type Sort: Sort;
}

/// The substrate `Bool` sort.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bool;

impl Sort for Bool {
    const ID: O256 = BOOL_SORT_V0;
}

/// The context assigning truth values to propositional variables.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PropContext;

/// A minimal proposition expression.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Prop {
    /// False.
    False,
    /// True.
    True,
    /// A variable supplied by the evaluation context.
    Var(Symbol),
    /// Negation.
    Not(Box<Self>),
    /// Conjunction.
    And(Box<Self>, Box<Self>),
    /// Disjunction.
    Or(Box<Self>, Box<Self>),
}

impl Prop {
    /// Evaluates this proposition against an explicit variable environment.
    ///
    /// # Errors
    ///
    /// Returns [`EvalError::MissingVariable`] when a referenced variable is
    /// absent. Absence is never interpreted as false.
    pub fn evaluate(
        &self,
        mut lookup: impl FnMut(&Symbol) -> Option<bool>,
    ) -> Result<bool, EvalError> {
        self.evaluate_with(&mut lookup)
    }

    fn evaluate_with(
        &self,
        lookup: &mut impl FnMut(&Symbol) -> Option<bool>,
    ) -> Result<bool, EvalError> {
        match self {
            Self::False => Ok(false),
            Self::True => Ok(true),
            Self::Var(variable) => lookup(variable).ok_or_else(|| EvalError::MissingVariable {
                variable: variable.clone(),
            }),
            Self::Not(proposition) => Ok(!proposition.evaluate_with(lookup)?),
            Self::And(left, right) => {
                let left = left.evaluate_with(lookup)?;
                let right = right.evaluate_with(lookup)?;
                Ok(left && right)
            }
            Self::Or(left, right) => {
                let left = left.evaluate_with(lookup)?;
                let right = right.evaluate_with(lookup)?;
                Ok(left || right)
            }
        }
    }
}

impl Expr for Prop {
    type Context = PropContext;
    type Sort = Bool;
}

/// Propositional evaluation failure.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum EvalError {
    /// A variable was absent from the supplied context.
    #[snafu(display("missing propositional variable `{variable}`"))]
    MissingVariable {
        /// Missing variable.
        variable: Symbol,
    },
}

#[derive(Clone, Copy)]
pub enum PropView<'a> {
    Atom(&'a str),
    Expr(&'a Prop),
}

pub struct PropChildren<'a> {
    items: [Option<PropView<'a>>; 3],
    next: usize,
}

impl<'a> PropChildren<'a> {
    const fn two(first: PropView<'a>, second: PropView<'a>) -> Self {
        Self {
            items: [Some(first), Some(second), None],
            next: 0,
        }
    }

    const fn three(first: PropView<'a>, second: PropView<'a>, third: PropView<'a>) -> Self {
        Self {
            items: [Some(first), Some(second), Some(third)],
            next: 0,
        }
    }
}

impl<'a> Iterator for PropChildren<'a> {
    type Item = PropView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.items.get(self.next).copied().flatten();
        self.next += usize::from(item.is_some());
        item
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.items[self.next..]
            .iter()
            .take_while(|item| item.is_some())
            .count();
        (remaining, Some(remaining))
    }
}

impl std::iter::FusedIterator for PropChildren<'_> {}
impl ExactSizeIterator for PropChildren<'_> {}

impl SView for Prop {
    type Atom = str;
    type Child<'a>
        = PropView<'a>
    where
        Self: 'a;
    type Children<'a>
        = PropChildren<'a>
    where
        Self: 'a;

    fn view(&self) -> SNode<&str, Self::Children<'_>> {
        match self {
            Self::False => SNode::Atom("false"),
            Self::True => SNode::Atom("true"),
            Self::Var(variable) => SNode::List(PropChildren::two(
                PropView::Atom("var"),
                PropView::Atom(variable.as_str()),
            )),
            Self::Not(proposition) => SNode::List(PropChildren::two(
                PropView::Atom("not"),
                PropView::Expr(proposition),
            )),
            Self::And(left, right) => SNode::List(PropChildren::three(
                PropView::Atom("and"),
                PropView::Expr(left),
                PropView::Expr(right),
            )),
            Self::Or(left, right) => SNode::List(PropChildren::three(
                PropView::Atom("or"),
                PropView::Expr(left),
                PropView::Expr(right),
            )),
        }
    }
}

impl SView for PropView<'_> {
    type Atom = str;
    type Child<'a>
        = PropView<'a>
    where
        Self: 'a;
    type Children<'a>
        = PropChildren<'a>
    where
        Self: 'a;

    fn view(&self) -> SNode<&str, Self::Children<'_>> {
        match self {
            Self::Atom(atom) => SNode::Atom(atom),
            Self::Expr(expression) => expression.view(),
        }
    }
}

impl ToEvents for Prop {
    type Atom = str;

    fn write_events<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: EventWriter<str>,
    {
        write_view(self, writer)
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use covalence_data_sexpr::sax::{Event, ToEvents};
    use covalence_data_symbol::Symbol;

    use super::{EvalError, Prop};

    #[test]
    fn evaluation_is_two_valued_and_missing_inputs_fail() {
        let p = Symbol::new("p");
        let q = Symbol::new("q");
        let proposition = Prop::And(
            Box::new(Prop::Var(p.clone())),
            Box::new(Prop::Not(Box::new(Prop::Var(q.clone())))),
        );
        assert_eq!(
            proposition.evaluate(|variable| match variable.as_str() {
                "p" => Some(true),
                "q" => Some(false),
                _ => None,
            }),
            Ok(true)
        );
        assert_eq!(
            Prop::Var(p.clone()).evaluate(|_| None),
            Err(EvalError::MissingVariable { variable: p })
        );
    }

    #[test]
    fn canonical_events_preserve_constructor_and_child_order() {
        let proposition = Prop::Or(Box::new(Prop::Var(Symbol::new("p"))), Box::new(Prop::False));
        let mut events = Vec::new();
        proposition
            .write_events(&mut |event: Event<&str>| -> Result<(), Infallible> {
                events.push(event.map(str::to_owned));
                Ok(())
            })
            .unwrap();
        assert_eq!(
            events,
            [
                Event::ListStart,
                Event::Atom(String::from("or")),
                Event::ListStart,
                Event::Atom(String::from("var")),
                Event::Atom(String::from("p")),
                Event::ListEnd,
                Event::Atom(String::from("false")),
                Event::ListEnd,
            ]
        );
    }
}
