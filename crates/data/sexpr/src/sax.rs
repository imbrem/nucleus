//! Streaming construction and emission of untagged S-expressions.
//!
//! The interfaces in this module deliberately separate syntax from data
//! models. A parser produces [`Event`]s, [`FromEvents`] constructs a value from
//! them, and [`ToEvents`] emits a value without first allocating an [`SExpr`].

use std::convert::Infallible;
use std::fmt;

use crate::{SExpr, SNode, SView, Symbol};

/// One event in a depth-first S-expression stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Event<A = Symbol> {
    /// Begin a list.
    ListStart,
    /// An atom.
    Atom(A),
    /// End the most recently opened list.
    ListEnd,
}

impl<A> Event<A> {
    /// Maps the atom while preserving structural events.
    pub fn map<B>(self, map: impl FnOnce(A) -> B) -> Event<B> {
        match self {
            Self::ListStart => Event::ListStart,
            Self::Atom(atom) => Event::Atom(map(atom)),
            Self::ListEnd => Event::ListEnd,
        }
    }

    /// Borrows this event's atom.
    #[must_use]
    pub const fn as_ref(&self) -> Event<&A> {
        match self {
            Self::ListStart => Event::ListStart,
            Self::Atom(atom) => Event::Atom(atom),
            Self::ListEnd => Event::ListEnd,
        }
    }
}

/// A fallible destination for borrowed SAX events.
///
/// Implementations can write a wire format, feed another state machine, or
/// simply collect events for testing.
pub trait EventWriter<A: ?Sized = Symbol> {
    /// The write error.
    type Error;

    /// Accepts one event.
    ///
    /// # Errors
    ///
    /// Returns the destination's error if it cannot accept the event.
    fn write(&mut self, event: Event<&A>) -> Result<(), Self::Error>;
}

impl<A: ?Sized, F, E> EventWriter<A> for F
where
    F: FnMut(Event<&A>) -> Result<(), E>,
{
    type Error = E;

    fn write(&mut self, event: Event<&A>) -> Result<(), E> {
        self(event)
    }
}

/// A value that can emit its S-expression representation as SAX events.
pub trait ToEvents {
    /// The atom representation borrowed during emission.
    type Atom: ?Sized;

    /// Emits a complete, balanced expression.
    ///
    /// # Errors
    ///
    /// Returns the writer's error and stops emitting.
    fn write_events<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: EventWriter<Self::Atom>;
}

impl<A> ToEvents for SExpr<A> {
    type Atom = A;

    fn write_events<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: EventWriter<A>,
    {
        write_view(self, writer)
    }
}

/// Emits any structural view in depth-first order.
///
/// # Errors
///
/// Returns the writer's error and stops traversing.
pub fn write_view<V, W>(value: V, writer: &mut W) -> Result<(), W::Error>
where
    V: SView,
    W: EventWriter<V::Atom>,
{
    match value.view() {
        SNode::Atom(atom) => writer.write(Event::Atom(atom)),
        SNode::List(children) => {
            writer.write(Event::ListStart)?;
            for child in children {
                write_view(child, writer)?;
            }
            writer.write(Event::ListEnd)
        }
    }
}

/// A type constructible from one complete SAX expression.
///
/// Implementations own validation and resource policy. In particular, a
/// domain type need not construct an [`SExpr`] first.
pub trait FromEvents<A = Symbol>: Sized {
    /// The construction error.
    type Error;

    /// Consumes exactly one complete expression.
    ///
    /// # Errors
    ///
    /// Returns an implementation-defined validation or construction error.
    fn from_events(events: impl IntoIterator<Item = Event<A>>) -> Result<Self, Self::Error>;
}

/// Structural errors while constructing an owned [`SExpr`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// The stream contained no expression.
    Empty,
    /// The stream contained more than one top-level expression.
    MultipleRoots,
    /// A list end had no matching list start.
    UnexpectedListEnd,
    /// The stream ended with one or more open lists.
    UnclosedList,
}

impl fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::Empty => "event stream contains no expression",
            Self::MultipleRoots => "event stream contains multiple top-level expressions",
            Self::UnexpectedListEnd => "list end has no matching list start",
            Self::UnclosedList => "event stream ends inside a list",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for BuildError {}

impl<A> FromEvents<A> for SExpr<A> {
    type Error = BuildError;

    fn from_events(events: impl IntoIterator<Item = Event<A>>) -> Result<Self, Self::Error> {
        let mut stack: Vec<Vec<Self>> = Vec::new();
        let mut root = None;

        for event in events {
            let completed = match event {
                Event::ListStart => {
                    stack.push(Vec::new());
                    continue;
                }
                Event::Atom(atom) => Self::Atom(atom),
                Event::ListEnd => {
                    let children = stack.pop().ok_or(BuildError::UnexpectedListEnd)?;
                    Self::List(children)
                }
            };

            if let Some(parent) = stack.last_mut() {
                parent.push(completed);
            } else if root.replace(completed).is_some() {
                return Err(BuildError::MultipleRoots);
            }
        }

        if !stack.is_empty() {
            return Err(BuildError::UnclosedList);
        }
        root.ok_or(BuildError::Empty)
    }
}

/// Collects emitted atoms by cloning them.
///
/// This is useful at ownership boundaries and in tests; streaming consumers
/// should implement [`EventWriter`] directly.
pub fn collect_events<T>(value: &T) -> Vec<Event<T::Atom>>
where
    T: ToEvents,
    T::Atom: Clone + Sized,
{
    let mut events = Vec::new();
    let mut writer = |event: Event<&T::Atom>| -> Result<(), Infallible> {
        events.push(event.map(Clone::clone));
        Ok(())
    };
    match value.write_events(&mut writer) {
        Ok(()) => events,
        Err(error) => match error {},
    }
}

#[cfg(test)]
mod tests {
    use super::{BuildError, Event, FromEvents, collect_events};
    use crate::SExpr;

    #[test]
    fn owned_tree_round_trips_through_events() {
        let expression = SExpr::list(vec![
            SExpr::atom(String::from("a")),
            SExpr::list(vec![]),
            SExpr::atom(String::from("b")),
        ]);
        let events = collect_events(&expression);
        assert_eq!(SExpr::from_events(events), Ok(expression));
    }

    #[test]
    fn builder_rejects_invalid_structure() {
        assert_eq!(SExpr::<String>::from_events([]), Err(BuildError::Empty));
        assert_eq!(
            SExpr::<String>::from_events([Event::ListEnd]),
            Err(BuildError::UnexpectedListEnd)
        );
        assert_eq!(
            SExpr::from_events([Event::Atom("a"), Event::Atom("b")]),
            Err(BuildError::MultipleRoots)
        );
        assert_eq!(
            SExpr::<String>::from_events([Event::ListStart]),
            Err(BuildError::UnclosedList)
        );
    }
}
