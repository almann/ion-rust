// Copyright Amazon.com, Inc. or its affiliates.

//! Provides the API for typed views of Ion data.
//!
//! Generally, this is done by narrowing views over [`Element`], but also any [`Value`], and also
//! the types that correspond to the _content_ of Ion values.  Types like `i64` and `f64` which are
//! have unambiguous representations have views (see *TBD*), but also the tagged versions of
//! _content_ types (i.e., [`SExp`], [`List`], [`Clob`], and [`Blob`]).

use crate::element::iterators::SymbolsIterator;
use crate::element::{Blob, Bytes, Clob, Element, Sequence, Value};
use crate::{IonError, IonType, Symbol};

// ----------------
// TRAITS
// ----------------

/// Represents a view of some Ion data that may have annotations.
///
/// A view of data containing no annotations are simply *empty*.
pub trait Annotated {
    fn annotations(&self) -> SymbolsIterator<'_>;
    fn has_annotation(&self, annotation: &str) -> bool;
}

// XXX all view types allow fallible conversion from Element and infallible conversion to Element

// XXX does not have `Into<X> for all the various value/content because this is a potentially destructive
//     and I think being explicit with into_xxx is a bit better and attached to the view for this

/// Root view of Ion data that is supported by all views.
pub trait View: Annotated + Into<Element> + TryFrom<Element> {
    type Content;

    fn ion_type(&self) -> IonType;

    /// Consumes the view into its annotations and content.
    fn into_components(self) -> (Vec<Symbol>, Self::Content);

    // XXX into_value is not Into<Value> because it is lossy

    /// Consumes the view into its constituent [`Value`] dropping the underlying annotations, if any.
    fn into_value(self) -> Value;
}

/// View of a `null` Ion value.
///
/// This is essentially a marker trait for all `null.*` values in Ion.
///
/// All `null` Ion values can be narrowed to this type, and the other Ion views are restricted to
/// non-null views.  For APIs requiring null-ability, this is better modeled with [`Option`],
/// unless there is some meaningful content within the null (e.g., annotations), in these cases
/// you should prefer an generic enum over `NullView` and the value view.
pub trait NullView: View {}

/// View of a non-null `bool`.
pub trait BoolView: View + From<bool> {
    fn as_bool(&self) -> bool;

    // XXX I don't think into_xxx is needed for copy capable primitives
}

// TODO fill in the other scalars

/// View of a non-null `clob` or `blob`.
pub trait BytesView: View + From<Bytes> + From<Clob> + From<Blob> + From<Vec<u8>> {
    fn as_bytes(&self) -> &Bytes;

    /// Consumes this view into [`Bytes`] dropping the underlying annotations, if any.
    fn into_bytes(self) -> Bytes;
}

/// View of a non-null `clob`.  A marker trait for a specific type of [`BytesView`].
pub trait ClobView: BytesView {
    /// Consumes this view into [`Clob`] dropping the underlying annotations, if any.
    fn into_clob(self) -> Clob;
}

/// View of a non-null `clob`.  A marker trait for a specific type of [`BytesView`].
pub trait BlobView: BytesView + From<Bytes> {
    /// Consumes this view into [`Blob`] dropping the underlying annotations, if any.
    fn into_blob(self) -> Blob;
}

/// View of a non-null `list` or `sexp`.
pub trait ElementsView: View {
    // XXX I think we should call `Sequence` -> `Elements`
    fn as_elements(&self) -> Sequence;

    /// Consumes this view into [`Sequence`] dropping the underlying annotations, if any.
    fn into_elements(self) -> Sequence;
}

/// View of a non-null `list`.  A marker trait for a specific type of [`ElementsView`].
pub trait ListView: ElementsView {}

/// View of a non-null `sexp`.  A marker trait for a specific type of [`ElementsView`].
pub trait SExpView: ElementsView {}

// TODO fill in struct

// ----------------
// IMPLEMENTATION
// ----------------

// XXX Just Clob for now to show an example
// XXX I would love to make this internal and type alias impl ClobView when externalized, but nightly...

/// Concrete implementation of [`ClobView`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClobElement {
    annotations: Vec<Symbol>,
    bytes: Bytes,
}

impl ClobElement {
    pub fn new(annotations: Vec<Symbol>, bytes: Bytes) -> Self {
        Self { annotations, bytes }
    }

    pub fn from(bytes: Bytes) -> Self {
        Self::new(vec![], bytes)
    }
}

impl Annotated for ClobElement {
    fn annotations(&self) -> SymbolsIterator<'_> {
        SymbolsIterator::new(&self.annotations)
    }

    fn has_annotation(&self, annotation: &str) -> bool {
        self.annotations
            .iter()
            .any(|a| a.text() == Some(annotation))
    }
}

impl View for ClobElement {
    type Content = Bytes;

    fn ion_type(&self) -> IonType {
        IonType::Clob
    }

    fn into_components(self) -> (Vec<Symbol>, Self::Content) {
        (self.annotations, self.bytes)
    }

    fn into_value(self) -> Value {
        Value::Clob(self.bytes)
    }
}

impl BytesView for ClobElement {
    fn as_bytes(&self) -> &Bytes {
        &self.bytes
    }

    fn into_bytes(self) -> Bytes {
        self.bytes
    }
}

impl ClobView for ClobElement {
    fn into_clob(self) -> Clob {
        Clob(self.bytes)
    }
}

impl TryFrom<Element> for ClobElement {
    type Error = IonError;

    fn try_from(element: Element) -> Result<Self, Self::Error> {
        element.try_into_clob_view()
    }
}

impl From<Bytes> for ClobElement {
    fn from(bytes: Bytes) -> Self {
        ClobElement::from(bytes)
    }
}

impl From<Clob> for ClobElement {
    fn from(clob: Clob) -> Self {
        ClobElement::from(clob.0)
    }
}

impl From<Blob> for ClobElement {
    fn from(blob: Blob) -> Self {
        ClobElement::from(blob.0)
    }
}

impl From<Vec<u8>> for ClobElement {
    fn from(bytes: Vec<u8>) -> Self {
        ClobElement::from(bytes.into())
    }
}

// TODO implement all the other relevant traits...
