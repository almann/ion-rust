// Copyright Amazon.com, Inc. or its affiliates.

//! Provides simple support for controlling lazy/strict evaluation.
//! See [`Thunk`] for details.

// TODO consider if this should be in a more general place in the crate
// TODO consider making these thunks memoize to avoid the only once restriction

use crate::result::illegal_operation;
use crate::IonResult;

/// Describes the state of a [`Thunk`].
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ThunkState {
    Deferred,
    Materialized,
    Error,
}

pub type ThunkFn<'a, T> = Box<dyn FnOnce() -> IonResult<T> + 'a>;

enum ThunkVal<'a, T> {
    Deferred(ThunkFn<'a, T>),
    Materialized(T),
}

/// A simple, potentially deferred or owned value.
///
/// The thunk can be in one of three states:
/// * [**Deferred**](ThunkState::Deferred): The value has not yet been evaluated.
/// * [**Materialize**](ThunkState::Materialized): The value has been evaluated and is owned.
/// * [**Error**](ThunkState::Error): The value can never be materialized.
///   This can happen when [`Thunk::memoize`] is used to *attempt* to materialize a deferred
///   value in place.
pub struct Thunk<'a, T>(IonResult<ThunkVal<'a, T>>);

impl<'a, T> Thunk<'a, T> {
    #[inline]
    pub fn wrap(value: T) -> Thunk<'static, T> {
        Thunk(Ok(ThunkVal::Materialized(value)))
    }

    #[inline]
    pub fn defer<F>(closure: F) -> Thunk<'a, T>
    where
        F: FnOnce() -> IonResult<T> + 'a,
    {
        Thunk(Ok(ThunkVal::Deferred(Box::new(closure))))
    }

    /// Evaluates the thunk, consuming it and returning the underlying value.
    pub fn evaluate(self) -> IonResult<T> {
        use ThunkVal::*;
        match self.0 {
            Ok(Deferred(func)) => func(),
            Ok(Materialized(value)) => Ok(value),
            Err(e) => Err(e),
        }
    }

    /// Evaluates the deferred value and returns it as a thunk.
    pub fn materialize(self) -> IonResult<Thunk<'static, T>> {
        use ThunkVal::*;
        match self.0 {
            Ok(Deferred(func)) => {
                let value = func()?;
                Ok(Thunk::wrap(value))
            }
            Ok(Materialized(value)) => Ok(Thunk::wrap(value)),
            Err(e) => Err(e),
        }
    }

    /// Evaluates in place and replaces deferred value with a materialized one.
    ///
    /// If the underlying deferred value is an error, the state of the thunk is in error.
    /// An error state can be thought of as a deferred value that will never happen.
    pub fn memoize(&mut self) -> IonResult<&T> {
        use ThunkVal::*;
        let value_res = self.remove();
        // move in the new, materialized value
        match value_res {
            Ok(val) => self.0 = Ok(Materialized(val)),
            Err(e) => self.0 = Err(e),
        };
        // at this point we can now return a reference to our internal materialized value
        // or the error
        match &self.0 {
            Ok(Deferred(_)) => {
                // XXX should not be possible
                panic!("Thunk memoization is still deferred")
            }
            Ok(Materialized(val_ref)) => Ok(val_ref),
            Err(e) => Err(e.clone()),
        }
    }

    /// Evaluates and removes the current value replacing it with an [**Error**](ThunkState::Error).
    /// state.
    pub fn remove(&mut self) -> IonResult<T> {
        use ThunkVal::*;
        // move out the current value
        let thunk_res = std::mem::replace(&mut self.0, illegal_operation("Empty thunk"));
        // attempt to evaluate (if possible/needed)
        let value_res = match thunk_res {
            Ok(Deferred(func)) => func(),
            Ok(Materialized(val)) => Ok(val),
            Err(e) => Err(e),
        };
        return value_res;
    }

    /// Evaluates and sets the current value with the given one, returning the
    /// result of evaluation that was previously in the thunk.
    ///
    /// This will make the thunk in an [**Materialized**](ThunkState::Materialized) state.
    pub fn replace(&mut self, value: T) -> IonResult<T> {
        let old_res = self.remove();
        // move in the new, materialized value
        self.0 = Ok(ThunkVal::Materialized(value));
        old_res
    }

    // TODO consider adding a deferred replace if we need it

    /// Returns the current status of the thunk.
    pub fn thunk_state(&self) -> ThunkState {
        use ThunkVal::*;
        match &self.0 {
            Ok(Deferred(_)) => ThunkState::Deferred,
            Ok(Materialized(_)) => ThunkState::Materialized,
            Err(_) => ThunkState::Error,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::IonResult;

    #[test]
    fn test_thunk_materialize() -> IonResult<()> {
        let thunk = {
            let i = 15;
            let i_ref = &i;
            let deferred = Thunk::defer(|| return Ok(*i_ref));
            assert_eq!(ThunkState::Deferred, deferred.thunk_state());
            deferred.materialize()?
        };
        assert_eq!(ThunkState::Materialized, thunk.thunk_state());
        assert_eq!(15, thunk.evaluate()?);
        Ok(())
    }

    #[test]
    fn test_thunk_memoize_value() -> IonResult<()> {
        let mut thunk = Thunk::defer(|| return Ok(5));
        assert_eq!(ThunkState::Deferred, thunk.thunk_state());
        assert_eq!(5, *thunk.memoize()?);
        assert_eq!(ThunkState::Materialized, thunk.thunk_state());
        Ok(())
    }

    #[test]
    fn test_thunk_memoize_error() -> IonResult<()> {
        let mut thunk: Thunk<i32> = Thunk::defer(|| return illegal_operation("Oops"));
        assert_eq!(ThunkState::Deferred, thunk.thunk_state());
        assert_eq!(illegal_operation("Oops"), thunk.memoize());
        assert_eq!(ThunkState::Error, thunk.thunk_state());
        Ok(())
    }

    #[test]
    fn test_thunk_remove() -> IonResult<()> {
        let mut thunk = Thunk::defer(|| return Ok(999));
        assert_eq!(ThunkState::Deferred, thunk.thunk_state());
        assert_eq!(999, thunk.remove()?);
        assert_eq!(ThunkState::Error, thunk.thunk_state());
        assert_eq!(illegal_operation("Empty thunk"), thunk.evaluate());
        Ok(())
    }

    #[test]
    fn test_thunk_replace() -> IonResult<()> {
        let mut thunk = Thunk::defer(|| return Ok(1024));
        assert_eq!(ThunkState::Deferred, thunk.thunk_state());
        assert_eq!(1024, thunk.replace(99)?);
        assert_eq!(ThunkState::Materialized, thunk.thunk_state());
        assert_eq!(99, thunk.evaluate()?);
        Ok(())
    }
}
