// Copyright Amazon.com, Inc. or its affiliates.

//! Provides simple support for controlling lazy/strict evaluation.

// TODO consider if this should be in a more general place in the crate
// TODO consider making these thunks memoize to avoid the only once restriction

use crate::IonResult;

pub type ThunkFn<'a, T> = Box<dyn FnOnce() -> IonResult<T> + 'a>;

/// A simple, consuming lazy value that optionally is an owned value which we call materialized.
pub enum Thunk<'a, T> {
    Deferred(ThunkFn<'a, T>),
    Materialized(T),
}

impl<'a, T> Thunk<'a, T> {
    #[inline]
    pub fn wrap(value: T) -> Thunk<'static, T> {
        Thunk::Materialized(value)
    }

    /// Evaluates the thunk, consuming it and returning the underlying value.
    pub fn evaluate(self) -> IonResult<T> {
        use Thunk::*;
        match self {
            Deferred(func) => func(),
            Materialized(value) => Ok(value),
        }
    }

    /// Evaluates the deferred value and returns it as a thunk.
    pub fn materialize(self) -> IonResult<Thunk<'static, T>> {
        use Thunk::*;
        match self {
            Deferred(func) => {
                let value = func()?;
                Ok(Materialized(value))
            }
            Materialized(value) => Ok(Thunk::wrap(value)),
        }
    }

    /// Convenience to determine if the thunk is materialized.
    pub fn is_materialized(&self) -> bool {
        match self {
            Thunk::Deferred(_) => false,
            Thunk::Materialized(_) => true,
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
            let func: ThunkFn<i32> = Box::new(|| return Ok(*i_ref));
            let deferred = Thunk::Deferred(func);
            assert!(!deferred.is_materialized());
            deferred.materialize()?
        };
        assert!(thunk.is_materialized());
        assert_eq!(15, thunk.evaluate()?);
        Ok(())
    }
}
