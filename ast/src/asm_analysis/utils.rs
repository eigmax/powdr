use std::{iter::once, ops::ControlFlow};

use crate::parsed::{asm::FunctionCall, Expression};

/// Traverses the expression tree and calls `f` in pre-order.
pub fn previsit_expression_mut<T, F, B>(e: &mut Expression<T>, f: &mut F) -> ControlFlow<B>
where
    F: FnMut(&mut Expression<T>) -> ControlFlow<B>,
{
    f(e)?;

    match e {
        Expression::PolynomialReference(_)
        | Expression::Constant(_)
        | Expression::PublicReference(_)
        | Expression::Number(_)
        | Expression::FreeInput(_)
        | Expression::String(_) => {}
        Expression::BinaryOperation(left, _, right) => {
            previsit_expression_mut(left, f)?;
            previsit_expression_mut(right, f)?;
        }
        Expression::UnaryOperation(_, e) => previsit_expression_mut(e.as_mut(), f)?,
        Expression::Tuple(items)
        | Expression::FunctionCall(FunctionCall {
            arguments: items, ..
        }) => items
            .iter_mut()
            .try_for_each(|item| previsit_expression_mut(item, f))?,
        Expression::MatchExpression(scrutinee, arms) => {
            once(scrutinee.as_mut())
                .chain(arms.iter_mut().map(|(_n, e)| e))
                .try_for_each(move |item| previsit_expression_mut(item, f))?;
        }
    };
    ControlFlow::Continue(())
}