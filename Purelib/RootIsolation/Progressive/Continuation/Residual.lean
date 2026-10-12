module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Winding.Box.Residual
public import Purelib.RootIsolation.Progressive.Continuation.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- The displayed anchor of every owner is a coefficient-computed residual
sample.  Nonzero winding, rather than an assumed root point, supplies the
bound. -/
theorem anchorResidual_le
    {initialTable : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (state : continuation.State) (index : continuation.Index) :
    Data.Gaussian.Norm.Basic.normSq
        ((continuation.table state).polynomial.eval
          (continuation.box state index).anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound
        (continuation.table state).polynomial
        (continuation.box continuation.initial index)
        (continuation.box state index) := by
  apply Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    (continuation.table state).polynomial
    (continuation.polynomialDegreePositive state)
    (continuation.refinesInitial state index)
    (continuation.proper state index)
  intro zero
  rw [continuation.rawWindingFour state index] at zero
  exact (show (4 : Int) ≠ 0 by decide) zero
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- After a request, every owner anchor has residual quadrance at most its
finite Horner-Lipschitz coefficient times the requested squared radius. -/
theorem refinedAnchorResidual_le_requested
    {initialTable : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (state : continuation.State) (index : continuation.Index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    let next := continuation.refine state epsilon positive
    Data.Gaussian.Norm.Basic.normSq
        ((continuation.table next).polynomial.eval
          (continuation.box next index).anchor) ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound
          (continuation.table next).polynomial
          (continuation.box continuation.initial index) * epsilon ^ 2 := by
  let next := continuation.refine state epsilon positive
  have residual := continuation.anchorResidual_le next index
  exact residual.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (continuation.accurate state epsilon positive index)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos
        (continuation.table next).polynomial
        (continuation.box continuation.initial index)).le)
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end
