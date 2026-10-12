module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Inverse
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Rational.Geometric.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Equivalence

/-- Finite-request statement of `d log(1+u)/du = 1/(1+u)`. The right side is an exact Gaussian rational for this
displayed rational input; every requested positive squared tolerance is met by a computed finite truncation index on the
left. -/
def log1p_derivative_equivalent_inverse
  (u : Data.Gaussian.Basic.Canonical)
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) :
    Gaussian.Equivalence.Equivalent (Sequence.log1pDerivativeApproximation u disk)
      (Constant.constantApproximation
        ((1 + u)⁻¹)) where
  compare := by
    intro leftStart rightStart target positive
    let index := (Sequence.log1pDerivativeApproximation u disk).refineIndex
      leftStart target positive
    have radiusSmall :
        Geometric.Basic.quarterRadius 1 index < target :=
      (Sequence.log1pDerivativeApproximation u disk).refineIndex_accurate
        leftStart target positive
    exact
      { leftIndex := index
        rightIndex := rightStart
        left_ge := (Sequence.log1pDerivativeApproximation u disk).refineIndex_ge
          leftStart target positive
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change Data.Gaussian.Norm.Basic.normSq
              (Sample.log1pDerivativeSample u leftLater - (1 + u)⁻¹) < target
          exact (Inverse.log1pDerivative_sub_inverse_bound disk leftLater).trans_lt
            ((quarterRadius_antitone (by
                decide : (0 : Fraction.Rational) ≤ 1) leftOrder).trans_lt radiusSmall) }
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Equivalence

end
