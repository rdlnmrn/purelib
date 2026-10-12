module

public import Purelib.Approximation.Rational.QuadraticTarget.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Nat.SquareThreshold.Basic
public import Purelib.Data.Nat.SquareThreshold.Resource
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Approximation.Rational

open Purelib.Data.Nat

open Purelib.Data.Nat.SquareThreshold

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Approximation.Rational.QuadraticTarget.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Ceiling supplied to the residual-target square scan. -/
def targetCeiling (coefficient target :
  Fraction.Rational) : Nat :=
  Floor.ceilNat (coefficient / target)
end Purelib.Approximation.Rational.QuadraticTarget.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Approximation.Rational.QuadraticTarget.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The explicit comparison budget for the target's square-threshold computation.

The budget is evaluated at the same rational-ceiling input used by the requested denominator. -/
def targetComparisonBudget (coefficient target :
  Fraction.Rational) : Nat :=
  Resource.squareThresholdComparisonBudget (targetCeiling coefficient
    target)
end Purelib.Approximation.Rational.QuadraticTarget.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Approximation.Rational.QuadraticTarget.Resource
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The target denominator has the exact predecessor/successor square bracket advertised in the paper. -/
theorem targetDenominator_bracket (coefficient target :
  Fraction.Rational) :
    let input := targetCeiling coefficient target
    let output := QuadraticTarget.Basic.targetDenominator coefficient target
    (output - 1) * (output - 1) ≤ input ∧ input < output * output := by
  dsimp only [targetCeiling, QuadraticTarget.Basic.targetDenominator]
  exact ⟨Resource.squareThreshold_predecessor_sq_le _,
    SquareThreshold.Basic.squareThreshold_spec _⟩
end Purelib.Approximation.Rational.QuadraticTarget.Resource

end
