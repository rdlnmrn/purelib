module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
public import Purelib.RootIsolation.Isolation.Coprime.UniformResidual
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.RationalFunctions.Residual.Local.Bounds
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Local.Basic
namespace LocalQuotientContext

variable {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

/-! ## Constructed epsilon residual states and pole blow-up -/

open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Refine the protected winding-one state to a uniformly small quotient-residual box.

The request epsilon is positive. The polynomial residual threshold is the retained positive opposite margin times
epsilon squared, preserving the original source track. -/
def epsilonResidualState
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) :
    State.WindingOne.Basic.WindingOneState source ambient :=
  Isolation.Coprime.UniformResidual.uniformlySmallState context.track
    context.protectedState (context.oppositeMargin * epsilon ^ 2)
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct context.oppositeMargin_pos
      (Rat.Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2))

open Purelib.Data in
open Purelib.RationalFunctions in
/-- The epsilon residual state refines the context's protected box. -/
theorem epsilonResidualState_refines
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) :
    (context.epsilonResidualState epsilon epsilonPositive).box.Refines
      context.protectedState.box := by
  exact context.track.nested context.protectedState _ _

open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Every sample in the epsilon residual box has quotient quadrance strictly below epsilon squared.

Protection keeps the opposite polynomial nonzero and bounds its quadrance below, allowing cancellation of the polynomial
residual estimate. -/
theorem
  epsilonResidualState_quotientResidualSq_lt
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {epsilon : Rational} (epsilonPositive : 0 < epsilon)
    {sample : Gaussian.Basic.Canonical}
    (inside : (context.epsilonResidualState epsilon epsilonPositive).box.Contains
      sample) :
    Residual.Basic.quotientResidualSq source opposite sample < epsilon ^ 2 := by
  let state := context.epsilonResidualState epsilon epsilonPositive
  let margin := context.oppositeMargin
  have sourceSmall : Gaussian.Norm.Basic.normSq (source.eval sample) < margin * epsilon ^ 2 :=
    Isolation.Coprime.UniformResidual.uniformlySmallState_residual_lt
      context.sourceDegreePositive context.track context.protectedState
      (Rat.Fraction.Order.Arithmetic.mul_pos_direct context.oppositeMargin_pos
        (Rat.Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2)) inside
  have refines := context.epsilonResidualState_refines epsilon epsilonPositive
  have oppositeNonzero := context.oppositeNonzero refines inside
  have lower := context.oppositeLower refines inside
  have identity := context.quotientResidualSq_mul_oppositeNorm refines inside
  have scaledLower : margin * epsilon ^ 2 ≤
      Gaussian.Norm.Basic.normSq (opposite.eval sample) * epsilon ^ 2 :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lower
      (Rat.Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2).le
  have productStrict :
      Residual.Basic.quotientResidualSq source opposite sample *
          Gaussian.Norm.Basic.normSq (opposite.eval sample) <
        epsilon ^ 2 * Gaussian.Norm.Basic.normSq (opposite.eval sample) := by
    calc
      Residual.Basic.quotientResidualSq source opposite sample *
          Gaussian.Norm.Basic.normSq (opposite.eval sample) = Gaussian.Norm.Basic.normSq (source.eval
            sample) :=
        identity
      _ < margin * epsilon ^ 2 := sourceSmall
      _ ≤ Gaussian.Norm.Basic.normSq (opposite.eval sample) * epsilon ^ 2 := scaledLower
      _ = epsilon ^ 2 * Gaussian.Norm.Basic.normSq (opposite.eval sample) := by ring1
  exact Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct productStrict
    (Gaussian.Norm.Basic.normSq_pos oppositeNonzero)

open Purelib.Data in
open Purelib.RationalFunctions in
/-- The reciprocal quotient quadrance is at least the reciprocal of epsilon squared in the residual box.

Epsilon is positive and the displayed source evaluation is nonzero. The small source-over-opposite residual and
protected opposite margin yield the reciprocal lower bound. -/
theorem oppositeQuotientSq_ge_inv_epsilonSq
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {epsilon : Rational} (epsilonPositive : 0 < epsilon)
    {sample : Gaussian.Basic.Canonical}
    (inside : (context.epsilonResidualState epsilon epsilonPositive).box.Contains
      sample)
    (sourceNonzero : source.eval sample ≠ 0) :
    1 / epsilon ^ 2 ≤ Gaussian.Norm.Basic.normSq (opposite.eval sample / source.eval sample) := by
  have refines := context.epsilonResidualState_refines epsilon epsilonPositive
  have oppositeNonzero := context.oppositeNonzero refines inside
  have reciprocalSmall :=
    context.epsilonResidualState_quotientResidualSq_lt epsilonPositive inside
  have identity := context.quotientResidualSq_mul_oppositeNorm refines inside
  have sourceStrict : Gaussian.Norm.Basic.normSq (source.eval sample) <
      epsilon ^ 2 * Gaussian.Norm.Basic.normSq (opposite.eval sample) := by
    calc
      Gaussian.Norm.Basic.normSq (source.eval sample) =
          Residual.Basic.quotientResidualSq source opposite sample *
            Gaussian.Norm.Basic.normSq (opposite.eval sample) := identity.symm
      _ < epsilon ^ 2 * Gaussian.Norm.Basic.normSq (opposite.eval sample) :=
        Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct reciprocalSmall
          (Gaussian.Norm.Basic.normSq_pos oppositeNonzero)
  rw [Gaussian.Field.normSq_div _ _ sourceNonzero]
  change 1 / epsilon ^ 2 ≤
    Gaussian.Norm.Basic.normSq (opposite.eval sample) / Gaussian.Norm.Basic.normSq (source.eval
      sample)
  exact Rat.Bounds.Reciprocal.reciprocalQuotientLower (Gaussian.Norm.Basic.normSq_pos sourceNonzero) epsilonPositive
    sourceStrict

end LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic

end
