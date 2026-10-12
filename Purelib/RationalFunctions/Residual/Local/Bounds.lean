module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Residual.Basic
import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.RootIsolation.Isolation.Coprime.Protection
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Winding.Bounds.Residual
public import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Local.Basic.LocalQuotientContext
section LocalQuotientContext

variable {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

section
open Purelib.Data
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Inside a refinement of the protected state, opposite-polynomial quadrance is at least the retained margin.

The sample lies in the refined winding-one state's box. Refinement transports membership back to the
coprimality-protected source box. -/
theorem oppositeLower
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    context.oppositeMargin ≤ Gaussian.Norm.Basic.normSq (opposite.eval sample) := by
  exact Isolation.Coprime.Protection.protectedState_right_lower
    context.sourceDegreePositive context.coprime context.track context.current
    (refinesProtected.contains inside)

/-- The opposite polynomial is nonzero at every sample inside a refinement of the protected state. -/
theorem oppositeNonzero
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    opposite.eval sample ≠ 0 := by
  intro evaluationZero
  have lower := context.oppositeLower refinesProtected inside
  rw [evaluationZero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower context.oppositeMargin_pos).elim

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Every sample in a source state has opposite-polynomial quadrance at most the ambient majorant. -/
theorem oppositeUpper
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    Gaussian.Norm.Basic.normSq (opposite.eval sample) ≤ context.oppositeMajorant :=
  Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant opposite
    (state.refinesAmbient.contains inside)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- A protected sample's quotient residual is bounded by its source-box squared diagonal.

The coefficient is four times the source Lipschitz bound divided by the positive opposite margin. The state refines the
protected box, and the sample lies inside that state. -/
theorem quotientResidualSq_le_diagonal
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    Residual.Basic.quotientResidualSq source opposite sample ≤
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq) /
        context.oppositeMargin := by
  have oppositeNonzero := context.oppositeNonzero refinesProtected inside
  have lower := context.oppositeLower refinesProtected inside
  have sourceBoundRaw :=
    Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
      context.sourceDegreePositive state inside
  have sourceBound :
      Gaussian.Norm.Basic.normSq (source.eval sample) ≤
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound source ambient * state.box.diagonalSq :=
    (Gaussian.Norm.Basic.normSq_eq_canonical (source.eval sample)).trans_le sourceBoundRaw
  have inverseOrder :=
    Rat.Fraction.Order.Field.inv_le_inv_of_pos_direct
      context.oppositeMargin_pos lower
  rw [Residual.Basic.quotientResidualSq, ← Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Field.normSq_div _ _
    oppositeNonzero,
    Field.ExplicitField.div_eq_mul_inv]
  exact
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseOrder
      (Gaussian.Norm.Basic.normSq_nonneg (source.eval sample))).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourceBound
      (Rat.Fraction.Order.Field.inv_pos_direct
        context.oppositeMargin_pos).le)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Multiplying a protected quotient residual by opposite quadrance recovers source quadrance.

The protected-box refinement and sample membership establish opposite nonzeroness. Taking quadrance of exact quotient
cancellation yields the identity. -/
theorem quotientResidualSq_mul_oppositeNorm
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    Residual.Basic.quotientResidualSq source opposite sample *
        Gaussian.Norm.Basic.normSq (opposite.eval sample) = Gaussian.Norm.Basic.normSq (source.eval
          sample) := by
  have oppositeNonzero := context.oppositeNonzero refinesProtected inside
  have valueIdentity :
      (source.eval sample / opposite.eval sample) * opposite.eval sample =
        source.eval sample :=
    Field.ExplicitField.div_mul_cancel _ oppositeNonzero
  have normIdentity := congrArg Gaussian.Norm.Basic.normSq valueIdentity
  rw [Gaussian.Norm.Basic.normSq_mul] at normIdentity
  rw [Residual.Basic.quotientResidualSq, ← Gaussian.Norm.Basic.normSq_eq_canonical]
  exact normIdentity

open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- A protected sample's source residual is bounded by quotient residual times the opposite majorant.

The exact residual identity is combined with the opposite-polynomial upper bound on the ambient box. -/
theorem
  sourceResidual_le_quotientResidualSq_mul_majorant
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient)
    {state : State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian.Basic.Canonical} (inside : state.box.Contains sample) :
    Gaussian.Norm.Basic.normSq (source.eval sample) ≤
      Residual.Basic.quotientResidualSq source opposite sample * context.oppositeMajorant := by
  have identity := context.quotientResidualSq_mul_oppositeNorm
    refinesProtected inside
  have upper := context.oppositeUpper inside
  calc
    Gaussian.Norm.Basic.normSq (source.eval sample) =
        Residual.Basic.quotientResidualSq source opposite sample *
          Gaussian.Norm.Basic.normSq (opposite.eval sample) := identity.symm
    _ ≤ Residual.Basic.quotientResidualSq source opposite sample * context.oppositeMajorant :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct upper
        (Residual.Basic.quotientResidualSq_nonneg source opposite sample)
end LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic.LocalQuotientContext

end
