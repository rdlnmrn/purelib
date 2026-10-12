module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Finite sign consistency at triple overlaps

Two ordinary Newton steps make each model's residual at most `1/256`.
At a common rational point, the three uniquely selected overlap signs then
satisfy the two-sheet cocycle equation.  All values and signs are finite
data.  This does not yet assert that a sign is constant along a whole edge.
-/

namespace Purelib.Riemann.Normalization.InverseModelOverlapCocycle.SignAlignment

open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment inverse_value_ne_zero)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

variable {reference middle candidate : Gaussian}

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A Gaussian value within the reference squared norm is no farther than its negation from that reference. -/
private theorem nearest_of_distance_lt_norm {reference value : Gaussian}
    (close : normSq (reference - value) < normSq reference) :
    normSq (reference - value) ≤ normSq (reference + value) := by
  apply le_of_lt
  apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct (c := normSq (reference - value))
  calc
    _ = normSq (reference - value) * 2 := by ring1
    _ < normSq reference * 2 := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct close (by decide)
    _ ≤ 2 * (normSq reference + normSq value) :=
      (by ring1 : normSq reference * 2 = 2 * normSq reference).trans_le
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (le_add_of_nonneg_right (Basic.Canonical.normSq_nonneg _)) (by decide))
    _ = normSq (reference + value) + normSq (reference - value) := by
      simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im]
      ring1

/-- Two inverse-root residual bounds at most one two-hundred-fifty-sixth give the retained sign alignment a
three-sixty-fourths relative distance bound. -/
private theorem tight_distance (alignment : SignAlignment reference candidate)
    {parameter : Gaussian} {leftError rightError : Coordinate}
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 256) (rightSmall : rightError ≤ 1 / 256) :
    normSq (reference - alignment.value) ≤ (3 / 64 : Coordinate) * normSq reference := by
  have allowance : 6 * (leftError + rightError) ≤ (3 / 64 : Coordinate) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftSmall rightSmall)
      (by decide)).trans_eq (by decide +kernel : (6 : Coordinate) * (1 / 256 + 1 / 256) = 3 / 64)
  exact (alignment.distance_le leftResidual rightResidual (leftSmall.trans (by decide +kernel))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct allowance (Basic.Canonical.normSq_nonneg _))

/-- Compose two successive nearest-sign alignments under small inverse-root residual bounds.

The second alignment is based at the first aligned value. Its exact chosen value and flip are retained, with nearestness
to the original reference proved from the three residual bounds. -/
def composeAligned (first : SignAlignment reference middle)
    (second : SignAlignment first.value candidate)
    {parameter : Gaussian} {firstError middleError lastError : Coordinate}
    (firstResidual : normSq (1 - parameter * reference ^ 2) ≤ firstError)
    (middleResidual : normSq (1 - parameter * middle ^ 2) ≤ middleError)
    (lastResidual : normSq (1 - parameter * candidate ^ 2) ≤ lastError)
    (firstSmall : firstError ≤ 1 / 256) (middleSmall : middleError ≤ 1 / 256)
    (lastSmall : lastError ≤ 1 / 256) : SignAlignment reference candidate := by
  have tightDistance :
      ∀ {left right : Gaussian} (alignment : SignAlignment left right)
        {leftError rightError : Coordinate},
        normSq (1 - parameter * left ^ 2) ≤ leftError →
        normSq (1 - parameter * right ^ 2) ≤ rightError →
        leftError ≤ 1 / 256 → rightError ≤ 1 / 256 →
        normSq (left - alignment.value) ≤ (3 / 64 : Coordinate) * normSq left := by
    intro left right alignment leftError rightError leftResidual rightResidual leftSmall rightSmall
    have allowance : 6 * (leftError + rightError) ≤ (3 / 64 : Coordinate) :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftSmall rightSmall) (by decide)).trans_eq
          (by decide +kernel : (6 : Coordinate) * (1 / 256 + 1 / 256) = 3 / 64)
    exact (alignment.distance_le leftResidual rightResidual
      (leftSmall.trans (by decide +kernel))).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          allowance (Basic.Canonical.normSq_nonneg _))
  have firstDistance := tightDistance first firstResidual middleResidual firstSmall middleSmall
  have middleAligned : normSq (1 - parameter * first.value ^ 2) ≤ middleError := by
    rw [first.square_eq]
    exact middleResidual
  have secondDistance := tightDistance second middleAligned lastResidual middleSmall lastSmall
  have middleNorm : normSq first.value ≤ 3 * normSq reference := by
    have identity : (reference - first.value) - reference = -first.value := by ring1
    have bound := Norm.Bounds.normSq_sub_le_two (reference - first.value) reference
    rw [identity, Norm.Basic.normSq_neg] at bound
    simp only [Norm.Basic.normSq_eq_canonical] at bound
    calc
      _ ≤ 2 * (normSq (reference - first.value) + normSq reference) := bound
      _ ≤ 2 * ((3 / 64 : Coordinate) * normSq reference + normSq reference) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstDistance le_rfl) (by decide)
      _ = (2 * (3 / 64 + 1) : Coordinate) * normSq reference := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (Basic.Canonical.normSq_nonneg _)
  have composedDistance : normSq (reference - second.value) ≤ (3 / 8 : Coordinate) * normSq reference := by
    calc
      _ ≤ 2 * (normSq (reference - first.value) + normSq (first.value - second.value)) := by
        simpa only [Norm.Basic.normSq_eq_canonical] using (Norm.Bounds.normSq_sub_le_via reference first.value
          second.value)
      _ ≤ 2 * ((3 / 64 : Coordinate) * normSq reference + (3 / 64 : Coordinate) * normSq first.value) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstDistance secondDistance) (by decide)
      _ ≤ 2 * ((3 / 64 : Coordinate) * normSq reference + (3 / 64 : Coordinate) * (3 * normSq reference)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct middleNorm
            (by decide +kernel))) (by decide)
      _ = (2 * (3 / 64 + (3 / 64) * 3) : Coordinate) * normSq reference := by ring1
      _ = _ := by rw [show (2 : Coordinate) * (3 / 64 + (3 / 64) * 3) = 3 / 8 by decide +kernel]
  have referencePositive := Norm.Basic.normSq_pos (inverse_value_ne_zero
    (firstResidual.trans (firstSmall.trans (by decide +kernel))))
  rw [Norm.Basic.normSq_eq_canonical] at referencePositive
  have close : normSq (reference - second.value) < normSq reference :=
    composedDistance.trans_lt ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (3 / 8 : Coordinate) < 1 by decide) referencePositive).trans_eq (by ring1))
  have nearest : normSq (reference - second.value) ≤
      normSq (reference + second.value) := by
    apply le_of_lt
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
      (c := normSq (reference - second.value))
    calc
      _ = normSq (reference - second.value) * 2 := by ring1
      _ < normSq reference * 2 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          close (by decide)
      _ ≤ 2 * (normSq reference + normSq second.value) :=
        (by ring1 : normSq reference * 2 = 2 * normSq reference).trans_le
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (le_add_of_nonneg_right (Basic.Canonical.normSq_nonneg _)) (by decide))
      _ = normSq (reference + second.value) +
          normSq (reference - second.value) := by
        simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im]
        ring1
  exact ⟨second.flip, second.value, second.value_eq, nearest⟩

end

open Purelib.Data.Gaussian in
/-- Rebase an original middle-to-candidate sign alignment at the first alignment's signed middle value.

The retained flip is complemented and value negated exactly when the first alignment flips; the original nearestness
inequality transports through negation. -/
def rebase (first : SignAlignment reference middle) (second : SignAlignment middle candidate) :
    SignAlignment first.value candidate where
  flip := if first.flip then !second.flip else second.flip
  value := if first.flip then -second.value else second.value
  value_eq := by
    rw [second.value_eq]
    cases first.flip <;> cases second.flip
    · exact Eq.refl _
    · exact Eq.refl _
    · exact Eq.refl _
    · change -(-candidate) = candidate
      ring1
  nearest := by
    rw [first.value_eq]
    cases first.flip
    · exact second.nearest
    · change normSq (-middle - (-second.value)) ≤ normSq (-middle + (-second.value))
      have difference : -middle - (-second.value) = -(middle - second.value) := by ring1
      have sum : -middle + (-second.value) = -(middle + second.value) := by ring1
      rw [difference, sum, Basic.Canonical.normSq_neg, Basic.Canonical.normSq_neg]
      exact second.nearest

/-- The direct sign alignment equals composition of the two retained intermediate flips under the stated small
inverse-root residual bounds. -/
theorem cocycle (first : SignAlignment reference middle) (second : SignAlignment middle candidate)
    (direct : SignAlignment reference candidate)
    {parameter : Gaussian} {firstError middleError lastError : Coordinate}
    (firstResidual : normSq (1 - parameter * reference ^ 2) ≤ firstError)
    (middleResidual : normSq (1 - parameter * middle ^ 2) ≤ middleError)
    (lastResidual : normSq (1 - parameter * candidate ^ 2) ≤ lastError)
    (firstSmall : firstError ≤ 1 / 256) (middleSmall : middleError ≤ 1 / 256)
    (lastSmall : lastError ≤ 1 / 256) :
    direct.flip = if first.flip then !second.flip else second.flip :=
  direct.flip_unique
    (composeAligned first (rebase first second) firstResidual middleResidual lastResidual firstSmall middleSmall
      lastSmall)
    firstResidual lastResidual (firstSmall.trans (by decide +kernel)) (lastSmall.trans (by decide +kernel))

end Purelib.Riemann.Normalization.InverseModelOverlapCocycle.SignAlignment

namespace Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial

open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- An original inverse-root model with residual bound at most one two-hundred-fifty-sixth.

The exact polynomial and box index the same model, retaining its cached value,
residual and original pointwise certificates at the tighter displayed bound. -/
structure OverlapReady (polynomial : Polynomial) (box : Box) where
  /-- The retained original inverse-root model on this polynomial and box. -/ model : Model polynomial box
  /-- The retained model residual bound is at most one two-hundred-fifty-sixth. -/ small : model.bound ≤ 1 / 256

constructive_injectivity OverlapReady

namespace OverlapReady

section
open Purelib.Data.Rat
/-- Two correction steps reduce any valid inverse-root model's retained bound to at most one two-hundred-fifty-sixth. -/
private theorem two_steps_small {polynomial : Polynomial} {box : Box} (model : Model polynomial box) :
    model.step.step.bound ≤ 1 / 256 := by
  change model.bound / 4 / 4 ≤ 1 / 256
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Coordinate) < 4)).2
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Coordinate) < 4)).2
  exact model.bound_small.trans_eq (by decide +kernel : (1 / 16 : Coordinate) = (1 / 256) * 4 * 4)

/-- Retain the original model if overlap-ready, otherwise take one or two certified correction steps.

The bound checks select the earliest of these three retained models satisfying the required residual threshold; the
two-step bound guarantees success. -/
def ofModel {polynomial : Polynomial} {box : Box} (model : Model polynomial box) : OverlapReady polynomial box :=
  if small : model.bound ≤ 1 / 256 then ⟨model, small⟩
  else
    let once := model.step
    if small : once.bound ≤ 1 / 256 then ⟨once, small⟩
    else ⟨once.step, by
      change model.bound / 4 / 4 ≤ 1 / 256
      apply (Fraction.Order.Field.div_le_iff_pos
        (by decide : (0 : Coordinate) < 4)).2
      apply (Fraction.Order.Field.div_le_iff_pos
        (by decide : (0 : Coordinate) < 4)).2
      exact model.bound_small.trans_eq
        (by decide +kernel : (1 / 16 : Coordinate) = (1 / 256) * 4 * 4)⟩

end

/-- At a point in three original model boxes, the retained overlap-sample flips satisfy the sign cocycle identity.

The three overlap-ready models supply their exact small residual bounds at the common point, and the sampled value
equalities identify the original sign alignments. -/
theorem cocycle {polynomial : Polynomial} {firstBox middleBox lastBox : Box}
    (first : OverlapReady polynomial firstBox) (middle : OverlapReady polynomial middleBox)
    (last : OverlapReady polynomial lastBox) {point : Gaussian}
    (firstInside : firstBox.Contains point) (middleInside : middleBox.Contains point) (lastInside : lastBox.Contains
      point)
    (firstMiddle : OverlapSample first.model middle.model point)
    (middleLast : OverlapSample middle.model last.model point)
    (firstLast : OverlapSample first.model last.model point) :
    firstLast.alignment.flip = if firstMiddle.alignment.flip then !middleLast.alignment.flip else
      middleLast.alignment.flip := by
  rcases firstMiddle with ⟨firstValue, firstEq, middleValue, middleEq, firstMiddle⟩
  rcases middleLast with ⟨middleValue', middleEq', lastValue, lastEq, middleLast⟩
  rcases firstLast with ⟨firstValue', firstEq', lastValue', lastEq', firstLast⟩
  subst firstValue middleValue middleValue' lastValue firstValue' lastValue'
  apply SignAlignment.cocycle firstMiddle middleLast firstLast (parameter := polynomial.eval point)
    (firstError := first.model.bound) (middleError := middle.model.bound) (lastError := last.model.bound)
    ?_ ?_ ?_ first.small middle.small last.small
  · rw [← first.model.residual_eq]
    exact first.model.residualBound point firstInside
  · rw [← middle.model.residual_eq]
    exact middle.model.residualBound point middleInside
  · rw [← last.model.residual_eq]
    exact last.model.residualBound point lastInside

end OverlapReady

end Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial
