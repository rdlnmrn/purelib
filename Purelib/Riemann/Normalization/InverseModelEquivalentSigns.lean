module
public import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Equivalent retained root channels determine polynomial signs

A finite comparison of the channels' own Newton samples determines the
nearest sign. The existing refinement-sign law transports that result to
any supplied finite model stages. Root comparison is proof data only.
-/

namespace Purelib.Riemann.Normalization.InverseModelEquivalentSigns

open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)
open Purelib.Riemann.Normalization.InverseModelOverlap (normalized_value_lower SignAlignment)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {polynomial : Polynomial} {leftBox rightBox : Box}
  {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}

/-- The retained channel point satisfies the inverse residual bound at every refined model stage. -/
private theorem residual_small {box : Box} {model : Model polynomial box}
    (channel : RootChannel model point) (index : Nat) :
    normSq (1 - polynomial.eval point * ((model.refine index).value.eval point) ^ 2) ≤ (model.refine index).bound := by
  rw [← (model.refine index).residual_eq]
  exact (model.refine index).residualBound _ channel.inside

section
open Purelib.Data
/-- Bound every retained Newton root sample away from zero using its parameter norm and cached upper bound.

The normalized inverse residual estimate gives a squared lower bound, which the uniform sample ceiling converts to the
stated rational lower bound. -/
private theorem root_lower {box : Box} {model : Model polynomial box}
    (channel : RootChannel model point) (index : Nat) :
    normSq (polynomial.eval point) / (3 * (channel.samples.bound + 1)) ≤ normSq (channel.samples.sample index) := by
  have normalized := normalized_value_lower ((residual_small channel index).trans (model.refine index).bound_small)
  have oneLe : (1 : Coordinate) ≤ 3 * (normSq (polynomial.eval point) * normSq ((model.refine index).value.eval point) ^
    2) :=
    (by decide : (1 : Coordinate) = 3 * (1 / 3)).trans_le
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normalized (by decide))
  have weighted := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe
    (Gaussian.Basic.Canonical.normSq_nonneg (polynomial.eval point))
  rw [Rat.Fraction.Field.mul_one_direct] at weighted
  have lowerSquare : normSq (polynomial.eval point) ≤ 3 * normSq (channel.samples.sample index) ^ 2 := by
    apply weighted.trans_eq
    rw [channel.samples.sample_eq, Gaussian.Basic.Canonical.normSq_mul]
    ring1
  have upper := (channel.samples.sample_bounded channel.inside index).trans
    (le_add_of_nonneg_right (by decide : (0 : Coordinate) ≤ 1))
  have squared : normSq (channel.samples.sample index) ^ 2 ≤
      normSq (channel.samples.sample index) * (channel.samples.bound + 1) := by
    rw [pow_two]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct upper (Gaussian.Basic.Canonical.normSq_nonneg
      _)
  have positive : 0 < 3 * (channel.samples.bound + 1) := Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct channel.samples.bound_nonnegative (by decide))
  apply (Rat.Fraction.Order.Field.div_le_iff_pos positive).mpr
  exact (lowerSquare.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared (by
    decide))).trans_eq (by ring1)

/-- A Gaussian difference no larger than the first value is no larger than the corresponding sum. -/
private theorem nearest_of_close {first last : Gaussian} (close : normSq (first - last) ≤ normSq first) :
    normSq (first - last) ≤ normSq (first + last) := by
  apply Rat.Fraction.Order.Arithmetic.le_of_add_le_add_right_direct (c := normSq (first - last))
  calc
    _ = 2 * normSq (first - last) := by ring1
    _ ≤ 2 * normSq first := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close (by decide)
    _ ≤ 2 * (normSq first + normSq last) := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (le_add_of_nonneg_right (Gaussian.Basic.Canonical.normSq_nonneg _)) (by decide)
    _ = _ := by
      simp only [normSq, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im];
      ring1

end

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Equivalent retained root channels select the unflipped inverse-polynomial sign at arbitrary refinement indices.

A finite comparison of their own Newton samples establishes the nearest sign at one sufficiently accurate pair of
stages. The original refinement-sign law transports it to the two requested stages. -/
theorem equivalent_flip (first : RootChannel left point) (last : RootChannel right point)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name last.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    (SignAlignment.build ((left.refine leftIndex).value.eval point) ((right.refine rightIndex).value.eval point)).flip =
      false := by
  have parameterPositive : 0 < normSq (polynomial.eval point) :=
    (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (Gaussian.Norm.Basic.normSq_pos
      (RootContinuation.SquareRootChannelOwnership.parameter_nonzero first.certificate)))
  let target := normSq (polynomial.eval point) / (3 * (first.samples.bound + 1))
  have positive : 0 < target := Rat.Fraction.Order.Field.div_pos_direct parameterPositive
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct first.samples.bound_nonnegative (by decide)))
  let equivalent := first.samples_equivalent.trans (Gaussian.Equivalence.Equivalent.trans roots
    last.samples_equivalent.symm)
  let compared := equivalent.compare 0 0 target positive
  have close : normSq (first.samples.sample compared.leftIndex - last.samples.sample compared.rightIndex) ≤
      normSq (first.samples.sample compared.leftIndex) := by
    have comparedClose := (compared.close le_rfl le_rfl).le
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at comparedClose
    exact comparedClose.trans (root_lower first compared.leftIndex)
  rw [first.samples.sample_eq, last.samples.sample_eq, ← mul_sub, Gaussian.Basic.Canonical.normSq_mul,
    Gaussian.Basic.Canonical.normSq_mul] at close
  rw [Rat.Fraction.Field.mul_comm (normSq (polynomial.eval point)),
    Rat.Fraction.Field.mul_comm (normSq (polynomial.eval point))] at close
  have inverseClose : normSq ((left.refine compared.leftIndex).value.eval point - (right.refine
    compared.rightIndex).value.eval point) ≤
      normSq ((left.refine compared.leftIndex).value.eval point) :=
    Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct close parameterPositive
  let aligned : SignAlignment ((left.refine compared.leftIndex).value.eval point) ((right.refine
    compared.rightIndex).value.eval point) :=
    ⟨false, (right.refine compared.rightIndex).value.eval point, rfl, nearest_of_close inverseClose⟩
  have lateFalse : (SignAlignment.build ((left.refine compared.leftIndex).value.eval point)
      ((right.refine compared.rightIndex).value.eval point)).flip = false :=
    (SignAlignment.build _ _).flip_unique aligned (residual_small first compared.leftIndex) (residual_small last
      compared.rightIndex)
      (left.refine compared.leftIndex).bound_small (right.refine compared.rightIndex).bound_small
  let initial := Normalization.InverseModelOverlap.OverlapSample.build left right point
  have initialFalse : initial.alignment.flip = false :=
    (Normalization.InverseModelRefinementSigns.OverlapSample.refine_flip initial first.inside last.inside first.small
      last.small compared.leftIndex compared.rightIndex).symm.trans lateFalse
  exact (Normalization.InverseModelRefinementSigns.OverlapSample.refine_flip initial first.inside last.inside
    first.small last.small leftIndex rightIndex).trans initialFalse

open Purelib.Approximation
/-- Equivalent root channels make the inverse-polynomial difference no larger than the sum.

The two finite model stages are independent; both are evaluated at the retained common point and use the operational
equivalence of the original root names. -/
theorem equivalent_nearest (first : RootChannel left point) (last : RootChannel right point)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name last.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    normSq ((left.refine leftIndex).value.eval point - (right.refine rightIndex).value.eval point) ≤
      normSq ((left.refine leftIndex).value.eval point + (right.refine rightIndex).value.eval point) := by
  have nearest := (SignAlignment.build ((left.refine leftIndex).value.eval point) ((right.refine rightIndex).value.eval
    point)).nearest
  rw [SignAlignment.value_eq, equivalent_flip first last roots leftIndex rightIndex] at nearest
  exact nearest

/-- Transport the nearest-sign inequality along equality of the two retained channel points.

Operational equivalence of the original root names supplies the comparison at any independent pair of model refinement
stages. -/
theorem equivalent_nearest_at {firstPoint lastPoint : Gaussian}
    (first : RootChannel left firstPoint) (last : RootChannel right lastPoint) (same : firstPoint = lastPoint)
    (roots : Gaussian.Equivalence.NamedEquivalent first.certificate.value.name last.certificate.value.name) (leftIndex
      rightIndex : Nat) :
    normSq ((left.refine leftIndex).value.eval firstPoint - (right.refine rightIndex).value.eval lastPoint) ≤
      normSq ((left.refine leftIndex).value.eval firstPoint + (right.refine rightIndex).value.eval lastPoint) := by
  cases same
  exact equivalent_nearest first last roots leftIndex rightIndex

end Purelib.Riemann.Normalization.InverseModelEquivalentSigns
