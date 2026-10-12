module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant

import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

@[expose] public section

/-!
# Primitive comparison through operational sheet equivalence

Restrict the patch's root process to a chosen accurate state.  All subsequent
coefficient candidates satisfy the polynomial estimate.  Finite operational
equivalence then compares them with the actual prepared reading and persisted
center.  No exact root or containment of the child's entire owner box is used.
-/

namespace Purelib.Riemann.Integration.PreparedPrimitiveEquivalence

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

section
open Purelib.Data
/-- Rational coordinates and squared error bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- Gaussian rational polynomial values and coefficient readings. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Approximation in
/-- Operational equivalence of named Gaussian processes. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {patch : ContinuedNeighborhood curve.polynomial count} {point : Gaussian}

/-- Restrict the retained root process to the selected accurate reading state. -/
def basedRoot (sample : ContinuedNeighborhood.Point patch point) (index : Nat) : CoherentNamed :=
  sample.certificate.value.based (sample.readingState index)

open Purelib.Approximation in
/-- Carry the original positive root lower bound into the based process. -/
def basedApart (sample : ContinuedNeighborhood.Point patch point) (index : Nat) :
    Gaussian.Name.Basic.Named.Apart (basedRoot sample index).name where
  certificate :=
    { lowerSq := sample.certificate.apart.certificate.lowerSq
      positive := sample.certificate.apart.certificate.positive
      lower := by
        intro state value inside
        exact sample.certificate.apart.certificate.lower state.source inside }

open Purelib.Curves in
/-- Evaluate the differential using the root process based at the selected reading.

The based apartness certificate retains the denominator's original positive lower bound. -/
def coefficient (sample : ContinuedNeighborhood.Point patch point) (index : Nat)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) : CoherentNamed :=
  Hyperelliptic.Differentials.Value.differentialValue differential point (basedRoot sample index) (basedApart sample
    index)

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound every possible based coefficient by the refined inverse-root polynomial estimate.

The point lies in the continuation box; the squared error is bounded by numerator norm times the retained geometric
inverse-error scale. -/
theorem coefficient_possible_bound (sample : ContinuedNeighborhood.Point patch point)
    (inside : patch.box.Contains point) (index : Nat) (differential : Hyperelliptic.Differentials.Basic.Differential
      genus)
    (state : (coefficient sample index differential).name.process.State) {value : Gaussian}
    (possible : (coefficient sample index differential).name.process.Possible state value) :
    normSq ((differentialNumerator differential).eval point * (patch.base.refine index).value.eval point - value) ≤
      normSq ((differentialNumerator differential).eval point) * Rational.Geometric.Basic.quarterRadius
        patch.inverseErrorScale index := by
  obtain ⟨root, rootPossible, equal⟩ := Hyperelliptic.Differentials.Value.differentialValue_possible_components
    differential point
    (basedRoot sample index) (basedApart sample index) state possible
  have atReading := state.2.persists rootPossible
  have inverseBound := sample.reading_inverse_error inside index atReading
  have inverseEq : root⁻¹ = Gaussian.Basic.Canonical.inv root := by
    rw [Gaussian.Field.inv_eq]
    simp only [Gaussian.Field.inv, Gaussian.Basic.Canonical.inv,
      Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self]
    rfl
  have identity : (differentialNumerator differential).eval point * (patch.base.refine index).value.eval point - value =
      (differentialNumerator differential).eval point * ((patch.base.refine index).value.eval point - inv root) := by
    rw [equal, Readings.PreparedPrimitiveSamples.differentialNumerator_eval, Field.ExplicitField.div_eq_mul_inv,
      inverseEq]
    ring1
  have productNorm := Gaussian.Norm.Basic.normSq_mul
    ((differentialNumerator differential).eval point) ((patch.base.refine index).value.eval point - inv root)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at productNorm
  rw [identity, productNorm]
  exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound
    (Gaussian.Basic.Canonical.normSq_nonneg _)

open Purelib.Curves in
open Purelib.Approximation in
/-- Transport root-process equivalence to the prepared and based differential coefficients.

The comparison uses the prepared edge's initial point and preserves its actual sheet query owner. -/
def coefficientEquivalent (prepared : PreparedEdge curve differential)
    (sample : ContinuedNeighborhood.Point patch (prepared.point 0)) (index : Nat)
    (roots : NamedEquivalent (prepared.rootName 0 prepared.baseInside) sample.certificate.value.name) :
    NamedEquivalent (prepared.coefficient 0 prepared.baseInside).name (coefficient sample index differential).name := by
  have originalRoots : NamedEquivalent (prepared.sheetValue 0 prepared.baseInside).value.name
    sample.certificate.value.name := by
    rw [prepared.sheetValue_name_eq_directQueryOwnerRootName 0 prepared.baseInside]
    rw [prepared.rootName_eq_directQueryOwnerRootName 0 prepared.baseInside] at roots
    exact roots
  have basedRoots := Gaussian.Equivalence.NamedEquivalent.trans originalRoots
    (sample.certificate.value.basedEquivalent (sample.readingState index))
  exact Hyperelliptic.Differentials.Value.differentialValue_respects_sheet differential (prepared.point 0)
    (prepared.sheetValue 0 prepared.baseInside).value (basedRoot sample index)
    (prepared.sheetValue 0 prepared.baseInside).apart (basedApart sample index) basedRoots

open Purelib.Data in
/-- Bound every later prepared base reading's squared distance from a retained center by four model allowances. -/
private theorem later_sub_center_le (prepared : PreparedEdge curve differential)
    (center : PreparedEdge.CenterState prepared) (index : Nat) :
    normSq (prepared.laterBaseValue index - center.value) ≤ 4 * prepared.modelErrorAllowance := by
  calc
    _ ≤ 2 * (normSq (prepared.laterBaseValue index - prepared.baseReading) + normSq (prepared.baseReading -
      center.value)) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (prepared.modelErrorAllowance + prepared.modelErrorAllowance) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add
        (by
          have scalar := (prepared.laterBaseValue_sub_baseReading_lt index).le
          rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
          exact scalar) (by
          have reverse : prepared.baseReading - center.value = -(center.value - prepared.baseReading) := by ring1
          rw [reverse]
          rw [← Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Norm.Basic.normSq_neg,
            Gaussian.Norm.Basic.normSq_eq_canonical]
          have scalar := center.value_sub_baseReading_lt.le
          rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
          exact scalar)) (by decide)
    _ = _ := by ring1

open Purelib.Approximation in
open Purelib.Data in
/-- Bound the polynomial coefficient's squared distance from a persisted prepared center.

Operational sheet equivalence and containment of the initial point give twice the numerator-weighted inverse error plus
twenty prepared model allowances. -/
theorem coefficient_center_le (prepared : PreparedEdge curve differential)
    (center : PreparedEdge.CenterState prepared)
    (sample : ContinuedNeighborhood.Point patch (prepared.point 0))
    (inside : patch.box.Contains (prepared.point 0)) (index : Nat)
    (roots : NamedEquivalent (prepared.rootName 0 prepared.baseInside) sample.certificate.value.name) :
    normSq ((differentialNumerator differential).eval (prepared.point 0) *
      (patch.base.refine index).value.eval (prepared.point 0) - center.value) ≤
        2 * normSq ((differentialNumerator differential).eval (prepared.point 0)) *
          Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 20 * prepared.modelErrorAllowance := by
  let value := coefficient sample index differential
  let equivalent := Gaussian.Equivalence.NamedEquivalent.trans (coefficientEquivalent prepared sample index roots).symm
    (PreparedEdge.CenterState.baseEquivalent prepared)
  let comparison := equivalent.compare 0 0 prepared.modelErrorAllowance prepared.modelErrorAllowance_positive
  let left := Gaussian.Process.Sampling.witnessAt value.name.process value.name.state comparison.leftIndex
  let right := prepared.laterBaseValue comparison.rightIndex
  have close : normSq (left - right) ≤ prepared.modelErrorAllowance := by
    have scalar := (comparison.close (Nat.le_refl _) (Nat.le_refl _)).le
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have modeled := coefficient_possible_bound sample inside index differential _
    (Gaussian.Process.Sampling.witnessAt_possible value.name.process value.name.state comparison.leftIndex)
  have centerBound : normSq (left - center.value) ≤ 10 * prepared.modelErrorAllowance := by
    calc
      _ ≤ 2 * (normSq (left - right) + normSq (right - center.value)) := by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (prepared.modelErrorAllowance + 4 * prepared.modelErrorAllowance) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add close (later_sub_center_le prepared center comparison.rightIndex)) (by decide)
      _ = _ := by ring1
  calc
    _ ≤ 2 * (normSq ((differentialNumerator differential).eval (prepared.point 0) *
        (patch.base.refine index).value.eval (prepared.point 0) - left) + normSq (left - center.value)) := by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * (normSq ((differentialNumerator differential).eval (prepared.point 0)) *
        Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 10 * prepared.modelErrorAllowance) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add modeled centerBound) (by decide)
    _ = _ := by ring1

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound the primitive increment's squared error against the centered prepared model.

Containment of both endpoints and root equivalence combine the Taylor remainder with inverse-root and prepared-center
errors, scaled by the actual squared movement. -/
theorem integral_error_le {index : Nat} (model : PrimitiveModel patch index (differentialNumerator differential))
    (prepared : PreparedEdge curve differential) (center : PreparedEdge.CenterState prepared)
    (sample : ContinuedNeighborhood.Point patch (prepared.point 0))
    (startInside : patch.box.Contains (prepared.point 0)) (finishInside : patch.box.Contains (prepared.point 1))
    (roots : NamedEquivalent (prepared.rootName 0 prepared.baseInside) sample.certificate.value.name) :
    normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
      (prepared.centeredModel center).integralSample) ≤
        2 * model.primitive.remainderBound * prepared.pointMovement ^ 2 +
          (4 * normSq ((differentialNumerator differential).eval (prepared.point 0)) *
            Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 40 * prepared.modelErrorAllowance) *
              prepared.pointMovement := by
  have taylor := model.primitive.increment_bound startInside finishInside
  rw [model.coefficient_eq] at taylor
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at taylor
  have centerBound := coefficient_center_le prepared center sample startInside index roots
  let delta := prepared.point 1 - prepared.point 0
  let value := (differentialNumerator differential).eval (prepared.point 0) * (patch.base.refine index).value.eval
    (prepared.point 0)
  have identity : model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
      (prepared.centeredModel center).integralSample =
        (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) - value * delta)
          +
          (value - center.value) * delta := by
    rw [Cell.Basic.CellModel.integralSample_constant
      (prepared.centeredModel center) center.value rfl]
    change _ - delta * center.value = _
    ring1
  rw [identity]
  calc
    _ ≤ 2 * (normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
      value * delta) +
        normSq ((value - center.value) * delta)) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (model.primitive.remainderBound * prepared.pointMovement ^ 2 +
        (2 * normSq ((differentialNumerator differential).eval (prepared.point 0)) *
          Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 20 * prepared.modelErrorAllowance) *
            prepared.pointMovement) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor (by
        have productNorm := Gaussian.Norm.Basic.normSq_mul (value - center.value) delta
        simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at productNorm
        have movement : normSq delta = prepared.pointMovement := by
          change Gaussian.Basic.Canonical.normSq (prepared.point 1 - prepared.point 0) =
            Gaussian.Norm.Basic.normSq (prepared.point 1 - prepared.point 0)
          rw [Gaussian.Norm.Basic.normSq_eq_canonical]
        rw [productNorm, movement]
        exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct centerBound
          (Gaussian.Norm.Basic.normSq_nonneg _))) (by decide)
    _ = _ := by ring1

open Purelib.Approximation in
open Purelib.Data in
/-- Replace local numerator, model-error and movement terms by supplied uniform upper bounds.

The primitive increment keeps the same centered model and operational sheet equivalence while its error is bounded using
those larger scalar quantities. -/
theorem integral_error_le_uniform {index : Nat} (model : PrimitiveModel patch index (differentialNumerator
  differential))
    (prepared : PreparedEdge curve differential) (center : PreparedEdge.CenterState prepared)
    (sample : ContinuedNeighborhood.Point patch (prepared.point 0))
    (startInside : patch.box.Contains (prepared.point 0)) (finishInside : patch.box.Contains (prepared.point 1))
    (roots : NamedEquivalent (prepared.rootName 0 prepared.baseInside) sample.certificate.value.name)
    {numeratorBound error movement : Coordinate}
    (numeratorLe : normSq ((differentialNumerator differential).eval (prepared.point 0)) ≤ numeratorBound)
    (errorLe : prepared.modelErrorAllowance ≤ error) (movementLe : prepared.pointMovement ≤ movement) :
    normSq (model.primitive.value.eval (prepared.point 1) - model.primitive.value.eval (prepared.point 0) -
      (prepared.centeredModel center).integralSample) ≤
        2 * model.primitive.remainderBound * movement ^ 2 +
          (4 * numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 40 * error) *
            movement := by
  have movementNonnegative : 0 ≤ prepared.pointMovement := Gaussian.Norm.Basic.normSq_nonneg _
  have numeratorNonnegative := (Gaussian.Basic.Canonical.normSq_nonneg _).trans numeratorLe
  have errorNonnegative := prepared.modelErrorAllowance_positive.le.trans errorLe
  have inverseNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg patch.inverseErrorScale_positive.le index
  have coefficientBound : 4 * normSq ((differentialNumerator differential).eval (prepared.point 0)) *
      Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 40 * prepared.modelErrorAllowance ≤
        4 * numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 40 * error :=
    add_le_add (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct numeratorLe (by decide)) inverseNonnegative)
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel))
  have coefficientNonnegative : 0 ≤ 4 * numeratorBound *
      Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index + 40 * error :=
    add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) numeratorNonnegative) inverseNonnegative)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) errorNonnegative)
  exact (integral_error_le model prepared center sample startInside finishInside roots).trans (add_le_add
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.pow_le_pow_direct movementNonnegative movementLe 2)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) model.primitive.remainderBound_nonnegative))
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct coefficientBound movementLe movementNonnegative
      coefficientNonnegative))

end Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
