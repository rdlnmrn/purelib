module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar
public import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual observations and boundary comparisons of named collar phases

Whole phase/name factory equalities retain the original sequence states and
visible radii. Their possible readings are actual later unit-circle samples.
A genuine raw-height comparison supplies executable boundary floors; the
zero-time comparison needs no radial boundary premise.
-/

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence.Observation (Reading)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

open Purelib.Data.Rat.Fraction

/-- Multiplying admitted unit heights by an admitted time preserves their squared displacement bound. -/
private theorem timed_distance_le (time left right : Fraction.Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    (time * left - time * right) ^ 2 ≤ (left - right) ^ 2 := by
  have productBound : time * time ≤ (1 : Fraction.Rational) :=
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inside.2 inside.1).trans
      ((Fraction.Field.one_mul time).trans_le inside.2)
  have timeSquare : time ^ 2 ≤ (1 : Fraction.Rational) :=
    (show time ^ 2 = time * time by ring1).trans_le productBound
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct timeSquare
    (Order.Arithmetic.sq_nonneg_direct (left - right))
  exact (show (time * left - time * right) ^ 2 = time ^ 2 * (left - right) ^ 2 by ring1).trans_le
    (scaled.trans_eq (Fraction.Field.one_mul _))

public section

namespace PhaseNames

variable {height : GeometricApproximation}
    {clipped : { value : GeometricApproximation // value = height.clipReal }}
    {time : Fraction.Rational} (names : PhaseNames (height := height) clipped time)

/-- Recover the actual original sequence index of a retained forward-phase reading. -/
def forwardIndex (reading : Reading names.2.val.1) : Nat :=
  castState names.2.property.1 reading.state

/-- Recover the actual original conjugate-sequence index of a retained backward-phase reading. -/
def backwardIndex (reading : Reading names.2.val.2.1) : Nat :=
  castState names.2.property.2 reading.state

/-- An actual forward reading has exactly the indexed visible radius of the same retained phase cache. -/
theorem forward_radius (reading : Reading names.2.val.1) :
    reading.radius = quarterRadius names.1.val.errorScale (names.forwardIndex reading) := by
  have same := congrArg (fun ball : Enclosure.Ball => ball.radiusSq)
    (castState_ball names.2.property.1 reading.state)
  exact reading.radius_eq.trans (same.symm.trans
    (Sequence.ApproximationData.toProcess_ball names.1.val.toApproximation (names.forwardIndex reading)).2)

/-- An actual backward reading has the same retained phase scale at its own original conjugate-sequence index. -/
theorem backward_radius (reading : Reading names.2.val.2.1) :
    reading.radius = quarterRadius names.1.val.errorScale (names.backwardIndex reading) := by
  have same := congrArg (fun ball : Enclosure.Ball => ball.radiusSq)
    (castState_ball names.2.property.2 reading.state)
  exact reading.radius_eq.trans (same.symm.trans
    (Sequence.ApproximationData.toProcess_ball names.1.val.conj.toApproximation (names.backwardIndex reading)).2)

/-- Every possible forward reading at an admitted sweep time is an actual unit-circle sample. -/
theorem forward_unit (inside : 0 ≤ time ∧ time ≤ 1) (reading : Reading names.2.val.1) :
    Norm.Basic.normSq reading.value = 1 := by
  have possible := possible_castState names.2.property.1 reading.state reading.possible
  change names.1.val.toApproximation.Possible (names.forwardIndex reading) reading.value at possible
  rcases possible with ⟨later, _, same⟩
  have cache := congrArg (fun value : GeometricApproximation => value.sample later) names.1.property
  have sample := cache.trans (phase_sample (height := height) clipped time inside later)
  exact (congrArg Norm.Basic.normSq (same.trans sample)).trans
    (Twist.phase (time * Interval.Unit.clamp (height.sample later).re)).unit

/-- Every possible backward reading at an admitted sweep time is the conjugate of an actual unit-circle sample. -/
theorem backward_unit (inside : 0 ≤ time ∧ time ≤ 1) (reading : Reading names.2.val.2.1) :
    Norm.Basic.normSq reading.value = 1 := by
  have possible := possible_castState names.2.property.2 reading.state reading.possible
  change names.1.val.conj.toApproximation.Possible (names.backwardIndex reading) reading.value at possible
  rcases possible with ⟨later, _, same⟩
  have cache := congrArg (fun value : GeometricApproximation => value.sample later) names.1.property
  have sample := cache.trans (phase_sample (height := height) clipped time inside later)
  have conjugate := (GeometricApproximation.conj_sample names.1.val later).trans
    (congrArg Basic.conj sample)
  exact (congrArg Norm.Basic.normSq (same.trans conjugate)).trans
    ((Norm.Basic.normSq_conj _).trans
      (Twist.phase (time * Interval.Unit.clamp (height.sample later).re)).unit)

end PhaseNames

/-- The actual clipped phase compares with a boundary phase from the original raw-height tail comparison.

The original comparison is requested at one sixty-fourth of the new target.
Its two computed floors are retained, and every later phase sample pays the
same target. No phase sample or named observation is selected by this operation.
-/
def phase_boundary {height : GeometricApproximation}
    (clipped : { value : GeometricApproximation // value = height.clipReal })
    (time value : Fraction.Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (valueInside : 0 ≤ value ∧ value ≤ 1)
    (heightBoundary : Equivalent height.toApproximation
      (Sequence.Constant.constantApproximation (⟨value, 0⟩ : Canonical))) :
    Equivalent (phase (height := height) clipped time).toApproximation
      (Sequence.Constant.constantApproximation (Twist.phase (time * value)).value) where
  compare firstStart lastStart target positive := by
    let compared := heightBoundary.compare firstStart lastStart ((1 / 64) * target)
      (Order.Arithmetic.mul_pos_direct (by decide +kernel) positive)
    exact
      { leftIndex := compared.leftIndex
        rightIndex := compared.rightIndex
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have raw := compared.close firstAfter lastAfter
          change Norm.Basic.normSq (height.sample firstLater - (⟨value, 0⟩ : Canonical)) < _ at raw
          have projected := Components.Projection.normSq_realPart_le
            (height.sample firstLater - (⟨value, 0⟩ : Canonical))
          have realScalar : Norm.Basic.normSq (Components.Projection.realPart
              (height.sample firstLater - (⟨value, 0⟩ : Canonical))) =
              ((height.sample firstLater).re - value) ^ 2 := by
            change ((height.sample firstLater).re - value) ^ 2 + (0 : Fraction.Rational) ^ 2 = _
            ring1
          have realBound := realScalar.symm.trans_le projected
          have clipping := Interval.Unit.clamp_distance_le (height.sample firstLater).re value
          rewrite [Interval.Unit.clamp_eq valueInside] at clipping
          have timed := timed_distance_le time (Interval.Unit.clamp (height.sample firstLater).re) value timeInside
          have firstInside := Interval.Unit.clamp_inside (height.sample firstLater).re
          have firstTimeInside : 0 ≤ time * Interval.Unit.clamp (height.sample firstLater).re ∧
              time * Interval.Unit.clamp (height.sample firstLater).re ≤ 1 :=
            ⟨Order.Arithmetic.mul_nonneg_direct timeInside.1 firstInside.1,
              ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct timeInside.2 firstInside.1).trans_eq
                (Fraction.Field.one_mul _)).trans firstInside.2⟩
          have lastTimeInside : 0 ≤ time * value ∧ time * value ≤ 1 :=
            ⟨Order.Arithmetic.mul_nonneg_direct timeInside.1 valueInside.1,
              ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct timeInside.2 valueInside.1).trans_eq
                (Fraction.Field.one_mul _)).trans valueInside.2⟩
          have phaseBound := Twist.phase_distance_le
            (time * Interval.Unit.clamp (height.sample firstLater).re) (time * value)
            firstTimeInside lastTimeInside
          have scalar : (time * value - time * Interval.Unit.clamp (height.sample firstLater).re) ^ 2 =
              (time * Interval.Unit.clamp (height.sample firstLater).re - time * value) ^ 2 := by ring1
          rewrite [scalar] at phaseBound
          have bounded := phaseBound.trans
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (timed.trans (clipping.trans realBound)) (by decide +kernel : (0 : Fraction.Rational) ≤ 64))
          have paid := bounded.trans_lt
            (Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide +kernel : (0 : Fraction.Rational) < 64) raw)
          change Norm.Basic.normSq ((phase (height := height) clipped time).sample firstLater -
            (Twist.phase (time * value)).value) < target
          rewrite [phase_sample (height := height) clipped time timeInside firstLater]
          have coefficient : (64 : Fraction.Rational) * (1 / 64) = 1 := by decide +kernel
          exact paid.trans_eq ((Fraction.Field.mul_assoc 64 (1 / 64) target).symm.trans
            ((congrArg (fun factor : Fraction.Rational => factor * target) coefficient).trans
              (Fraction.Field.one_mul target))) }

namespace PhaseNames

variable {height : GeometricApproximation}
    {clipped : { value : GeometricApproximation // value = height.clipReal }}
    {time : Fraction.Rational} (names : PhaseNames (height := height) clipped time)

/-- Compare the retained forward name with its boundary phase, preserving the actual raw-height comparison procedure. -/
def forward_boundary (timeInside : 0 ≤ time ∧ time ≤ 1)
    (value : Fraction.Rational) (valueInside : 0 ≤ value ∧ value ≤ 1)
    (heightBoundary : Equivalent height.toApproximation
      (Sequence.Constant.constantApproximation (⟨value, 0⟩ : Canonical))) :
    NamedEquivalent names.2.val.1.name (Named.exact (Twist.phase (time * value)).value) := by
  let compared := phase_boundary (height := height) clipped time value timeInside valueInside heightBoundary
  have cached := compared.withSamples names.1.val.toApproximation
    (Sequence.Constant.constantApproximation (Twist.phase (time * value)).value)
    (fun index => congrArg (fun current : GeometricApproximation => current.sample index) names.1.property)
    (fun _ => rfl)
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name names.2.property.1.symm) rfl
      (cached.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed _).symm)

/-- Compare the retained backward name with the conjugate boundary phase using the original height procedure. -/
def backward_boundary (timeInside : 0 ≤ time ∧ time ≤ 1)
    (value : Fraction.Rational) (valueInside : 0 ≤ value ∧ value ≤ 1)
    (heightBoundary : Equivalent height.toApproximation
      (Sequence.Constant.constantApproximation (⟨value, 0⟩ : Canonical))) :
    NamedEquivalent names.2.val.2.1.name (Named.exact ((Twist.phase (time * value)).value.conj)) := by
  let boundary := phase_boundary (height := height) clipped time value timeInside valueInside heightBoundary
  have cached : Equivalent names.1.val.conj.toApproximation
      (Sequence.Constant.constantApproximation ((Twist.phase (time * value)).value.conj)) :=
    { compare := fun firstStart lastStart target positive =>
        let compared := boundary.compare firstStart lastStart target positive
        { leftIndex := compared.leftIndex
          rightIndex := compared.rightIndex
          left_ge := compared.left_ge
          right_ge := compared.right_ge
          close := by
            intro firstLater lastLater firstAfter lastAfter
            have sample := congrArg (fun current : GeometricApproximation => current.sample firstLater) names.1.property
            change Norm.Basic.normSq (names.1.val.conj.sample firstLater -
              (Twist.phase (time * value)).value.conj) < target
            rewrite [GeometricApproximation.conj_sample, sample, Norm.Basic.normSq_eq_canonical,
              Basic.Canonical.normSq_conj_sub, ← Norm.Basic.normSq_eq_canonical]
            exact compared.close firstAfter lastAfter } }
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name names.2.property.2.symm) rfl
      (cached.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed _).symm)

/-- At time zero the retained forward phase name agrees with one, with no boundary-height premise. -/
def forward_zero (names : PhaseNames (height := height) clipped 0) :
    NamedEquivalent names.2.val.1.name (Named.exact 1) := by
  have samples : ∀ index, names.1.val.toApproximation.sample index = (1 : Canonical) := by
    intro index
    have cached := congrArg (fun current : GeometricApproximation => current.sample index) names.1.property
    have point := phase_sample (height := height) clipped 0 ⟨by decide +kernel, by decide +kernel⟩ index
    rewrite [Fraction.Field.zero_mul_direct, Twist.phase_zero_value] at point
    exact cached.trans point
  let compared := Equivalent.of_constant_samples names.1.val.toApproximation
    (Sequence.Constant.constantApproximation 1) 1 samples (fun _ => rfl)
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name names.2.property.1.symm) rfl
      (compared.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed 1).symm)

/-- At time zero the retained backward phase name agrees with one, with no boundary-height premise. -/
def backward_zero (names : PhaseNames (height := height) clipped 0) :
    NamedEquivalent names.2.val.2.1.name (Named.exact 1) := by
  have samples : ∀ index, names.1.val.conj.toApproximation.sample index = (1 : Canonical) := by
    intro index
    have cached := congrArg (fun current : GeometricApproximation => current.sample index) names.1.property
    have point := phase_sample (height := height) clipped 0 ⟨by decide +kernel, by decide +kernel⟩ index
    rewrite [Fraction.Field.zero_mul_direct, Twist.phase_zero_value] at point
    have conjugate := (GeometricApproximation.conj_sample names.1.val index).trans
      (congrArg Basic.conj (cached.trans point))
    exact conjugate.trans (by apply Basic.ext <;> decide +kernel)
  let compared := Equivalent.of_constant_samples names.1.val.conj.toApproximation
    (Sequence.Constant.constantApproximation 1) 1 samples (fun _ => rfl)
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name names.2.property.2.symm) rfl
      (compared.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed 1).symm)

end PhaseNames

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar
