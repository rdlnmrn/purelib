module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.CCL.Prefix.Sensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Field

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

namespace Purelib.Measure.CCL.Cylinder

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Probe variance around a retained cylinder witness is bounded by the square of sensitivity times cylinder spread.

Every original distribution atom realizes the same completed block list, and the probe's nonnegative sensitivity bounds
separation by chordal square. -/
theorem realizedProbeVarianceAroundWitness_le_radius_sq {ι : Type}
    (distribution : Measure.Distribution ι)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) ^ 2 := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation
          (fun _ => (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) ^ 2) := by
      apply distribution.expectation_mono
      intro atom member
      have separationLe := Approximation.CCL.Prefix.realized_probe_separation_le
        (pointsRealize atom member) witnessRealizes probe factor
          factorNonnegative sensitive
      have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
        (Distance.rationalSeparation_nonneg
          (probe (points atom.item)) (probe witness)) separationLe 2
      rw [Distance.NaturalLp.rationalSeparation_sq] at powered
      exact powered
    _ = (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) ^ 2 :=
      distribution.expectation_constant _

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A chordal-square-sensitive probe on one realized cylinder has variance at most the squared sensitivity-scaled
spread. -/
theorem realizedProbeVariance_le_radius_sq {ι : Type}
    (distribution : Measure.Distribution ι)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    distribution.variance (fun item => probe (points item)) ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) ^ 2 := by
  let value := fun item => probe (points item)
  let center := probe witness
  exact (distribution.variance_le_varianceAround value center).trans
    (realizedProbeVarianceAroundWitness_le_radius_sq distribution blocks
      witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive)

open Purelib in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Deviation from the retained cylinder witness has probability zero when the sensitivity-scaled spread is below the
threshold. -/
theorem realizedProbe_deviationProbability_eq_zero_of_radius_lt {ι : Type}
    (distribution : Measure.Distribution ι)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational)
    (radiusSmall : factor * Approximation.CCL.Cylinder.cylinderSpread blocks < threshold) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold Distribution.probability
  apply CylinderConcentration.eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have separationSmall :=
    (Approximation.CCL.Prefix.realized_probe_separation_le (pointsRealize atom member)
      witnessRealizes probe factor factorNonnegative sensitive).trans_lt
      radiusSmall
  unfold Measure.separationAtLeast
  apply decide_eq_false
  exact fun thresholdLe => (thresholdLe.trans_lt separationSmall).false

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A sufficient original block count makes the witness-deviation event have probability zero at the supplied positive
threshold. -/
theorem realizedProbe_deviationProbability_eq_zero_of_requested {ι : Type}
    (distribution : Measure.Distribution ι)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (enough : Budget.requiredProbeBlockCount threshold factor ≤ blocks.length) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested witness
    witnessRealizes probe factor factorPositive sensitive threshold
      thresholdPositive enough
  have radiusNonnegative : 0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
    Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
      (Approximation.CCL.Cylinder.cylinderSpread_nonneg blocks)
  have radiusLeWidth : factor * Approximation.CCL.Cylinder.cylinderSpread blocks ≤
      (Approximation.CCL.Prefix.completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width := by
    rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width]
    calc
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks =
          0 + factor * Approximation.CCL.Cylinder.cylinderSpread blocks := by ring1
      _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread blocks +
          factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
        Fraction.Order.Arithmetic.add_le_add_direct radiusNonnegative le_rfl
      _ = 2 * (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) := by ring1
  exact realizedProbe_deviationProbability_eq_zero_of_radius_lt distribution
    blocks witness witnessRealizes points pointsRealize probe factor
    factorPositive.le sensitive threshold (radiusLeWidth.trans_lt widthSmall)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A sufficient original block count for the centered-variance request gives probe variance below the positive target.
-/
theorem realizedProbeVariance_lt_of_requested {ι : Type}
    (distribution : Measure.Distribution ι)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount
      (Budget.centeredVarianceMeanTarget target)
      factor ≤ blocks.length) :
    distribution.variance (fun item => probe (points item)) < target := by
  let radius := factor * Approximation.CCL.Cylinder.cylinderSpread blocks
  let meanTarget := Budget.centeredVarianceMeanTarget target
  have radiusNonnegative : 0 ≤ radius :=
    Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
      (Approximation.CCL.Cylinder.cylinderSpread_nonneg blocks)
  have widthSmall :
      (Approximation.CCL.Prefix.completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width < meanTarget :=
    Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested witness witnessRealizes probe
      factor factorPositive sensitive meanTarget
      (Budget.centeredVarianceMeanTarget_positive targetPositive)
      enough
  have radiusLeWidth : radius ≤
      (Approximation.CCL.Prefix.completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width := by
    rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width]
    change radius ≤ 2 * radius
    calc
      radius = 0 + radius := by ring1
      _ ≤ radius + radius :=
        Fraction.Order.Arithmetic.add_le_add_direct radiusNonnegative le_rfl
      _ = 2 * radius := by ring1
  have radiusLeTarget : radius ≤ meanTarget :=
    (radiusLeWidth.trans_lt widthSmall).le
  have radiusSquareLe : radius ^ 2 ≤ meanTarget ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusNonnegative
      radiusLeTarget 2
  exact (realizedProbeVariance_le_radius_sq distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (radiusSquareLe.trans_lt
        ((Budget.centeredVarianceMeanTarget_sq_lt_half
            targetPositive).trans
          (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self targetPositive)))

end Purelib.Measure.CCL.Cylinder

end
