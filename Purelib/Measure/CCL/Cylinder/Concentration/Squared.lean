module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Event

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)
open Purelib.Data.CCL.Encoding.Cylinder.Projective (ProjectiveRealizes)
open Purelib.Geometry.Projective.Chordal.Probe (SquaredProbeSensitive)

section
@[expose] public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.Measure.CCL.Cylinder

section
open Purelib
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A squared-sensitive probe's variance around the retained cylinder witness is at most sensitivity times cylinder
spread.

Every original distribution occurrence and the witness realize the same completed blocks; the supplied
squared-sensitivity certificate and nonnegative factor determine the bound. -/
theorem realizedSquaredProbeVarianceAroundWitness_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation (fun _ =>
          factor * Approximation.CCL.Cylinder.cylinderSpread blocks) := by
      apply distribution.expectation_mono
      intro atom member
      rw [← Distance.NaturalLp.rationalSeparation_sq]
      exact Approximation.CCL.Prefix.realized_probe_separation_sq_le (pointsRealize atom member)
        witnessRealizes probe factor factorNonnegative sensitive
    _ = factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
      distribution.expectation_constant _

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A squared-sensitive probe on one realized cylinder has variance at most sensitivity times its exact spread. -/
theorem realizedSquaredProbeVariance_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe (points item)) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
  (distribution.variance_le_varianceAround
    (fun item => probe (points item)) (probe witness)).trans
      (realizedSquaredProbeVarianceAroundWitness_le distribution blocks
        witness witnessRealizes points pointsRealize probe factor
        factorNonnegative sensitive)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Projective cylinder realizations bound the squared-sensitive probe's variance around the retained witness by
sensitivity times spread. -/
theorem projectiveRealizedSquaredProbeVarianceAroundWitness_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation (fun _ =>
          factor * Approximation.CCL.Cylinder.cylinderSpread blocks) := by
      apply distribution.expectation_mono
      intro atom member
      rw [← Distance.NaturalLp.rationalSeparation_sq]
      exact Approximation.CCL.Prefix.projectiveRealized_probe_separation_sq_le
        (pointsRealize atom member) witnessRealizes probe factor
          factorNonnegative sensitive
    _ = factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
      distribution.expectation_constant _

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- A squared-sensitive probe on projective realizations of one cylinder has variance at most sensitivity times spread.
-/
theorem projectiveRealizedSquaredProbeVariance_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe (points item)) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks :=
  (distribution.variance_le_varianceAround
    (fun item => probe (points item)) (probe witness)).trans
      (projectiveRealizedSquaredProbeVarianceAroundWitness_le distribution
        blocks witness witnessRealizes points pointsRealize probe factor
        factorNonnegative sensitive)

/-- At a positive threshold, witness-deviation probability is at most sensitivity-scaled cylinder spread divided by
threshold squared. -/
theorem realizedSquaredProbe_deviationProbability_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) / threshold ^ 2 := by
  have markov := distribution.probability_separationAtLeast_le_poweredLpDistance
    2 threshold thresholdPositive
    (fun item => probe (points item)) (fun _ => probe witness)
  rw [distribution.poweredLpDistance_two] at markov
  have poweredL2Le : distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks := by
    change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
    exact realizedSquaredProbeVarianceAroundWitness_le distribution blocks
      witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive
  apply markov.trans
  change distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) *
        (threshold ^ 2)⁻¹ ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) * (threshold ^ 2)⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    poweredL2Le
    (Fraction.Order.Field.inv_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2)).le

/-- Projective realizations give the same squared-sensitive witness-deviation bound using the exact cylinder spread and
positive threshold. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) / threshold ^ 2 := by
  have markov := distribution.probability_separationAtLeast_le_poweredLpDistance
    2 threshold thresholdPositive
    (fun item => probe (points item)) (fun _ => probe witness)
  rw [distribution.poweredLpDistance_two] at markov
  have poweredL2Le : distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) ≤
      factor * Approximation.CCL.Cylinder.cylinderSpread blocks := by
    change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
    exact projectiveRealizedSquaredProbeVarianceAroundWitness_le distribution
      blocks witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive
  apply markov.trans
  change distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) *
        (threshold ^ 2)⁻¹ ≤
      (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) * (threshold ^ 2)⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    poweredL2Le
    (Fraction.Order.Field.inv_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2)).le

end

section
open Purelib.CCL.Measure
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Witness-deviation probability vanishes when the squared-sensitivity budget is below the positive threshold squared.
-/
theorem realizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (budgetSmall : factor * Approximation.CCL.Cylinder.cylinderSpread blocks < threshold ^ 2) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold Distribution.probability
  apply SquaredCylinderConcentration.eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have squareSmall := (Approximation.CCL.Prefix.realized_probe_separation_sq_le
    (pointsRealize atom member) witnessRealizes probe factor
      factorNonnegative sensitive).trans_lt budgetSmall
  have separationSmall := Purelib.Data.Rat.Distance.rationalSeparation_lt_of_sq_lt_sq thresholdPositive
    squareSmall
  unfold Measure.separationAtLeast
  exact decide_eq_false_iff_not.mpr
    (fun thresholdLe => (thresholdLe.trans_lt separationSmall).false)

/-- For projective realizations, witness-deviation probability vanishes when the exact squared-sensitivity budget is
below threshold squared. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (budgetSmall : factor * Approximation.CCL.Cylinder.cylinderSpread blocks < threshold ^ 2) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold Distribution.probability
  apply SquaredCylinderConcentration.eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have squareSmall := (Approximation.CCL.Prefix.projectiveRealized_probe_separation_sq_le
    (pointsRealize atom member) witnessRealizes probe factor
      factorNonnegative sensitive).trans_lt budgetSmall
  have separationSmall := Purelib.Data.Rat.Distance.rationalSeparation_lt_of_sq_lt_sq thresholdPositive
    squareSmall
  unfold Measure.separationAtLeast
  exact decide_eq_false_iff_not.mpr
    (fun thresholdLe => (thresholdLe.trans_lt separationSmall).false)

end

section
open Purelib.Approximation.Rational
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The required squared-variance block count makes the realized probe variance strictly below the positive target. -/
theorem realizedSquaredProbeVariance_lt_of_requested {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  (realizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
        target factor targetPositive factorPositive enough)

/-- The required squared-variance block count makes projectively realized probe variance strictly below the positive
target. -/
theorem projectiveRealizedSquaredProbeVariance_lt_of_requested {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : Budget.requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  (projectiveRealizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
        target factor targetPositive factorPositive enough)

/-- The required block count at the squared threshold makes realized witness-deviation probability zero. -/
theorem realizedSquaredProbe_deviationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (enough : Budget.requiredSquaredVarianceBlockCount (threshold ^ 2) factor ≤
      blocks.length) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  exact realizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive.le sensitive threshold thresholdPositive
    (Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (threshold ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2)
      factorPositive enough)

/-- The required block count at the squared threshold makes projectively realized witness-deviation probability zero. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (enough : Budget.requiredSquaredVarianceBlockCount (threshold ^ 2) factor ≤
      blocks.length) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  exact projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive.le sensitive threshold thresholdPositive
    (Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (threshold ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2)
      factorPositive enough)

/-! ## Concrete nonconstant chordal-probe consequences -/

end

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The chordal omega probe on projective cylinder realizations has variance at most twice the exact cylinder spread. -/
theorem projectiveRealizedChordalOmegaProbeVariance_le {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Block) (witness : Line.GaussianLine)
    (witnessRealizes : ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes blocks (points atom.item)) :
    distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe (points item)) ≤
      2 * Approximation.CCL.Cylinder.cylinderSpread blocks :=
  projectiveRealizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive
end

end Purelib.Measure.CCL.Cylinder

end
