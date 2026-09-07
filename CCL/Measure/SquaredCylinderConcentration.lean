import mathlib.Tactic.QuotientFreeOmega
import CCL.Measure.EncodedSquaredStability
import FiniteMeasure.Moments

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace CCL.FiniteMeasure

/-- Squared deviation about one canonical cylinder witness is bounded by the
sensitivity-scaled cylinder spread. -/
theorem realizedSquaredProbeVarianceAroundWitness_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      factor * cylinderSpread blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation (fun _ =>
          factor * cylinderSpread blocks) := by
      apply distribution.expectation_mono
      intro atom member
      rw [← _root_.FiniteMeasure.rationalSeparation_sq]
      exact realized_probe_separation_sq_le (pointsRealize atom member)
        witnessRealizes probe factor factorNonnegative sensitive
    _ = factor * cylinderSpread blocks :=
      distribution.expectation_constant _

/-- Variance of a squared-sensitive probe on a finite law supported by one
canonical CCL cylinder has the same linear-in-spread bound. -/
theorem realizedSquaredProbeVariance_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe (points item)) ≤
      factor * cylinderSpread blocks :=
  (distribution.variance_le_varianceAround
    (fun item => probe (points item)) (probe witness)).trans
      (realizedSquaredProbeVarianceAroundWitness_le distribution blocks
        witness witnessRealizes points pointsRealize probe factor
        factorNonnegative sensitive)

/-- Projectively rescaled encoder traces obey the same witness-centred
second-moment bound. -/
theorem projectiveRealizedSquaredProbeVarianceAroundWitness_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      factor * cylinderSpread blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation (fun _ =>
          factor * cylinderSpread blocks) := by
      apply distribution.expectation_mono
      intro atom member
      rw [← _root_.FiniteMeasure.rationalSeparation_sq]
      exact projectiveRealized_probe_separation_sq_le
        (pointsRealize atom member) witnessRealizes probe factor
          factorNonnegative sensitive
    _ = factor * cylinderSpread blocks :=
      distribution.expectation_constant _

/-- Variance bound for a finite law supported by one projectively rescaled
encoder cylinder. -/
theorem projectiveRealizedSquaredProbeVariance_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe (points item)) ≤
      factor * cylinderSpread blocks :=
  (distribution.variance_le_varianceAround
    (fun item => probe (points item)) (probe witness)).trans
      (projectiveRealizedSquaredProbeVarianceAroundWitness_le distribution
        blocks witness witnessRealizes points pointsRealize probe factor
        factorNonnegative sensitive)

/-- Powered Markov tail bound around a canonical cylinder witness. -/
theorem realizedSquaredProbe_deviationProbability_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) ≤
      (factor * cylinderSpread blocks) / threshold ^ 2 := by
  have markov := distribution.probability_separationAtLeast_le_poweredLpDistance
    2 threshold thresholdPositive
    (fun item => probe (points item)) (fun _ => probe witness)
  rw [distribution.poweredLpDistance_two] at markov
  have poweredL2Le : distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) ≤
      factor * cylinderSpread blocks := by
    change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
    exact realizedSquaredProbeVarianceAroundWitness_le distribution blocks
      witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive
  apply markov.trans
  change distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) *
        (threshold ^ 2)⁻¹ ≤
      (factor * cylinderSpread blocks) * (threshold ^ 2)⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    poweredL2Le
    (RFAP.ConstructiveFraction.inv_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2)).le

/-- Powered Markov tail bound around a projectively rescaled cylinder
witness. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) ≤
      (factor * cylinderSpread blocks) / threshold ^ 2 := by
  have markov := distribution.probability_separationAtLeast_le_poweredLpDistance
    2 threshold thresholdPositive
    (fun item => probe (points item)) (fun _ => probe witness)
  rw [distribution.poweredLpDistance_two] at markov
  have poweredL2Le : distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) ≤
      factor * cylinderSpread blocks := by
    change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
    exact projectiveRealizedSquaredProbeVarianceAroundWitness_le distribution
      blocks witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive
  apply markov.trans
  change distribution.poweredL2Distance
      (fun item => probe (points item)) (fun _ => probe witness) *
        (threshold ^ 2)⁻¹ ≤
      (factor * cylinderSpread blocks) * (threshold ^ 2)⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    poweredL2Le
    (RFAP.ConstructiveFraction.inv_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2)).le

private theorem eventWeight_eq_zero_of_false_on_atoms {index : Type}
    (atoms : List (_root_.FiniteMeasure.Weighted index))
    (event : index → Bool)
    (falseOn : ∀ atom, atom ∈ atoms → event atom.item = false) :
    _root_.FiniteMeasure.eventWeight atoms event = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have headFalse := falseOn atom List.mem_cons_self
      have tailFalse : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false := by
        intro candidate member
        exact falseOn candidate (List.mem_cons_of_mem atom member)
      simp only [_root_.FiniteMeasure.eventWeight, headFalse, zero_add]
      exact inductionHypothesis tailFalse

private theorem separation_lt_of_sq_lt_sq
    {left right threshold : Coordinate} (thresholdPositive : 0 < threshold)
    (small : _root_.FiniteMeasure.rationalSeparation left right ^ 2 <
      threshold ^ 2) :
    _root_.FiniteMeasure.rationalSeparation left right < threshold := by
  rcases lt_trichotomy
      (_root_.FiniteMeasure.rationalSeparation left right) threshold with
    less | equal | greater
  · exact less
  · subst threshold
    exact (lt_irrefl _ small).elim
  · have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      thresholdPositive.le greater.le 2
    exact ((not_lt_of_ge squareOrder) small).elim

/-- If the squared cylinder budget is strictly below the displayed threshold
square, no atom of a canonically realized finite law can cross it. -/
theorem realizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (budgetSmall : factor * cylinderSpread blocks < threshold ^ 2) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold _root_.FiniteMeasure.Distribution.probability
  apply eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have squareSmall := (realized_probe_separation_sq_le
    (pointsRealize atom member) witnessRealizes probe factor
      factorNonnegative sensitive).trans_lt budgetSmall
  have separationSmall := separation_lt_of_sq_lt_sq thresholdPositive
    squareSmall
  unfold _root_.FiniteMeasure.separationAtLeast
  simp only [decide_eq_false_iff_not]
  exact fun thresholdLe => (thresholdLe.trans_lt separationSmall).false

/-- Projectively rescaled encoder traces have the same exact threshold
exclusion theorem. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (budgetSmall : factor * cylinderSpread blocks < threshold ^ 2) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold _root_.FiniteMeasure.Distribution.probability
  apply eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have squareSmall := (projectiveRealized_probe_separation_sq_le
    (pointsRealize atom member) witnessRealizes probe factor
      factorNonnegative sensitive).trans_lt budgetSmall
  have separationSmall := separation_lt_of_sq_lt_sq thresholdPositive
    squareSmall
  unfold _root_.FiniteMeasure.separationAtLeast
  simp only [decide_eq_false_iff_not]
  exact fun thresholdLe => (thresholdLe.trans_lt separationSmall).false

/-- Computed block count for making a squared-sensitive variance budget
smaller than a positive rational target. -/
def requiredSquaredVarianceBlockCount
    (target factor : Coordinate) : Nat :=
  requiredBlockCount (target / factor)

/-- Meeting the computed block count makes the sensitivity-scaled cylinder
spread strictly smaller than the variance target. -/
theorem scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
    {blocks : List Block} (target factor : Coordinate)
    (targetPositive : 0 < target) (factorPositive : 0 < factor)
    (enough : requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    factor * cylinderSpread blocks < target := by
  have quotientPositive : 0 < target / factor :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive factorPositive
  have spreadSmall : cylinderSpread blocks < target / factor :=
    cylinderSpread_lt_of_requiredBlockCount_le quotientPositive enough
  calc
    factor * cylinderSpread blocks < factor * (target / factor) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        factorPositive spreadSmall
    _ = target := by
      calc
        factor * (target / factor) = (target / factor) * factor :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = target := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          target factor factorPositive.ne'

/-- A computed finite block request makes every canonical-cylinder variance
smaller than a supplied positive rational target. -/
theorem realizedSquaredProbeVariance_lt_of_requested {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  (realizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
        target factor targetPositive factorPositive enough)

/-- The same computed variance request applies to projectively rescaled
encoder cylinders. -/
theorem projectiveRealizedSquaredProbeVariance_lt_of_requested {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredSquaredVarianceBlockCount target factor ≤
      blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  (projectiveRealizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
        target factor targetPositive factorPositive enough)

/-- A computed block count excludes a positive rational deviation threshold
exactly for canonical cylinders. -/
theorem realizedSquaredProbe_deviationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (enough : requiredSquaredVarianceBlockCount (threshold ^ 2) factor ≤
      blocks.length) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  exact realizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive.le sensitive threshold thresholdPositive
    (scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (threshold ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2)
      factorPositive enough)

/-- Projective encoder-facing version of exact finite threshold exclusion. -/
theorem projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (enough : requiredSquaredVarianceBlockCount (threshold ^ 2) factor ≤
      blocks.length) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  exact projectiveRealizedSquaredProbe_deviationProbability_eq_zero_of_budget_lt
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive.le sensitive threshold thresholdPositive
    (scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (threshold ^ 2) factor
      (RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive 2)
      factorPositive enough)

/-! ## Concrete nonconstant chordal-probe consequences -/

/-- Variance of the nonconstant distance-to-`omega` probe in one projective
encoder cylinder is at most twice its explicit CCL spread. -/
theorem projectiveRealizedChordalOmegaProbeVariance_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks witness)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes blocks (points atom.item)) :
    distribution.variance (fun item => chordalOmegaProbe (points item)) ≤
      2 * cylinderSpread blocks :=
  projectiveRealizedSquaredProbeVariance_le distribution blocks witness
    witnessRealizes points pointsRealize chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive

/-- An actual finite encoder run therefore gives a variance certificate for
every finite law supported by its emitted projective cylinder. -/
theorem encodedChordalOmegaProbeVariance_le {index : Type}
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item)) :
    distribution.variance (fun item => chordalOmegaProbe (points item)) ≤
      2 * cylinderSpread
        (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks :=
  projectiveRealizedChordalOmegaProbeVariance_le distribution
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point
    (CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero)
    points pointsRealize

end CCL.FiniteMeasure
