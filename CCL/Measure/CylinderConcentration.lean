import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixCenteredVarianceProcess

/-!
# Finite concentration inside one completed CCL cylinder

A finite probability law of explicitly supplied realizations of one completed
prefix is concentrated because the CCL cylinder has a rational diameter.
The statements quantify only over the displayed finite distribution and its
realization certificates; no distribution on the full cylinder is formed.
-/

namespace CCL.FiniteMeasure

/-- Squared deviation about the displayed witness is uniformly bounded by
the squared CCL probe radius. -/
theorem realizedProbeVarianceAroundWitness_le_radius_sq {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    distribution.varianceAround (fun item => probe (points item))
        (probe witness) ≤
      (factor * cylinderSpread blocks) ^ 2 := by
  change distribution.expectation (fun item =>
      (probe (points item) - probe witness) ^ 2) ≤ _
  calc
    distribution.expectation (fun item =>
          (probe (points item) - probe witness) ^ 2) ≤
        distribution.expectation
          (fun _ => (factor * cylinderSpread blocks) ^ 2) := by
      apply distribution.expectation_mono
      intro atom member
      have separationLe := realized_probe_separation_le
        (pointsRealize atom member) witnessRealizes probe factor
          factorNonnegative sensitive
      have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
        (_root_.FiniteMeasure.rationalSeparation_nonneg
          (probe (points atom.item)) (probe witness)) separationLe 2
      rw [_root_.FiniteMeasure.rationalSeparation_sq] at powered
      exact powered
    _ = (factor * cylinderSpread blocks) ^ 2 :=
      distribution.expectation_constant _

/-- If every row of a finite law realizes one completed prefix, the variance
of a sensitive rational probe is at most the squared prefix radius around one
displayed witness. -/
theorem realizedProbeVariance_le_radius_sq {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    distribution.variance (fun item => probe (points item)) ≤
      (factor * cylinderSpread blocks) ^ 2 := by
  let value := fun item => probe (points item)
  let center := probe witness
  exact (distribution.variance_le_varianceAround value center).trans
    (realizedProbeVarianceAroundWitness_le_radius_sq distribution blocks
      witness witnessRealizes points pointsRealize probe factor
      factorNonnegative sensitive)

private theorem eventWeight_eq_zero_of_false_on_atoms {ι : Type}
    (atoms : List (_root_.FiniteMeasure.Weighted ι)) (event : ι → Bool)
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

/-- If the displayed threshold is strictly larger than one prefix's probe
radius, no row of any finite law supported by that cylinder can cross it. -/
theorem realizedProbe_deviationProbability_eq_zero_of_radius_lt {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (radiusSmall : factor * cylinderSpread blocks < threshold) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  unfold _root_.FiniteMeasure.Distribution.probability
  apply eventWeight_eq_zero_of_false_on_atoms
  intro atom member
  have separationSmall :=
    (realized_probe_separation_le (pointsRealize atom member)
      witnessRealizes probe factor factorNonnegative sensitive).trans_lt
      radiusSmall
  unfold _root_.FiniteMeasure.separationAtLeast
  simp only [decide_eq_false_iff_not]
  exact fun thresholdLe => (thresholdLe.trans_lt separationSmall).false

/-- A computable completed-block budget resolves every witness-centred
deviation event at a positive rational threshold exactly, with probability
zero for all finite laws supported by the displayed cylinder. -/
theorem realizedProbe_deviationProbability_eq_zero_of_requested {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (enough : requiredProbeBlockCount threshold factor ≤ blocks.length) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 := by
  have widthSmall := completedPrefixProbeBound_width_lt_requested witness
    witnessRealizes probe factor factorPositive sensitive threshold
      thresholdPositive enough
  have radiusNonnegative : 0 ≤ factor * cylinderSpread blocks :=
    RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
      (cylinderSpread_nonneg blocks)
  have radiusLeWidth : factor * cylinderSpread blocks ≤
      (completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width := by
    rw [completedPrefixProbeBound_width]
    calc
      factor * cylinderSpread blocks =
          0 + factor * cylinderSpread blocks := by ring1
      _ ≤ factor * cylinderSpread blocks +
          factor * cylinderSpread blocks :=
        RFAP.ConstructiveFraction.add_le_add_direct radiusNonnegative le_rfl
      _ = 2 * (factor * cylinderSpread blocks) := by ring1
  exact realizedProbe_deviationProbability_eq_zero_of_radius_lt distribution
    blocks witness witnessRealizes points pointsRealize probe factor
    factorPositive.le sensitive threshold (radiusLeWidth.trans_lt widthSmall)

private theorem half_lt_self {target : Coordinate} (positive : 0 < target) :
    target / 2 < target := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    target = target * 1 := by ring1
    _ < target * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

/-- A computable completed-block budget forces the variance of every finite
law supported by the displayed cylinder below any positive rational target.
The half-power target avoids introducing a square root. -/
theorem realizedProbeVariance_lt_of_requested {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (blocks : List Block) (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredProbeBlockCount
      (PrefixFamilyProcess.centeredVarianceMeanTarget target)
      factor ≤ blocks.length) :
    distribution.variance (fun item => probe (points item)) < target := by
  let radius := factor * cylinderSpread blocks
  let meanTarget := PrefixFamilyProcess.centeredVarianceMeanTarget target
  have radiusNonnegative : 0 ≤ radius :=
    RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
      (cylinderSpread_nonneg blocks)
  have widthSmall :
      (completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width < meanTarget :=
    completedPrefixProbeBound_width_lt_requested witness witnessRealizes probe
      factor factorPositive sensitive meanTarget
      (PrefixFamilyProcess.centeredVarianceMeanTarget_positive targetPositive)
      enough
  have radiusLeWidth : radius ≤
      (completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive).width := by
    rw [completedPrefixProbeBound_width]
    change radius ≤ 2 * radius
    calc
      radius = 0 + radius := by ring1
      _ ≤ radius + radius :=
        RFAP.ConstructiveFraction.add_le_add_direct radiusNonnegative le_rfl
      _ = 2 * radius := by ring1
  have radiusLeTarget : radius ≤ meanTarget :=
    (radiusLeWidth.trans_lt widthSmall).le
  have radiusSquareLe : radius ^ 2 ≤ meanTarget ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusNonnegative
      radiusLeTarget 2
  exact (realizedProbeVariance_le_radius_sq distribution blocks witness
    witnessRealizes points pointsRealize probe factor factorPositive.le
    sensitive).trans_lt
      (radiusSquareLe.trans_lt
        ((PrefixFamilyProcess.centeredVarianceMeanTarget_sq_lt_half
            targetPositive).trans
          (half_lt_self targetPositive)))

end CCL.FiniteMeasure
