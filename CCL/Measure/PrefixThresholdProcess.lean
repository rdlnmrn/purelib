import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixProcess
import CCL.Measure.PrefixThreshold

/-!
# Progressive threshold probabilities from finite CCL prefixes

A lower-threshold event can be decided after one finite prefix request when
each displayed witness probe has an explicit positive rational margin from
the threshold.  The requested completed-block count makes every current
probe enclosure narrower than that margin, so every finite row is classified
and the resulting probability enclosure has width zero.  No eventual CCL
point or infinite refinement sequence is introduced.
-/

namespace CCL.FiniteMeasure

/-- A sufficiently narrow completed-prefix probe enclosure is resolved by
an explicit rational margin separating its witness value from the threshold. -/
theorem completedPrefixProbeBound_thresholdResolved_of_margin
    {blocks : List Block} (witness : Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated :
      threshold + margin ≤ probe witness ∨
        probe witness + margin ≤ threshold)
    (enough : requiredProbeBlockCount margin factor ≤ blocks.length) :
    _root_.FiniteMeasure.ThresholdResolved
      (completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive)
      threshold := by
  let radius := factor * cylinderSpread blocks
  have radiusNonnegative : 0 ≤ radius :=
    RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
      (cylinderSpread_nonneg blocks)
  have widthSmall := completedPrefixProbeBound_width_lt_requested
    witness witnessRealizes probe factor factorPositive sensitive
    margin marginPositive enough
  have radiusSmall : radius < margin := by
    calc
      radius = radius + 0 := by ring1
      _ ≤ radius + radius := add_le_add le_rfl radiusNonnegative
      _ = 2 * radius := by ring1
      _ = (completedPrefixProbeBound blocks witness witnessRealizes probe
          factor factorPositive.le sensitive).width := by
        rw [completedPrefixProbeBound_width]
      _ < margin := widthSmall
  change threshold ≤ probe witness - radius ∨
    probe witness + radius < threshold
  rcases separated with inside | outside
  · apply Or.inl
    apply (le_sub_iff_add_le).2
    exact (RFAP.ConstructiveFraction.add_lt_add_left_direct
      radiusSmall threshold).le.trans inside
  · apply Or.inr
    exact (RFAP.ConstructiveFraction.add_lt_add_left_direct
      radiusSmall (probe witness)).trans_le outside

namespace PrefixFamilyProcess

/-- Current rational enclosure of a probe on one process-controlled CCL
prefix row. -/
def probeRange {ι : Type} (process : PrefixFamilyProcess ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (item : ι) : _root_.FiniteMeasure.Bound :=
  completedPrefixProbeBound (process.blocks state item)
    (process.witness item) (process.realizes state item)
    probe factor factorNonnegative sensitive

/-- Current finite threshold-probability enclosure of a process-controlled
family of CCL prefixes. -/
def probeThresholdBound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (state : process.State) :
    _root_.FiniteMeasure.Bound :=
  _root_.FiniteMeasure.eventBound
    (distribution.thresholdFrontier
      (process.probeRange probe factor factorNonnegative sensitive state)
      threshold)

private theorem requestedProbeThresholdResolved {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (atom : _root_.FiniteMeasure.Weighted ι)
    (member : atom ∈ distribution.atoms) :
    _root_.FiniteMeasure.ThresholdResolved
      (process.probeRange probe factor factorPositive.le sensitive
        (process.request state (requiredProbeBlockCount margin factor))
        atom.item)
      threshold := by
  unfold probeRange
  exact completedPrefixProbeBound_thresholdResolved_of_margin
    (process.witness atom.item)
    (process.realizes
      (process.request state (requiredProbeBlockCount margin factor))
      atom.item)
    probe factor factorPositive sensitive threshold margin marginPositive
    (separated atom member)
    (process.request_length state
      (requiredProbeBlockCount margin factor) atom.item)

/-- A positive rational witness margin turns process-controlled finite CCL
prefixes into an exact finite threshold-probability process.  Every request
performs the same computable resolving block request; the resulting bound has
zero width and hence satisfies every supplied positive accuracy target. -/
def toProbeThresholdProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold) :
    _root_.FiniteMeasure.BoundProcess where
  State := process.State
  bound state := process.probeThresholdBound distribution probe factor
    factorPositive.le sensitive threshold state
  initial := process.initial
  request state epsilon positive :=
    process.request state (requiredProbeBlockCount margin factor)
  request_refines state epsilon positive := by
    unfold probeThresholdBound
    apply distribution.thresholdFrontier_eventBound_refines
    intro atom member
    rcases process.request_extends state
      (requiredProbeBlockCount margin factor) atom.item with
      ⟨suffix, equal⟩
    unfold probeRange
    have spreadLe :
        cylinderSpread
            (process.blocks
              (process.request state
                (requiredProbeBlockCount margin factor)) atom.item) ≤
          cylinderSpread (process.blocks state atom.item) := by
      rw [equal]
      exact cylinderSpread_le_of_append
        (process.blocks state atom.item) suffix
    have scaledLe :
        factor * cylinderSpread
            (process.blocks
              (process.request state
                (requiredProbeBlockCount margin factor)) atom.item) ≤
          factor * cylinderSpread (process.blocks state atom.item) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaledLe
  accurate state epsilon positive := by
    unfold probeThresholdBound
    rw [distribution.thresholdFrontier_width_eq_zero_of_resolved]
    · exact positive
    · intro atom member
      exact process.requestedProbeThresholdResolved distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated
        state atom member
  refinesInitial state := by
    unfold probeThresholdBound
    apply distribution.thresholdFrontier_eventBound_refines
    intro atom member
    rcases process.extendsInitial state atom.item with ⟨suffix, equal⟩
    unfold probeRange
    have spreadLe : cylinderSpread (process.blocks state atom.item) ≤
        cylinderSpread (process.blocks process.initial atom.item) := by
      rw [equal]
      exact cylinderSpread_le_of_append
        (process.blocks process.initial atom.item) suffix
    have scaledLe : factor * cylinderSpread (process.blocks state atom.item) ≤
        factor * cylinderSpread (process.blocks process.initial atom.item) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaledLe

/-- The resolving request has exactly zero probability-enclosure width. -/
theorem request_probeThreshold_width_eq_zero {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeThresholdProcess distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound
      ((process.toProbeThresholdProcess distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated)
        |>.request state epsilon positive)).width = 0 := by
  unfold toProbeThresholdProcess probeThresholdBound
  apply distribution.thresholdFrontier_width_eq_zero_of_resolved
  intro atom member
  exact process.requestedProbeThresholdResolved distribution probe factor
    factorPositive sensitive threshold margin marginPositive separated
    state atom member

/-- Every explicitly supplied realization family has its exact finite
threshold probability inside the process's current enclosure. -/
theorem probability_mem_toProbeThresholdProcess_bound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeThresholdProcess distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound state).Contains
      (distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (points item))) := by
  unfold toProbeThresholdProcess probeThresholdBound
  apply distribution.probability_mem_thresholdFrontier
  intro atom member
  unfold probeRange
  exact completedPrefixProbeBound_contains
    (process.blocks state atom.item) (process.witness atom.item)
    (process.realizes state atom.item) probe factor factorPositive.le sensitive
    (pointsRealize atom member)

/-- After the finite resolving request, every two realization families still
admitted by the returned prefixes have exactly the same threshold-event
probability.  The displayed separation margin is the constructive stability
hypothesis for this discontinuous observable. -/
theorem request_probeThreshold_probabilities_eq {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Proj)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeThresholdProcess distribution probe factor
            factorPositive sensitive threshold margin marginPositive separated)
            |>.request state epsilon positive) atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeThresholdProcess distribution probe factor
            factorPositive sensitive threshold margin marginPositive separated)
            |>.request state epsilon positive) atom.item)
        (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  let thresholdProcess := process.toProbeThresholdProcess distribution probe
    factor factorPositive sensitive threshold margin marginPositive separated
  let requested := thresholdProcess.request state epsilon positive
  apply _root_.FiniteMeasure.Bound.eq_of_contains_of_contains_of_width_eq_zero
    (bound := thresholdProcess.bound requested)
  · exact process.probability_mem_toProbeThresholdProcess_bound distribution
      probe factor factorPositive sensitive threshold margin marginPositive
      separated requested leftPoints leftRealize
  · exact process.probability_mem_toProbeThresholdProcess_bound distribution
      probe factor factorPositive sensitive threshold margin marginPositive
      separated requested rightPoints rightRealize
  · exact process.request_probeThreshold_width_eq_zero distribution probe
      factor factorPositive sensitive threshold margin marginPositive separated
      state epsilon positive

end PrefixFamilyProcess

end CCL.FiniteMeasure
