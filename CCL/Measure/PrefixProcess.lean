import CCL.Measure.PrefixProfile

/-!
# Finite-request processes of CCL prefixes

This module packages the operational use of progressively longer finite CCL
prefixes.  A request supplies a natural-number block count and returns one
new finite state whose displayed prefixes extend the current ones and meet
that count.  There is no stream of states and no eventual CCL value.
-/

namespace CCL.FiniteMeasure

/-- An executable finite-prefix controller for a family indexed by `ι`.
Every state supplies explicit prefix blocks, a fixed rational-projective
witness for each index, and a finite realization certificate. -/
structure PrefixFamilyProcess (ι : Type) where
  State : Type
  blocks : State → ι → List Block
  witness : ι → Proj
  realizes : ∀ state item,
    CCL.Cylinder.Realizes (blocks state item) (witness item)
  initial : State
  request : State → Nat → State
  request_extends : ∀ state count item,
    ∃ suffix, blocks (request state count) item = blocks state item ++ suffix
  request_length : ∀ state count item,
    count ≤ (blocks (request state count) item).length
  extendsInitial : ∀ state item,
    ∃ suffix, blocks state item = blocks initial item ++ suffix

namespace PrefixFamilyProcess

/-- Turn finite CCL prefix requests into pointwise rational probe-enclosure
requests on one fixed finite probability table. -/
def toProbePointwiseProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.PointwiseEnclosureProcess distribution where
  State := process.State
  ranges state item := completedPrefixProbeBound
    (process.blocks state item) (process.witness item)
    (process.realizes state item) probe factor factorPositive.le sensitive
  initial := process.initial
  request state epsilon positive :=
    process.request state (requiredProbeBlockCount epsilon factor)
  request_refines state epsilon positive atom member := by
    rcases process.request_extends state
      (requiredProbeBlockCount epsilon factor) atom.item with
      ⟨suffix, equal⟩
    have spreadLe :
        cylinderSpread
            (process.blocks
              (process.request state
                (requiredProbeBlockCount epsilon factor)) atom.item) ≤
          cylinderSpread (process.blocks state atom.item) := by
      rw [equal]
      exact cylinderSpread_le_of_append
        (process.blocks state atom.item) suffix
    have scaledLe :
        factor * cylinderSpread
            (process.blocks
              (process.request state
                (requiredProbeBlockCount epsilon factor)) atom.item) ≤
          factor * cylinderSpread (process.blocks state atom.item) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaledLe
  accurate state epsilon positive atom member := by
    exact (completedPrefixProbeBound_width_lt_requested
      (process.witness atom.item)
      (process.realizes
        (process.request state (requiredProbeBlockCount epsilon factor))
        atom.item)
      probe factor factorPositive sensitive epsilon positive
      (process.request_length state
        (requiredProbeBlockCount epsilon factor) atom.item)).le
  refinesInitial state atom member := by
    rcases process.extendsInitial state atom.item with ⟨suffix, equal⟩
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

/-- Finite CCL prefix requests therefore induce an arbitrary-accuracy
rational process for the finite expectation of the supplied probe. -/
def toProbeExpectationProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.BoundProcess :=
  (process.toProbePointwiseProcess distribution probe factor
    factorPositive sensitive).toExpectationBoundProcess

/-- Every explicitly supplied family of realizations at one finite state has
its exact rational probe expectation inside the process's current bound. -/
theorem expectation_mem_probeExpectationProcess_bound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.expectation fun item => probe (points item)) := by
  apply (process.toProbePointwiseProcess distribution probe factor
    factorPositive sensitive).expectation_mem
  intro atom member
  exact completedPrefixProbeBound_contains
    (process.blocks state atom.item) (process.witness atom.item)
    (process.realizes state atom.item) probe factor factorPositive.le
    sensitive (pointsRealize atom member)

/-- One finite rational request makes the complete probe-expectation
enclosure narrower than the supplied tolerance. -/
theorem request_probeExpectation_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  (process.toProbeExpectationProcess distribution probe factor
    factorPositive sensitive).accurate state epsilon positive

/-- One finite request makes the expectation of every realization family
admitted by the returned prefixes close to the fixed, computable witness
expectation. -/
theorem request_probeExpectation_separation_witness_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item => probe (process.witness item)) <
      epsilon := by
  let boundProcess := process.toProbeExpectationProcess distribution probe
    factor factorPositive sensitive
  let requested := boundProcess.request state epsilon positive
  apply boundProcess.request_rationalSeparation_lt state epsilon positive
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested points pointsRealize
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested process.witness
      (fun atom member => process.realizes requested atom.item)

/-- After one computed finite request, the expectations of every two
realization families admitted by the returned prefixes are within the
requested rational separation. -/
theorem request_probeExpectations_pairwise_separation_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Proj)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => probe (leftPoints item))
        (distribution.expectation fun item => probe (rightPoints item)) <
      epsilon := by
  let boundProcess := process.toProbeExpectationProcess distribution probe
    factor factorPositive sensitive
  let requested := boundProcess.request state epsilon positive
  apply boundProcess.request_rationalSeparation_lt state epsilon positive
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested leftPoints leftRealize
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested rightPoints rightRealize

end PrefixFamilyProcess

end CCL.FiniteMeasure
