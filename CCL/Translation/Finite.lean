import mathlib.Tactic.QuotientFreeOmega
import CCL.Arithmetic.Enclosures

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace CCL.FiniteTranslation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

/-- Boundary information which a translation is not permitted to erase. -/
inductive BoundaryConvention where
  | closed
  | halfOpen
  | redundant
  | projective
deriving DecidableEq, Repr

/-- A positive rational squared-precision request. -/
structure Request where
  targetSq : Coordinate
  positive : 0 < targetSq

/-- The observable finite actions performed by one translation request. -/
structure Schedule where
  sourceRefinements : Nat
  emittedUnits : Nat
  arithmeticSteps : Nat
deriving DecidableEq, Repr

namespace Schedule

/-- The deliberately simple reference cost model: every displayed action has
unit cost.  More specialized realizers may expose sharper auxiliary bounds. -/
def work (schedule : Schedule) : Nat :=
  schedule.sourceRefinements + schedule.emittedUnits +
    schedule.arithmeticSteps

def zero : Schedule :=
  { sourceRefinements := 0
    emittedUnits := 0
    arithmeticSteps := 0 }

def add (left right : Schedule) : Schedule :=
  { sourceRefinements := left.sourceRefinements + right.sourceRefinements
    emittedUnits := left.emittedUnits + right.emittedUnits
    arithmeticSteps := left.arithmeticSteps + right.arithmeticSteps }

@[simp] theorem work_zero : zero.work = 0 := rfl

theorem work_add (left right : Schedule) :
    (left.add right).work = left.work + right.work := by
  change
    (left.sourceRefinements + right.sourceRefinements) +
          (left.emittedUnits + right.emittedUnits) +
        (left.arithmeticSteps + right.arithmeticSteps) =
      (left.sourceRefinements + left.emittedUnits + left.arithmeticSteps) +
        (right.sourceRefinements + right.emittedUnits + right.arithmeticSteps)
  omega

end Schedule

/-- The common finite-observation contract.  `precisionSq` is the native
squared gauge of the representation; its interpretation is documented by each
instance rather than being forced to be a Euclidean diameter. -/
structure FiniteRepresentation where
  Observation : Type
  Possible : Observation → Gaussian → Prop
  witness : Observation → Gaussian
  witness_possible : ∀ observation, Possible observation (witness observation)
  Refines : Observation → Observation → Prop
  refines_refl : ∀ observation, Refines observation observation
  refines_trans : ∀ {inner middle outer},
    Refines inner middle → Refines middle outer → Refines inner outer
  possible_persists : ∀ {inner outer value},
    Refines inner outer → Possible inner value → Possible outer value
  precisionSq : Observation → Coordinate
  precisionSq_nonneg : ∀ observation, 0 ≤ precisionSq observation
  boundary : BoundaryConvention

namespace FiniteRepresentation

/-- Two observations are finitely compatible when one displayed rational
reading is admitted by both. -/
def Compatible (representation : FiniteRepresentation)
    (left right : representation.Observation) : Prop :=
  ∃ value : Gaussian,
    representation.Possible left value ∧
      representation.Possible right value

theorem compatible_refl (representation : FiniteRepresentation)
    (observation : representation.Observation) :
    representation.Compatible observation observation :=
  ⟨representation.witness observation,
    representation.witness_possible observation,
    representation.witness_possible observation⟩

theorem compatible_symm {representation : FiniteRepresentation}
    {left right : representation.Observation}
    (compatible : representation.Compatible left right) :
    representation.Compatible right left := by
  rcases compatible with ⟨value, leftPossible, rightPossible⟩
  exact ⟨value, rightPossible, leftPossible⟩

theorem compatible_of_refines {representation : FiniteRepresentation}
    {inner outer : representation.Observation}
    (refines : representation.Refines inner outer) :
    representation.Compatible inner outer :=
  ⟨representation.witness inner,
    representation.witness_possible inner,
    representation.possible_persists refines
      (representation.witness_possible inner)⟩

end FiniteRepresentation

/-- A direct conversion of one fixed observation.  It cannot claim precision
which was not already supplied by the source. -/
structure ObservationMap
    (source target : FiniteRepresentation) where
  map : source.Observation → target.Observation
  covers : ∀ {observation value},
    source.Possible observation value →
      target.Possible (map observation) value
  coherent : ∀ {inner outer}, source.Refines inner outer →
    target.Compatible (map inner) (map outer)
  precisionLoss : source.Observation → Coordinate
  precisionLoss_nonneg : ∀ observation, 0 ≤ precisionLoss observation
  precision_le : ∀ observation,
    target.precisionSq (map observation) ≤
      source.precisionSq observation + precisionLoss observation
  schedule : source.Observation → Schedule
  costBound : source.Observation → Nat
  cost_le : ∀ observation, (schedule observation).work ≤ costBound observation

namespace ObservationMap

def identity (representation : FiniteRepresentation) :
    ObservationMap representation representation where
  map observation := observation
  covers possible := possible
  coherent refines := FiniteRepresentation.compatible_of_refines refines
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by simp
  schedule _ := Schedule.zero
  costBound _ := 0
  cost_le _ := Nat.le_refl 0

def comp {first middle last : FiniteRepresentation}
    (right : ObservationMap middle last)
    (left : ObservationMap first middle) :
    ObservationMap first last where
  map observation := right.map (left.map observation)
  covers possible := right.covers (left.covers possible)
  coherent refines := by
    rcases left.coherent refines with
      ⟨value, innerPossible, outerPossible⟩
    exact ⟨value, right.covers innerPossible, right.covers outerPossible⟩
  precisionLoss observation :=
    left.precisionLoss observation +
      right.precisionLoss (left.map observation)
  precisionLoss_nonneg observation :=
    add_nonneg (left.precisionLoss_nonneg observation)
      (right.precisionLoss_nonneg (left.map observation))
  precision_le observation := by
    calc
      last.precisionSq (right.map (left.map observation)) ≤
          middle.precisionSq (left.map observation) +
            right.precisionLoss (left.map observation) :=
        right.precision_le (left.map observation)
      _ ≤ (first.precisionSq observation +
            left.precisionLoss observation) +
            right.precisionLoss (left.map observation) :=
        add_le_add (left.precision_le observation) le_rfl
      _ = first.precisionSq observation +
          (left.precisionLoss observation +
            right.precisionLoss (left.map observation)) := by
        rw [add_assoc]
  schedule observation :=
    (left.schedule observation).add
      (right.schedule (left.map observation))
  costBound observation :=
    left.costBound observation + right.costBound (left.map observation)
  cost_le observation := by
    rw [Schedule.work_add]
    exact Nat.add_le_add (left.cost_le observation)
      (right.cost_le (left.map observation))

end ObservationMap

/-- A finite family of target observations used when a boundary prevents one
target observation from covering every source reading. -/
structure FiniteCover
    (source target : FiniteRepresentation)
    (observation : source.Observation) where
  observations : List target.Observation
  nonempty : observations ≠ []
  covers : ∀ {value : Gaussian}, source.Possible observation value →
    ∃ targetObservation,
      targetObservation ∈ observations ∧
        target.Possible targetObservation value

/-- One certified response of a progressive finite realizer.  Both directions
of the reading relation are explicit; enclosure-only clients may choose a
relation whose reverse direction contains the required witness data. -/
structure TranslationResult
    (source target : FiniteRepresentation)
    (observation : source.Observation) (request : Request) where
  source' : source.Observation
  output : target.Observation
  source_refines : source.Refines source' observation
  relates : Gaussian → Gaussian → Prop
  source_to_target : ∀ {sourceValue : Gaussian},
    source.Possible source' sourceValue →
      ∃ targetValue : Gaussian,
        target.Possible output targetValue ∧ relates sourceValue targetValue
  target_to_source : ∀ {targetValue : Gaussian},
    target.Possible output targetValue →
      ∃ sourceValue : Gaussian,
        source.Possible source' sourceValue ∧ relates sourceValue targetValue
  precisionLoss : Coordinate
  precisionLoss_nonneg : 0 ≤ precisionLoss
  precision : target.precisionSq output <
    request.targetSq + precisionLoss
  schedule : Schedule
  costBound : Nat
  cost_le : schedule.work ≤ costBound

/-- A request-driven translation.  Coherence is derived below from the two
explicit reading directions rather than incorrectly demanding that approximate
target observations share the same rational representative. -/
structure FiniteRealizer
    (source target : FiniteRepresentation) where
  translate : (observation : source.Observation) → (request : Request) →
    TranslationResult source target observation request

namespace FiniteRealizer

/-- Relational coherence of two independent finite requests.  A common source
reading is transported to one explicitly related reading in each output.  If
both result relations are equality, the two target observations are literally
compatible in `FiniteRepresentation.Compatible`. -/
theorem coherent {source target : FiniteRepresentation}
    (realizer : FiniteRealizer source target)
    (observation : source.Observation) (leftRequest rightRequest : Request)
    (sourceCompatible : source.Compatible
      (realizer.translate observation leftRequest).source'
      (realizer.translate observation rightRequest).source') :
    ∃ sourceValue : Gaussian,
      source.Possible
          (realizer.translate observation leftRequest).source' sourceValue ∧
        source.Possible
          (realizer.translate observation rightRequest).source' sourceValue ∧
        (∃ leftValue : Gaussian,
          target.Possible
              (realizer.translate observation leftRequest).output leftValue ∧
            (realizer.translate observation leftRequest).relates
              sourceValue leftValue) ∧
        (∃ rightValue : Gaussian,
          target.Possible
              (realizer.translate observation rightRequest).output rightValue ∧
            (realizer.translate observation rightRequest).relates
              sourceValue rightValue) := by
  rcases sourceCompatible with
    ⟨sourceValue, leftSourcePossible, rightSourcePossible⟩
  rcases (realizer.translate observation leftRequest).source_to_target
      leftSourcePossible with ⟨leftValue, leftPossible, leftRelated⟩
  rcases (realizer.translate observation rightRequest).source_to_target
      rightSourcePossible with ⟨rightValue, rightPossible, rightRelated⟩
  exact ⟨sourceValue, leftSourcePossible, rightSourcePossible,
    ⟨leftValue, leftPossible, leftRelated⟩,
    ⟨rightValue, rightPossible, rightRelated⟩⟩

end FiniteRealizer

end CCL.FiniteTranslation
