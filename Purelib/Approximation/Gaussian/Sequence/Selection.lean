module

public import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stable selection among finitely separated approximation programs

Finite localization supplies an original candidate program near each
sufficiently refined source sample. A positive uniform separation budget and
the source's own coherence prove that every small later localization has the
same original candidate index. Further requests compare those same two
programs at unrelated starting indices.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.Selection

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)

variable {count : Nat} {candidates : Fin count → ApproximationData}

set_option genInjectivity false in
/-- A positive squared gap after the retained starts of distinct original finite candidate programs. -/
structure Separated (candidates : Fin count → ApproximationData) where
  /-- The original family's retained common squared separation budget. -/
  gap : Rational
  /-- The common budget is positive. -/
  positive : 0 < gap
  /-- The actual original candidate stage from which the common gap is certified. -/
  starts : Fin count → Nat
  /-- Distinct original candidate tails keep the same lower budget at every permitted original sample pair. -/
  lower : ∀ first second, first ≠ second → ∀ firstIndex secondIndex,
    starts first ≤ firstIndex → starts second ≤ secondIndex →
    gap ≤ normSq ((candidates first).sample firstIndex - (candidates second).sample secondIndex)

constructive_injectivity Separated

set_option genInjectivity false in
/-- A retained original candidate whose actual tail readings are near one displayed finite point. -/
structure Nearby (candidates : Fin count → ApproximationData) (point : Canonical) (target : Rational) where
  /-- The bounded index in the original candidate family. -/
  owner : Fin count
  /-- The actual starting stage of the retained original candidate tail. -/
  index : Nat
  /-- Every later sample of that same original candidate meets the displayed squared-distance request. -/
  close : ∀ later, index ≤ later → normSq ((candidates owner).sample later - point) < target

constructive_injectivity Nearby

set_option genInjectivity false in
/-- One computed source refinement stage with localization for every later original sample. -/
structure CoverAt (source : ApproximationData) (candidates : Fin count → ApproximationData)
    (current : Nat) (target : Rational) where
  /-- The actual sufficient source stage returned by the localization procedure. -/
  index : Nat
  /-- The procedure preserves the original requested starting stage. -/
  index_ge : current ≤ index
  /-- Each later original source sample has a nearby original candidate at the same retained target. -/
  locate : ∀ later, index ≤ later → Nearby candidates (source.sample later) target

constructive_injectivity CoverAt

set_option genInjectivity false in
/-- Executable finite localization of an original source program into its original candidate family. -/
structure Coverage (source : ApproximationData) (candidates : Fin count → ApproximationData) where
  /-- Compute sufficient refinement and later-sample localization for every positive squared-distance request. -/
  prepare : ∀ current target, 0 < target → CoverAt source candidates current target

constructive_injectivity Coverage

namespace Coverage

set_option genInjectivity false in
/-- One original coverage result and the subsequent source refinement for the same request.

The complete cover and computed source index are retained with their defining
equalities. A supplied nearby reading can therefore consume this exact request
without executing its localization function again.
-/
structure Request {source : ApproximationData} (coverage : Coverage source candidates)
    (current : Nat) (target : Rational) where
  /-- The requested squared tolerance is positive. -/
  positive : 0 < target
  /-- The original coverage procedure's complete retained result. -/
  cover : CoverAt source candidates current target
  /-- The retained cover is the same original request result. -/
  cover_eq : cover = coverage.prepare current target positive
  /-- The original source refinement index after this cover. -/
  index : Nat
  /-- The index is the original source refiner's result at the retained cover. -/
  index_eq : index = source.refineIndex cover.index target positive

constructive_injectivity Request

/-- Compute and retain one original coverage result and its subsequent source refinement index. -/
@[expose] def request {source : ApproximationData} (coverage : Coverage source candidates)
    (current : Nat) (target : Rational) (positive : 0 < target) : Request coverage current target :=
  let cover := coverage.prepare current target positive
  let index := source.refineIndex cover.index target positive
  ⟨positive, cover, rfl, index, rfl⟩

namespace Request

variable {source : ApproximationData} {coverage : Coverage source candidates}
  {current : Nat} {target : Rational}

/-- The retained source index is no earlier than its actual coverage index. -/
theorem index_ge (request : Request coverage current target) : request.cover.index ≤ request.index := by
  rewrite [request.index_eq]
  exact source.refineIndex_ge request.cover.index target request.positive

/-- The retained source index pays the original requested starting stage. -/
theorem current_ge (request : Request coverage current target) : current ≤ request.index :=
  request.cover.index_ge.trans request.index_ge

/-- The retained source index meets the same original positive squared tolerance. -/
theorem accurate (request : Request coverage current target) : source.radiusSq request.index < target := by
  rewrite [request.index_eq]
  exact source.refineIndex_accurate request.cover.index target request.positive

/-- Localize the same original source sample through the complete retained coverage result. -/
@[expose] def locate (request : Request coverage current target) :
    Nearby candidates (source.sample request.index) target :=
  request.cover.locate request.index request.index_ge

end Request

end Coverage

set_option genInjectivity false in
/-- One actual source anchor and original candidate localization below the family's separation budget.

The source's own refinement meets one sixteenth of the same retained gap.
The nearby candidate and anchor remain the actual original readings used by
later selection and all-input comparisons.
-/
structure Anchor (source : ApproximationData) (separated : Separated candidates) where
  /-- The actual refined original source index used to select the candidate. -/
  index : Nat
  /-- The source's same-index movement allowance is below one sixteenth of the original gap. -/
  radiusSmall : source.radiusSq index < separated.gap / 16
  /-- The retained nearby original candidate at this same original source reading. -/
  nearby : Nearby candidates (source.sample index) (separated.gap / 16)

constructive_injectivity Anchor

namespace Anchor

/-- Construct the original selection anchor from an authenticated retained nearby reading.

The request retains the original coverage and source refinement. The supplied
complete nearby record is exactly its localization result, so construction
reads those retained values without executing localization again.
-/
@[expose] def ofNearby (source : ApproximationData) (separated : Separated candidates)
    (coverage : Coverage source candidates)
    (request : Coverage.Request coverage 0 (separated.gap / 16))
    (nearby : { value : Nearby candidates (source.sample request.index) (separated.gap / 16) //
      value = request.locate }) : Anchor source separated :=
  ⟨request.index, request.accurate, nearby.val⟩

/-- Compute a stable-selection anchor through the same original localization and source-refinement programs. -/
def ofCoverage (source : ApproximationData) (separated : Separated candidates)
    (coverage : Coverage source candidates) : Anchor source separated :=
  let target := separated.gap / 16
  have positive : 0 < target := Fraction.Order.Field.div_pos_direct separated.positive (by decide)
  let request := coverage.request 0 target positive
  ofNearby source separated coverage request ⟨request.locate, rfl⟩

/-- An authenticated retained nearby reading preserves the complete original selection anchor. -/
theorem ofNearby_eq (source : ApproximationData) (separated : Separated candidates)
    (coverage : Coverage source candidates)
    (request : Coverage.Request coverage 0 (separated.gap / 16))
    (nearby : { value : Nearby candidates (source.sample request.index) (separated.gap / 16) //
      value = request.locate }) :
    ofNearby source separated coverage request nearby = ofCoverage source separated coverage := by
  rcases request with ⟨positive, cover, coverEq, index, indexEq⟩
  cases coverEq
  cases indexEq
  rcases nearby with ⟨nearby, nearbyEq⟩
  cases nearbyEq
  rfl

private theorem normSq_sub_reverse (first second : Canonical) :
    normSq (first - second) = normSq (second - first) := by
  have reversed : first - second = -(second - first) := by ring0
  rewrite [reversed, Norm.Basic.normSq_neg]
  rfl

/-- Every sufficiently small later localization selects the same original candidate index as the retained anchor. -/
theorem sameOwner {source : ApproximationData} {separated : Separated candidates}
    (anchor : Anchor source separated) {later : Nat} (later_ge : anchor.index ≤ later)
    {target : Rational} (small : target ≤ separated.gap / 16)
    (nearby : Nearby candidates (source.sample later) target) : nearby.owner = anchor.nearby.owner := by
  by_cases same : nearby.owner = anchor.nearby.owner
  · exact same
  · let nearStart := Nat.max anchor.nearby.index nearby.index
    let separationStart := Nat.max (separated.starts anchor.nearby.owner) (separated.starts nearby.owner)
    let common := Nat.max nearStart separationStart
    have nearGe : nearStart ≤ common := Data.Nat.Order.le_max_left _ _
    have separationGe : separationStart ≤ common := Data.Nat.Order.le_max_right _ _
    have firstNear := anchor.nearby.close common ((Data.Nat.Order.le_max_left _ _).trans nearGe)
    have secondNear := (nearby.close common ((Data.Nat.Order.le_max_right _ _).trans nearGe)).trans_le small
    have movement := (source.later_close later_ge).trans_lt anchor.radiusSmall
    let first := (candidates anchor.nearby.owner).sample common
    let second := (candidates nearby.owner).sample common
    have firstDistance : normSq (first - source.sample anchor.index) < separated.gap / 16 := firstNear
    have secondDistance : normSq (source.sample later - second) < separated.gap / 16 := by
      rewrite [normSq_sub_reverse]
      exact secondNear
    have middleDistance : normSq (source.sample anchor.index - source.sample later) < separated.gap / 16 := by
      rewrite [normSq_sub_reverse]
      exact movement
    have distance : normSq (first - second) < 9 * (separated.gap / 16) := by
      have identity : first - second = (first - source.sample anchor.index) +
          (source.sample anchor.index - source.sample later) + (source.sample later - second) := by ring0
      rewrite [identity]
      exact (Norm.Sum.Indexed.normSq_add_add_le _ _ _).trans_lt
        ((Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Order.Arithmetic.add_lt_add_direct
            (Order.Arithmetic.add_lt_add_direct firstDistance middleDistance) secondDistance)).trans_eq
          (by ring0))
    have nineSixteenths : 9 * (separated.gap / 16) < separated.gap := by
      have scaled := Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (show (9 / 16 : Rational) < 1 by decide) separated.positive
      have identity : (9 / 16 : Rational) * separated.gap = 9 * (separated.gap / 16) := by
        rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
        ring0
      rewrite [identity, one_mul] at scaled
      exact scaled
    have lower := separated.lower anchor.nearby.owner nearby.owner (fun equal => same equal.symm) common common
      ((Data.Nat.Order.le_max_left _ _).trans separationGe) ((Data.Nat.Order.le_max_right _ _).trans separationGe)
    exact (not_lt_of_ge lower (distance.trans nineSixteenths)).elim

/-- Compare the original selected programs using an authenticated retained nearby reading.

The same coverage result, source refinement and original candidate localization
determine both returned indices. Only their retained values are read; the
localization procedure is not executed by this constructor.
-/
def compareFromNearby {source : ApproximationData} {separated : Separated candidates}
    (anchor : Anchor source separated) (coverage : Coverage source candidates)
    (sourceStart candidateStart : Nat) (target : Rational) (targetPositive : 0 < target)
    (request : Coverage.Request coverage (Nat.max sourceStart anchor.index)
      (min (separated.gap / 16) (target / 8)))
    (retained : { value : Nearby candidates (source.sample request.index)
      (min (separated.gap / 16) (target / 8)) // value = request.locate }) :
    Equivalence.Comparison source (candidates anchor.nearby.owner) sourceStart candidateStart target := by
  let accuracy := min (separated.gap / 16) (target / 8)
  let cover := request.cover
  let index := request.index
  have indexGe : cover.index ≤ index := request.index_ge
  let nearby := retained.val
  have anchorGe : anchor.index ≤ index :=
    (Data.Nat.Order.le_max_right _ _).trans (cover.index_ge.trans indexGe)
  have same := anchor.sameOwner anchorGe (Fraction.Order.Basic.min_le_left _ _) nearby
  let candidateIndex := Nat.max candidateStart nearby.index
  refine
    { leftIndex := index
      rightIndex := candidateIndex
      left_ge := (Data.Nat.Order.le_max_left _ _).trans (cover.index_ge.trans indexGe)
      right_ge := Data.Nat.Order.le_max_left _ _
      close := ?_ }
  intro sourceLater candidateLater sourceOrder candidateOrder
  have sourceNear := (source.later_close sourceOrder).trans_lt request.accurate
  have candidateNear := nearby.close candidateLater
    ((Data.Nat.Order.le_max_right _ _).trans candidateOrder)
  rewrite [same] at candidateNear
  have reversed :
      normSq (source.sample index - (candidates anchor.nearby.owner).sample candidateLater) < accuracy := by
    rewrite [normSq_sub_reverse]
    exact candidateNear
  have paid := (Norm.Bounds.normSq_sub_le_via (source.sample sourceLater) (source.sample index)
    ((candidates anchor.nearby.owner).sample candidateLater)).trans_lt
    (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Order.Arithmetic.add_lt_add_direct sourceNear reversed))
  have allocation : 2 * (accuracy + accuracy) ≤ (1 / 2 : Rational) * target := by
    have bound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Basic.min_le_right (separated.gap / 16) (target / 8)) (show (0 : Rational) ≤ 4 by decide)
    have leftIdentity : 2 * (accuracy + accuracy) = 4 * accuracy := by ring0
    have rightIdentity : 4 * (target / 8) = (1 / 2 : Rational) * target := by
      calc
        4 * (target / 8) = ((4 : Rational) * (8 : Rational)⁻¹) * target := by
          rewrite [Fraction.Field.div_eq_mul_inv_direct]
          ring0
        _ = (1 / 2 : Rational) * target := congrArg (fun coefficient => coefficient * target) (by decide)
    rewrite [leftIdentity, ← rightIdentity]
    exact bound
  have halfLess : (1 / 2 : Rational) * target < target := by
    have less := Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Rational) < 1 by decide) targetPositive
    rewrite [one_mul] at less
    exact less
  exact paid.trans_le allocation |>.trans halfLess

/-- Compare the original source and selected candidate through their actual finite coverage requests. -/
def equivalent {source : ApproximationData} {separated : Separated candidates}
    (anchor : Anchor source separated) (coverage : Coverage source candidates) :
    Equivalence.Equivalent source (candidates anchor.nearby.owner) where
  compare sourceStart candidateStart target targetPositive :=
    let accuracy := min (separated.gap / 16) (target / 8)
    have accuracyPositive : 0 < accuracy := Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct separated.positive (by decide))
      (Fraction.Order.Field.div_pos_direct targetPositive (by decide))
    let request := coverage.request (Nat.max sourceStart anchor.index) accuracy accuracyPositive
    anchor.compareFromNearby coverage sourceStart candidateStart target targetPositive request ⟨request.locate, rfl⟩

/-- Retained nearby execution preserves the complete original independent-start comparison record. -/
theorem compareFromNearby_eq {source : ApproximationData} {separated : Separated candidates}
    (anchor : Anchor source separated) (coverage : Coverage source candidates)
    (sourceStart candidateStart : Nat) (target : Rational) (targetPositive : 0 < target)
    (request : Coverage.Request coverage (Nat.max sourceStart anchor.index)
      (min (separated.gap / 16) (target / 8)))
    (retained : { value : Nearby candidates (source.sample request.index)
      (min (separated.gap / 16) (target / 8)) // value = request.locate }) :
    anchor.compareFromNearby coverage sourceStart candidateStart target targetPositive request retained =
      (anchor.equivalent coverage).compare sourceStart candidateStart target targetPositive := by
  rcases request with ⟨positive, cover, coverEq, index, indexEq⟩
  cases coverEq
  cases indexEq
  rcases retained with ⟨nearby, nearbyEq⟩
  cases nearbyEq
  rfl

end Anchor

end Purelib.Approximation.Gaussian.Sequence.Selection

end
