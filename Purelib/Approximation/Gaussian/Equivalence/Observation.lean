module

public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Gaussian.Name.Coherent.Request
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Retained observations and original operational comparisons

Retained finite observations extend original operational sample comparisons
to their actual possible candidates using the same cached witnesses and
spreads. Retained readings keep their original named processes, states and
visible radii. Their based views and computed tail comparison preserve both
input observations and supply the actual sample caches used by each bound.
-/

public section

namespace Purelib.Approximation.Gaussian.Equivalence.Comparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

variable {left right : Named} {leftStart rightStart : Nat} {target : Fraction.Rational}

/-- Every candidate of the exact retained right observation pays its spread against the original left sample. -/
theorem candidate_right_distance_le
    (comparison : Comparison (Name.Sampling.approximation left) (Name.Sampling.approximation right)
      leftStart rightStart target)
    {leftIndex rightIndex : Nat} (leftAfter : comparison.leftIndex ≤ leftIndex)
    (rightAfter : comparison.rightIndex ≤ rightIndex)
    (observed : Approximation.Observation Canonical (fun first last => Norm.Basic.normSq (first - last)))
    (cache : observed = right.process.observation
      (Process.Sampling.stateAt right.process right.state rightIndex))
    {candidate : Canonical} (possible : observed.Possible candidate) :
    Norm.Basic.normSq (candidate - (Name.Sampling.approximation left).sample leftIndex) ≤
      2 * (observed.spread + target) := by
  have witness : observed.witness = (Name.Sampling.approximation right).sample rightIndex := by
    rewrite [cache]
    rfl
  have spread := observed.pairwise possible observed.witness_possible
  have close := comparison.close leftAfter rightAfter
  rewrite [Norm.Bounds.normSq_sub_symm] at close
  have error : candidate - (Name.Sampling.approximation left).sample leftIndex =
      (candidate - observed.witness) +
        (observed.witness - (Name.Sampling.approximation left).sample leftIndex) := by ring1
  rewrite [error]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct spread (by rewrite [witness]; exact close.le))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))

/-- Every candidate of the exact retained left observation pays its spread against the original right sample. -/
theorem candidate_left_distance_le
    (comparison : Comparison (Name.Sampling.approximation left) (Name.Sampling.approximation right)
      leftStart rightStart target)
    {leftIndex rightIndex : Nat} (leftAfter : comparison.leftIndex ≤ leftIndex)
    (rightAfter : comparison.rightIndex ≤ rightIndex)
    (observed : Approximation.Observation Canonical (fun first last => Norm.Basic.normSq (first - last)))
    (cache : observed = left.process.observation
      (Process.Sampling.stateAt left.process left.state leftIndex))
    {candidate : Canonical} (possible : observed.Possible candidate) :
    Norm.Basic.normSq (candidate - (Name.Sampling.approximation right).sample rightIndex) ≤
      2 * (observed.spread + target) := by
  have witness : observed.witness = (Name.Sampling.approximation left).sample leftIndex := by
    rewrite [cache]
    rfl
  have spread := observed.pairwise possible observed.witness_possible
  have close := comparison.close leftAfter rightAfter
  have error : candidate - (Name.Sampling.approximation right).sample rightIndex =
      (candidate - observed.witness) +
        (observed.witness - (Name.Sampling.approximation right).sample rightIndex) := by ring1
  rewrite [error]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct spread (by rewrite [witness]; exact close.le))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))

/-- Independent candidates of both cached observations pay their separate spreads and actual comparison target. -/
theorem candidates_distance_le
    (comparison : Comparison (Name.Sampling.approximation left) (Name.Sampling.approximation right)
      leftStart rightStart target)
    {leftIndex rightIndex : Nat} (leftAfter : comparison.leftIndex ≤ leftIndex)
    (rightAfter : comparison.rightIndex ≤ rightIndex)
    (first last : Approximation.Observation Canonical (fun first last => Norm.Basic.normSq (first - last)))
    (firstCache : first = left.process.observation
      (Process.Sampling.stateAt left.process left.state leftIndex))
    (lastCache : last = right.process.observation
      (Process.Sampling.stateAt right.process right.state rightIndex))
    {firstCandidate lastCandidate : Canonical}
    (firstPossible : first.Possible firstCandidate) (lastPossible : last.Possible lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      2 * (first.spread + 2 * (last.spread + target)) := by
  have witness : first.witness = (Name.Sampling.approximation left).sample leftIndex := by
    rewrite [firstCache]
    rfl
  have firstBound := first.pairwise firstPossible first.witness_possible
  rewrite [witness] at firstBound
  have lastBound := comparison.candidate_right_distance_le leftAfter rightAfter last lastCache lastPossible
  rewrite [Norm.Bounds.normSq_sub_symm] at lastBound
  exact (Norm.Bounds.normSq_sub_le_via firstCandidate
    ((Name.Sampling.approximation left).sample leftIndex) lastCandidate).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct firstBound lastBound)
        (by decide +kernel : (0 : Fraction.Rational) ≤ 2))

end Purelib.Approximation.Gaussian.Equivalence.Comparison

namespace Purelib.Approximation.Gaussian.Equivalence.Observation

open Purelib.Approximation.Rational.Geometric

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

set_option genInjectivity false in
/-- An actual finite possible reading and cached visible radius at an original named-process state. -/
structure Reading (original : CoherentNamed) where
  /-- The actual state of the original retained process. -/
  state : original.name.process.State
  /-- The actual original Gaussian reading at this state. -/
  value : Canonical
  /-- The reading is possible at that exact original state. -/
  possible : original.name.process.Possible state value
  /-- The cached visible squared radius of that same state. -/
  radius : Rational
  /-- The cached radius belongs to the exact original state and process. -/
  radius_eq : radius = (original.name.process.ball state).radiusSq

constructive_injectivity Reading

namespace Reading

/-- Retain an actual original reading and compute its visible state radius once. -/
@[expose] def retain (original : CoherentNamed) (state : original.name.process.State) (value : Canonical)
    (possible : original.name.process.Possible state value) : Reading original :=
  ⟨state, value, possible, (original.name.process.ball state).radiusSq, rfl⟩

/-- Every original possible reading is the complete original retain construction at its own supplied state and value. -/
theorem eq_retain {original : CoherentNamed} (reading : Reading original) :
    reading = retain original reading.state reading.value reading.possible := by
  cases reading with
  | mk state value possible radius radiusEq =>
      cases radiusEq
      rfl

/-- The cached radius of an actual original process state is nonnegative. -/
theorem radius_nonnegative {original : CoherentNamed} (reading : Reading original) : 0 ≤ reading.radius := by
  rewrite [reading.radius_eq]
  exact (original.name.process.ball reading.state).radiusSq_nonneg

/-- The actual two operand readings at one original sum state and their exact sum value.

The two complete readings keep their own original coherent names. Their
state identities point to the two literal components of the supplied sum
reading, and their values add to that same retained sum value.
-/
abbrev SumParts (left right : CoherentNamed) (sum : Reading (left.add right)) :=
  { readings : Reading left × Reading right //
    readings.1.state = sum.state.1 ∧ readings.2.state = sum.state.2 ∧
      sum.value = readings.1.value + readings.2.value }

/-- An actual original reading is close to every original sample whose semantic request is sufficiently small.

The reading and sample remain possible at their actual original states.
Both semantic allowances are paid independently; no visible-radius bound
is substituted for the process's semantic allowance.
-/
theorem sample_distance_le {original : CoherentNamed} {target : Rational}
    (reading : Reading original) (positive : 0 < target)
    (paidReading : original.coherent.allowance reading.state < target) (index : Nat)
    (small : Process.Sampling.refinementTarget index < original.coherent.accuracyRequest target) :
    Norm.Basic.normSq (reading.value - (Name.Sampling.approximation original.name).sample index) ≤
      8 * target := by
  have late := original.coherent.stateAt_allowance_lt original.name.state index target positive small
  have close := original.coherent.possible_close reading.possible
    (Process.Sampling.witnessAt_possible original.name.process original.name.state index)
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 4)
    (Order.Arithmetic.add_lt_add_direct paidReading late)
  have grouped : (4 : Rational) * (target + target) = 8 * target := by ring1
  exact close.trans (paid.le.trans_eq grouped)

/-- An actual finite comparison controls two independently paid original readings.

The retained comparison may include a nonzero spatial error. Explicit
finite searches place both original samples beyond its selected indices
and pay both semantic allowances before the three-leg distance bound.
-/
theorem distance_le {left right : CoherentNamed} {leftTarget rightTarget target : Rational}
    (first : Reading left) (last : Reading right)
    (firstPositive : 0 < leftTarget) (lastPositive : 0 < rightTarget)
    (firstPaid : left.coherent.allowance first.state < leftTarget)
    (lastPaid : right.coherent.allowance last.state < rightTarget) {leftStart rightStart : Nat}
    (comparison : Equivalence.Comparison (Name.Sampling.approximation left.name)
      (Name.Sampling.approximation right.name) leftStart rightStart target) :
    Norm.Basic.normSq (first.value - last.value) ≤
      32 * (leftTarget + rightTarget) + 4 * target := by
  let leftIndex := Search.firstQuarterBelow 1 comparison.leftIndex
    (left.coherent.accuracyRequest leftTarget)
  let rightIndex := Search.firstQuarterBelow 1 comparison.rightIndex
    (right.coherent.accuracyRequest rightTarget)
  have leftAfter := Search.firstQuarterBelow_ge 1 comparison.leftIndex
    (left.coherent.accuracyRequest leftTarget)
  have rightAfter := Search.firstQuarterBelow_ge 1 comparison.rightIndex
    (right.coherent.accuracyRequest rightTarget)
  have leftBound := first.sample_distance_le firstPositive firstPaid leftIndex
    (Search.firstQuarterBelow_accurate 1 (by decide) comparison.leftIndex
      (left.coherent.accuracyRequest leftTarget) (left.coherent.accuracyRequest_pos firstPositive))
  have rightBound := last.sample_distance_le lastPositive lastPaid rightIndex
    (Search.firstQuarterBelow_accurate 1 (by decide) comparison.rightIndex
      (right.coherent.accuracyRequest rightTarget) (right.coherent.accuracyRequest_pos lastPositive))
  let leftSample := (Name.Sampling.approximation left.name).sample leftIndex
  let rightSample := (Name.Sampling.approximation right.name).sample rightIndex
  have middle := (comparison.close leftAfter rightAfter).le
  have decomposition : first.value - last.value =
      (first.value - leftSample) + ((leftSample - rightSample) + (rightSample - last.value)) := by
    ring1
  have lastBound : Norm.Basic.normSq (rightSample - last.value) ≤ 8 * rightTarget := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact rightBound
  have inner := (Norm.Bounds.normSq_add_le_two (leftSample - rightSample)
    (rightSample - last.value)).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct middle lastBound) (by decide))
  have outer := (Norm.Bounds.normSq_add_le_two (first.value - leftSample)
    ((leftSample - rightSample) + (rightSample - last.value))).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct leftBound inner) (by decide))
  have firstScaled : (16 : Rational) * leftTarget ≤ 32 * leftTarget :=
    Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 16) (n := 32) (by decide)) firstPositive.le
  rewrite [decomposition]
  calc
    _ ≤ 2 * (8 * leftTarget + 2 * (target + 8 * rightTarget)) := outer
    _ = 16 * leftTarget + (32 * rightTarget + 4 * target) := by ring1
    _ ≤ 32 * leftTarget + (32 * rightTarget + 4 * target) :=
      Order.Arithmetic.add_le_add_direct firstScaled (Order.Basic.le_refl _)
    _ = _ := by ring1

/-- A paid reading of an exact scalar product is bounded by an actual finite comparison of its retained factor.

The same original factor comparison is multiplied by the displayed scalar.
The supplied reading pays its own semantic allowance, and the exact zero
reading supplies the other endpoint without another process refinement.
The bound keeps the input comparison's nonzero error explicitly.
-/
theorem mul_zero_normSq_le (coefficient : Canonical) (value : CoherentNamed)
    (reading : Reading ((CoherentNamed.Coherence.exact coefficient).mul value))
    {target : Rational} (positive : 0 < target)
    (paidReading : ((CoherentNamed.Coherence.exact coefficient).mul value).coherent.allowance reading.state < target)
    (upper : Rational)
    (comparison : Equivalence.Comparison (Name.Sampling.approximation value.name)
      (Name.Sampling.approximation (CoherentNamed.Coherence.exact 0).name) 0 0 (upper + target)) :
    Norm.Basic.normSq reading.value ≤
      64 * target + 4 * (4 * (Norm.Basic.normSq coefficient * (upper + target)) + target) := by
  let zero := Reading.retain (CoherentNamed.Coherence.exact 0)
    (CoherentNamed.Coherence.exact 0).name.state 0 rfl
  have zeroPaid : (CoherentNamed.Coherence.exact 0).coherent.allowance zero.state < target := positive
  let multiplied := Name.Coherent.Arithmetic.Product.Congruence.compare_exact_mul_zero
    coefficient value comparison 0 target positive
  have paid := reading.distance_le zero positive positive paidReading zeroPaid multiplied
  change Norm.Basic.normSq (reading.value - 0) ≤
    32 * (target + target) + 4 * (4 * (Norm.Basic.normSq coefficient * (upper + target)) + target) at paid
  rewrite [Data.Gaussian.Basic.sub_zero] at paid
  have grouped : (32 : Rational) * (target + target) = 64 * target := by ring1
  rewrite [grouped] at paid
  exact paid

/-- Multiply one actual retained reading by an exact scalar without refining its state.

The product keeps the supplied right state and its possible value. Its
left state is the original terminating scalar state. Its exact visible
product radius consumes the supplied cached right radius without reading
that original process ball again.
-/
def exact_mul {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    Reading ((CoherentNamed.Coherence.exact coefficient).mul original) := by
  refine ⟨((CoherentNamed.Coherence.exact coefficient).name.state, reading.state),
    coefficient * reading.value, ⟨coefficient, reading.value, rfl, reading.possible, rfl⟩,
    4 * (Norm.Basic.normSq coefficient * reading.radius), ?_⟩
  change _ = 4 * ((0 : Rational) * Norm.Basic.normSq (original.name.process.ball reading.state).center +
    Norm.Basic.normSq coefficient * (original.name.process.ball reading.state).radiusSq) +
      2 * (0 * (original.name.process.ball reading.state).radiusSq)
  rewrite [← reading.radius_eq]
  ring1

/-- Exact scalar multiplication retains the actual supplied whole right state. -/
theorem exact_mul_state {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    (reading.exact_mul coefficient).state =
      ((CoherentNamed.Coherence.exact coefficient).name.state, reading.state) := by
  unfold exact_mul
  rfl

/-- Exact scalar multiplication reads the actual supplied value without another witness selection. -/
theorem exact_mul_value {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    (reading.exact_mul coefficient).value = coefficient * reading.value := by
  unfold exact_mul
  rfl

/-- The original exact scalar-product radius consumes the supplied cached right radius. -/
theorem exact_mul_radius {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    (reading.exact_mul coefficient).radius = 4 * (Norm.Basic.normSq coefficient * reading.radius) := by
  unfold exact_mul
  rfl

/-- The cached scalar product is the complete original paired-state retained reading, including its exact radius. -/
theorem exact_mul_retain {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    reading.exact_mul coefficient =
      retain ((CoherentNamed.Coherence.exact coefficient).mul original)
        ((CoherentNamed.Coherence.exact coefficient).name.state, reading.state) (coefficient * reading.value)
        ⟨coefficient, reading.value, rfl, reading.possible, rfl⟩ := by
  exact (reading.exact_mul coefficient).eq_retain

/-- The original product coherence has its actual scalar specialization at the unchanged retained right state. -/
theorem exact_mul_allowance {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical) :
    ((CoherentNamed.Coherence.exact coefficient).mul original).coherent.allowance
      (reading.exact_mul coefficient).state =
        4 * (original.coherent.allowance reading.state * original.coherent.allowance reading.state +
          Norm.Basic.normSq coefficient * original.coherent.allowance reading.state) := by
  change Process.Coherence.Basic.Coherent.productAllowance (Norm.Basic.normSq coefficient)
    original.name.process.centerBound 0 (original.coherent.allowance reading.state) = _
  unfold Process.Coherence.Basic.Coherent.productAllowance Process.Coherence.Basic.Coherent.productBase
  ring1

/-- A common finite scalar ceiling pays every exact product of the same retained reading.

The original right allowance is paid below one and below the displayed
positive target divided by the actual ceiling. The full original product
allowance, including its quadratic term, is bounded without refinement.
-/
theorem exact_mul_paid {original : CoherentNamed} (reading : Reading original) (coefficient : Canonical)
    {upper budget target : Rational} (ceiling : Norm.Basic.normSq coefficient ≤ upper)
    (paid : original.coherent.allowance reading.state < budget) (unit : budget ≤ 1)
    (payment : budget * (4 * (1 + upper)) < target) :
    ((CoherentNamed.Coherence.exact coefficient).mul original).coherent.allowance
      (reading.exact_mul coefficient).state < target := by
  let value := original.coherent.allowance reading.state
  have nonnegative : 0 ≤ value := original.coherent.allowance_nonneg reading.state
  have square := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (paid.le.trans unit) nonnegative
  rewrite [Fraction.Field.one_mul] at square
  have product := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct ceiling nonnegative
  have added := Order.Arithmetic.add_le_add_direct square product
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct added (by decide : (0 : Rational) ≤ 4)
  have upperNonnegative : 0 ≤ upper := (Norm.Basic.normSq_nonneg coefficient).trans ceiling
  have factorPositive : 0 < 4 * (1 + upper) := Order.Arithmetic.mul_pos_direct (by decide)
    (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) upperNonnegative)
  have last := Order.Arithmetic.mul_lt_mul_of_pos_right_direct paid factorPositive
  rewrite [exact_mul_allowance]
  have grouped : 4 * (value + upper * value) = value * (4 * (1 + upper)) := by ring1
  exact (scaled.trans_eq grouped).trans_lt (last.trans payment)

/-- An actual guarded constant-numerator quotient is close to that scalar times one supplied reciprocal reading.

The same original denominator and apartness guard appear on both sides.
Original quotient cancellation factors the scalar operationally; both
actual semantic allowances and the comparison accuracy are paid separately.
The supplied reciprocal reading is consumed without another request.
-/
theorem exact_div_distance_le (coefficient : Canonical) (denominator : CoherentNamed)
    (apart : Name.Basic.Named.Apart denominator.name)
    (reading : Reading (CoherentNamed.div (CoherentNamed.Coherence.exact coefficient) denominator apart))
    (reciprocal : Reading (CoherentNamed.div (CoherentNamed.Coherence.exact 1) denominator apart))
    {sourceTarget productTarget accuracy : Rational} (sourcePositive : 0 < sourceTarget)
    (productPositive : 0 < productTarget) (accuracyPositive : 0 < accuracy)
    (sourcePaid : (CoherentNamed.div (CoherentNamed.Coherence.exact coefficient) denominator apart).coherent.allowance
      reading.state < sourceTarget)
    (productPaid : ((CoherentNamed.Coherence.exact coefficient).mul
      (CoherentNamed.div (CoherentNamed.Coherence.exact 1) denominator apart)).coherent.allowance
        (reciprocal.exact_mul coefficient).state < productTarget) :
    Norm.Basic.normSq (reading.value - coefficient * reciprocal.value) ≤
      32 * (sourceTarget + productTarget) + 4 * accuracy := by
  let scalar := CoherentNamed.Coherence.exact coefficient
  let one := CoherentNamed.Coherence.exact 1
  have remove := Name.Coherent.Division.Equivalence.coherentDiv_respects
    (scalar.mul one) scalar denominator denominator apart apart
    (Arithmetic.Mul.coherentMul_one_right scalar) (Equivalence.NamedEquivalent.refl _)
  have factored := remove.symm.trans (Division.Cancellation.coherentDiv_mul_left scalar one denominator apart)
  let comparison := factored.compare 0 0 accuracy accuracyPositive
  have estimate := reading.distance_le (reciprocal.exact_mul coefficient)
    sourcePositive productPositive sourcePaid productPaid comparison
  rewrite [exact_mul_value] at estimate
  exact estimate

end Reading

set_option genInjectivity false in
/-- A paid finite reading request on one original coherent named process.

The actual original state is refined once at the retained common visible
and semantic request. The reading and its radius consume that same state
and its actual finite witness. -/
structure Request (original : CoherentNamed) (target : Rational) where
  /-- The original named owner retained as executable data. -/
  owner : CoherentNamed
  /-- The retained owner is the original request input. -/
  owner_eq : owner = original
  /-- The original requested visible radius is positive. -/
  positive : 0 < target
  /-- The cached common visible and semantic request. -/
  tolerance : Rational
  /-- The tolerance belongs to the original coherent request procedure. -/
  tolerance_eq : tolerance = Name.Coherent.Request.channelTarget original target
  /-- The cached original request tolerance is positive. -/
  tolerance_positive : 0 < tolerance
  /-- The actual original state selected by the retained request. -/
  reading : Reading original
  /-- The reading uses the actual original process refinement. -/
  state_eq : reading.state = original.name.process.refine original.name.state tolerance tolerance_positive
  /-- The cached value is the actual witness at that same original state. -/
  value_eq : reading.value = (original.name.process.witness reading.state).val
  /-- The actual original requested reading's visible radius pays the request. -/
  radius_lt : reading.radius < target

constructive_injectivity Request

namespace Request

/-- Transport the same whole original paid Request along an exact equality of its displayed targets. -/
@[expose] def transportTarget {original : CoherentNamed} {first last : Rational}
    (request : Request original first) (same : first = last) : Request original last :=
  Eq.mp (congrArg (Request original) same) request

/-- Equal-target transport preserves the complete original supplied Request and all its retained fields. -/
theorem transportTarget_heq {original : CoherentNamed} {first last : Rational}
    (request : Request original first) (same : first = last) : HEq (request.transportTarget same) request := by
  unfold transportTarget
  exact cast_heq _ _

/-- Transporting a Request to its own target retains that same whole original supplied Request literally. -/
theorem transportTarget_self {original : CoherentNamed} {target : Rational} (request : Request original target) :
    request.transportTarget rfl = request :=
  (rfl)

/-- Exact target transport reads the same original retained whole reading and state. -/
theorem transportTarget_reading {original : CoherentNamed} {first last : Rational}
    (request : Request original first) (same : first = last) : (request.transportTarget same).reading =
      request.reading := by
  cases same
  rfl

/-- Refine one original state and materialize its same-state reading together with retained executable data.

The materializer must return the original finite witness value at that
state. The actual reading and payload are evaluated together once; all
request fields consume that same materialized reading.
-/
@[inline] private def materialize (original : CoherentNamed) (target : Rational) (positive : 0 < target)
    (Payload : Reading original → Type)
    (retain : (state : original.name.process.State) →
      (reading : Reading original) ×
        { _payload : Payload reading //
          reading.state = state ∧ reading.value = (original.name.process.witness reading.state).val }) :
    (request : Request original target) × Payload request.reading := by
  let tolerance := Name.Coherent.Request.channelTarget original target
  have tolerancePositive := Name.Coherent.Request.channelTarget_pos original positive
  let state := original.name.process.refine original.name.state tolerance tolerancePositive
  let retained := retain state
  let reading := retained.1
  have accurate := original.name.process.accurate original.name.state tolerance tolerancePositive
  have paid : reading.radius < target := by
    rewrite [reading.radius_eq, retained.2.property.1]
    exact accurate.trans (Name.Coherent.Request.channelTarget_lt_target original positive)
  exact ⟨⟨original, rfl, positive, tolerance, rfl, tolerancePositive, reading,
    retained.2.property.1, retained.2.property.2, paid⟩, retained.2.val⟩

/-- Refine one original named state and retain its actual finite possible reading and paid radius. -/
def build (original : CoherentNamed) (target : Rational) (positive : 0 < target) : Request original target :=
  (materialize original target positive (fun _ => Unit) (fun state =>
    let witness := original.name.process.witness state
    let reading := Reading.retain original state witness.val witness.property
    ⟨reading, ⟨(), rfl, rfl⟩⟩)).1

/-- Refine the original sum once and retain its two actual operand readings from that same paired state.

Each original operand witness and visible radius is computed once. The
saved sum reading uses those same values and radii, while the payload keeps
both full readings, their original states and their literal sum identity.
-/
def buildSum (left right : CoherentNamed) (target : Rational) (positive : 0 < target) :
    (request : Request (left.add right) target) × Reading.SumParts left right request.reading :=
  materialize (left.add right) target positive (Reading.SumParts left right) (fun state => by
    let firstWitness := left.name.process.witness state.1
    let lastWitness := right.name.process.witness state.2
    let first := Reading.retain left state.1 firstWitness.val firstWitness.property
    let last := Reading.retain right state.2 lastWitness.val lastWitness.property
    let sum : Reading (left.add right) :=
      ⟨state, first.value + last.value,
        ⟨first.value, last.value, first.possible, last.possible, rfl⟩,
        2 * (first.radius + last.radius), rfl⟩
    exact ⟨sum, ⟨⟨⟨first, last⟩, rfl, rfl, rfl⟩, rfl, rfl⟩⟩)

/-- Retaining the original operand readings preserves the complete original sum request. -/
theorem buildSum_request (left right : CoherentNamed) (target : Rational) (positive : 0 < target) :
    (buildSum left right target positive).1 = build (left.add right) target positive := by
  unfold buildSum build materialize
  rfl

/-- The same retained paid request also meets its original semantic allowance target. -/
theorem allowance_lt {original : CoherentNamed} {target : Rational} (request : Request original target) :
    original.coherent.allowance request.reading.state < target := by
  rewrite [request.state_eq]
  apply original.coherent.refine_accurate original.name.state target request.positive
    request.tolerance request.tolerance_positive
  rewrite [request.tolerance_eq]
  exact Name.Coherent.Request.channelTarget_lt_allowanceRequest original request.positive

/-- A paid original reading is close to every original sample whose semantic request is sufficiently small.

The retained original request supplies its actual reading and semantic
allowance. The sample pays its own original semantic allowance separately.
-/
theorem sample_distance_le {original : CoherentNamed} {target : Rational}
    (request : Request original target) (index : Nat)
    (small : Process.Sampling.refinementTarget index < original.coherent.accuracyRequest target) :
    Norm.Basic.normSq (request.reading.value - (Name.Sampling.approximation original.name).sample index) ≤
      8 * target :=
  request.reading.sample_distance_le request.positive request.allowance_lt index small

/-- An actual finite comparison controls two independently paid original readings.

The original requests supply their own actual readings and semantic
allowances. The finite comparison retains its independent selected starts
and nonzero operational error target.
-/
theorem distance_le {left right : CoherentNamed} {leftTarget rightTarget target : Rational}
    (first : Request left leftTarget) (last : Request right rightTarget) {leftStart rightStart : Nat}
    (comparison : Equivalence.Comparison (Name.Sampling.approximation left.name)
      (Name.Sampling.approximation right.name) leftStart rightStart target) :
    Norm.Basic.normSq (first.reading.value - last.reading.value) ≤
      32 * (leftTarget + rightTarget) + 4 * target :=
  first.reading.distance_le last.reading first.positive last.positive first.allowance_lt last.allowance_lt comparison

end Request

namespace Reading.SumParts

/-- Each actual operand state's semantic allowance is bounded by its original sum allowance. -/
private theorem operand_allowances {left right : CoherentNamed}
    (sum : Reading (left.add right)) (parts : Reading.SumParts left right sum) :
    left.coherent.allowance parts.val.1.state ≤ (left.add right).coherent.allowance sum.state ∧
      right.coherent.allowance parts.val.2.state ≤ (left.add right).coherent.allowance sum.state := by
  let first := left.coherent.allowance sum.state.1
  let last := right.coherent.allowance sum.state.2
  have firstNonnegative : 0 ≤ first := left.coherent.allowance_nonneg _
  have lastNonnegative : 0 ≤ last := right.coherent.allowance_nonneg _
  have sumNonnegative := Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative
  rewrite [Fraction.Field.zero_add] at sumNonnegative
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide : (1 : Rational) ≤ 2) sumNonnegative
  rewrite [Fraction.Field.one_mul] at scaled
  have firstBound := Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl first) lastNonnegative
  rewrite [Fraction.Field.add_comm first 0, Fraction.Field.zero_add] at firstBound
  have lastBound := Order.Arithmetic.add_le_add_direct firstNonnegative (Order.Basic.le_refl last)
  rewrite [Fraction.Field.zero_add] at lastBound
  constructor
  · rewrite [parts.property.1]
    exact firstBound.trans scaled
  · rewrite [parts.property.2.1]
    exact lastBound.trans scaled

/-- The left retained operand meets the semantic target paid by the same actual original sum request. -/
theorem left_allowance_lt {left right : CoherentNamed} {target : Rational}
    {request : Request (left.add right) target} (parts : Reading.SumParts left right request.reading) :
    left.coherent.allowance parts.val.1.state < target :=
  (operand_allowances request.reading parts).1.trans_lt request.allowance_lt

/-- The right retained operand meets the semantic target paid by the same actual original sum request. -/
theorem right_allowance_lt {left right : CoherentNamed} {target : Rational}
    {request : Request (left.add right) target} (parts : Reading.SumParts left right request.reading) :
    right.coherent.allowance parts.val.2.state < target :=
  (operand_allowances request.reading parts).2.trans_lt request.allowance_lt

/-- The visible radius of the left actual operand is bounded by its own paid semantic allowance. -/
theorem left_radius_lt {left right : CoherentNamed} {target : Rational}
    {request : Request (left.add right) target} (parts : Reading.SumParts left right request.reading) :
    parts.val.1.radius < target := by
  rewrite [parts.val.1.radius_eq]
  exact (left.coherent.ball_radius_le _).trans_lt (left_allowance_lt parts)

/-- The visible radius of the right actual operand is bounded by its own paid semantic allowance. -/
theorem right_radius_lt {left right : CoherentNamed} {target : Rational}
    {request : Request (left.add right) target} (parts : Reading.SumParts left right request.reading) :
    parts.val.2.radius < target := by
  rewrite [parts.val.2.radius_eq]
  exact (right.coherent.ball_radius_le _).trans_lt (right_allowance_lt parts)

end Reading.SumParts

set_option genInjectivity false in
/-- A cached finite operational comparison of two original possible readings.

Both original named owners and the actual relation procedure are retained.
The two based views retain their original states, and the computed tail
comparison supplies the exact sample indices and sample readings used in
the quantitative bound on the original reading difference. -/
structure Comparison {left right : CoherentNamed} (leftReading : Reading left) (rightReading : Reading right)
    (target : Rational) where
  /-- The original left observation, including its actual state, reading and radius cache. -/
  leftObservation : Reading left
  /-- The retained left observation is the original input observation. -/
  leftObservation_eq : leftObservation = leftReading
  /-- The original right observation, including its actual state, reading and radius cache. -/
  rightObservation : Reading right
  /-- The retained right observation is the original input observation. -/
  rightObservation_eq : rightObservation = rightReading
  /-- The original left named owner as executable data. -/
  leftOwner : CoherentNamed
  /-- The retained left owner is the original input owner. -/
  leftOwner_eq : leftOwner = left
  /-- The original right named owner as executable data. -/
  rightOwner : CoherentNamed
  /-- The retained right owner is the original input owner. -/
  rightOwner_eq : rightOwner = right
  /-- The actual original operational relation procedure. -/
  equivalent : NamedEquivalent left.name right.name
  /-- The cached left refinement-future view of its actual original observation state. -/
  leftBased : CoherentNamed
  /-- The left view is based at the exact original observation state. -/
  leftBased_eq : leftBased = left.based leftReading.state
  /-- The cached right refinement-future view of its actual original observation state. -/
  rightBased : CoherentNamed
  /-- The right view is based at the exact original observation state. -/
  rightBased_eq : rightBased = right.based rightReading.state
  /-- The actual retained finite tail comparison of these same based views. -/
  tail : Equivalence.Comparison (Name.Sampling.approximation leftBased.name)
    (Name.Sampling.approximation rightBased.name) 0 0 target
  /-- The cached sample at the actual selected left comparison index. -/
  leftSample : Canonical
  /-- The sample comes from that same original based view and retained index. -/
  leftSample_eq : leftSample = (Name.Sampling.approximation leftBased.name).sample tail.leftIndex
  /-- The cached sample at the actual selected right comparison index. -/
  rightSample : Canonical
  /-- The sample comes from that same original based view and retained index. -/
  rightSample_eq : rightSample = (Name.Sampling.approximation rightBased.name).sample tail.rightIndex
  /-- The actual retained difference of the original two readings. -/
  residual : Canonical
  /-- The residual belongs to the original observations. -/
  residual_eq : residual = leftReading.value - rightReading.value
  /-- The cached comparison budget from the actual original radii and tail target. -/
  bound : Rational
  /-- The bound consumes the same original radii and original requested comparison target. -/
  bound_eq : bound = 16 * (leftReading.radius + rightReading.radius) + 4 * target
  /-- The actual original reading difference obeys the retained computed comparison bound. -/
  residual_le : Norm.Basic.normSq residual ≤ bound

constructive_injectivity Comparison

namespace Comparison

/-- Both original observation radii and the actual tail target bound the unchanged original reading difference. -/
theorem reading_error_le {left right : CoherentNamed} {leftReading : Reading left}
    {rightReading : Reading right} {target : Rational} (comparison : Comparison leftReading rightReading target) :
    Norm.Basic.normSq (leftReading.value - rightReading.value) ≤
      16 * (leftReading.radius + rightReading.radius) + 4 * target := by
  have paid := comparison.residual_le
  rewrite [comparison.residual_eq, comparison.bound_eq] at paid
  exact paid

/-- Independent original reading requests pay their own state radii in the same retained finite comparison. -/
theorem requested_error_lt {left right : CoherentNamed} {leftTarget rightTarget target : Rational}
    (leftRequest : Request left leftTarget) (rightRequest : Request right rightTarget)
    (comparison : Comparison leftRequest.reading rightRequest.reading target) :
    Norm.Basic.normSq (leftRequest.reading.value - rightRequest.reading.value) <
      16 * (leftTarget + rightTarget) + 4 * target :=
  comparison.reading_error_le.trans_lt
    (Order.Arithmetic.add_lt_add_right_direct
      (Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide +kernel : (0 : Rational) < 16)
        (Order.Arithmetic.add_lt_add_direct leftRequest.radius_lt rightRequest.radius_lt)) _)

/-- A sample from a based view remains possible at its original observation state. -/
private theorem based_sample_possible (original : CoherentNamed) (state : original.name.process.State)
    (index : Nat) : original.name.process.Possible state
      ((Name.Sampling.approximation (original.based state).name).sample index) :=
  Process.Based.based_initial_persists original.name.process state
    (Process.Sampling.witnessAt_possible (original.based state).name.process
      (original.based state).name.state index)

/-- The retained left comparison sample is possible in the SAME original left observation state. -/
theorem leftSample_possible {left right : CoherentNamed} {leftReading : Reading left}
    {rightReading : Reading right} {target : Rational} (comparison : Comparison leftReading rightReading target) :
    left.name.process.Possible leftReading.state comparison.leftSample := by
  let index : Nat := comparison.tail.leftIndex
  have sample : comparison.leftSample =
      (Name.Sampling.approximation (left.based leftReading.state).name).sample index :=
    comparison.leftSample_eq.trans (congrArg (fun original : CoherentNamed =>
      (Name.Sampling.approximation original.name).sample index) comparison.leftBased_eq)
  rewrite [sample]
  exact based_sample_possible left leftReading.state index

/-- The retained right comparison sample is possible in the SAME original right observation state. -/
theorem rightSample_possible {left right : CoherentNamed} {leftReading : Reading left}
    {rightReading : Reading right} {target : Rational} (comparison : Comparison leftReading rightReading target) :
    right.name.process.Possible rightReading.state comparison.rightSample := by
  let index : Nat := comparison.tail.rightIndex
  have sample : comparison.rightSample =
      (Name.Sampling.approximation (right.based rightReading.state).name).sample index :=
    comparison.rightSample_eq.trans (congrArg (fun original : CoherentNamed =>
      (Name.Sampling.approximation original.name).sample index) comparison.rightBased_eq)
  rewrite [sample]
  exact based_sample_possible right rightReading.state index

/-- The two actual selected comparison samples pay the original retained operational tail request. -/
theorem sample_distance_lt {left right : CoherentNamed} {leftReading : Reading left}
    {rightReading : Reading right} {target : Rational} (comparison : Comparison leftReading rightReading target) :
    Norm.Basic.normSq (comparison.leftSample - comparison.rightSample) < target := by
  rewrite [comparison.leftSample_eq, comparison.rightSample_eq]
  exact comparison.tail.close (Nat.le_refl _) (Nat.le_refl _)

/-- The original two state radii and actual finite tail comparison control the original reading difference. -/
private theorem reading_bound {left right : CoherentNamed} (leftReading : Reading left) (rightReading : Reading right)
    (leftSample rightSample : Canonical) (target : Rational)
    (leftPossible : left.name.process.Possible leftReading.state leftSample)
    (rightPossible : right.name.process.Possible rightReading.state rightSample)
    (close : Norm.Basic.normSq (leftSample - rightSample) < target) :
    Norm.Basic.normSq (leftReading.value - rightReading.value) ≤
      16 * (leftReading.radius + rightReading.radius) + 4 * target := by
  have leftBound := Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq
    (left.name.process.possible_inside leftReading.possible) (left.name.process.possible_inside leftPossible)
  have rightBound := Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq
    (right.name.process.possible_inside rightPossible) (right.name.process.possible_inside rightReading.possible)
  rewrite [← leftReading.radius_eq] at leftBound
  rewrite [← rightReading.radius_eq] at rightBound
  have decomposition : leftReading.value - rightReading.value =
      (leftReading.value - leftSample) + ((leftSample - rightSample) + (rightSample - rightReading.value)) := by ring1
  rewrite [decomposition]
  have inner := (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct close.le rightBound) (by decide))
  have total := (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct leftBound inner) (by decide))
  have upper : 8 * leftReading.radius ≤ 16 * leftReading.radius :=
    Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) leftReading.radius_nonnegative
  calc
    _ ≤ 2 * (4 * leftReading.radius + 2 * (target + 4 * rightReading.radius)) := total
    _ = 8 * leftReading.radius + (16 * rightReading.radius + 4 * target) := by ring1
    _ ≤ 16 * leftReading.radius + (16 * rightReading.radius + 4 * target) :=
      Order.Arithmetic.add_le_add_direct upper (Order.Basic.le_refl _)
    _ = _ := by ring1

/-- Compute one retained finite comparison of the two actual original observations. -/
def build {left right : CoherentNamed} (leftReading : Reading left) (rightReading : Reading right)
    (equivalent : NamedEquivalent left.name right.name) (target : Rational) (positive : 0 < target) :
    Comparison leftReading rightReading target := by
  let leftBased := left.based leftReading.state
  let rightBased := right.based rightReading.state
  let basedEquivalent := (left.basedEquivalent leftReading.state).symm.trans
    (equivalent.trans (right.basedEquivalent rightReading.state))
  let tail := basedEquivalent.compare 0 0 target positive
  let leftSample := (Name.Sampling.approximation leftBased.name).sample tail.leftIndex
  let rightSample := (Name.Sampling.approximation rightBased.name).sample tail.rightIndex
  let residual := leftReading.value - rightReading.value
  let bound := 16 * (leftReading.radius + rightReading.radius) + 4 * target
  have estimate := reading_bound leftReading rightReading leftSample rightSample target
    (based_sample_possible left leftReading.state tail.leftIndex)
    (based_sample_possible right rightReading.state tail.rightIndex)
    (tail.close (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨leftReading, rfl, rightReading, rfl, left, rfl, right, rfl, equivalent, leftBased, rfl, rightBased, rfl, tail,
    leftSample, rfl, rightSample, rfl, residual, rfl, bound, rfl, estimate⟩

/-- The comparison's own retained observation values obey the same two actual request targets and accuracy budget. -/
theorem observations_distance_le {left right : CoherentNamed} {leftTarget rightTarget target : Rational}
    (first : Request left leftTarget) (last : Request right rightTarget)
    (comparison : Comparison first.reading last.reading target) :
    Norm.Basic.normSq (comparison.leftObservation.value - comparison.rightObservation.value) ≤
      16 * (leftTarget + rightTarget) + 4 * target := by
  rewrite [comparison.leftObservation_eq, comparison.rightObservation_eq]
  exact (requested_error_lt first last comparison).le

end Comparison

end Purelib.Approximation.Gaussian.Equivalence.Observation

end
