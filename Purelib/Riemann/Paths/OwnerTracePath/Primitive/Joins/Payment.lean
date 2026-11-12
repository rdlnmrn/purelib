module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # Four requested endpoint handoffs on two retained moving Spines

A count-four allocation precedes new coefficient observations. The two
actual moving paths and four supplied joins remain unchanged. Three new
external Vertices share their literal middle cache, and both joined Spines
retain the original comparison and append factories. The resulting payment
is only for the four endpoint handoffs, including empty moving paths.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Data.List
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}

universe u

section EndpointJoins

variable {firstPoint middlePoint lastPoint : Canonical}
    {outerFirst : Owner (polynomial.eval firstPoint)} {outerMiddle : Owner (polynomial.eval middlePoint)}
    {outerLast : Owner (polynomial.eval lastPoint)}
    {innerFirst : Owner (polynomial.eval firstPoint)}
    {innerMiddleBefore innerMiddleAfter : Owner (polynomial.eval middlePoint)}
    {innerLast : Owner (polynomial.eval lastPoint)}
    (before : OwnerPath polynomial firstPoint innerFirst middlePoint innerMiddleBefore)
    (after : OwnerPath polynomial middlePoint innerMiddleAfter lastPoint innerLast)
    (beforeSource : OwnerJoin outerFirst innerFirst) (beforeTarget : OwnerJoin innerMiddleBefore outerMiddle)
    (afterSource : OwnerJoin outerMiddle innerMiddleAfter) (afterTarget : OwnerJoin innerLast outerLast)

/-- The same shared middle Vertex cancels when the two actual endpoint-joined increments are added. -/
private theorem endpoint_change_le
    (beforeMoving : Spine expression accuracy before) (afterMoving : Spine expression accuracy after)
    (firstJoined : WithJoins beforeMoving beforeSource beforeTarget)
    (lastJoined : WithJoins afterMoving afterSource afterTarget)
    (shared : firstJoined.last = lastJoined.first) :
    Norm.Basic.normSq ((lastJoined.last.value - firstJoined.first.value) -
      ((beforeMoving.last.value - beforeMoving.first.value) +
        (afterMoving.last.value - afterMoving.first.value))) ≤ 16 * accuracy.tolerance := by
  have firstBound := WithJoins.increment_error_le (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy)
    (moving := beforeMoving) (source := beforeSource) (target := beforeTarget) firstJoined
  have lastBound := WithJoins.increment_error_le (polynomial := polynomial)
    (expression := expression) (accuracy := accuracy)
    (moving := afterMoving) (source := afterSource) (target := afterTarget) lastJoined
  have firstStart := WithJoins.observed_first (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (moving := beforeMoving) (source := beforeSource) (target := beforeTarget) firstJoined
  have firstFinish := WithJoins.observed_last (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (moving := beforeMoving) (source := beforeSource) (target := beforeTarget) firstJoined
  have lastStart := WithJoins.observed_first (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (moving := afterMoving) (source := afterSource) (target := afterTarget) lastJoined
  have lastFinish := WithJoins.observed_last (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (moving := afterMoving) (source := afterSource) (target := afterTarget) lastJoined
  rewrite [firstStart, firstFinish] at firstBound
  rewrite [lastStart, lastFinish] at lastBound
  have same : firstJoined.last.value = lastJoined.first.value :=
    congrArg (fun vertex : Vertex expression middlePoint outerMiddle accuracy => vertex.value) shared
  have identity :
      (lastJoined.last.value - firstJoined.first.value) -
          ((beforeMoving.last.value - beforeMoving.first.value) +
            (afterMoving.last.value - afterMoving.first.value)) =
        ((firstJoined.last.value - firstJoined.first.value) -
          (beforeMoving.last.value - beforeMoving.first.value)) +
        ((lastJoined.last.value - lastJoined.first.value) -
          (afterMoving.last.value - afterMoving.first.value)) := by
    rewrite [same]
    ring1
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct firstBound lastBound)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

/-- The signed jump is read from the same original stationary comparison residual. -/
private theorem comparison_jump {point : Canonical}
    {left right : Owner (polynomial.eval point)}
    (first : Vertex expression point left accuracy) (last : Vertex expression point right accuracy)
    (comparison : Observation.Comparison first.observation last.observation (tailRequest accuracy).tolerance) :
    -comparison.residual = last.value - first.value := by
  rewrite [comparison.residual_eq]
  change -(first.value - last.value) = last.value - first.value
  ring1

/-- The original count-four schedule pays the four actual endpoint handoffs. -/
private theorem endpoint_schedule (request : AccuracyRequest) :
    16 * (localRequest request 4).tolerance < request.tolerance := by
  have finite := Aggregate.count_mul_perTerm_lt request.positive 4
  change (4 : Rational) * (4 * (localRequest request 4).tolerance) < request.tolerance at finite
  exact (show (16 : Rational) * (localRequest request 4).tolerance =
    4 * (4 * (localRequest request 4).tolerance) from by ring1).trans_lt finite

variable (firstDefined : expression.Defined firstPoint) (middleDefined : expression.Defined middlePoint)
    (lastDefined : expression.Defined lastPoint)
    (beforeDefined : Defined expression before) (afterDefined : Defined expression after)

/-- Scheduled original observations, four actual endpoint comparisons and both unchanged moving Spines.

The count-four request precedes every coefficient observation. The three
external Vertices are retained once, with the middle cache literally shared
by the two joined Spines. The separate four-jump list names only these
endpoint handoffs, including both joins of an empty moving word.
-/
@[expose] def EndpointConsumer (request : AccuracyRequest) (Result : Type u) :=
  (accuracy : AccuracyRequest) → accuracy = localRequest request 4 →
  (first : Vertex expression firstPoint outerFirst accuracy) →
  first = Vertex.build expression firstPoint outerFirst accuracy firstDefined →
  (middle : Vertex expression middlePoint outerMiddle accuracy) →
  middle = Vertex.build expression middlePoint outerMiddle accuracy middleDefined →
  (last : Vertex expression lastPoint outerLast accuracy) →
  last = Vertex.build expression lastPoint outerLast accuracy lastDefined →
  (beforeMoving : Spine expression accuracy before) →
  beforeMoving = Spine.build (expression := expression) (accuracy := accuracy) before beforeDefined →
  (afterMoving : Spine expression accuracy after) →
  afterMoving = Spine.build (expression := expression) (accuracy := accuracy) after afterDefined →
  (firstCompared : JoinComparisons beforeMoving beforeSource beforeTarget first middle) →
  (lastCompared : JoinComparisons afterMoving afterSource afterTarget middle last) →
  (firstJoined : WithJoins beforeMoving beforeSource beforeTarget) →
  firstJoined.first = first → firstJoined.last = middle →
  HEq firstJoined.comparisons firstCompared →
  firstJoined.observed = attachSpines beforeMoving beforeSource beforeTarget first middle firstCompared →
  (lastJoined : WithJoins afterMoving afterSource afterTarget) →
  lastJoined.first = middle → lastJoined.last = last →
  HEq lastJoined.comparisons lastCompared →
  lastJoined.observed = attachSpines afterMoving afterSource afterTarget middle last lastCompared →
  (jumps : List Canonical) →
  jumps = [-firstCompared.1.val.residual, -firstCompared.2.val.residual,
    -lastCompared.1.val.residual, -lastCompared.2.val.residual] →
  jumps.length = 4 →
  (∀ value ∈ jumps, Norm.Basic.normSq value ≤ accuracy.tolerance) →
  (change : Canonical) →
  change = (last.value - first.value) -
    ((beforeMoving.last.value - beforeMoving.first.value) +
      (afterMoving.last.value - afterMoving.first.value)) →
  change = Norm.Sum.Basic.gaussianSum jumps →
  Norm.Basic.normSq change ≤ 16 * accuracy.tolerance →
  Norm.Basic.normSq change < request.tolerance → Result

/-- Observe the same two moving paths and pay their four actual endpoint joins at one preselected request.

Only the actual supplied joins determine stationary comparisons. The
original moving paths are observed once each; three original external
Owners are observed once each, sharing the middle Vertex. The original
increment comparison laws and finite count schedule derive the payment.
This pays neither internal moving-path handoffs nor independent primitive
constants or an entire geometric integral.
-/
def withEndpointJoins (request : AccuracyRequest) {Result : Type u}
    (consume : EndpointConsumer (expression := expression) before after
      beforeSource beforeTarget afterSource afterTarget
      firstDefined middleDefined lastDefined beforeDefined afterDefined request Result) : Result :=
  let accuracy := localRequest request 4
  let first := Vertex.build expression firstPoint outerFirst accuracy firstDefined
  let middle := Vertex.build expression middlePoint outerMiddle accuracy middleDefined
  let last := Vertex.build expression lastPoint outerLast accuracy lastDefined
  let beforeMoving := Spine.build (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) before beforeDefined
  let afterMoving := Spine.build (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) after afterDefined
  let beforeFirst := Spine.first (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (path := before) beforeMoving
  let beforeLast := Spine.last (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (path := before) beforeMoving
  let afterFirst := Spine.first (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (path := after) afterMoving
  let afterLast := Spine.last (polynomial := polynomial) (expression := expression)
    (accuracy := accuracy) (path := after) afterMoving
  let firstSource := Stationary.compare (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    (OwnerLink.stationary polynomial firstPoint beforeSource) rfl first beforeFirst
  let firstTarget := Stationary.compare (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    (OwnerLink.stationary polynomial middlePoint beforeTarget) rfl beforeLast middle
  let lastSource := Stationary.compare (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    (OwnerLink.stationary polynomial middlePoint afterSource) rfl middle afterFirst
  let lastTarget := Stationary.compare (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    (OwnerLink.stationary polynomial lastPoint afterTarget) rfl afterLast last
  let firstCompared : JoinComparisons (polynomial := polynomial) (expression := expression)
      (accuracy := accuracy) beforeMoving beforeSource beforeTarget first middle :=
    ⟨⟨firstSource, rfl⟩, ⟨firstTarget, rfl⟩⟩
  let lastCompared : JoinComparisons (polynomial := polynomial) (expression := expression)
      (accuracy := accuracy) afterMoving afterSource afterTarget middle last :=
    ⟨⟨lastSource, rfl⟩, ⟨lastTarget, rfl⟩⟩
  let firstObserved := attachSpines (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    beforeMoving beforeSource beforeTarget first middle firstCompared
  let lastObserved := attachSpines (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    afterMoving afterSource afterTarget middle last lastCompared
  let firstJoined : WithJoins (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      beforeMoving beforeSource beforeTarget := ⟨first, middle, firstCompared, ⟨firstObserved, rfl⟩⟩
  let lastJoined : WithJoins (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      afterMoving afterSource afterTarget := ⟨middle, last, lastCompared, ⟨lastObserved, rfl⟩⟩
  let jumps := [-firstCompared.1.val.residual, -firstCompared.2.val.residual,
    -lastCompared.1.val.residual, -lastCompared.2.val.residual]
  have firstSourceEq := comparison_jump first beforeFirst firstCompared.1.val
  have firstTargetEq := comparison_jump beforeLast middle firstCompared.2.val
  have lastSourceEq := comparison_jump middle afterFirst lastCompared.1.val
  have lastTargetEq := comparison_jump afterLast last lastCompared.2.val
  have bounded : ∀ value ∈ jumps, Norm.Basic.normSq value ≤ accuracy.tolerance := by
    intro value member
    rcases Membership.mem_cons.mp member with equal | member
    · cases equal
      exact (congrArg Norm.Basic.normSq firstSourceEq).trans_le
        (Stationary.jump_lt first beforeFirst firstCompared.1.val).le
    · rcases Membership.mem_cons.mp member with equal | member
      · cases equal
        exact (congrArg Norm.Basic.normSq firstTargetEq).trans_le
          (Stationary.jump_lt beforeLast middle firstCompared.2.val).le
      · rcases Membership.mem_cons.mp member with equal | member
        · cases equal
          exact (congrArg Norm.Basic.normSq lastSourceEq).trans_le
            (Stationary.jump_lt middle afterFirst lastCompared.1.val).le
        · rcases Membership.mem_cons.mp member with equal | member
          · cases equal
            exact (congrArg Norm.Basic.normSq lastTargetEq).trans_le
              (Stationary.jump_lt afterLast last lastCompared.2.val).le
          · cases member
  let change := (last.value - first.value) -
    ((beforeLast.value - beforeFirst.value) +
      (afterLast.value - afterFirst.value))
  have changeEq : change = Norm.Sum.Basic.gaussianSum jumps := by
    change _ = -firstCompared.1.val.residual + (-firstCompared.2.val.residual +
      (-lastCompared.1.val.residual + (-lastCompared.2.val.residual + 0)))
    rewrite [firstSourceEq, firstTargetEq, lastSourceEq, lastTargetEq]
    change (last.value - first.value) -
      ((beforeLast.value - beforeFirst.value) +
        (afterLast.value - afterFirst.value)) = _
    ring1
  have finite : Norm.Basic.normSq change ≤ 16 * accuracy.tolerance :=
    endpoint_change_le (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      (before := before) (after := after) (beforeSource := beforeSource) (beforeTarget := beforeTarget)
      (afterSource := afterSource) (afterTarget := afterTarget) beforeMoving afterMoving firstJoined lastJoined rfl
  have paid : Norm.Basic.normSq change < request.tolerance := finite.trans_lt (endpoint_schedule request)
  consume accuracy rfl first rfl middle rfl last rfl beforeMoving rfl afterMoving rfl firstCompared lastCompared
    firstJoined rfl rfl (HEq.refl firstCompared) rfl lastJoined rfl rfl (HEq.refl lastCompared) rfl
    jumps rfl rfl bounded change rfl changeEq finite paid

end EndpointJoins

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

end
