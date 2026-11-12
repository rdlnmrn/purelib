module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins.Payment
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Sewing
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Tactic.QuotientFreeOmega

/-! # Requested payment for all handoffs on two retained joined paths

The original trace-link count and four explicit endpoint joins are known
before coefficient observations. An inverse allocation and the original
minimum request select one endpoint acquisition paying both endpoint changes and
the entire stationary-jump list. Existing joined Spines are appended at
their identical middle Vertex; no observation or root transport is replayed.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

universe u

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}
    {firstPoint middlePoint lastPoint : Canonical}
    {outerFirst : Owner (polynomial.eval firstPoint)} {outerMiddle : Owner (polynomial.eval middlePoint)}
    {outerLast : Owner (polynomial.eval lastPoint)}
    {innerFirst : Owner (polynomial.eval firstPoint)}
    {innerMiddleBefore innerMiddleAfter : Owner (polynomial.eval middlePoint)}
    {innerLast : Owner (polynomial.eval lastPoint)}
    (before : OwnerPath polynomial firstPoint innerFirst middlePoint innerMiddleBefore)
    (after : OwnerPath polynomial middlePoint innerMiddleAfter lastPoint innerLast)
    (beforeSource : OwnerJoin outerFirst innerFirst) (beforeTarget : OwnerJoin innerMiddleBefore outerMiddle)
    (afterSource : OwnerJoin outerMiddle innerMiddleAfter) (afterTarget : OwnerJoin innerLast outerLast)

namespace WithJoins

variable {before after beforeSource beforeTarget afterSource afterTarget}
    (beforeMoving : Spine expression accuracy before) (afterMoving : Spine expression accuracy after)
    (firstJoined : WithJoins beforeMoving beforeSource beforeTarget)
    (lastJoined : WithJoins afterMoving afterSource afterTarget)
    (shared : firstJoined.last = lastJoined.first)

/-- Append both existing joined Spines at their same whole middle Vertex, retaining the outer endpoints unchanged. -/
def append : Between (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    firstJoined.first lastJoined.last :=
  let same := lastJoined.observed_first.trans (shared.symm.trans firstJoined.observed_last.symm)
  let observed := Spine.append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    firstJoined.observed lastJoined.observed same
  ⟨(before.withJoins beforeSource beforeTarget).append (after.withJoins afterSource afterTarget),
    ⟨observed,
      ⟨(Spine.append_first firstJoined.observed lastJoined.observed same).trans firstJoined.observed_first,
        (Spine.append_last firstJoined.observed lastJoined.observed same).trans lastJoined.observed_last⟩⟩⟩

/-- The appended cache keeps exactly the two original paths with their same four supplied endpoint joins. -/
theorem append_path :
    (append beforeMoving afterMoving firstJoined lastJoined shared).1 =
      (before.withJoins beforeSource beforeTarget).append (after.withJoins afterSource afterTarget) := by
  unfold append
  rfl

/-- The actual combined observation cache is the original append of the two supplied complete joined caches. -/
theorem append_observed :
    HEq (append beforeMoving afterMoving firstJoined lastJoined shared).2.val
      (Spine.append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
        firstJoined.observed lastJoined.observed
        (lastJoined.observed_first.trans (shared.symm.trans firstJoined.observed_last.symm))) := by
  unfold append
  rfl

end WithJoins

/-- The exact composed path has both original trace counts and four retained endpoint-link occurrences. -/
private theorem joined_count :
    ((before.withJoins beforeSource beforeTarget).append
      (after.withJoins afterSource afterTarget)).vertices.length =
      before.vertices.length + after.vertices.length + 4 := by
  rewrite [OwnerPath.append_vertices, Append.length_append,
    OwnerPath.withJoins_vertices, OwnerPath.withJoins_vertices]
  change ((before.vertices ++ [middlePoint]).length + 1) +
    ((after.vertices ++ [lastPoint]).length + 1) = _
  rewrite [Append.length_append, Append.length_append]
  change ((before.vertices.length + 1) + 1) + ((after.vertices.length + 1) + 1) = _
  omega0

/-- Choose one actual endpoint request paying both its original demand and the full retained handoff count.

The inverse count-four request is computed from the full path local
allowance. The minimum is taken before coefficient observations, without
altering either original positive request or any completed reading.
-/
@[expose] def handoffRequest (endpointTarget handoffTarget : AccuracyRequest) : AccuracyRequest :=
  endpointTarget.minimum
    (requestFor (localRequest handoffTarget (before.vertices.length + after.vertices.length + 4)) 4)

/-- The selected endpoint request pays the original independent endpoint demand. -/
theorem handoffRequest_le_endpoint (endpointTarget handoffTarget : AccuracyRequest) :
    (handoffRequest before after endpointTarget handoffTarget).tolerance ≤ endpointTarget.tolerance :=
  AccuracyRequest.minimum_le_left _ _

/-- The same preselected request gives the original local allowance for every retained full path occurrence. -/
theorem handoffRequest_local_bound (endpointTarget handoffTarget : AccuracyRequest) :
    (localRequest (handoffRequest before after endpointTarget handoffTarget) 4).tolerance ≤
      Aggregate.perTerm handoffTarget.tolerance (before.vertices.length + after.vertices.length + 4) := by
  let reserved := localRequest handoffTarget (before.vertices.length + after.vertices.length + 4)
  have selected : (handoffRequest before after endpointTarget handoffTarget).tolerance ≤
      (requestFor reserved 4).tolerance := AccuracyRequest.minimum_le_right _ _
  have scaled := Aggregate.perTerm_mono selected 4
  have inverse := congrArg AccuracyRequest.tolerance (localRequest_requestFor reserved 4)
  exact scaled.trans_eq inverse

/-- One actual complete joined Spine with its original outer Vertices, exact path/count readbacks and requested payment.

The existing Between container retains the constructed path and complete
observation cache. The subtype certifies its same four-join path, literal
occurrence count and actual stationary-jump sum; no replacement owner or
new context record is introduced.
-/
@[expose] def HandoffCompletion (endpointTarget handoffTarget : AccuracyRequest) :=
  let selected := handoffRequest before after endpointTarget handoffTarget
  Σ first : Vertex expression firstPoint outerFirst (localRequest selected 4),
  Σ last : Vertex expression lastPoint outerLast (localRequest selected 4),
  {whole : Between (polynomial := polynomial) (expression := expression)
      (accuracy := localRequest selected 4) first last //
    whole.1 = (before.withJoins beforeSource beforeTarget).append (after.withJoins afterSource afterTarget) ∧
    whole.1.vertices.length = before.vertices.length + after.vertices.length + 4 ∧
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum whole.2.val.jumps) < handoffTarget.tolerance}

namespace HandoffCompletion

variable {before after beforeSource beforeTarget afterSource afterTarget}
    (endpointTarget handoffTarget : AccuracyRequest)
    (completed : HandoffCompletion (expression := expression) before after
      beforeSource beforeTarget afterSource afterTarget endpointTarget handoffTarget)

/-- Read the same original outer source Vertex retained by the complete observation. -/
@[expose] def first : Vertex expression firstPoint outerFirst
    (localRequest (handoffRequest before after endpointTarget handoffTarget) 4) := completed.1

/-- Read the same original outer target Vertex retained by the complete observation. -/
@[expose] def last : Vertex expression lastPoint outerLast
    (localRequest (handoffRequest before after endpointTarget handoffTarget) 4) := completed.2.1

/-- Read the actual concatenated path on the unchanged outer Owners. -/
@[expose] def path : OwnerPath polynomial firstPoint outerFirst lastPoint outerLast := completed.2.2.val.1

/-- Read the whole combined original Spine with all retained internal and endpoint comparisons. -/
@[expose] def observed : Spine expression
    (localRequest (handoffRequest before after endpointTarget handoffTarget) 4)
    (path endpointTarget handoffTarget completed) := completed.2.2.val.2.val

/-- The complete observed path retains exactly the original two traces and their same four joins. -/
theorem path_eq : path endpointTarget handoffTarget completed =
    (before.withJoins beforeSource beforeTarget).append (after.withJoins afterSource afterTarget) :=
  completed.2.2.property.1

/-- The actual complete path count includes every original trace link and four endpoint occurrences. -/
theorem count_eq : (path endpointTarget handoffTarget completed).vertices.length =
    before.vertices.length + after.vertices.length + 4 := completed.2.2.property.2.1

/-- The actual jump list retains one occurrence for every original joined-path link. -/
theorem jumps_length : (observed endpointTarget handoffTarget completed).jumps.length =
    before.vertices.length + after.vertices.length + 4 := by
  let sampled := observed endpointTarget handoffTarget completed
  exact (Tail.jumps_length (polynomial := polynomial) (expression := expression)
    (accuracy := localRequest (handoffRequest before after endpointTarget handoffTarget) 4)
    (path endpointTarget handoffTarget completed)
    (Spine.first (polynomial := polynomial) (expression := expression)
      (accuracy := localRequest (handoffRequest before after endpointTarget handoffTarget) 4)
      (path := path endpointTarget handoffTarget completed) sampled) sampled.2).trans
    (count_eq endpointTarget handoffTarget completed)

/-- The whole original first observation is the retained outer source Vertex. -/
theorem first_eq : (observed endpointTarget handoffTarget completed).first =
    first endpointTarget handoffTarget completed := completed.2.2.val.2.property.1

/-- The whole original final observation is the retained outer target Vertex. -/
theorem last_eq : (observed endpointTarget handoffTarget completed).last =
    last endpointTarget handoffTarget completed := completed.2.2.val.2.property.2

/-- The whole stationary-jump sum pays the requested original handoff demand. -/
theorem error_lt : Norm.Basic.normSq
    (Norm.Sum.Basic.gaussianSum (observed endpointTarget handoffTarget completed).jumps) < handoffTarget.tolerance :=
  completed.2.2.property.2.2

end HandoffCompletion

variable (firstDefined : expression.Defined firstPoint) (middleDefined : expression.Defined middlePoint)
    (lastDefined : expression.Defined lastPoint)
    (beforeDefined : Defined expression before) (afterDefined : Defined expression after)

/-- Acquire one endpoint observation run and pay every actual stationary handoff on its combined retained path.

The request is selected before observations. The original callback sees
all original endpoint caches unchanged. The returned completion appends those same two
joined Spines at their shared middle Vertex, using the actual count and
original jump-payment theorem. Moving integral increments and primitive
constant normalization are separate from this stationary-jump sum.
-/
def withHandoffPayment (endpointTarget handoffTarget : AccuracyRequest) {Result : Type u}
    (consume : EndpointConsumer (expression := expression) before after
      beforeSource beforeTarget afterSource afterTarget firstDefined middleDefined lastDefined
      beforeDefined afterDefined (handoffRequest before after endpointTarget handoffTarget) Result) :
    HandoffCompletion (expression := expression) before after beforeSource beforeTarget afterSource afterTarget
      endpointTarget handoffTarget × Result :=
  let selected := handoffRequest before after endpointTarget handoffTarget
  withEndpointJoins (polynomial := polynomial) (expression := expression)
    (before := before) (after := after) (beforeSource := beforeSource) (beforeTarget := beforeTarget)
    (afterSource := afterSource) (afterTarget := afterTarget)
    (firstDefined := firstDefined) (middleDefined := middleDefined) (lastDefined := lastDefined)
    (beforeDefined := beforeDefined) (afterDefined := afterDefined) selected
    (fun accuracy accuracyEq first firstEq middle middleEq last lastEq beforeMoving beforeMovingEq
      afterMoving afterMovingEq firstCompared lastCompared firstJoined firstFirstEq firstMiddleEq
      firstComparedEq firstObservedEq lastJoined lastMiddleEq lastLastEq lastComparedEq lastObservedEq
      jumps jumpsEq jumpsCount jumpsBound change changeEq changeSum changeBound endpointPaid => by
      cases accuracyEq
      have shared : firstJoined.last = lastJoined.first := firstMiddleEq.trans lastMiddleEq.symm
      let whole := WithJoins.append (polynomial := polynomial) (expression := expression)
        (accuracy := localRequest selected 4) beforeMoving afterMoving firstJoined lastJoined shared
      have pathEq := WithJoins.append_path (polynomial := polynomial) (expression := expression)
        (accuracy := localRequest selected 4) beforeMoving afterMoving firstJoined lastJoined shared
      have counted : whole.1.vertices.length = before.vertices.length + after.vertices.length + 4 :=
        (congrArg (fun path : OwnerPath polynomial firstPoint outerFirst lastPoint outerLast =>
          path.vertices.length) pathEq).trans
          (joined_count (before := before) (after := after) (beforeSource := beforeSource)
            (beforeTarget := beforeTarget) (afterSource := afterSource) (afterTarget := afterTarget))
      have paid := Spine.jumps_error_lt (polynomial := polynomial) (expression := expression)
        (accuracy := localRequest selected 4) (path := whole.1) whole.2.val handoffTarget.positive counted.le
        (handoffRequest_local_bound before after endpointTarget handoffTarget)
      let completed : HandoffCompletion (polynomial := polynomial) (expression := expression)
          before after beforeSource beforeTarget afterSource afterTarget endpointTarget handoffTarget :=
        ⟨firstJoined.first, lastJoined.last, ⟨whole, ⟨pathEq, counted, paid⟩⟩⟩
      exact ⟨completed,
        consume (localRequest selected 4) rfl first firstEq middle middleEq last lastEq beforeMoving beforeMovingEq
          afterMoving afterMovingEq firstCompared lastCompared firstJoined firstFirstEq firstMiddleEq
          firstComparedEq firstObservedEq lastJoined lastMiddleEq lastLastEq lastComparedEq lastObservedEq
          jumps jumpsEq jumpsCount jumpsBound change changeEq changeSum changeBound endpointPaid⟩)

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

end
