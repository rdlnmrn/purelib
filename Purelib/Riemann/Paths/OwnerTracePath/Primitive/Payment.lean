module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Count-paid stationary observations on the actual original owner path

The original finite aggregate allowance pays both factors of the actual
path-link count. Each stationary sample jump is derived from its unchanged
observations and stored link certificate. A new acquisition computes the
count-dependent request first, then constructs genuinely shrinking original
vertex observations. Selecting a smaller auxiliary comparison target never
substitutes for shrinking those actual original observation requests.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

variable {polynomial : Coefficients} {expression : Expression polynomial}
variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start left finish right}

namespace Spine

variable {accuracy : AccuracyRequest}

/-- The accumulated actual stationary jumps are paid by both factors of the unchanged original path-link count. -/
theorem jumps_error_le (observed : Spine expression accuracy path) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum observed.jumps) ≤
      (path.vertices.length : Rational) * ((path.vertices.length : Rational) * accuracy.tolerance) := by
  have bounded := Norm.Sum.Bounds.normSq_sum_le observed.jumps accuracy.tolerance
    (Tail.jumps_bounded path observed.first observed.2)
  have length : observed.jumps.length = path.vertices.length := Tail.jumps_length path observed.first observed.2
  rewrite [length] at bounded
  exact bounded

/-- A genuine count-dependent bound on the original local request pays the complete stationary-jump sum. -/
theorem jumps_error_lt (observed : Spine expression accuracy path) {target : Rational} (positive : 0 < target)
    {budgetCount : Nat} (countBound : path.vertices.length ≤ budgetCount)
    (localBound : accuracy.tolerance ≤ Aggregate.perTerm target budgetCount) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum observed.jumps) < target := by
  have payment := Aggregate.count_mul_allowance_lt countBound positive localBound
  simp only [Aggregate.countCoordinate_eq] at payment
  exact observed.jumps_error_le.trans_lt payment

end Spine

namespace Closing

variable {base : Canonical} {source target : Owner (polynomial.eval base)}
variable {returning : OwnerPath polynomial base source base target} {accuracy : AccuracyRequest}

/-- The actual closing comparison consumes the same retained final and initial observations and literal original join.

Its complete generic Comparison is stored with the exact original join
comparison factory equation. No observation, trace or join is acquired
again. This extra closing edge is kept separate from the original OwnerPath.
-/
@[expose] def Comparison (observed : Spine expression accuracy returning) (join : OwnerJoin target source) :=
  { retained : Observation.Comparison observed.last.observation observed.first.observation
      (tailRequest accuracy).tolerance //
    retained = join.compareDenotations observed.last.original observed.first.original
      observed.last.observation observed.first.observation (tailRequest accuracy) }

namespace Comparison

/-- Retain one actual closing comparison on the identical original last and first primitive observation caches. -/
def build (observed : Spine expression accuracy returning) (join : OwnerJoin target source) :
    Comparison observed join :=
  ⟨join.compareDenotations observed.last.original observed.first.original
    observed.last.observation observed.first.observation (tailRequest accuracy), rfl⟩

variable {observed : Spine expression accuracy returning} {join : OwnerJoin target source}
variable (compared : Comparison observed join)

/-- Read the signed closing primitive jump from the SAME original comparison's retained residual cache. -/
@[expose] def jump : Canonical := -compared.val.residual

/-- The retained closing residual has the original last-to-first path orientation. -/
theorem jump_eq : compared.jump = observed.first.value - observed.last.value := by
  change -compared.val.residual = _
  rewrite [compared.val.residual_eq]
  change -(observed.last.value - observed.first.value) = observed.first.value - observed.last.value
  ring1

/-- Both old closing endpoint requests and the actual tail target pay the exact signed closing primitive jump. -/
theorem jump_lt : Norm.Basic.normSq compared.jump < accuracy.tolerance := by
  rewrite [compared.jump_eq]
  exact Stationary.jump_lt observed.last observed.first compared.val

/-- The actual returned-minus-initial residual and literal closing jump cancel with the same integral value. -/
theorem integral_eq_neg_return_residual_add_jump (integral : Canonical) :
    integral = -(((observed.last.value - observed.first.value) - integral) + compared.jump) := by
  rewrite [compared.jump_eq]
  ring1

/-- The literal closing comparison pays an arbitrary retained integral through its actual return residual.

The same old final and initial values occur in both the return residual
and this comparison. Their signed differences cancel exactly. The actual
closing observation radii and tail target are charged by `jump_lt`.
-/
theorem integral_le_return_residual (compared : Comparison observed join) (integral : Canonical) :
    Norm.Basic.normSq integral ≤
      2 * (Norm.Basic.normSq ((observed.last.value - observed.first.value) - integral) + accuracy.tolerance) := by
  calc
    Norm.Basic.normSq integral = Norm.Basic.normSq
        (-(((observed.last.value - observed.first.value) - integral) + compared.jump)) :=
      congrArg Norm.Basic.normSq (compared.integral_eq_neg_return_residual_add_jump integral)
    _ = Norm.Basic.normSq (((observed.last.value - observed.first.value) - integral) + compared.jump) :=
      Norm.Basic.normSq_neg _
    _ ≤ 2 * (Norm.Basic.normSq ((observed.last.value - observed.first.value) - integral) + accuracy.tolerance) :=
      (Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) compared.jump_lt.le)
          (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))

/-- Read all stationary path jumps followed by the literal join's signed closing jump, retaining their exact order. -/
@[expose] def jumps : List Canonical := observed.jumps ++ [compared.jump]

/-- The closing comparison contributes exactly one additional occurrence beyond the same original path-link count. -/
theorem jumps_length : compared.jumps.length = returning.vertices.length + 1 := by
  change (observed.jumps ++ [compared.jump]).length = _
  rewrite [Append.length_append]
  change observed.jumps.length + 1 = _
  exact congrArg (· + 1) (Tail.jumps_length returning observed.first observed.2)

/-- Every stationary occurrence, including the actual closing join, pays its own unchanged original observation data. -/
theorem jumps_bounded : ∀ jump ∈ compared.jumps, Norm.Basic.normSq jump ≤ accuracy.tolerance := by
  intro jump member
  rcases Membership.mem_append.mp member with member | member
  · exact Tail.jumps_bounded returning observed.first observed.2 jump member
  · cases member with
    | head => exact compared.jump_lt.le
    | tail _ empty => cases empty

/-- The actual vertex count pays every original stationary path jump and the retained closing join. -/
theorem error_lt {request : AccuracyRequest}
    (localBound : accuracy.tolerance ≤ Aggregate.perTerm request.tolerance (returning.vertices.length + 1)) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum compared.jumps) < request.tolerance := by
  have bounded := Norm.Sum.Bounds.normSq_sum_le compared.jumps accuracy.tolerance compared.jumps_bounded
  rewrite [compared.jumps_length] at bounded
  have payment := Aggregate.count_mul_allowance_lt (Nat.le_refl (returning.vertices.length + 1))
    request.positive localBound
  simp only [Aggregate.countCoordinate_eq] at payment
  exact bounded.trans_lt payment

end Comparison

end Closing

/-- Compute the original finite aggregate allowance as one actual positive local AccuracyRequest. -/
@[expose] def localRequest (request : AccuracyRequest) (count : Nat) : AccuracyRequest :=
  ⟨Aggregate.perTerm request.tolerance count, Aggregate.perTerm_positive request.positive count⟩

/-- Compute the positive whole-path request whose original count allocation is the exact supplied local request.

The retained count is the original observer's budget count, including its
reserved closing occurrence. No observation is constructed or weakened.
-/
@[expose] def requestFor (accuracy : AccuracyRequest) (count : Nat) : AccuracyRequest :=
  ⟨Aggregate.targetFor accuracy.tolerance count, Aggregate.targetFor_positive accuracy.positive count⟩

/-- The inverse allocation retains the original binary count and supplied exact local tolerance. -/
theorem requestFor_tolerance (accuracy : AccuracyRequest) (count : Nat) :
    (requestFor accuracy count).tolerance = Aggregate.targetFor accuracy.tolerance count := rfl

/-- The original local request factory recovers the SAME exact supplied local request. -/
theorem localRequest_requestFor (accuracy : AccuracyRequest) (count : Nat) :
    localRequest (requestFor accuracy count) count = accuracy :=
  AccuracyRequest.eq_of_tolerance_eq (Aggregate.perTerm_targetFor accuracy.tolerance count)

/-- One automatic original-path observation acquisition retains its actual vertex list, local request and whole spine.

The literal vertex-list readback is computed once from the supplied path.
The vertex count reserves one occurrence for an optional closing join.
The count-dependent local request is computed before any primitive
observation. Every original observation and stationary Comparison is then
retained in the same actual Spine, with its whole factory equation. No
OwnerPath or continuation is reconstructed.
-/
@[expose] def Acquisition (path : OwnerPath polynomial start left finish right)
    (defined : Defined expression path) (request : AccuracyRequest) :=
  Σ vertices : { retained : List Canonical // retained = path.vertices },
    Σ accuracy : { retained : AccuracyRequest // retained = localRequest request (vertices.val.length + 1) },
      { observed : Spine expression accuracy.val path //
        observed = Spine.build (expression := expression) (accuracy := accuracy.val) path defined }

namespace Acquisition

variable {defined : Defined expression path} {request : AccuracyRequest}

/-- Select sufficient original requests and retain one actual primitive-observation spine on this SAME path. -/
def build (path : OwnerPath polynomial start left finish right) (defined : Defined expression path)
    (request : AccuracyRequest) : Acquisition path defined request :=
  let vertices := path.vertices
  let accuracy := localRequest request (vertices.length + 1)
  let observed := Spine.build (expression := expression) (accuracy := accuracy) path defined
  ⟨⟨vertices, rfl⟩, ⟨accuracy, rfl⟩, ⟨observed, rfl⟩⟩

/-- Retain the original vertex list once before computing requests and observing the SAME supplied path.

The exact list identity belongs to the original path. The old observer and
all stationary factories run once using its actual count-derived request.
-/
def ofVertices (path : OwnerPath polynomial start left finish right) (defined : Defined expression path)
    (vertices : List Canonical) (same : vertices = path.vertices) (request : AccuracyRequest) :
    Acquisition path defined request :=
  let accuracy := localRequest request (vertices.length + 1)
  let observed := Spine.build (expression := expression) (accuracy := accuracy) path defined
  ⟨⟨vertices, same⟩, ⟨accuracy, rfl⟩, ⟨observed, rfl⟩⟩

/-- The whole original vertex/accuracy/observation cache is its SAME original factory on the retained exact list. -/
theorem ofVertices_eq (path : OwnerPath polynomial start left finish right) (defined : Defined expression path)
    (vertices : List Canonical) (same : vertices = path.vertices) (request : AccuracyRequest) :
    ofVertices path defined vertices same request = build path defined request := by
  cases same
  rfl

variable (acquired : Acquisition path defined request)

/-- Read the exact retained original owner-path vertex list used for the finite count budget. -/
@[expose] def vertices : List Canonical := acquired.1.val

/-- Read the same actual original local request computed before all retained primitive observations. -/
@[expose] def accuracy : AccuracyRequest := acquired.2.1.val

/-- Read the entire actual ordered original primitive-observation and stationary-comparison cache unchanged. -/
@[expose] def observed : Spine expression acquired.accuracy path := acquired.2.2.val

/-- The count uses precisely the same original owner-path vertex list. -/
theorem vertices_eq : acquired.vertices = path.vertices := acquired.1.property

/-- The retained original local request is the exact count-dependent aggregate factory on these stored vertices. -/
theorem accuracy_eq : acquired.accuracy = localRequest request (acquired.vertices.length + 1) :=
  acquired.2.1.property

/-- The entire observation spine is the same factory result at this retained request and original path. -/
theorem observed_eq : acquired.observed = Spine.build (expression := expression) (accuracy := acquired.accuracy)
    path defined := acquired.2.2.property

/-- The same retained request and original vertex-list readbacks give the exact count-dependent local allocation. -/
theorem accuracy_tolerance : acquired.accuracy.tolerance =
    Aggregate.perTerm request.tolerance (path.vertices.length + 1) := by
  rewrite [acquired.accuracy_eq]
  change Aggregate.perTerm request.tolerance (acquired.vertices.length + 1) =
    Aggregate.perTerm request.tolerance (path.vertices.length + 1)
  exact congrArg (fun count => Aggregate.perTerm request.tolerance (count + 1))
    (congrArg List.length acquired.vertices_eq)

/-- The computed local request pays the actual old observation radii and all finite stationary sample jumps. -/
theorem error_lt : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum acquired.observed.jumps) < request.tolerance :=
  acquired.observed.jumps_error_lt request.positive (Nat.le_succ _) acquired.accuracy_tolerance.le

/-- Every complete original acquisition is the identical whole factory result fixed by its retained cache laws. -/
theorem eq_build : acquired = build path defined request := by
  cases acquired with
  | mk vertices rest =>
    cases vertices with
    | mk vertices verticesEq =>
      cases verticesEq
      cases rest with
      | mk accuracy observed =>
        cases accuracy with
        | mk accuracy accuracyEq =>
          cases accuracyEq
          cases observed with
          | mk observed observedEq =>
            cases observedEq
            rfl

end Acquisition

section Returning

variable {base : Canonical} {source target : Owner (polynomial.eval base)}
variable (returning : OwnerPath polynomial base source base target)
variable (defined : Defined expression returning) (join : OwnerJoin target source)

section Complete

variable (request : AccuracyRequest)

/-- One original-path acquisition and its literal closing comparison retain every complete factory cache.

The same expression and original vertex guards index both inputs. The
closing factory consumes the acquisition's identical old last and first
observations; no root, path, OwnerJoin or endpoint observation is rerun.
-/
@[expose] def Closed :=
  Σ observations : { retained : Acquisition returning defined request //
      retained = Acquisition.build returning defined request },
    { compared : Closing.Comparison observations.val.observed join //
      compared = Closing.Comparison.build observations.val.observed join }

namespace Closed

/-- Retain an already completed original acquisition and construct only its closing comparison on the SAME old
vertices. -/
def ofAcquisition (observations : Acquisition returning defined request) : Closed returning defined join request :=
  let compared := Closing.Comparison.build observations.observed join
  ⟨⟨observations, Acquisition.eq_build observations⟩, ⟨compared, rfl⟩⟩

/-- Construct the original complete observation execution once and compare its old endpoints through this literal
join. -/
def build : Closed returning defined join request :=
  let observations := Acquisition.build returning defined request
  ofAcquisition returning defined join request observations

/-- Use the exact already cached original vertex list to compute requests before observing this SAME original path. -/
def ofVertices (vertices : List Canonical) (same : vertices = returning.vertices) :
    Closed returning defined join request :=
  let observations := Acquisition.ofVertices returning defined vertices same request
  ofAcquisition returning defined join request observations

/-- The complete closing acquisition is the identical original factory after exact retained vertex-list transport. -/
theorem ofVertices_eq (vertices : List Canonical) (same : vertices = returning.vertices) :
    ofVertices returning defined join request vertices same = build returning defined join request := by
  cases same
  rfl

variable {returning defined join request}
variable (retained : Closed returning defined join request)

/-- Read the whole original observation/request execution unchanged. -/
@[expose] def observations : Acquisition returning defined request := retained.1.val

/-- Read the literal closing comparison on these SAME original old endpoint observations and original join. -/
@[expose] def closing : Closing.Comparison retained.observations.observed join := retained.2.val

/-- The complete old observation execution is the original factory on this exact path and supplied guards. -/
theorem observations_eq : retained.observations = Acquisition.build returning defined request := retained.1.property

/-- The whole old closing comparison is its original factory on the same retained original endpoint observations. -/
theorem closing_eq : retained.closing = Closing.Comparison.build retained.observations.observed join :=
  retained.2.property

/-- Every complete old closing execution is the SAME whole factory fixed by its retained original cache laws. -/
theorem eq_build : retained = build returning defined join request := by
  cases retained with
  | mk observations compared =>
    cases observations with
    | mk observations observationsEq =>
      cases observationsEq
      cases compared with
      | mk compared comparedEq =>
        cases comparedEq
        rfl

/-- The original count-dependent request pays all actual stationary occurrences and this SAME literal closing join. -/
theorem error_lt : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum retained.closing.jumps) < request.tolerance :=
  retained.closing.error_lt retained.observations.accuracy_tolerance.le

end Closed

end Complete

namespace Closed

variable (accuracy : AccuracyRequest)

/-- An exact-local-accuracy acquisition retains its original vertex list, inverse request and closing execution.

The count is computed before observations. The inverse aggregate request
makes the original observer's local request exactly the supplied accuracy,
while every retained observation and comparison is constructed only once.
-/
@[expose] def Requested :=
  Σ vertices : { retained : List Canonical // retained = returning.vertices },
    Σ request : { retained : AccuracyRequest //
        retained = requestFor accuracy (vertices.val.length + 1) },
      { closed : Closed returning defined join request.val //
        closed = Closed.ofVertices returning defined join request.val vertices.val vertices.property }

namespace Requested

/-- Cache the actual path vertices once, derive the inverse request, then observe and close that SAME supplied path
once. -/
def build : Closed.Requested returning defined join accuracy :=
  let vertices := returning.vertices
  let request := requestFor accuracy (vertices.length + 1)
  let closed := Closed.ofVertices returning defined join request vertices rfl
  ⟨⟨vertices, rfl⟩, ⟨request, rfl⟩, ⟨closed, rfl⟩⟩

variable {returning defined join accuracy}
variable (retained : Closed.Requested returning defined join accuracy)

/-- Read the identical original vertex list cached before the request and observer factories. -/
@[expose] def vertices : List Canonical := retained.1.val

/-- Read the exact original whole-path request computed from the supplied local accuracy and stored count. -/
@[expose] def request : AccuracyRequest := retained.2.1.val

/-- Read the complete actual old observation/closing execution at its exact original request. -/
@[expose] def closed : Closed returning defined join retained.request := retained.2.2.val

/-- The count uses the SAME literal original path vertices. -/
theorem vertices_eq : retained.vertices = returning.vertices := retained.1.property

/-- The whole-path request is the original inverse allocator on the identical retained count and local request. -/
theorem request_eq : retained.request = requestFor accuracy (retained.vertices.length + 1) := retained.2.1.property

/-- The completed old cache is the actual cached-vertices factory, with neither a second observer nor a second join. -/
theorem closed_factory_eq : retained.closed = Closed.ofVertices returning defined join retained.request
    retained.vertices retained.vertices_eq := retained.2.2.property

/-- The completed cache also obeys the original whole closing factory's exact contract. -/
theorem closed_eq : retained.closed = Closed.build returning defined join retained.request :=
  retained.closed_factory_eq.trans
    (Closed.ofVertices_eq returning defined join retained.request retained.vertices retained.vertices_eq)

/-- The original observer's retained local request is exactly the supplied request, with all old observations
unchanged. -/
theorem accuracy_eq : retained.closed.observations.accuracy = accuracy := by
  apply AccuracyRequest.eq_of_tolerance_eq
  have allocated := retained.closed.observations.accuracy_tolerance
  have count := congrArg (fun vertices : List Canonical => vertices.length + 1) retained.vertices_eq
  have requested := congrArg (fun original : AccuracyRequest =>
    Aggregate.perTerm original.tolerance (returning.vertices.length + 1)) retained.request_eq
  have counted := congrArg (fun original : Nat =>
    Aggregate.perTerm (requestFor accuracy original).tolerance (returning.vertices.length + 1)) count
  exact allocated.trans (requested.trans
    (counted.trans (Aggregate.perTerm_targetFor accuracy.tolerance (returning.vertices.length + 1))))

end Requested

end Closed

end Returning

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

end
