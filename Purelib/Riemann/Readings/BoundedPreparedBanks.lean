module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Paths.PreparedClearPathModels

public section

/-!
# Cheap certified attempts at a displayed dyadic bank

Try the bounded source preparation at each requested edge, with at most two
checked moving resets and no recursive retry loop or total uniform fallback.
Keep the actual accepted spine and prove
that the original canonical checker returns that very spine.  An unfinished
attempt retains its accepted prefix and the exact unresolved request.  It is
not a rejection of the original checker, which may do substantially more work.

Adaptive selection can advance its depth on these reports.  Its existing
sufficient-depth constructor remains the unconditional final fallback.
Accepted edges still use the original canonical transport and endpoint-owner
retention; that separate operation can perform a finite reset.  This module
does not claim a wall-time bound or remove every possible refinement cost.
-/

namespace Purelib.Riemann.Readings.BoundedPreparedBanks

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Readings
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint ownerAtStart CompleteSegment PreparedPath)

open Purelib.Polynomial in
set_option genInjectivity false in
/-- The exact stopping point and accepted prefix of a bounded segment scan.

Each accepted prefix node retains its cached source and checker equation; the final node records either unordered
parameters or the unresolved finite source request. -/
inductive StepFailure {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) → Owner (polynomial.eval (segment.pointAt current.parameter)) →
      List StepRequest → Type where
  /-- The next requested endpoint precedes the current parameter. -/ | unordered (current : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (request : StepRequest) (remaining : List StepRequest)
      (violated : ¬ current.parameter ≤ request.endpoint.parameter) :
      StepFailure segment within current owner (request :: remaining)
  /-- An ordered request has an inconclusive bounded source preparation. -/ | unresolved (current : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (request : StepRequest) (remaining : List StepRequest)
      (ordered : current.parameter ≤ request.endpoint.parameter)
      (report : BoundedPreparedSource.Inconclusive segment current owner request) :
      StepFailure segment within current owner (request :: remaining)
  /-- Prepend an actually accepted cached step to the retained tail failure. -/ | next (current : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (request : StepRequest) (remaining : List StepRequest)
      (ordered : current.parameter ≤ request.endpoint.parameter)
      (accepted : BoundedPreparedSource.Accepted segment current owner request)
      (found : BoundedPreparedSource.check segment current owner request = .ok accepted)
      (tail : StepFailure segment within request.endpoint
        (advanceCached segment within current owner request accepted.cached accepted.small) remaining) :
      StepFailure segment within current owner (request :: remaining)

constructive_injectivity StepFailure

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained segment subdivision accepted by the original step checker.

The success equation identifies this exact subdivision, including its cached owners, for the displayed request list. -/
structure StepSuccess {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) where
  /-- The accepted subdivision with its original endpoint owner. -/ subdivision : Subdivision segment within current
    owner
  /-- The original checker returns exactly the retained subdivision. -/ success : Subdivision.trySteps segment within
    current owner requests = some subdivision

constructive_injectivity StepSuccess

section
open Purelib.Polynomial
/-- Prepending an accepted cached step preserves the original checker's success equation.

The retained accepted cache and exact tail success equation identify the same original subdivision. The proof preserves
the displayed ordered request and its canonical source certificate. -/
theorem prepend_success {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (remaining : List StepRequest)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (accepted : BoundedPreparedSource.Accepted segment current owner request)
    (tail : StepSuccess segment within request.endpoint
      (advanceCached segment within current owner request accepted.cached accepted.small) remaining) :
    Subdivision.trySteps segment within current owner (request :: remaining) =
      some (Subdivision.nextCached segment within current owner request accepted.cached ordered
        accepted.small accepted.canonical_small tail.subdivision) := by
  cases accepted with
  | mk cached small =>
      cases cached with
      | mk preparedOwner preparedOwnerEq =>
          cases preparedOwnerEq
          rw [Subdivision.trySteps, dif_pos ordered]
          simp only [CachedSource.canonical]
          rw [dif_pos small, tail.success]

/-- Scan the displayed requests with bounded source preparation.

Return either the exact accepted subdivision and canonical success equation or the accepted prefix and unresolved
request; each accepted edge retains its original owner transport. -/
@[expose] def steps {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    (requests : List StepRequest) →
      Except (StepFailure segment within current owner requests)
        (StepSuccess segment within current owner requests)
  | [] => .ok ⟨.stop current owner, rfl⟩
  | request :: remaining =>
      if ordered : current.parameter ≤ request.endpoint.parameter then
        match found : BoundedPreparedSource.check segment current owner request with
        | .error report => .error (.unresolved current owner request remaining ordered report)
        | .ok accepted =>
            match steps segment within request.endpoint
                (advanceCached segment within current owner request accepted.cached accepted.small) remaining with
            | .error failure => .error (.next current owner request remaining ordered accepted found failure)
            | .ok tail => .ok
                { subdivision := Subdivision.nextCached segment within current owner request accepted.cached
                    ordered accepted.small accepted.canonical_small tail.subdivision
                  success := prepend_success segment within current owner request remaining ordered accepted tail }
      else .error (.unordered current owner request remaining ordered)

end

open Purelib.Polynomial in
/-- The bounded step scanner returns exactly the error represented by a retained failure. -/
theorem StepFailure.steps_error {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {requests : List StepRequest} (failure : StepFailure segment within current owner requests) :
    steps segment within current owner requests = .error failure := by
  induction failure with
  | unordered current owner request remaining violated =>
      rw [steps, dif_neg violated]
  | unresolved current owner request remaining ordered report =>
      rw [steps, dif_pos ordered]
      split
      · rename_i other found
        have equal : other = report := Except.error.inj (found.symm.trans report.check_error)
        cases equal
        rfl
      · rename_i other found
        have impossible := found.symm.trans report.check_error
        cases impossible
  | next current owner request remaining ordered accepted found tail ih =>
      rw [steps, dif_pos ordered]
      split
      · rename_i other observed
        have impossible := observed.symm.trans found
        cases impossible
      · rename_i other observed
        have equal : other = accepted := Except.ok.inj (observed.symm.trans found)
        cases equal
        rw [ih]

/-- The dyadic unit-interval requests at the displayed depth and positive diameter. -/
abbrev Requests (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :=
  Subdivision.dyadicRequests depth zeroEndpoint oneEndpoint diameter positive

open Purelib.Polynomial in
/-- Turn an accepted bounded dyadic scan into its certified complete segment.

The accepted dyadic scan supplies the original cached subdivision and its checker equality. The resulting complete
segment retains that exact head, initial owner and finish owner. -/
@[expose] def completeHead {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (head : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (accepted : StepSuccess head within zeroEndpoint (ownerAtStart head owner)
      (Requests depth diameter positive)) : CompleteSegment head within owner :=
  CompleteSegment.ofTryDyadic head within owner depth diameter positive accepted.success

open Purelib.Polynomial in
set_option genInjectivity false in
/-- The accepted segment prefix and exact unresolved tail of a bounded path scan.

Each successful head retains its checker result and finish owner; the terminal head retains the original segment
failure. -/
inductive PathFailure {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :
    {start finish : Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) →
      path.WithinAmbient → Owner (polynomial.eval start) → Type where
  /-- The first segment has the retained bounded-scan failure. -/ | head {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (within : (Polynomial.Geometry.ClearPath.cons head tail).WithinAmbient)
      (owner : Owner (polynomial.eval start))
      (failure : StepFailure head within.head zeroEndpoint (ownerAtStart head owner)
        (Requests depth diameter positive)) :
      PathFailure depth diameter positive (.cons head tail) within owner
  /-- An accepted head leads to the retained failure on the remaining path. -/ | tail {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (within : (Polynomial.Geometry.ClearPath.cons head tail).WithinAmbient)
      (owner : Owner (polynomial.eval start))
      (accepted : StepSuccess head within.head zeroEndpoint (ownerAtStart head owner)
        (Requests depth diameter positive))
      (found : steps head within.head zeroEndpoint (ownerAtStart head owner)
        (Requests depth diameter positive) = .ok accepted)
      (failure : PathFailure depth diameter positive tail within.tail
        (completeHead head within.head owner depth diameter positive accepted).finishOwner) :
      PathFailure depth diameter positive (.cons head tail) within owner

constructive_injectivity PathFailure

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A prepared path returned by the original dyadic checker.

The retained equation certifies the same path, initial owner, depth and requested diameter. -/
structure PathSuccess {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start finish : Gaussian} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The actual prepared path with its original initial owner. -/ prepared : PreparedPath path owner
  /-- The original dyadic checker returns the retained prepared path. -/ success : PreparedPath.tryDyadic path within
    owner depth diameter positive = some prepared

constructive_injectivity PathSuccess

section
open Purelib.Polynomial
/-- Prepending an accepted segment preserves the canonical dyadic path success equation.

The accepted head retains its exact complete segment and finish owner, and the tail starts from that same owner. Their
original checker equalities identify the prepared path without rebuilding either cache. -/
theorem prepend_path_success {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian} (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
    (within : (Polynomial.Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (accepted : StepSuccess head within.head zeroEndpoint (ownerAtStart head owner)
      (Requests depth diameter positive))
    (rest : PathSuccess depth diameter positive tail within.tail
      (completeHead head within.head owner depth diameter positive accepted).finishOwner) :
    PreparedPath.tryDyadic (.cons head tail) within owner depth diameter positive =
      some (.cons head tail owner within.head
        (completeHead head within.head owner depth diameter positive accepted) rest.prepared) := by
  have headSuccess : Subdivision.tryDyadic head within.head zeroEndpoint oneEndpoint
      (ownerAtStart head owner) depth diameter positive = some accepted.subdivision := accepted.success
  rw [PreparedPath.tryDyadic]
  split
  · rename_i found
    have impossible := found.symm.trans headSuccess
    cases impossible
  · rename_i subdivision found
    have equal : subdivision = accepted.subdivision := Option.some.inj (found.symm.trans headSuccess)
    cases equal
    have restSuccess := rest.success
    dsimp only [completeHead] at restSuccess ⊢
    rw [restSuccess]

/-- Attempt a complete path bank at the displayed finite depth and diameter.

Retain either the exact completed path or the accepted prefix and finite obligation where the bounded scan stopped. -/
@[expose] def path {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :
    {start finish : Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) →
      (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
        Except (PathFailure depth diameter positive path within owner)
          (PathSuccess depth diameter positive path within owner)
  | _, _, .nil point, _, owner => .ok ⟨.nil point owner, rfl⟩
  | _, _, .cons head tail, within, owner =>
      match found : steps head within.head zeroEndpoint (ownerAtStart head owner)
          (Requests depth diameter positive) with
      | .error failure => .error (.head head tail within owner failure)
      | .ok accepted =>
          match path depth diameter positive tail within.tail
              (completeHead head within.head owner depth diameter positive accepted).finishOwner with
          | .error failure => .error (.tail head tail within owner accepted found failure)
          | .ok rest => .ok
              { prepared := .cons head tail owner within.head
                  (completeHead head within.head owner depth diameter positive accepted) rest.prepared
                success := prepend_path_success head tail within owner depth diameter positive accepted rest }

end

section
open Purelib.Polynomial
/-- The bounded path scanner returns exactly the error represented by a retained failure. -/
theorem PathFailure.path_error {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {start finish : Gaussian} {source : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {within : source.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (failure : PathFailure depth diameter positive source within owner) :
    path depth diameter positive source within owner = .error failure := by
  induction failure with
  | head head tail within owner failure =>
      rw [path]
      split
      · rename_i other found
        have equal : other = failure := Except.error.inj (found.symm.trans failure.steps_error)
        cases equal
        rfl
      · rename_i other found
        have impossible := found.symm.trans failure.steps_error
        cases impossible
  | tail head tail within owner accepted found failure ih =>
      rw [path]
      split
      · rename_i other observed
        have impossible := observed.symm.trans found
        cases impossible
      · rename_i other observed
        have equal : other = accepted := Except.ok.inj (observed.symm.trans found)
        cases equal
        rw [ih]

/-- Package the retained successful path and checker equation as an executed dyadic bank. -/
@[expose] def PathSuccess.bank {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {start finish : Gaussian} {source : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {within : source.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (accepted : PathSuccess depth diameter positive source within owner) :
    PreparedPath.DyadicBank depth diameter positive source owner :=
  .executed within accepted.prepared accepted.success

end

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A bounded path attempt's displayed budget and exact unresolved obligation.

The report retains the attempted depth, requested diameter and accepted prefix, with equations tying them to this
invocation. -/
structure Inconclusive {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start finish : Gaussian} (source : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : source.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The depth actually attempted by this finite scan. -/ attemptedDepth : Nat
  /-- The retained attempted depth equals the requested depth. -/ attemptedDepth_eq : attemptedDepth = depth
  /-- The diameter requested for the finite scan. -/ requestedDiameter : Coordinate
  /-- The retained diameter equals the request's diameter. -/ requestedDiameter_eq : requestedDiameter = diameter
  /-- The exact accepted prefix and unresolved finite obligation. -/ failure : PathFailure depth diameter positive
    source within owner

constructive_injectivity Inconclusive

open Purelib.Polynomial
/-- Attempt a bounded path bank and retain the budget in any inconclusive result.

Successful attempts preserve the prepared path; unsuccessful attempts carry the actual scanner failure without asserting
that another refinement cannot succeed. -/
@[expose] def attempt {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start finish : Gaussian} (source : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : source.WithinAmbient) (owner : Owner (polynomial.eval start)) :
    Except (Inconclusive depth diameter positive source within owner)
      (PathSuccess depth diameter positive source within owner) :=
  match path depth diameter positive source within owner with
  | .ok accepted => .ok accepted
  | .error failure => .error ⟨depth, rfl, diameter, rfl, failure⟩

/-- The bounded attempt returns exactly the error described by its inconclusive report. -/
theorem Inconclusive.attempt_error {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {start finish : Gaussian} {source : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {within : source.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (report : Inconclusive depth diameter positive source within owner) :
    attempt depth diameter positive source within owner = .error report := by
  cases report with
  | mk attemptedDepth depthEq requestedDiameter diameterEq failure =>
      cases depthEq
      cases diameterEq
      rw [attempt, failure.path_error]

end Purelib.Riemann.Readings.BoundedPreparedBanks
