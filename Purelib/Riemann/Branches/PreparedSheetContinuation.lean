module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

public import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

namespace Purelib.Riemann.Branches.PreparedSheetContinuation

open Purelib.Data.Rat

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A finite sequence of prepared square-root continuation steps indexed by the original source owner.

Each step retains its exact request and prepared cache, endpoint ordering, strict variation bound, and continuation from
the actual advanced owner. -/
public inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Endpoint) ->
      Owner (polynomial.eval (segment.pointAt left.parameter)) -> Type
  /-- Stop at the exact current endpoint and root owner. -/ | stop (left : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :
      Subdivision segment within left owner
  /-- Retain one ordered prepared step, its cache and strict variation bound, and the tail from its exact advanced
    owner. -/ | next (left : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
      (request : StepRequest)
      (cached : CachedSource segment left owner request)
      (ordered : left.parameter <= request.endpoint.parameter)
      (small : ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
      (remaining : Subdivision segment within request.endpoint
        (advance segment within left owner request small)) :
      Subdivision segment within left owner

constructive_injectivity Subdivision

namespace Subdivision

section
open Purelib.Polynomial
/-- Transport a subdivision along equality of its exact initial owner. -/
@[expose] public def castOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    Subdivision segment within left second := by
  cases equal
  exact subdivision

/-- Changing the owner index by equality preserves the original subdivision heterogeneously. -/
public theorem castOwner_heq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    HEq (subdivision.castOwner equal) subdivision := by
  cases equal
  rfl

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Prepend a step using its retained prepared cache and the exact cached-advance tail.

The cached-to-canonical owner equality transports the existing tail to the constructor's required index; the cached
preparation is retained in the resulting step. -/
@[expose] public def nextCached {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    Subdivision segment within left owner :=
  .next left owner request cached ordered canonicalSmall
    (remaining.castOwner
      (advanceCached_eq_advance segment within left owner request cached
        cachedSmall canonicalSmall))

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A finite mesh whose original endpoint values equal one fixed radicand and reuse its original root owner.

Each request retains equality at both endpoints, ordering, readiness, and enough clearance for its actual move. -/
public inductive StationaryMesh
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (baseOwner : Owner base) :
    (current : Endpoint) → List StepRequest → Type
  /-- Finish the stationary mesh with equality of the current polynomial value to the retained base radicand. -/ | stop
    (current : Endpoint)
      (currentEq : polynomial.eval (segment.pointAt current.parameter) = base) :
      StationaryMesh segment baseOwner current []
  /-- Retain a stationary request with exact source and target radicand equalities, ordering, readiness, clearance, and
    its original tail. -/ | next (current : Endpoint) (request : StepRequest)
      (remaining : List StepRequest)
      (currentEq : polynomial.eval (segment.pointAt current.parameter) = base)
      (targetEq :
        polynomial.eval (segment.pointAt request.endpoint.parameter) = base)
      (ordered : current.parameter ≤ request.endpoint.parameter)
      (ready : AlreadyPrepared segment current
        (SquareRoot.Owner.Transport.castOwnerParameter currentEq.symm baseOwner) request)
      (carries : ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (SquareRoot.Owner.Transport.castOwnerParameter currentEq.symm
          baseOwner).track.initial.clearance.bound)
      (tail : StationaryMesh segment baseOwner request.endpoint remaining) :
      StationaryMesh segment baseOwner current (request :: remaining)

constructive_injectivity StationaryMesh

open Purelib.Polynomial in
/-- The stationary mesh's current polynomial value equals its fixed base radicand. -/
public theorem StationaryMesh.currentEq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {baseOwner : Owner base} {current : Endpoint}
    {requests : List StepRequest}
    (mesh : StationaryMesh segment baseOwner current requests) :
    polynomial.eval (segment.pointAt current.parameter) = base :=
  match mesh with
  | .stop _ currentEq => currentEq
  | .next _ _ _ currentEq _ _ _ _ _ => currentEq

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Construct continuation along a stationary mesh using the same retained base owner.

Exact parameter transports and zero-move owner equalities connect the cached advances, preserving the original mesh and
root selection. -/
@[expose] public def stationarySubdivision
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (baseOwner : Owner base)
    {current : Endpoint} {requests : List StepRequest}
    (mesh : StationaryMesh segment baseOwner current requests) :
    Subdivision segment within current
      (SquareRoot.Owner.Transport.castOwnerParameter mesh.currentEq.symm baseOwner) := by
  cases mesh with
  | stop current currentEq =>
      exact .stop current (SquareRoot.Owner.Transport.castOwnerParameter currentEq.symm baseOwner)
  | next current request remaining currentEq targetEq ordered ready carries
      tail =>
      let currentOwner := SquareRoot.Owner.Transport.castOwnerParameter currentEq.symm baseOwner
      have preparedEq : prepared segment current currentOwner request =
          currentOwner :=
        prepared_eq_self_of_ready segment current currentOwner request ready
          carries
      have canonicalSmall :
          ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            (prepared segment current currentOwner
              request).track.initial.clearance.bound := by
        rw [preparedEq]
        exact carries
      let cached := CachedSource.canonical segment current currentOwner request
      have cachedSmall :
          ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound :=
        canonicalSmall
      let nextOwner := advanceCached segment within current currentOwner request
        cached cachedSmall
      let targetOwner := SquareRoot.Owner.Transport.castOwnerParameter targetEq.symm baseOwner
      have nextOwnerEq : nextOwner = targetOwner := by
        apply eq_of_heq
        have nextPrepared : HEq nextOwner cached.preparedOwner := by
          unfold nextOwner advanceCached
          unfold transportReserve
          exact retainedReservedTransport_heq_self_of_eq cached.preparedOwner
            (segment.pointAt_eval_ne_zero request.endpoint.parameter
              request.endpoint.inside)
            _ (preparedClearanceLower segment current request)
            (by
              rw [cached.preparedOwner_eq]
              exact preparedClearanceLower_le segment current currentOwner
                request)
            (currentEq.trans targetEq.symm)
        have preparedCurrent : HEq cached.preparedOwner currentOwner := by
          rw [cached.preparedOwner_eq, preparedEq]
        have nextCurrent : HEq nextOwner currentOwner :=
          nextPrepared.trans preparedCurrent
        have currentTarget : HEq currentOwner targetOwner := by
          exact (SquareRoot.Owner.Transport.castOwnerParameter_heq currentEq.symm baseOwner).trans
            (SquareRoot.Owner.Transport.castOwnerParameter_heq targetEq.symm baseOwner).symm
        exact nextCurrent.trans currentTarget
      exact Subdivision.nextCached segment within current currentOwner request
        cached ordered cachedSmall canonicalSmall
          ((stationarySubdivision segment within baseOwner tail).castOwner
            nextOwnerEq.symm)

/- Explicit constructor elimination reads the retained fields.  Ordinary
dependent pattern matching can compile these projections to replaying
`advance` solely to reconstruct recursive indices.  The public operations
directly use the stored-data implementations; no extensional function equality
or compiler-rewrite proof is required. -/
section StoredEndpointProjections

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}

/-- Follow the finite subdivision spine to its retained terminal endpoint. -/
@[expose] public def endpointStored {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : Endpoint :=
  Subdivision.casesOn (motive := fun _ _ _ => Endpoint) subdivision
    (fun endpoint _ => endpoint)
    (fun _ _ _ _ _ _ remaining => endpointStored remaining)
termination_by structural subdivision

open Purelib.Polynomial in
/-- Read the retained terminal endpoint of the subdivision. -/
@[inline, expose] public def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : Endpoint := endpointStored subdivision

/-- Follow the subdivision spine to the exact owner stored at its terminal endpoint. -/
@[expose] public def terminalOwnerStored {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    Owner (polynomial.eval (segment.pointAt subdivision.endpoint.parameter)) :=
  Subdivision.casesOn
    (motive := fun _ _ spine => Owner (polynomial.eval (segment.pointAt spine.endpoint.parameter))) subdivision
    (fun _ owner => owner)
    (fun _ _ _ _ _ _ remaining => terminalOwnerStored remaining)
termination_by structural subdivision

open Purelib.Polynomial in
/-- Read the exact terminal owner indexed by the subdivision's retained endpoint. -/
@[inline, expose] public def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    Owner (polynomial.eval (segment.pointAt subdivision.endpoint.parameter)) := terminalOwnerStored subdivision

/-- Count the actual continuation steps in the finite subdivision spine. -/
@[expose] public def stepCountStored {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : Nat :=
  Subdivision.casesOn (motive := fun _ _ _ => Nat) subdivision
    (fun _ _ => 0)
    (fun _ _ _ _ _ _ remaining => stepCountStored remaining + 1)
termination_by structural subdivision

open Purelib.Polynomial in
/-- Read the number of retained continuation steps. -/
@[inline, expose] public def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : Nat := stepCountStored subdivision

end StoredEndpointProjections

/- Constructor equations are the proof interface; unfolding the recursive
stored-data helpers under an unknown tail is deliberately unnecessary. -/
section EndpointProjectionEquations

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  (left : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))

/-- A stopped subdivision retains its starting endpoint. -/
@[simp] public theorem endpoint_stop :
    (stop (segment := segment) (within := within) left owner).endpoint = left := rfl

/-- A stopped subdivision retains its starting owner. -/
@[simp] public theorem terminalOwner_stop :
    (stop (segment := segment) (within := within) left owner).terminalOwner = owner := rfl

/-- A stopped subdivision has zero steps. -/
@[simp] public theorem stepCount_stop :
    (stop (segment := segment) (within := within) left owner).stepCount = 0 := rfl

variable (request : StepRequest) (cached : CachedSource segment left owner request)
  (ordered : left.parameter ≤ request.endpoint.parameter)
  (small : Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound)
  (remaining : Subdivision segment within request.endpoint
    (advance segment within left owner request small))

/-- Prepending a continuation step preserves the tail's terminal endpoint. -/
@[simp] public theorem endpoint_next :
    (next left owner request cached ordered small remaining).endpoint =
      remaining.endpoint := rfl

/-- Prepending a continuation step preserves the tail's exact terminal owner. -/
@[simp] public theorem terminalOwner_next :
    (next left owner request cached ordered small remaining).terminalOwner =
      remaining.terminalOwner := rfl

/-- Prepending one step increases the retained step count by one. -/
@[simp] public theorem stepCount_next :
    (next left owner request cached ordered small remaining).stepCount =
      remaining.stepCount + 1 := rfl

end EndpointProjectionEquations

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- A strict squared-displacement certificate from the fixed original source value to a retained current endpoint.

The bound is measured against the original source owner's clearance, so every direct move retains that same owner. -/
public structure DirectMoveSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint) : Prop where
  /-- The strict squared-displacement bound against the fixed original source owner's clearance. -/ proof :
    Data.Gaussian.Norm.Basic.normSq
    (polynomial.eval (segment.pointAt origin.parameter) -
      polynomial.eval (segment.pointAt current.parameter)) <
    source.track.initial.clearance.bound

open Purelib.Polynomial in
/-- Advance the fixed original source owner directly to the given endpoint using its retained displacement certificate.
-/
@[expose] public def directOwnerAt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (small : DirectMoveSmall segment origin source current) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  source.advance
    (segment.pointAt_eval_ne_zero current.parameter current.inside) small.proof

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Cached root names and their equivalence for two exact owners at the same segment endpoint.

The two name equalities connect the retained names to their original owners, so the equivalence does not replace either
owner. -/
public structure RootEquivalentAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt current.parameter))) where
  /-- The retained coherent root name for the first original owner. -/ firstName : Named
  /-- The retained coherent root name for the second original owner. -/ secondName : Named
  /-- Operational equivalence between the two retained names. -/ equivalent : NamedEquivalent firstName secondName
  /-- The first retained name is exactly the root name read from the first original owner. -/ first_eq : firstName =
    SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero current.parameter current.inside) first
  /-- The second retained name is exactly the root name read from the second original owner. -/ second_eq : secondName =
    SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero current.parameter current.inside) second

constructive_injectivity RootEquivalentAt

namespace RootEquivalentAt

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Transport the retained name equivalence to the root names of the two original indexed owners. -/
@[expose] public def toNamedEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt current.parameter))}
    (relation : RootEquivalentAt segment current first second) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero current.parameter current.inside) first)
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
        second) := by
  rw [← relation.first_eq, ← relation.second_eq]
  exact relation.equivalent

end RootEquivalentAt

open Purelib.Polynomial in
/-- The zero move from the original endpoint fits the source owner's positive clearance. -/
public theorem sameDirectMoveSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter))) :
    DirectMoveSmall segment origin source origin :=
  ⟨samePointSmall source⟩

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Compare the direct zero-move owner with a retained equivalent original owner. -/
@[expose] public def initialDirectRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source owner : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (equivalent : RootEquivalentAt segment origin source owner) :
    RootEquivalentAt segment origin
      (directOwnerAt origin source origin (sameDirectMoveSmall origin source))
      owner :=
  { firstName := SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero origin.parameter origin.inside)
      (directOwnerAt origin source origin (sameDirectMoveSmall origin source))
    secondName := SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero origin.parameter origin.inside) owner
    equivalent := Equivalence.NamedEquivalent.trans
      (SquareRootTrackEquivalence.rootEquivalent_advance_same
        (segment.pointAt_eval_ne_zero origin.parameter origin.inside) source
          (by simpa only [Norm.Basic.normSq_eq_canonical] using (sameDirectMoveSmall origin source).proof)).symm
      equivalent.toNamedEquivalent
    first_eq := rfl
    second_eq := rfl }

section
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
/-- The continuation-congruence certificate relating direct advancement and preparation at the next requested endpoint.

Both the fixed original source and current child owner are retained, together with the direct move certificate
identifying the current direct owner. -/
public structure DirectStepSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Prop where
  /-- The exact continuation-congruence bounds for the current direct owner and prepared child source. -/ congruence :
    SquareRootTrackEquivalence.ContinuationCongruenceSmall
      (segment.pointAt_eval_ne_zero current.parameter current.inside)
      (directOwnerAt origin source current sourceCurrentSmall)
      (prepared segment current owner request)
      (polynomial.eval (segment.pointAt request.endpoint.parameter))

/-- Decide the continuation-congruence bounds for the exact direct owner and prepared child source. -/
public instance directStepSmallDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Decidable (DirectStepSmall segment origin source current
      sourceCurrentSmall owner request) := by
  by_cases congruence :
      SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
        (directOwnerAt origin source current sourceCurrentSmall)
        (prepared segment current owner request)
        (polynomial.eval (segment.pointAt request.endpoint.parameter))
  · exact isTrue ⟨congruence⟩
  · exact isFalse (fun small => congruence small.congruence)

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Propagate the retained direct-to-child root equivalence through one certified prepared step.

The construction consumes the original source-to-current and source-to-next bounds and the exact continuation-congruence
certificate. -/
@[expose] public def directNextRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (currentEquivalent : RootEquivalentAt segment current
      (directOwnerAt origin source current sourceCurrentSmall) owner)
    (request : StepRequest)
    (childSmall : ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        (prepared segment current owner request).track.initial.clearance.bound)
    (sourceNextSmall : DirectMoveSmall segment origin source request.endpoint)
    (stepSmall : DirectStepSmall segment origin source current
      sourceCurrentSmall owner request) :
    RootEquivalentAt segment request.endpoint
      (directOwnerAt origin source request.endpoint sourceNextSmall)
      (advance segment within current owner request childSmall) :=
  { firstName := SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (directOwnerAt origin source request.endpoint sourceNextSmall)
    secondName := SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (advance segment within current owner request childSmall)
    equivalent := directToAdvanceRootEquivalent segment within origin current
      source owner request childSmall sourceCurrentSmall.proof
        sourceNextSmall.proof currentEquivalent.toNamedEquivalent
          stepSmall.congruence
    first_eq := rfl
    second_eq := rfl }

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A subdivision equipped at every step with agreement to direct continuation of one fixed original source.

The dependent spine retains the actual subdivision, current root equivalence, direct move bounds, and the exact next
equivalence used by the tail. -/
public inductive DirectlyCoherent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter))) :
    {current : Endpoint} ->
      (sourceCurrentSmall : DirectMoveSmall segment origin source current) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
      RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner ->
      Subdivision segment within current owner -> Type 2
  /-- Certify direct coherence at the terminal endpoint with its retained original-source comparison. -/ | stop
      (current : Endpoint)
      (sourceCurrentSmall : DirectMoveSmall segment origin source current)
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter)))
      (currentEquivalent : RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner) :
      DirectlyCoherent segment within origin source sourceCurrentSmall owner
        currentEquivalent (.stop current owner)
  /-- Retain the next direct move and congruence certificates and direct coherence of the actual subdivision tail. -/ |
    next
      (current : Endpoint)
      (sourceCurrentSmall : DirectMoveSmall segment origin source current)
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter)))
      (currentEquivalent : RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner)
      (request : StepRequest)
      (cached : CachedSource segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (childSmall : ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
          (prepared segment current owner request).track.initial.clearance.bound)
      (remaining : Subdivision segment within request.endpoint
        (advance segment within current owner request childSmall))
      (sourceNextSmall : DirectMoveSmall segment origin source request.endpoint)
      (stepSmall : DirectStepSmall segment origin source current
        sourceCurrentSmall owner request)
      (tail : DirectlyCoherent segment within origin source sourceNextSmall
        (advance segment within current owner request childSmall)
        (directNextRootEquivalent segment within origin source current
          sourceCurrentSmall owner currentEquivalent request childSmall
            sourceNextSmall stepSmall)
        remaining) :
      DirectlyCoherent segment within origin source sourceCurrentSmall owner
        currentEquivalent
          (.next current owner request cached ordered childSmall remaining)

constructive_injectivity DirectlyCoherent

section StoredGeometryProjections

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}

open Purelib.Riemann.Branches in
/-- Read the ordered list of original parameter-edge occurrences from the subdivision spine. -/
@[expose] public def parameterEdgesStored {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    List ClearSheetContinuation.Subdivision.ParameterEdge :=
  Subdivision.casesOn
    (motive := fun _ _ _ => List ClearSheetContinuation.Subdivision.ParameterEdge) subdivision
    (fun _ _ => [])
    (fun left _ request _ _ _ remaining =>
      { left := left, right := request.endpoint } :: parameterEdgesStored remaining)
termination_by structural subdivision

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Read the original ordered parameter-edge occurrences of the subdivision. -/
@[inline, expose] public def parameterEdges {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    List ClearSheetContinuation.Subdivision.ParameterEdge := parameterEdgesStored subdivision

/-- Read each step's initial box directly from its retained prepared-owner cache. -/
@[expose] public def preparedBoxesStored {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : List Box :=
  Subdivision.casesOn (motive := fun _ _ _ => List Box) subdivision
    (fun _ _ => [])
    (fun _ _ _ cached _ _ remaining =>
      cached.preparedOwner.track.initial.box :: preparedBoxesStored remaining)
termination_by structural subdivision

open Purelib.Polynomial in
/-- Read the ordered boxes of the actual cached prepared owners. -/
@[inline, expose] public def preparedBoxes {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : List Box := preparedBoxesStored subdivision

end StoredGeometryProjections

/- Constructor equations are the proof interface; unfolding the recursive
stored-data helpers under an unknown tail is deliberately unnecessary. -/
section GeometryProjectionEquations

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  (left : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))

/-- A stopped subdivision has no parameter edges. -/
@[simp] public theorem parameterEdges_stop :
    (stop (segment := segment) (within := within) left owner).parameterEdges = [] := rfl

/-- A stopped subdivision has no cached prepared boxes. -/
@[simp] public theorem preparedBoxes_stop :
    (stop (segment := segment) (within := within) left owner).preparedBoxes = [] := rfl

variable (request : StepRequest) (cached : CachedSource segment left owner request)
  (ordered : left.parameter ≤ request.endpoint.parameter)
  (small : Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound)
  (remaining : Subdivision segment within request.endpoint
    (advance segment within left owner request small))

/-- Prepending a step prepends its exact source and request endpoints to the parameter-edge list. -/
@[simp] public theorem parameterEdges_next :
    (next left owner request cached ordered small remaining).parameterEdges =
      { left := left, right := request.endpoint } :: remaining.parameterEdges := rfl

/-- Prepending a step prepends the exact cached prepared box. -/
@[simp] public theorem preparedBoxes_next :
    (next left owner request cached ordered small remaining).preparedBoxes =
      cached.preparedOwner.track.initial.box :: remaining.preparedBoxes := rfl

end GeometryProjectionEquations

section
open Purelib.Polynomial
/-- There is one retained prepared box for each continuation step. -/
@[simp] public theorem preparedBoxes_length
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.preparedBoxes.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next _left _owner _request _cached _ordered _small remaining
      inductionHypothesis =>
      rewrite [preparedBoxes_next, List.length_cons, stepCount_next,
        inductionHypothesis]
      exact Eq.refl _

/-- Read the original requests in their subdivision order. -/
@[expose] public def requestsStored {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : List StepRequest :=
  Subdivision.casesOn (motive := fun _ _ _ => List StepRequest) subdivision
    (fun _ _ => [])
    (fun _ _ request _ _ _ remaining => request :: requestsStored remaining)
termination_by structural subdivision

/-- Read the exact original request list retained by the subdivision. -/
@[inline, expose] public def requests {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) : List StepRequest := requestsStored subdivision

/- Constructor equations are the proof interface; unfolding the recursive
stored-data helpers under an unknown tail is deliberately unnecessary. -/
end

section RequestProjectionEquations

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  (left : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))

/-- A stopped subdivision has no requests. -/
@[simp] public theorem requests_stop :
    (stop (segment := segment) (within := within) left owner).requests = [] := rfl

variable (request : StepRequest) (cached : CachedSource segment left owner request)
  (ordered : left.parameter ≤ request.endpoint.parameter)
  (small : Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound)
  (remaining : Subdivision segment within request.endpoint
    (advance segment within left owner request small))

/-- Prepending a step prepends that exact request to the retained list. -/
@[simp] public theorem requests_next :
    (next left owner request cached ordered small remaining).requests =
      request :: remaining.requests := rfl

end RequestProjectionEquations

section
open Purelib.Polynomial
/-- There is one retained parameter edge for each continuation step. -/
@[simp] public theorem parameterEdges_length
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.parameterEdges.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next _left _owner _request _cached _ordered _small remaining
      inductionHypothesis =>
      rewrite [parameterEdges_next, List.length_cons, stepCount_next,
        inductionHypothesis]
      exact Eq.refl _

/-- There is one retained request for each continuation step. -/
@[simp] public theorem requests_length
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.requests.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next _left _owner _request _cached _ordered _small remaining
      inductionHypothesis =>
      rewrite [requests_next, List.length_cons, stepCount_next, inductionHypothesis]
      exact Eq.refl _

/-- Transport along initial-owner equality preserves the terminal endpoint. -/
@[simp] public theorem castOwner_endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).endpoint = subdivision.endpoint := by
  cases equal
  rfl

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Prepending a cached step preserves the retained tail's terminal endpoint. -/
@[simp] public theorem nextCached_endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).endpoint = remaining.endpoint := by
  rewrite [nextCached, endpoint_next, castOwner_endpoint]
  exact Eq.refl _

section
open Purelib.Polynomial
/-- Transport along initial-owner equality preserves the step count. -/
@[simp] public theorem castOwner_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).stepCount = subdivision.stepCount := by
  cases equal
  rfl

/-- Transport along initial-owner equality preserves every original parameter-edge occurrence. -/
@[simp] public theorem castOwner_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).parameterEdges =
      subdivision.parameterEdges := by
  cases equal
  rfl

/-- Transport along initial-owner equality preserves the exact prepared-box list. -/
@[simp] public theorem castOwner_preparedBoxes
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).preparedBoxes =
      subdivision.preparedBoxes := by
  cases equal
  rfl

/-- Transport along initial-owner equality preserves the exact request list. -/
@[simp] public theorem castOwner_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).requests = subdivision.requests := by
  cases equal
  rfl

end

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Prepending a cached step increases the tail's step count by one. -/
@[simp] public theorem nextCached_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).stepCount = remaining.stepCount + 1 := by
  rewrite [nextCached, stepCount_next, castOwner_stepCount]
  exact Eq.refl _

/-- Prepending a cached step adds its exact source-to-request parameter edge. -/
@[simp] public theorem nextCached_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).parameterEdges =
        { left := left, right := request.endpoint } ::
          remaining.parameterEdges := by
  rewrite [nextCached, parameterEdges_next, castOwner_parameterEdges]
  exact Eq.refl _

/-- Prepending a cached step adds the retained cache's actual initial box. -/
@[simp] public theorem nextCached_preparedBoxes
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
          left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).preparedBoxes =
        cached.preparedOwner.track.initial.box ::
          remaining.preparedBoxes := by
  rewrite [nextCached, preparedBoxes_next, castOwner_preparedBoxes]
  exact Eq.refl _

end

open Purelib.Polynomial in
/-- Follow the stationary mesh to its retained final endpoint. -/
@[expose] public def StationaryMesh.endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {baseOwner : Owner base} {current : Endpoint} :
    {requests : List StepRequest} →
      StationaryMesh segment baseOwner current requests → Endpoint
  | [], .stop current _ => current
  | _ :: _, .next _ _ _ _ _ _ _ _ tail => tail.endpoint

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Read the stationary mesh's original source-to-request parameter edges in order. -/
@[expose] public def StationaryMesh.parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {baseOwner : Owner base} {current : Endpoint} :
    {requests : List StepRequest} →
      StationaryMesh segment baseOwner current requests →
        List ClearSheetContinuation.Subdivision.ParameterEdge
  | [], .stop _ _ => []
  | _ :: _, .next current request _ _ _ _ _ _ tail =>
      { left := current, right := request.endpoint } :: tail.parameterEdges

section
open Purelib.Polynomial
/-- Constructing a stationary subdivision preserves the original mesh's terminal endpoint. -/
@[simp] public theorem stationarySubdivision_endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (baseOwner : Owner base)
    {current : Endpoint} {requests : List StepRequest}
    (mesh : StationaryMesh segment baseOwner current requests) :
    (stationarySubdivision segment within baseOwner mesh).endpoint =
      mesh.endpoint := by
  induction mesh with
  | stop => rfl
  | next current request remaining currentEq targetEq ordered ready carries
      tail inductionHypothesis =>
      rw [stationarySubdivision]
      rw [Subdivision.nextCached_endpoint, Subdivision.castOwner_endpoint,
        inductionHypothesis]
      rfl

/-- Constructing a stationary subdivision preserves the original mesh's parameter-edge occurrences. -/
@[simp] public theorem stationarySubdivision_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish base : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (baseOwner : Owner base)
    {current : Endpoint} {requests : List StepRequest}
    (mesh : StationaryMesh segment baseOwner current requests) :
    (stationarySubdivision segment within baseOwner mesh).parameterEdges =
      mesh.parameterEdges := by
  induction mesh with
  | stop => rfl
  | next current request remaining currentEq targetEq ordered ready carries
      tail inductionHypothesis =>
      rw [stationarySubdivision]
      rw [Subdivision.nextCached_parameterEdges,
        Subdivision.castOwner_parameterEdges, inductionHypothesis]
      rfl

end

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Prepending a cached step adds that exact request to the tail's retained list. -/
@[simp] public theorem nextCached_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).requests = request :: remaining.requests := by
  rewrite [nextCached, requests_next, castOwner_requests]
  exact Eq.refl _

/-- Attempt the exact finite request list by checking ordering and clearance of each retained prepared cache.

A successful result retains those caches and advances from their actual owners. A failed finite check returns no
subdivision and asserts no global obstruction to continuation. -/
@[expose] public def trySteps {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :
    (requests : List StepRequest) ->
      Option (Subdivision segment within left owner)
  | [] => some (.stop left owner)
  | request :: remaining =>
      let cached := CachedSource.canonical segment left owner request
      if ordered : left.parameter <= request.endpoint.parameter then
        if cachedSmall : ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          let small : ClearSheetContinuation.variationBound segment
              left.parameter request.endpoint.parameter <
                (prepared segment left owner request).track.initial.clearance.bound := by
            rw [cached.preparedOwner_eq] at cachedSmall
            exact cachedSmall
          let nextOwner := advanceCached segment within left owner request
            cached cachedSmall
          match trySteps segment within request.endpoint
              nextOwner remaining with
          | none => none
          | some tail =>
              some (nextCached segment within left owner request cached
                ordered cachedSmall small tail)
        else none
      else none

/-- Every step passes the ordered clearance check along the actual sequence of cached advancements.

The recursive condition uses the exact computed next owner, retaining the execution path instead of an owner-independent
clearance estimate. -/
@[expose] public def ExecutedMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          List StepRequest -> Prop
  | _current, _owner, [] => True
  | current, owner, request :: remaining =>
      let cached := CachedSource.canonical segment current owner request
      current.parameter <= request.endpoint.parameter ∧
        if small : ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
            remaining
        else False

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Decide mesh safety along the actual prepared-cache and advancement sequence. -/
public instance executedMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          (requests : List StepRequest) ->
            Decidable (ExecutedMeshSafe segment within current owner requests)
  | _current, _owner, [] => isTrue trivial
  | current, owner, request :: remaining => by
      let cached := CachedSource.canonical segment current owner request
      if ordered : current.parameter <= request.endpoint.parameter then
        if small : ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          letI := executedMeshSafeDecidable segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining
          exact decidable_of_iff
            (ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached small)
                remaining)
            (by
              constructor
              · intro tail
                change current.parameter <= request.endpoint.parameter ∧
                  (if witness :
                      ClearSheetContinuation.variationBound segment
                          current.parameter request.endpoint.parameter <
                        cached.preparedOwner.track.initial.clearance.bound then
                    ExecutedMeshSafe segment within request.endpoint
                      (advanceCached segment within current owner request cached
                        witness) remaining
                  else False)
                exact ⟨ordered, by simpa only [dif_pos small] using tail⟩
              · intro safe
                have right := safe.2
                change (if witness :
                    ClearSheetContinuation.variationBound segment
                        current.parameter request.endpoint.parameter <
                      cached.preparedOwner.track.initial.clearance.bound then
                  ExecutedMeshSafe segment within request.endpoint
                    (advanceCached segment within current owner request cached
                      witness) remaining
                else False) at right
                simpa only [dif_pos small] using right)
        else
          exact isFalse (fun safe => by
            have right := safe.2
            change (if witness :
                ClearSheetContinuation.variationBound segment
                    current.parameter request.endpoint.parameter <
                  cached.preparedOwner.track.initial.clearance.bound then
              ExecutedMeshSafe segment within request.endpoint
                (advanceCached segment within current owner request cached
                  witness) remaining
            else False) at right
            rw [dif_neg small] at right
            exact right)
      else
        exact isFalse (fun safe => ordered safe.1)

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Construct the exact subdivision from certified checks along its executed owner sequence.

Each retained prepared cache supplies the next actual owner, and the remaining safety proof applies to that same owner.
-/
@[expose] public def ofExecutedMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          (requests : List StepRequest) ->
            ExecutedMeshSafe segment within current owner requests ->
              Subdivision segment within current owner
  | current, owner, [], _safe => .stop current owner
  | current, owner, request :: remaining, safe => by
      let cached := CachedSource.canonical segment current owner request
      if small : ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound then
        have tail : ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining := by
          have right := safe.2
          change (if witness :
              ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simpa only [dif_pos small] using right
        have canonicalSmall :
            ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (prepared segment current owner request).track.initial.clearance.bound := by
          rw [cached.preparedOwner_eq] at small
          exact small
        exact nextCached segment within current owner request cached safe.1
          small canonicalSmall
            (ofExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached small)
                remaining tail)
      else
        have impossible : False := by
          have right := safe.2
          change (if witness :
              ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simp only [dif_neg small] at right
        exact impossible.elim

/-- Certified execution safety makes the attempt return exactly the subdivision constructed from that proof. -/
public theorem trySteps_eq_some_ofExecutedMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {current : Endpoint}
    {owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))}
    (requests : List StepRequest)
    (safe : ExecutedMeshSafe segment within current owner requests) :
    trySteps segment within current owner requests =
      some (ofExecutedMeshSafe segment within current owner requests safe) := by
  induction requests generalizing current owner with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      let cached := CachedSource.canonical segment current owner request
      if small : ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound then
        have tail : ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining := by
          have right := safe.2
          change (if witness :
              ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simpa only [dif_pos small] using right
        rw [trySteps]
        dsimp only
        rw [dif_pos safe.1, dif_pos small, inductionHypothesis tail]
        let canonicalSafe : ExecutedMeshSafe segment within current owner
            (request :: remaining) := by
          change current.parameter <= request.endpoint.parameter ∧
            (if witness :
                ClearSheetContinuation.variationBound segment
                    current.parameter request.endpoint.parameter <
                  cached.preparedOwner.track.initial.clearance.bound then
              ExecutedMeshSafe segment within request.endpoint
                (advanceCached segment within current owner request cached
                  witness) remaining
            else False)
          exact ⟨safe.1, by simpa only [dif_pos small] using tail⟩
        have safeEqual : safe = canonicalSafe := Subsingleton.elim _ _
        have outputEqual :
            ofExecutedMeshSafe segment within current owner
                (request :: remaining) safe =
              ofExecutedMeshSafe segment within current owner
                (request :: remaining) canonicalSafe :=
          congrArg
            (fun proof : ExecutedMeshSafe segment within current owner
                (request :: remaining) =>
              ofExecutedMeshSafe segment within current owner
                (request :: remaining) proof)
            safeEqual
        calc
          _ = some (ofExecutedMeshSafe segment within current owner
              (request :: remaining) canonicalSafe) := by
                dsimp only [canonicalSafe, ofExecutedMeshSafe]
                split
                · rfl
                · contradiction
          _ = some (ofExecutedMeshSafe segment within current owner
              (request :: remaining) safe) :=
                congrArg some outputEqual.symm
      else
        have impossible : False := by
          have right := safe.2
          change (if witness :
              ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simp only [dif_neg small] at right
        exact impossible.elim

/-- Construct continuation for a mesh whose variations fit the owner-independent predicted floors.

The construction retains the original source and computes each next step from its actual cached advancement; the uniform
bounds certify every encountered owner. -/
@[expose] public def ofFreshMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (prior : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (requests : List StepRequest) ->
      FreshMeshSafe segment current requests ->
        Subdivision segment within current prior
  | [], _safe => .stop current prior
  | request :: remaining, safe =>
      let small : ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
          (prepared segment current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (canonicalPredictedClearanceFloor_le_prepared segment current prior
            request)
      let cached := CachedSource.canonical segment current prior request
      let cachedSmall : ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound := small
      let nextOwner := advanceCached segment within current prior request
        cached cachedSmall
      nextCached segment within current prior request cached safe.1 cachedSmall
        small (ofFreshMeshSafe segment within request.endpoint nextOwner
          remaining safe.2.2)

/-- Construct continuation from the initial owner's clearance check and uniform safety of the remaining mesh. -/
@[expose] public def ofMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (requests : List StepRequest) -> MeshSafe segment current owner requests ->
      Subdivision segment within current owner
  | [], _safe => .stop current owner
  | request :: remaining, safe =>
      let cached := CachedSource.canonical segment current owner request
      let cachedSmall : ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound := safe.2.1
      let nextOwner := advanceCached segment within current owner request
        cached cachedSmall
      nextCached segment within current owner request cached safe.1 cachedSmall
        safe.2.1 (ofFreshMeshSafe segment within request.endpoint nextOwner
          remaining safe.2.2)

/-- Uniform mesh safety makes the attempt return exactly the uniform-safety construction. -/
public theorem trySteps_eq_some_ofFreshMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (prior : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest)
    (safe : FreshMeshSafe segment current requests) :
    trySteps segment within current prior requests =
      some (ofFreshMeshSafe segment within current prior requests safe) := by
  induction requests generalizing current prior with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      let small : ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
          (prepared segment current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (canonicalPredictedClearanceFloor_le_prepared segment current prior
            request)
      have cachedSmall : ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            ((CachedSource.canonical segment current prior request).preparedOwner).track.initial.clearance.bound :=
        small
      simp only [trySteps, dif_pos safe.1, dif_pos cachedSmall]
      let nextOwner := advanceCached segment within current prior request
        (CachedSource.canonical segment current prior request) cachedSmall
      have tailSuccess :
          trySteps segment within request.endpoint
              nextOwner remaining =
            some (ofFreshMeshSafe segment within request.endpoint
              nextOwner remaining safe.2.2) := by
        exact inductionHypothesis request.endpoint
          nextOwner safe.2.2
      rw [tailSuccess]
      rfl

/-- The initial and uniform-tail safety conditions make the attempt return exactly their certified construction. -/
public theorem trySteps_eq_some_ofMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest)
    (safe : MeshSafe segment current owner requests) :
    trySteps segment within current owner requests =
      some (ofMeshSafe segment within current owner requests safe) := by
  cases requests with
  | nil => rfl
  | cons request remaining =>
      have cachedSmall : ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            ((CachedSource.canonical segment current owner request).preparedOwner).track.initial.clearance.bound :=
        safe.2.1
      simp only [trySteps, dif_pos safe.1, dif_pos cachedSmall]
      let nextOwner := advanceCached segment within current owner request
        (CachedSource.canonical segment current owner request) cachedSmall
      have tailSuccess :
          trySteps segment within request.endpoint
              nextOwner remaining =
            some (ofFreshMeshSafe segment within request.endpoint
              nextOwner remaining safe.2.2) := by
        exact trySteps_eq_some_ofFreshMeshSafe segment within request.endpoint
          nextOwner remaining safe.2.2
      rw [tailSuccess]
      rfl

end

open Purelib.Polynomial in
/-- A successful request attempt retains exactly one continuation step per input request. -/
public theorem trySteps_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests =
      some subdivision) :
    subdivision.stepCount = requests.length := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_stepCount, List.length_cons]
            exact congrArg Nat.succ
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

/-- Follow the original request list to its last target, retaining the current endpoint for an empty list. -/
@[expose] public def finalTarget (current : Endpoint) : List StepRequest -> Endpoint
  | [] => current
  | request :: remaining => finalTarget request.endpoint remaining

/-- Read the target endpoints from the exact request list in order. -/
@[expose] public def requestEndpoints : List StepRequest -> List Endpoint
  | [] => []
  | request :: remaining => request.endpoint :: requestEndpoints remaining

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- A successful attempt retains exactly the parameter edges determined by the original requests. -/
public theorem trySteps_parameterEdges {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests =
      some subdivision) :
    subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.parameterEdgesFrom left
        (requestEndpoints requests) := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_parameterEdges, requestEndpoints,
              ClearSheetContinuation.Subdivision.parameterEdgesFrom]
            exact congrArg
              (List.cons
                (ClearSheetContinuation.Subdivision.ParameterEdge.mk
                  left request.endpoint))
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

section
open Purelib.Polynomial
/-- A successful attempt retains the exact original request list. -/
public theorem trySteps_requests {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.requests = requests := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_requests]
            exact congrArg (List.cons request)
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

/-- Take the minimum of one and the predicted canonical clearance floors along the exact request list. -/
@[expose] public def FreshMeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Coordinate
  | _current, [] => 1
  | current, request :: remaining =>
      min (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshClearanceFloor segment request.endpoint remaining)

/-- Combine the first actual prepared clearance with the predicted floors for the remaining requests. -/
@[expose] public def MeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Coordinate
  | [] => 1
  | request :: remaining =>
      min (prepared segment current owner request).track.initial.clearance.bound
        (FreshMeshClearanceFloor segment request.endpoint remaining)

/-- Take the minimum of one and all predicted canonical floors along successive request endpoints. -/
@[expose] public def FreshMeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Coordinate
  | _current, [] => 1
  | current, request :: remaining =>
      min (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshPredictedClearanceFloor segment request.endpoint remaining)

/-- Combine the first predicted preparation clearance with the remaining predicted mesh floor. -/
@[expose] public def MeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (_owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Coordinate
  | [] => 1
  | request :: remaining =>
      min (preparedClearanceLower segment current request)
        (FreshMeshPredictedClearanceFloor segment request.endpoint remaining)

/-- The predicted clearance floor of every finite fresh mesh is strictly positive. -/
public theorem freshMeshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      0 < FreshMeshPredictedClearanceFloor segment current requests
  | _current, [] => by
      change (0 : Coordinate) < 1
      decide
  | current, request :: remaining => by
      apply Fraction.Order.Basic.lt_min
      · exact canonicalPredictedClearanceFloor_positive segment current request
      · exact freshMeshPredictedClearanceFloor_positive segment
          request.endpoint remaining

/-- The predicted clearance floor of every finite request mesh is strictly positive. -/
public theorem meshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      0 < MeshPredictedClearanceFloor segment current owner requests
  | [] => by
      change (0 : Coordinate) < 1
      decide
  | request :: remaining => by
      apply Fraction.Order.Basic.lt_min
      · exact preparedClearanceLower_positive segment current request
      · exact freshMeshPredictedClearanceFloor_positive segment
          request.endpoint remaining

/-- The predicted fresh-mesh floor is bounded by the fresh-mesh clearance floor. -/
public theorem freshMeshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      FreshMeshPredictedClearanceFloor segment current requests ≤
        FreshMeshClearanceFloor segment current requests
  | _current, [] => le_rfl
  | _current, request :: remaining =>
      Fraction.Order.Basic.min_le_min
        le_rfl
        (freshMeshPredictedClearanceFloor_le_actual segment request.endpoint
          remaining)

/-- The predicted mesh floor is bounded by the floor using the first actual prepared clearance. -/
public theorem meshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      MeshPredictedClearanceFloor segment current owner requests ≤
        MeshClearanceFloor segment current owner requests
  | [] => le_rfl
  | request :: remaining =>
      Fraction.Order.Basic.min_le_min (preparedClearanceLower_le segment current owner request)
        (freshMeshPredictedClearanceFloor_le_actual segment request.endpoint
          remaining)

/-- The finite fresh-mesh clearance floor is strictly positive. -/
public theorem freshMeshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      0 < FreshMeshClearanceFloor segment current requests
  | current, [] => by
      change (0 : Coordinate) < 1
      decide
  | current, request :: remaining => by
      apply Fraction.Order.Basic.lt_min
      · exact canonicalPredictedClearanceFloor_positive segment current request
      · exact freshMeshClearanceFloor_positive segment request.endpoint
          remaining

/-- The floor combining actual first clearance and predicted tail clearances is strictly positive. -/
public theorem meshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      0 < MeshClearanceFloor segment current owner requests
  | [] => by
      change (0 : Coordinate) < 1
      decide
  | request :: remaining => by
      apply Fraction.Order.Basic.lt_min
      · exact (prepared segment current owner request).track.initial.clearance.positive
      · exact freshMeshClearanceFloor_positive segment request.endpoint
          remaining

end

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- A common ordered edge-variation bound below the fresh-mesh floor certifies uniform mesh safety. -/
public theorem freshMeshSafe_of_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest)
      (bound : Coordinate),
      ClearSheetContinuation.Subdivision.EdgeVariationBound
          segment bound current (requestEndpoints requests) ->
        bound < FreshMeshClearanceFloor segment current requests ->
          FreshMeshSafe segment current requests
  | _current, [], _bound, _edgeBound, _below => trivial
  | current, request :: remaining, bound, edgeBound, below => by
      change current.parameter <= request.endpoint.parameter /\
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <= bound /\
          ClearSheetContinuation.Subdivision.EdgeVariationBound
            segment bound request.endpoint (requestEndpoints remaining) at edgeBound
      change bound < min
        (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshClearanceFloor segment request.endpoint remaining) at below
      exact
        ⟨edgeBound.1,
          edgeBound.2.1.trans_lt (below.trans_le (Fraction.Order.Basic.min_le_left _ _)),
          freshMeshSafe_of_edgeVariationBound segment request.endpoint
            remaining bound edgeBound.2.2
              (below.trans_le (Fraction.Order.Basic.min_le_right _ _))⟩

/-- A common ordered edge-variation bound below the owner-specific mesh floor certifies mesh safety. -/
public theorem meshSafe_of_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) (bound : Coordinate)
    (edgeBound :
      ClearSheetContinuation.Subdivision.EdgeVariationBound
        segment bound current (requestEndpoints requests))
    (below : bound < MeshClearanceFloor segment current owner requests) :
    MeshSafe segment current owner requests := by
  cases requests with
  | nil => trivial
  | cons request remaining =>
      change current.parameter <= request.endpoint.parameter /\
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <= bound /\
          ClearSheetContinuation.Subdivision.EdgeVariationBound
            segment bound request.endpoint (requestEndpoints remaining) at edgeBound
      change bound < min
        (prepared segment current owner request).track.initial.clearance.bound
        (FreshMeshClearanceFloor segment request.endpoint remaining) at below
      exact
        ⟨edgeBound.1,
          edgeBound.2.1.trans_lt (below.trans_le (Fraction.Order.Basic.min_le_left _ _)),
          freshMeshSafe_of_edgeVariationBound segment request.endpoint
            remaining bound edgeBound.2.2
              (below.trans_le (Fraction.Order.Basic.min_le_right _ _))⟩

end

section
open Purelib.Polynomial
/-- A successful attempt ends at the original request list's final target. -/
public theorem trySteps_endpoint {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.endpoint = finalTarget left requests := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            exact inductionHypothesis request.endpoint
              (advance segment within left owner request small)
              (subdivision := tail) recursiveSuccess
        next notSmall => contradiction
      next notOrdered => contradiction

/-- A successful attempt's terminal parameter is the final target parameter of the original requests. -/
public theorem trySteps_endpoint_parameter {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.endpoint.parameter = (finalTarget left requests).parameter := by
  exact congrArg (fun endpoint : Endpoint => endpoint.parameter)
    (trySteps_endpoint segment within left owner requests success)

end

open Purelib.Riemann.Branches in
/-- Extracting request endpoints preserves the original list's final target. -/
public theorem finalTarget_requestEndpoints (current : Endpoint)
    (requests : List StepRequest) :
    ClearSheetContinuation.Subdivision.finalTarget current
        (requestEndpoints requests) =
      finalTarget current requests := by
  induction requests generalizing current with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      exact inductionHypothesis request.endpoint

/-- Attach the same positive root-diameter request to each original endpoint in order. -/
@[expose] public def requestsAtDiameter (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    List Endpoint -> List StepRequest
  | [] => []
  | endpoint :: remaining =>
      { endpoint := endpoint
        rootDiameter := rootDiameter
        rootDiameterPositive := rootDiameterPositive } ::
        requestsAtDiameter rootDiameter rootDiameterPositive remaining

/-- Attaching a common diameter preserves the number of endpoints. -/
@[simp] public theorem requestsAtDiameter_length (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) (endpoints : List Endpoint) :
    (requestsAtDiameter rootDiameter rootDiameterPositive endpoints).length =
      endpoints.length := by
  induction endpoints with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      rewrite [requestsAtDiameter, List.length_cons, inductionHypothesis]
      exact Eq.refl _

/-- Reading endpoints after attaching a diameter recovers the exact original endpoint list. -/
@[simp] public theorem requestEndpoints_requestsAtDiameter
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (endpoints : List Endpoint) :
    requestEndpoints
        (requestsAtDiameter rootDiameter rootDiameterPositive endpoints) =
      endpoints := by
  induction endpoints with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      rewrite [requestsAtDiameter, requestEndpoints, inductionHypothesis]
      exact Eq.refl _

section
open Purelib.Polynomial
/-- A common positive diameter's uniform floor bounds the predicted fresh-mesh floor for any finite endpoint list. -/
public theorem uniformPreparedClearanceFloor_le_freshRequests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall (current : Endpoint) (endpoints : List Endpoint),
      uniformPreparedClearanceFloor segment rootDiameter <=
        FreshMeshPredictedClearanceFloor segment current
          (requestsAtDiameter rootDiameter rootDiameterPositive endpoints)
  | _current, [] => Fraction.Order.Basic.min_le_right _ _
  | current, endpoint :: remaining => by
      simp only [requestsAtDiameter, FreshMeshPredictedClearanceFloor]
      apply le_min
      · unfold canonicalPredictedClearanceFloor
          canonicalPredictedClearance preparedClearanceLower
        rw [min_self]
        exact uniformPreparedClearanceFloor_le_predicted segment rootDiameter
      · exact uniformPreparedClearanceFloor_le_freshRequests segment
          rootDiameter rootDiameterPositive endpoint remaining

/-- A common positive diameter's uniform floor bounds the predicted owner-specific mesh floor. -/
public theorem uniformPreparedClearanceFloor_le_meshRequests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall endpoints : List Endpoint,
      uniformPreparedClearanceFloor segment rootDiameter <=
        MeshPredictedClearanceFloor segment current owner
          (requestsAtDiameter rootDiameter rootDiameterPositive endpoints)
  | [] => Fraction.Order.Basic.min_le_right _ _
  | endpoint :: remaining => by
      simp only [requestsAtDiameter, MeshPredictedClearanceFloor]
      apply le_min
      · exact uniformPreparedClearanceFloor_le_predicted segment rootDiameter
      · exact uniformPreparedClearanceFloor_le_freshRequests segment
          rootDiameter rootDiameterPositive endpoint remaining

end

section
open Purelib.Riemann.Branches
/-- Attach the same positive root diameter to the exact dyadic targets between the original endpoints. -/
@[expose] public def dyadicRequests (depth : Nat) (left right : Endpoint)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    List StepRequest :=
  requestsAtDiameter rootDiameter rootDiameterPositive
    (ClearSheetContinuation.Subdivision.dyadicTargets depth left
      right)

/-- The target list of dyadic requests is exactly the original dyadic target list. -/
@[simp] public theorem requestEndpoints_dyadicRequests
    (depth : Nat) (left right : Endpoint)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    requestEndpoints
        (dyadicRequests depth left right rootDiameter rootDiameterPositive) =
      ClearSheetContinuation.Subdivision.dyadicTargets depth left
        right := by
  rewrite [dyadicRequests, requestEndpoints_requestsAtDiameter]
  exact Eq.refl _

end

section
open Purelib.Polynomial
/-- Read the clearance floor of the exact dyadic request mesh, using the original owner's first preparation. -/
@[expose] public def dyadicMeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Fraction.Rational :=
  MeshClearanceFloor segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- Every finite dyadic request mesh has positive clearance floor. -/
public theorem dyadicMeshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    0 < dyadicMeshClearanceFloor segment left right owner depth rootDiameter
      rootDiameterPositive :=
  meshClearanceFloor_positive segment left owner _

/-- Read the predicted clearance floor of the exact dyadic request mesh. -/
@[expose] public def dyadicMeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Fraction.Rational :=
  MeshPredictedClearanceFloor segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- Every finite dyadic request mesh has positive predicted clearance floor. -/
public theorem dyadicMeshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    0 < dyadicMeshPredictedClearanceFloor segment left right owner depth
      rootDiameter rootDiameterPositive :=
  meshPredictedClearanceFloor_positive segment left owner _

/-- The common diameter's uniform floor bounds every depth's predicted dyadic mesh floor. -/
public theorem uniformPreparedClearanceFloor_le_dyadicPredicted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    uniformPreparedClearanceFloor segment rootDiameter <=
      dyadicMeshPredictedClearanceFloor segment left right owner depth
        rootDiameter rootDiameterPositive := by
  unfold dyadicMeshPredictedClearanceFloor dyadicRequests
  exact uniformPreparedClearanceFloor_le_meshRequests segment left owner
    rootDiameter rootDiameterPositive _

/-- The predicted dyadic mesh floor is no greater than its owner-specific clearance floor. -/
public theorem dyadicMeshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    dyadicMeshPredictedClearanceFloor segment left right owner depth
        rootDiameter rootDiameterPositive ≤
      dyadicMeshClearanceFloor segment left right owner depth rootDiameter
        rootDiameterPositive :=
  meshPredictedClearanceFloor_le_actual segment left owner _

/-- Attempt continuation along the exact depth-indexed dyadic requests with a fixed positive root diameter. -/
@[expose] public def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (Subdivision segment within left owner) :=
  trySteps segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- The exact dyadic request mesh passes all checks along its actual cached-advance owner sequence. -/
@[expose] public def ExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Prop :=
  ExecutedMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

end

open Purelib.Polynomial in
/-- Decide safety along the actual execution of the exact finite dyadic request mesh. -/
public instance executedDyadicMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Decidable (ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :=
  executedMeshSafeDecidable segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

section
open Purelib.Polynomial
/-- Construct the dyadic subdivision from its certified actual execution checks. -/
@[expose] public def ofExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :
    Subdivision segment within left owner :=
  ofExecutedMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) safe

/-- Certified dyadic execution safety makes the attempt return exactly its certified construction. -/
public theorem tryDyadic_eq_some_ofExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :
    tryDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive =
      some (ofExecutedDyadicMeshSafe segment within left right owner depth
        rootDiameter rootDiameterPositive safe) := by
  unfold tryDyadic ofExecutedDyadicMeshSafe
  exact trySteps_eq_some_ofExecutedMeshSafe segment within _ safe

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- A successful dyadic attempt retains exactly the original depth-indexed dyadic edges. -/
public theorem tryDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges depth left
        right := by
  have edges := trySteps_parameterEdges segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) success
  rw [requestEndpoints_dyadicRequests,
    ClearSheetContinuation.Subdivision.parameterEdgesFrom_dyadicTargets]
    at edges
  exact edges

section
open Purelib.Polynomial
/-- A successful dyadic attempt retains exactly the original dyadic request list. -/
public theorem tryDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.requests =
      dyadicRequests depth left right rootDiameter rootDiameterPositive := by
  exact trySteps_requests segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) success

/-- The dyadic mesh fits the first actual prepared clearance and all remaining uniform predicted floors. -/
@[expose] public def DyadicMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Prop :=
  MeshSafe segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

end

section
open Purelib.Approximation.Rational
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Ordered endpoints and a dyadic variation estimate below the mesh clearance floor certify dyadic safety. -/
public theorem dyadicMeshSafe_of_variation_lt_clearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (below :
      Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound segment
            left.parameter right.parameter) depth <
        dyadicMeshClearanceFloor segment left right owner depth rootDiameter
          rootDiameterPositive) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive := by
  unfold DyadicMeshSafe
  apply meshSafe_of_edgeVariationBound segment left owner _ _
  · rw [requestEndpoints_dyadicRequests]
    exact
      ClearSheetContinuation.Subdivision.dyadicTargets_edgeVariationBound
        segment depth left right ordered
  · exact below

/-- Ordered endpoints and a dyadic variation estimate below the predicted floor certify dyadic safety. -/
public theorem dyadicMeshSafe_of_variation_lt_predictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (below :
      Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound segment
            left.parameter right.parameter) depth <
        dyadicMeshPredictedClearanceFloor segment left right owner depth
          rootDiameter rootDiameterPositive) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive :=
  dyadicMeshSafe_of_variation_lt_clearanceFloor segment left right owner depth
    rootDiameter rootDiameterPositive ordered
    (below.trans_le
      (dyadicMeshPredictedClearanceFloor_le_actual segment left right owner
        depth rootDiameter rootDiameterPositive))

/-- Search from depth zero for the first geometric variation bound below the uniform preparation floor.

For a positive root diameter the floor is positive, and the geometric search supplies a certified finite depth for the
original segment endpoints. -/
@[expose] public def sufficientDyadicDepth
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint) (rootDiameter : Coordinate) : Nat :=
  Geometric.Search.firstQuarterBelow
    (ClearSheetContinuation.variationBound segment
      left.parameter right.parameter)
    0 (uniformPreparedClearanceFloor segment rootDiameter)

/-- The selected sufficient depth makes the geometric variation bound strictly smaller than the uniform floor. -/
public theorem sufficientDyadicDepth_variation_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint) {rootDiameter : Coordinate}
    (rootDiameterPositive : 0 < rootDiameter) :
    Geometric.Basic.quarterRadius
        (ClearSheetContinuation.variationBound segment
          left.parameter right.parameter)
        (sufficientDyadicDepth segment left right rootDiameter) <
      uniformPreparedClearanceFloor segment rootDiameter := by
  exact Geometric.Search.firstQuarterBelow_accurate _
    (ClearSheetContinuation.variationBound_nonneg segment
      left.parameter right.parameter)
    0 _ (uniformPreparedClearanceFloor_positive segment rootDiameterPositive)

end

open Purelib.Polynomial in
/-- The selected sufficient depth yields a safe dyadic mesh for ordered endpoints and any original root owner. -/
public theorem sufficientDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    DyadicMeshSafe segment left right owner
      (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
        rootDiameterPositive := by
  apply dyadicMeshSafe_of_variation_lt_predictedClearanceFloor segment left
    right owner (sufficientDyadicDepth segment left right rootDiameter)
      rootDiameter rootDiameterPositive ordered
  exact (sufficientDyadicDepth_variation_lt segment left right
      rootDiameterPositive).trans_le
    (uniformPreparedClearanceFloor_le_dyadicPredicted segment left right owner
      (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
        rootDiameterPositive)

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Every depth at least the selected sufficient depth yields a safe dyadic mesh. -/
public theorem dyadicMeshSafe_of_sufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (enough : sufficientDyadicDepth segment left right rootDiameter <= depth) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive := by
  apply dyadicMeshSafe_of_variation_lt_predictedClearanceFloor segment left
    right owner depth rootDiameter rootDiameterPositive ordered
  have laterLe := quarterRadius_antitone
    (ClearSheetContinuation.variationBound_nonneg segment
      left.parameter right.parameter) enough
  exact (laterLe.trans_lt
      (sufficientDyadicDepth_variation_lt segment left right
        rootDiameterPositive)).trans_le
    (uniformPreparedClearanceFloor_le_dyadicPredicted segment left right owner
      depth rootDiameter rootDiameterPositive)

open Purelib.Polynomial in
/-- Decide the first-owner and uniform-tail safety checks for the exact dyadic requests. -/
public instance dyadicMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Decidable (DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) := by
  unfold DyadicMeshSafe
  infer_instance

section
open Purelib.Polynomial
/-- Compute the Boolean result of the exact dyadic mesh-safety decision. -/
@[expose] public def dyadicMeshAccepted {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Bool :=
  decide (DyadicMeshSafe segment left right owner depth rootDiameter
    rootDiameterPositive)

/-- A true acceptance result supplies the corresponding dyadic mesh-safety proof. -/
public theorem dyadicMeshSafe_of_accepted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (accepted : dyadicMeshAccepted segment left right owner depth rootDiameter
      rootDiameterPositive = true) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive :=
  of_decide_eq_true accepted

/-- Construct continuation along the exact dyadic requests from their retained mesh-safety certificate. -/
@[expose] public def checkedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) : Subdivision segment within left owner :=
  ofMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) safe

/-- Construct a safe dyadic continuation at the searched sufficient depth for ordered endpoints.

The construction retains the original source owner, exact dyadic requests, and actual prepared caches throughout the
finite continuation. -/
@[expose] public def sufficientDyadic
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    Subdivision segment within left owner :=
  checkedDyadic segment within left right owner
    (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
      rootDiameterPositive
      (sufficientDyadicMeshSafe segment left right owner rootDiameter
        rootDiameterPositive ordered)

/-- A dyadic safety certificate makes the attempt return exactly the checked construction. -/
public theorem tryDyadic_eq_some_checkedDyadic
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) :
    tryDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive =
      some (checkedDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive safe) :=
  trySteps_eq_some_ofMeshSafe segment within left owner _ safe

/-- The attempt at the searched sufficient depth returns exactly the sufficient-depth construction. -/
public theorem tryDyadic_sufficient_eq_some
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    tryDyadic segment within left right owner
        (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
          rootDiameterPositive =
      some (sufficientDyadic segment within left right owner rootDiameter
        rootDiameterPositive ordered) :=
  tryDyadic_eq_some_checkedDyadic segment within left right owner
    (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
      rootDiameterPositive
      (sufficientDyadicMeshSafe segment left right owner rootDiameter
        rootDiameterPositive ordered)

end

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- A successful depth-indexed dyadic attempt has exactly two to that depth continuation steps. -/
public theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.stepCount = 2 ^ depth := by
  exact (trySteps_stepCount segment within left owner _ success).trans (by
    rewrite [dyadicRequests, requestsAtDiameter_length,
      ClearSheetContinuation.Subdivision.dyadicTargets_length]
    exact Eq.refl _)

/-- A successful dyadic attempt ends at the exact original right endpoint. -/
public theorem tryDyadic_endpoint {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.endpoint = right := by
  calc
    subdivision.endpoint =
        finalTarget left
          (dyadicRequests depth left right rootDiameter
            rootDiameterPositive) :=
      trySteps_endpoint segment within left owner _ success
    _ = ClearSheetContinuation.Subdivision.finalTarget left
          (requestEndpoints
            (dyadicRequests depth left right rootDiameter
              rootDiameterPositive)) :=
      (finalTarget_requestEndpoints left _).symm
    _ = right := by
      rewrite [requestEndpoints_dyadicRequests,
        ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget]
      exact Eq.refl _

end

section
open Purelib.Polynomial
/-- Build the geometric path by restricting the original cleared segment along each retained parameter edge. -/
@[expose] public def toClearPathStored {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) :=
  Subdivision.casesOn
    (motive := fun left _ spine => Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt spine.endpoint.parameter)) subdivision
    (fun left _ => .nil (segment.pointAt left.parameter))
    (fun left _ request _ _ _ remaining =>
      .cons (segment.restrict within left.parameter request.endpoint.parameter
        left.inside request.endpoint.inside) (toClearPathStored remaining))
termination_by structural subdivision

/-- Read the cleared geometric path determined by the subdivision's exact parameter edges. -/
@[inline, expose] public def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) := toClearPathStored subdivision

/- Constructor equations are the proof interface; unfolding the recursive
stored-data helpers under an unknown tail is deliberately unnecessary. -/
end

section ClearPathProjectionEquations

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  (left : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))

open Purelib.Polynomial in
/-- A stopped subdivision gives the empty path at its original segment point. -/
@[simp] public theorem toClearPath_stop :
    (stop (segment := segment) (within := within) left owner).toClearPath = Polynomial.Geometry.ClearPath.nil
      (segment.pointAt left.parameter) := rfl

variable (request : StepRequest) (cached : CachedSource segment left owner request)
  (ordered : left.parameter ≤ request.endpoint.parameter)
  (small : Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound)
  (remaining : Subdivision segment within request.endpoint
    (advance segment within left owner request small))

open Purelib.Polynomial in
/-- Prepending a step prepends the corresponding restriction of the original cleared segment. -/
@[simp] public theorem toClearPath_next :
    (next left owner request cached ordered small remaining).toClearPath =
      Polynomial.Geometry.ClearPath.cons
        (segment.restrict within left.parameter request.endpoint.parameter
          left.inside request.endpoint.inside) remaining.toClearPath := rfl

end ClearPathProjectionEquations

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- The subdivision's terminal endpoint equals the final right endpoint of its retained parameter edges. -/
public theorem endpoint_eq_finalTarget_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.endpoint =
      ClearSheetContinuation.Subdivision.finalTarget left
        (subdivision.parameterEdges.map (fun edge => edge.right)) := by
  induction subdivision with
  | stop => rfl
  | next current owner request cached ordered small remaining
      inductionHypothesis =>
      simpa only [endpoint_next, parameterEdges_next, List.map_cons,
        ClearSheetContinuation.Subdivision.finalTarget] using
          inductionHypothesis

/-- The retained subdivision path equals the geometric path through its exact edge endpoints after terminal-index
transport. -/
public theorem toClearPath_eq_geometricPath_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            (endpoint_eq_finalTarget_parameterEdges subdivision)) =
      ClearSheetContinuation.Subdivision.geometricPath segment
        within left
          (subdivision.parameterEdges.map (fun edge => edge.right)) := by
  induction subdivision with
  | stop => rfl
  | next current owner request cached ordered small remaining
      inductionHypothesis =>
      simp only [toClearPath_next, endpoint_next, parameterEdges_next, List.map_cons,
        ClearSheetContinuation.Subdivision.geometricPath,
        Polynomial.Geometry.ClearPath.castFinish_cons]
      exact congrArg
        (Polynomial.Geometry.ClearPath.cons
          (segment.restrict within current.parameter
            request.endpoint.parameter current.inside
              request.endpoint.inside)) inductionHypothesis

end

open Purelib.Polynomial in
/-- Transporting the initial root owner preserves the original cleared path after terminal-index transport. -/
public theorem castOwner_toClearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
          (castOwner_endpoint equal subdivision)) =
      subdivision.toClearPath := by
  cases equal
  rfl

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Prepending a cached step prepends its exact segment restriction to the original tail path. -/
@[simp] public theorem nextCached_toClearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
          (nextCached_endpoint segment within left owner request cached ordered
            cachedSmall canonicalSmall remaining)) =
        .cons
          (segment.restrict within left.parameter request.endpoint.parameter
            left.inside request.endpoint.inside)
          remaining.toClearPath := by
  unfold nextCached
  simp only [toClearPath_next, endpoint_next, Polynomial.Geometry.ClearPath.castFinish_cons]
  apply congrArg (Polynomial.Geometry.ClearPath.cons
    (segment.restrict within left.parameter request.endpoint.parameter
      left.inside request.endpoint.inside))
  exact castOwner_toClearPath
    (advanceCached_eq_advance segment within left owner request cached
      cachedSmall canonicalSmall) remaining

/-- A successful attempt's cleared path equals the geometric path through the exact input request endpoints. -/
public theorem trySteps_toClearPath_eq_geometricPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            ((trySteps_endpoint segment within left owner requests
              success).trans
                (finalTarget_requestEndpoints left requests).symm)) =
      ClearSheetContinuation.Subdivision.geometricPath segment
        within left (requestEndpoints requests) := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            let cached := CachedSource.canonical segment left owner request
            let canonicalSmall :
                ClearSheetContinuation.variationBound segment
                    left.parameter request.endpoint.parameter <
                  (prepared segment left owner request).track.initial.clearance.bound :=
              small
            let nextOwner := advanceCached segment within left owner request
              cached small
            let computed := nextCached segment within left owner request cached
              ordered small canonicalSmall tail
            let endpointEqual := congrArg (fun endpoint : Endpoint =>
                segment.pointAt endpoint.parameter)
              (nextCached_endpoint segment within left owner request cached
                ordered small canonicalSmall tail)
            let tailEqual := congrArg (fun endpoint : Endpoint =>
                segment.pointAt endpoint.parameter)
              ((trySteps_endpoint segment within request.endpoint nextOwner
                  remaining recursiveSuccess).trans
                (finalTarget_requestEndpoints request.endpoint remaining).symm)
            change computed.toClearPath.castFinish
                (endpointEqual.trans tailEqual) =
              ClearSheetContinuation.Subdivision.geometricPath
                segment within left (requestEndpoints (request :: remaining))
            let head := segment.restrict within left.parameter
              request.endpoint.parameter left.inside request.endpoint.inside
            calc
              computed.toClearPath.castFinish
                    (endpointEqual.trans tailEqual) =
                  (computed.toClearPath.castFinish endpointEqual).castFinish
                    tailEqual :=
                (Polynomial.Geometry.ClearPath.castFinish_castFinish computed.toClearPath
                  endpointEqual tailEqual).symm
              _ = (Polynomial.Geometry.ClearPath.cons head tail.toClearPath).castFinish
                    tailEqual := by
                exact congrArg (fun path => path.castFinish tailEqual)
                  (nextCached_toClearPath segment within left owner request
                    cached ordered small canonicalSmall tail)
              _ = Polynomial.Geometry.ClearPath.cons head
                    (tail.toClearPath.castFinish tailEqual) :=
                Polynomial.Geometry.ClearPath.castFinish_cons head tail.toClearPath tailEqual
              _ = Polynomial.Geometry.ClearPath.cons head
                    (ClearSheetContinuation.Subdivision.geometricPath
                      segment within request.endpoint
                        (requestEndpoints remaining)) := by
                exact congrArg (Polynomial.Geometry.ClearPath.cons head)
                  (inductionHypothesis request.endpoint nextOwner
                    (subdivision := tail) recursiveSuccess)
              _ = ClearSheetContinuation.Subdivision.geometricPath
                    segment within left
                      (requestEndpoints (request :: remaining)) := rfl
        next notSmall => contradiction
      next notOrdered => contradiction

/-- A successful dyadic attempt's cleared path equals the original dyadic path after exact terminal-index transport. -/
public theorem tryDyadic_toClearPath_eq_dyadicPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            (tryDyadic_endpoint segment within left right owner depth
              rootDiameter rootDiameterPositive success)) =
      ClearSheetContinuation.Subdivision.dyadicPath segment within
        depth left right := by
  let requests :=
    dyadicRequests depth left right rootDiameter rootDiameterPositive
  have mesh := trySteps_toClearPath_eq_geometricPath segment within left owner
    requests success
  let endpointsEqual : requestEndpoints requests =
      ClearSheetContinuation.Subdivision.dyadicTargets depth left
        right :=
    requestEndpoints_dyadicRequests depth left right rootDiameter
      rootDiameterPositive
  let requestsFinishEqual := congrArg
    (fun endpoints : List Endpoint =>
      segment.pointAt
        ((ClearSheetContinuation.Subdivision.finalTarget left
          endpoints).parameter)) endpointsEqual
  let targetsFinishEqual := congrArg
    (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
        depth left right)
  have transportGeometry : forall (first second : List Endpoint)
      (equal : first = second),
      (ClearSheetContinuation.Subdivision.geometricPath segment
        within left first).castFinish
          (congrArg
            (fun endpoints : List Endpoint =>
              segment.pointAt
                ((ClearSheetContinuation.Subdivision.finalTarget
                  left endpoints).parameter)) equal) =
        ClearSheetContinuation.Subdivision.geometricPath segment
          within left second := by
    intro first second equal
    subst second
    rfl
  have geometricEqual :
      (ClearSheetContinuation.Subdivision.geometricPath segment
        within left (requestEndpoints requests)).castFinish
          requestsFinishEqual =
        ClearSheetContinuation.Subdivision.geometricPath segment
          within left
            (ClearSheetContinuation.Subdivision.dyadicTargets depth
              left right) := by
    exact transportGeometry _ _ endpointsEqual
  calc
    subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter)
              (tryDyadic_endpoint segment within left right owner depth
                rootDiameter rootDiameterPositive success)) =
        ((subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter)
              ((trySteps_endpoint segment within left owner requests
                success).trans
                  (finalTarget_requestEndpoints left requests).symm))).castFinish
            requestsFinishEqual).castFinish targetsFinishEqual := by
      rewrite [Polynomial.Geometry.ClearPath.castFinish_castFinish,
        Polynomial.Geometry.ClearPath.castFinish_castFinish]
      exact Eq.refl _
    _ = ((ClearSheetContinuation.Subdivision.geometricPath segment
          within left (requestEndpoints requests)).castFinish
            requestsFinishEqual).castFinish targetsFinishEqual := by
      rw [mesh]
    _ = (ClearSheetContinuation.Subdivision.geometricPath segment
          within left
            (ClearSheetContinuation.Subdivision.dyadicTargets depth
              left right)).castFinish targetsFinishEqual := by
      rw [geometricEqual]
    _ = ClearSheetContinuation.Subdivision.dyadicPath segment within
          depth left right := rfl

end

open Purelib.Polynomial in
/-- The retained cleared path has exactly one segment per subdivision step. -/
@[simp] public theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.toClearPath.segmentCount = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end Subdivision

end Purelib.Riemann.Branches.PreparedSheetContinuation
