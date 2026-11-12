module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Endpoints
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead

/-! # Actual old trace endpoint queries before source observations

The original View retains the whole source and moving suffix Owners.
Whole-factory/HEq laws turn those SAME Owners into original QueryAt
certificates; their proof-only name and box readbacks execute no query or
transport. The cached endpoint provider then feeds the actual geometry
producer before any source Targets or primitive accuracy is selected.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (QueryAt Queries)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last current : Endpoint} {budget : PreparedTraceBudget segment first last}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (view : View budget current inherited request cached ordered small remaining fits trace)

/-- Read the GIVEN source-suffix Owner, changing only its exact physical-point parameter index. -/
def sourceOwner : Owner (curve.polynomial.eval (segment.pointAt current.parameter)) :=
  castOwnerParameter (congrArg curve.polynomial.eval view.source_point) view.source.owner

/-- The complete source Owner is preserved through that exact physical index transport. -/
theorem sourceOwner_heq : HEq view.sourceOwner view.source.owner := castOwnerParameter_heq _ _

/-- The GIVEN source suffix is the original cached prepared Owner as a whole retained value. -/
theorem sourceOwner_eq : view.sourceOwner = cached.preparedOwner :=
  eq_of_heq (view.sourceOwner_heq.trans view.source_owner_heq)

/-- Certify the SAME actual source-suffix Owner as the original zero Query, without executing a query producer. -/
def sourceQuery (sheet : Fin 2) :
    QueryAt (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      0 (of_decide_eq_true rfl) (segment.pointAt current.parameter) where
  owner := view.sourceOwner
  name_eq := (congrArg (fun owner => ownerRootName owner.parameterNonzero owner) view.sourceOwner_eq).trans
    (PreparedEdge.rootName_zero_eq_cached
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)).symm
  refines := by
    rewrite [view.sourceOwner_eq]
    exact Geometry.Rational.Box.refines_refl _

/-- Certify the GIVEN actual moving Owner's original source-box refinement using its whole original factory identity. -/
private theorem moving_refines : view.movingOwner.track.initial.box.Refines cached.preparedOwner.track.initial.box := by
  rewrite [view.movingOwner_eq, cached.preparedOwner_eq]
  unfold PreparedSheetContinuation.transported
  exact RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
    (PreparedSheetContinuation.prepared segment current inherited request)
    (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside) _
    (PreparedSheetContinuation.transportReserve segment current request)

/-- Certify the SAME actual moving-suffix Owner as the original unit Query, without transporting any Owner again. -/
def movingQuery (sheet : Fin 2) :
    QueryAt (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl) (segment.pointAt request.endpoint.parameter) where
  owner := view.movingOwner
  name_eq := (congrArg (fun owner => ownerRootName owner.parameterNonzero owner) view.movingOwner_eq).trans
    (PreparedEdge.rootName_one_eq_transported
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)).symm
  refines := view.moving_refines

/-- Both genuine endpoint query records and exact factories on the SAME retained original View.

The existing pair/Subtype containers store the two complete records once.
The first and second actual Owners remain distinct, and their name/box
certificates come from whole old factory identities, never coordinates or
sheet labels alone. No primitive observation is selected here.
-/
@[expose] def EndpointQueries (sheet : Fin 2) :=
  (_source : {value : QueryAt
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      0 (of_decide_eq_true rfl) (segment.pointAt current.parameter) //
    value = view.sourceQuery (differential := differential) sheet}) ×
  {value : QueryAt
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl) (segment.pointAt request.endpoint.parameter) //
    value = view.movingQuery (differential := differential) sheet}

namespace EndpointQueries

/-- Retain both original old endpoint Owners once, with their genuine QueryAt certificates and complete factories. -/
def build (sheet : Fin 2) : view.EndpointQueries (differential := differential) sheet :=
  let source := view.sourceQuery (differential := differential) sheet
  let moving := view.movingQuery (differential := differential) sheet
  ⟨⟨source, rfl⟩, ⟨moving, rfl⟩⟩

variable {view} {sheet : Fin 2} (retained : view.EndpointQueries (differential := differential) sheet)

/-- Read the SAME whole source QueryAt certificate with its original actual Owner. -/
@[expose] def source : QueryAt
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
    0 (of_decide_eq_true rfl) (segment.pointAt current.parameter) := retained.1.val

/-- Read the separate SAME whole moving QueryAt certificate with its actual old moving Owner. -/
@[expose] def moving : QueryAt
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
    1 (of_decide_eq_true rfl) (segment.pointAt request.endpoint.parameter) := retained.2.val

/-- The complete cached source query is the genuine constructor on that SAME retained View. -/
theorem source_eq : retained.source = view.sourceQuery (differential := differential) sheet := retained.1.property

/-- The complete cached moving query is the genuine constructor on its SAME original old suffix. -/
theorem moving_eq : retained.moving = view.movingQuery (differential := differential) sheet := retained.2.property

/-- The cached source query retains the SAME whole old source-suffix Owner up to exact physical index transport. -/
theorem source_owner_heq : HEq retained.source.owner view.source.owner :=
  (heq_of_eq (congrArg (fun query : QueryAt
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      0 (of_decide_eq_true rfl) (segment.pointAt current.parameter) => query.owner) retained.source_eq)).trans
        view.sourceOwner_heq

/-- The cached moving query retains the independent SAME whole old moving-suffix Owner. -/
theorem moving_owner_heq : HEq retained.moving.owner view.moving.owner :=
  (heq_of_eq (congrArg (fun query : QueryAt
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl) (segment.pointAt request.endpoint.parameter) => query.owner) retained.moving_eq)).trans
        view.movingOwner_heq

/-- Derive the actual inherited-to-source-query comparison from the SAME original stationary source link.

The supplied endpoint query retains its actual Owner and whole-Owner HEq.
Its exact physical index transports only that given comparison; no cached
source preparation, query, root transport or independent Owner is rebuilt.
-/
def sourceEquivalent : NamedEquivalent (ownerName inherited) (ownerName retained.source.owner) :=
  let sameName : ownerName retained.source.owner = ownerName view.source.owner :=
    PreparedBankRootChains.ownerName_eq_of_heq
      (congrArg curve.polynomial.eval view.source_point).symm retained.source_owner_heq
  let original := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
  NamedEquivalent.transport rfl sameName.symm original

/-- Derive the actual moving-query-to-following-source comparison from the SAME original retention link.

The right Owner is read from remaining.sourceOwner, the original explicit
stored-data projection. The actual endpoint-query Owner and retained
suffix Owner remain distinct inputs with whole-Owner transport evidence;
no dependent advance index is evaluated to recover the right Owner.
-/
def followingEquivalent : NamedEquivalent (ownerName retained.moving.owner) (ownerName remaining.sourceOwner) :=
  let sameName : ownerName retained.moving.owner = ownerName view.moving.owner :=
    PreparedBankRootChains.ownerName_eq_of_heq
      (congrArg curve.polynomial.eval view.moving_point).symm retained.moving_owner_heq
  NamedEquivalent.transport sameName.symm view.tail_name_eq view.retentionEquivalent

/-- Reuse both SAME actual old endpoint queries and acquire original queries only at strict interior fractions. -/
@[expose] def queries : Queries
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet) :=
  let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
  Queries.withEndpoints edge (retained.source.castPoint edge.point_zero.symm)
    (retained.moving.castPoint edge.point_one.symm)

/-- Build actual covered child geometry on the GIVEN old endpoint queries before source Targets or accuracy selection.

The actual checked block and all its mesh/factory evidence are forwarded
by the original shared geometry worker. Its root comparison consumes the
same endpoint caches throughout. Existing old primitive observations,
if later supplied, retain their actual original requests and accuracies.
-/
def withGeometry (center : PreparedEdge.CenterState
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet))
    (diameter : Rational) (positive : 0 < diameter) {count : Nat} {Result : Type u}
    (stationary : PrimitiveCover.StationaryConsumerFromQueries
      (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet,
        center⟩ : CenteredEdge curve differential) retained.queries Result)
    (refined : (proper : current.parameter < request.endpoint.parameter) →
      PrimitiveCover.ConsumerFromQueries (count := count)
        (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet,
          center⟩ : CenteredEdge curve differential) retained.queries proper diameter positive Result) : Result :=
  PrimitiveCover.withCoverOrStationaryFromQueries (count := count)
    (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet,
      center⟩ : CenteredEdge curve differential) retained.queries diameter positive stationary refined

end EndpointQueries

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View

end
