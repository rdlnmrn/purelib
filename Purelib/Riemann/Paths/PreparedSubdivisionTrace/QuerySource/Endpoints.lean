module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead

/-! # Query agreement at literal moving and retention suffixes

Exact original endpoint readbacks attach the same retained upper Query to
the actual moving Owner. The materialized third link supplies the signed
retention comparison. No transport, reset, direct query or source factory
is executed to recover any of these original occurrences.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

namespace PreparedTraceBudget.Trace.View

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
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
variable {sheet : Fin 2}

/-- The exact nominal index transport of the moving suffix preserves its original root name. -/
theorem movingName_eq : ownerName view.movingOwner = ownerName view.moving.owner :=
  PreparedBankRootChains.ownerName_eq_of_heq
    (congrArg curve.polynomial.eval view.moving_point).symm view.movingOwner_heq

/-- The original upper query reads the same full-root name as the literal stored moving suffix.

This is a name readback of the identical original endpoint computation,
not an equality of independently selected Owner records. The actual
View's complete moving-Owner factory identity supplies the last step.
-/
theorem movingQuery_name_eq :
    (edgeOfStep curve differential segment within current inherited request cached ordered small sheet).rootName
      1 (of_decide_eq_true rfl) = ownerName view.moving.owner := by
  let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
  have moved := congrArg
    (fun owner : Owner (curve.polynomial.eval (segment.pointAt request.endpoint.parameter)) =>
      ownerRootName owner.parameterNonzero owner) view.movingOwner_eq
  exact (edge.rootName_one_eq_transported.trans moved.symm).trans view.movingName_eq

/-- Relate the supplied actual upper Query to this literal moving Owner through exact original name readbacks.

The relation retains the Query's own name and original sample procedure.
Its actual Owner stays separate from the moving suffix, even though the
original whole-factory laws prove the displayed channels agree.
-/
def queryMovingEquivalent
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    NamedEquivalent
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).rootName
        1 (of_decide_eq_true rfl)) (ownerName view.moving.owner) :=
  NamedEquivalent.transport query.name_eq.symm (query.name_eq.symm.trans view.movingQuery_name_eq)
    (NamedEquivalent.refl (ownerName query.owner))

/-- Derive signed agreement across the actual retained endpoint-reset link.

The complete original link supplies both tails and realized displacement
bounds. Its endpoints are the two stored suffixes, so the actual reset
Owner is not replaced by the transported moving Owner.
-/
def retentionEquivalent : NamedEquivalent (ownerName view.moving.owner) (ownerName view.tail.owner) :=
  view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
    (view.tail_point.trans view.moving_point.symm)

/-- Compare the same upper Query with the literal post-retention Owner through the same stored reset link. -/
def queryRetainedEquivalent
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    NamedEquivalent
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).rootName
        1 (of_decide_eq_true rfl)) (ownerName view.tail.owner) :=
  (view.queryMovingEquivalent query).trans view.retentionEquivalent

/-- The actual moving Owner agrees with the same original primitive Point at its exact retained endpoint.

The point equation is derived from the original edge endpoint and actual
View. The same supplied Query is used once in each comparison; the old
Point, its request, its certificate and its refinement remain unchanged.
-/
def movingSampleEquivalent
    (center : PreparedEdge.CenterState
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet))
    {count : Nat} {target : Rational}
    (localRequest : LocalRequest
      (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet, center⟩ :
        CenteredEdge curve differential) count target)
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl))
    (inside : localRequest.neighborhood.box.Contains view.moving.point)
    (sample : ContinuedNeighborhood.Point localRequest.neighborhood view.moving.point) :
    NamedEquivalent (ownerName view.moving.owner) sample.certificate.value.name :=
  (view.queryMovingEquivalent query).symm.trans
    (localRequest.retainedQueryEquivalent 1 (of_decide_eq_true rfl) query
      ((PreparedEdge.point_one _).trans view.moving_point.symm) inside sample)

/-- The distinct post-retention Owner agrees with the same supplied endpoint Point through its actual reset.

The endpoint Point is not retagged as a moving-source or a following-parent
sample. Its own physical coordinate, neighborhood and observed Owner are
preserved, while the actual stored retention relation supplies the sign.
-/
def retainedSampleEquivalent
    (center : PreparedEdge.CenterState
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet))
    {count : Nat} {target : Rational}
    (localRequest : LocalRequest
      (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet, center⟩ :
        CenteredEdge curve differential) count target)
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl))
    (inside : localRequest.neighborhood.box.Contains view.tail.point)
    (sample : ContinuedNeighborhood.Point localRequest.neighborhood view.tail.point) :
    NamedEquivalent (ownerName view.tail.owner) sample.certificate.value.name :=
  (view.queryRetainedEquivalent query).symm.trans
    (localRequest.retainedQueryEquivalent 1 (of_decide_eq_true rfl) query
      ((PreparedEdge.point_one _).trans view.tail_point.symm) inside sample)

end PreparedTraceBudget.Trace.View

end Purelib.Riemann.Paths.PreparedSubdivisionTrace

end
