module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Cached
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Observations
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Comparison

/-! # SAME old moving Vertices at the actual retained endpoint-query Owners

The original old head observations and independently retained actual
QueryAt records stay separate. Their whole Owner HEq certificates and
exact physical-point laws transport each complete Vertex, preserving its
denotation, request, state and value. No Owner or observation is produced.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View.EndpointQueries

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

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
variable {view : View budget current inherited request cached ordered small remaining fits trace} {sheet : Fin 2}
variable (endpoints : view.EndpointQueries (curve := curve) (differential := differential) sheet)
variable {expression : Expression curve.polynomial} {accuracy : AccuracyRequest}
variable (old : Primitive.Spine expression accuracy trace.path) (parts : view.Observations old)

/-- Transport the complete SAME old moving-source Vertex only to its actual retained source-query Owner. -/
def sourceVertex : Primitive.Vertex expression (segment.pointAt current.parameter) endpoints.source.owner accuracy :=
  Primitive.Vertex.castOwner view.source_point endpoints.source_owner_heq.symm parts.moving.before.first

/-- Transport the independent SAME old moving-target Vertex only to its actual retained moving-query Owner. -/
def movingVertex : Primitive.Vertex expression (segment.pointAt request.endpoint.parameter)
    endpoints.moving.owner accuracy :=
  Primitive.Vertex.castOwner view.moving_point endpoints.moving_owner_heq.symm parts.moving.before.last

/-- The whole original source Vertex, including its actual request and denotation, survives unchanged. -/
theorem sourceVertex_heq : HEq (endpoints.sourceVertex old parts) parts.moving.before.first :=
  Primitive.Vertex.castOwner_heq _ _ _

/-- The whole independent original target Vertex and all its actual observation data survive unchanged. -/
theorem movingVertex_heq : HEq (endpoints.movingVertex old parts) parts.moving.before.last :=
  Primitive.Vertex.castOwner_heq _ _ _

/-- The exact original source reading survives the whole-owner index transport. -/
theorem sourceVertex_value : (endpoints.sourceVertex old parts).value = parts.moving.before.first.value :=
  Primitive.Vertex.castOwner_value _ _ _

/-- The distinct original moving reading survives the same exact transport without resampling. -/
theorem movingVertex_value : (endpoints.movingVertex old parts).value = parts.moving.before.last.value :=
  Primitive.Vertex.castOwner_value _ _ _

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace.View.EndpointQueries

end
