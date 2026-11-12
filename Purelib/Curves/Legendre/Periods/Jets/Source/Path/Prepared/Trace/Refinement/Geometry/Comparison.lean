module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry

/-! # Original comparison factories on the same given geometry

Every actual Cache head already retains its whole Entry.build equation.
Direct structural equality therefore recovers the original Cache factory
from the given-geometry execution without running that factory for data.
The existing Compared type and scalar telescope remain the public result.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Cache

/-- Complete retained head factories identify two actual comparison caches on the same old trace and observations.

Each original request supplies a whole head equality. Structural recursion
then identifies the same literal tails at their actual Trace/Spine indices;
no coordinate, sheet label or final numerical comparison identifies data.
-/
theorem eq_of_factories (row : Row) (diameter : Rational) (positive : 0 < diameter)
    (request : AccuracyRequest) (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    (first last : Cache (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed) → first = last
  | _, _, .stop _ _, _, _, _, _, first, last => by
      cases first
      cases last
      rfl
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, first, last => by
      rcases first with ⟨⟨firstHead, firstFactory⟩, firstTail⟩
      rcases last with ⟨⟨lastHead, lastFactory⟩, lastTail⟩
      have same : firstHead = lastHead := firstFactory.trans lastFactory.symm
      cases same
      have following := eq_of_factories
        row diameter positive request budget remaining centers.2 fits.2.2
        firstHead.nextTrace firstHead.nextObserved firstTail lastTail
      cases following
      rfl
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

end Cache

variable (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
variable (budget : PreparedTraceBudget segment left right) {current : PreparedSheetContinuation.Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable (subdivision : Subdivision segment within current owner)
variable (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
variable (fits : budget.RequestsFit current subdivision.requests)
variable (trace : PreparedTraceBudget.Trace budget subdivision fits)
variable (geometry : Cache.Geometry (count := count) diameter positive budget subdivision centers fits trace)
variable (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)

/-- Compare the actual old observations on the same retained geometry and return the original complete comparison type.

The numerical fold consumes the given geometry once. Its original Cache
factory is derived from complete retained head equations in an erased
proof; Cache.build is not executed to recover any geometry or observation.
-/
def compareFromGeometry : Compared (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed :=
  let retained := Cache.fromGeometry (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry observed
  have factory := Cache.eq_of_factories (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed retained
    (Cache.build (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed)
  ⟨⟨centers, rfl⟩, ⟨trace, rfl⟩, ⟨observed, rfl⟩, ⟨retained, factory⟩⟩

/-- The original comparison retains the exact given-geometry numerical execution as its complete cache. -/
theorem compareFromGeometry_completed :
    HEq (compareFromGeometry (frame := frame) (basis := basis) (sheet := sheet)
      (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry observed).completed
      (Cache.fromGeometry (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace geometry observed) := by
  unfold compareFromGeometry Compared.completed
  rfl

/-- The complete original comparison uses precisely the total child count available before old observations. -/
theorem compareFromGeometry_childCount :
    (compareFromGeometry (frame := frame) (basis := basis) (sheet := sheet)
      (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry observed).childCount =
      Cache.Geometry.childCount diameter positive budget subdivision centers fits trace geometry := by
  change Cache.childCount (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed
    (Cache.fromGeometry (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry observed) = _
  exact Cache.fromGeometry_childCount (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry observed

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

end
