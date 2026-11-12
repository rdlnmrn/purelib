module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Sources
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Cached.Completed.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain

/-! # One actual ordered source path from a supplied raw source bank

The literal child list, successful cover and centered chain come from the
SAME retained geometry. Concatenating the given covered source products
reads their whole existing caches. Existing sources joins those cells on
that actual chain; the stored bank-cell list is recovered exactly.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

namespace Cache.Geometry.Sources

/-- Concatenate the SAME complete source-preparation products on the SAME literal acquired raw cover. -/
@[expose] def preparations (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry →
      PreparedParents (Geometry.covered diameter positive budget subdivision centers fits trace geometry) floor targets
  | _, _, .stop _ _, _, _, _, _, _ => PUnit.unit
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry, shared =>
      PreparedParents.append geometry.1.val.acquisition.covered
        (Geometry.covered diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
        (Cached.Completed.Sources.preparations (count := count) (floor := floor) (targets := targets)
          geometry.1.val.view centers.1 geometry.1.val.endpoints diameter positive geometry.1.val.acquisition shared.1)
        (preparations diameter positive budget remaining centers.2 fits.2.2
          geometry.1.val.nextTrace geometry.2 shared.2)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The actual global raw preparation reads precisely the original supplied bank's six source-cell lists. -/
theorem cells_preparations (channel : Fin 6) (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry) →
      PreparedParents.cells
        (covered := Geometry.covered diameter positive budget subdivision centers fits trace geometry)
        (preparations diameter positive budget subdivision centers fits trace geometry shared) channel =
      cells channel diameter positive budget subdivision centers fits trace geometry shared
  | _, _, .stop _ _, _, _, _, _, _ => PreparedParents.cells_nil channel
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry, shared =>
      (PreparedParents.cells_append channel geometry.1.val.acquisition.covered
        (Geometry.covered diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2)
        (Cached.Completed.Sources.preparations (count := count) (floor := floor) (targets := targets)
          geometry.1.val.view centers.1 geometry.1.val.endpoints diameter positive geometry.1.val.acquisition shared.1)
        (preparations diameter positive budget remaining centers.2 fits.2.2
          geometry.1.val.nextTrace geometry.2 shared.2)).trans
          (congrArg₂ List.append
            (Cached.Completed.Sources.cells_preparations (count := count) (floor := floor) (targets := targets)
              geometry.1.val.view centers.1 geometry.1.val.endpoints diameter positive channel
              geometry.1.val.acquisition shared.1)
            (cells_preparations channel diameter positive budget remaining centers.2 fits.2.2
              geometry.1.val.nextTrace geometry.2 shared.2))
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

end Cache.Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

end
