module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Cached.Completed
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition.Chain

/-! # The original covered source product of one acquired child chain

The supplied source bank already stores every original parent preparation.
This reader returns that SAME whole product at the SAME acquired covering
spine; it performs no source, Point, query or primitive observation work.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (edgeOfStep)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right current : PreparedSheetContinuation.Endpoint}
    {budget : PreparedTraceBudget segment left right} {sheet : Fin 2}
variable {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : PreparedTraceBudget.Trace budget
  (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (view : PreparedTraceBudget.Trace.View
  budget current inherited request cached ordered small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
variable (endpoints : view.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet)
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}
variable (diameter : Rational) (positive : 0 < diameter)

namespace Completed.Sources

/-- Read the SAME supplied whole parent product on its actual acquired cover, including an empty stationary word. -/
@[expose] def preparations
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry →
      PreparedParents geometry.covered floor targets :=
  match geometry with
  | .inl _ => fun _ => PUnit.unit
  | .inr _ => fun shared => shared.val

/-- The acquired-cover product retains exactly the supplied bank's original literal source-cell list. -/
theorem cells_preparations (channel : Fin 6)
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry) :
    PreparedParents.cells (covered := geometry.covered)
      (preparations (count := count) (floor := floor) (targets := targets)
          view center endpoints diameter positive geometry shared) channel =
      cells (count := count) (floor := floor) (targets := targets)
        view center endpoints diameter positive channel geometry shared := by
  cases geometry with
  | inl stationary =>
      cases shared
      exact PreparedParents.cells_nil channel
  | inr retained => rfl

end Completed.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

end
