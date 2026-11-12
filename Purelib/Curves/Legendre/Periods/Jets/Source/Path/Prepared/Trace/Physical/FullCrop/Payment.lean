module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.FullCrop
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Observations
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Internal source-model payment for the actual observed full crop

The original source preparation and old moving Vertices construct both
actual source/model comparison caches. Consumers retain that completed
cache together with the once-executed crop and its new observations;
neither a comparison cache nor a final integral estimate is an admission.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest CachedSource Subdivision)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right current : Endpoint} {budget : PreparedTraceBudget segment left right} {sheet : Fin 2}
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
variable (view :
  PreparedTraceBudget.Trace.View budget current inherited request cached ordered small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
variable {row : Row} {accuracy : AccuracyRequest}
variable (old : Primitive.Spine (row.expression parameter) accuracy trace.path)
variable (parts : view.Observations old)
variable (physical : PreparedTraceBudget.Trace.CropComparisons
  (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
    center⟩ : CenteredEdge (Fibre.frameCurve frame) basis) 0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl))
variable (firstQuery : PreparedEdge.Query
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet)
  0 (of_decide_eq_true rfl))
variable (lastQuery : PreparedEdge.Query
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet)
  1 (of_decide_eq_true rfl))
variable {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage}
variable {patch : PreparedPatch
  (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
    center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)}
variable {covered : (patch.neighborhood count).box.Contains
  ((edgeOfStep (Fibre.frameCurve frame) basis segment within
    current inherited request cached ordered small sheet).point 1)}
variable (prepared : PreparedParent patch count floor covered targets)
variable (allocation : targets.endpoint = 4 * accuracy.tolerance)

/-- The actual observed full crop and completed source-model payment share the same original prepared parent.

The second component is the existing correctness-bearing Comparisons
cache on the exact original old moving Vertices. This is an exact Sigma
alias, retaining both completed executions and all original owners.
-/
@[expose] def PaidFullCrop :=
  Σ compared : FullCrop (parameter := parameter) (frame := frame) (basis := basis)
      (row := row) (accuracy := accuracy) view center old parts physical firstQuery lastQuery,
    PreparedParent.Comparisons (frame := frame) (basis := basis)
      row prepared compared.sourceVertex compared.targetVertex allocation

/-- Observe the actual full crop once and construct its source-model comparison cache internally.

The supplied source preparation is read unchanged. The two old moving
Vertices cross only exact whole-Owner reindices. Their two actual finite
source/model comparisons are constructed once and retained with the new
crop observations; no source, Query, Point or old observation is rebuilt.
-/
def observePaidFullCrop : PaidFullCrop (parameter := parameter) (frame := frame) (basis := basis)
    (row := row) (accuracy := accuracy) view center old parts physical firstQuery lastQuery prepared allocation :=
  let compared := observeFullCrop view center old parts physical firstQuery lastQuery
  let sources := PreparedParent.Comparisons.build (frame := frame) (basis := basis)
    row prepared compared.sourceVertex compared.targetVertex allocation
  ⟨compared, sources⟩

namespace PaidFullCrop

variable {view center old parts physical firstQuery lastQuery prepared allocation}
variable (paid : PaidFullCrop (parameter := parameter) (frame := frame) (basis := basis)
  (row := row) (accuracy := accuracy) view center old parts physical firstQuery lastQuery prepared allocation)

/-- Read the retained once-executed crop, original old heads and actual new observation comparison caches. -/
abbrev observed := paid.1

/-- Read the completed actual source-model comparison cache without constructing either comparison again. -/
abbrev sources := paid.2

/-- The retained source-model cache derives the complete actual new crop primitive-increment payment. -/
theorem integral_le : Norm.Basic.normSq ((paid.observed.sampled.last.value - paid.observed.sampled.first.value) -
    (row.cell prepared.preparation.models).integralSample) ≤
    8 * accuracy.tolerance + 16 * targets.endpoint + 8 * prepared.preparation.cell.primitives.bound :=
  paid.observed.integral_le paid.sources

end PaidFullCrop

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

end
