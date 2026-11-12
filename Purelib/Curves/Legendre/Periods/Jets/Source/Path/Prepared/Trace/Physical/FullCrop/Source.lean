module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.FullCrop.Payment
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
import Purelib.Riemann.Paths.PreparedTraceEdges.Queries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # The original affine source on its actual selected full-parent query crop

Inside the existing withParent callback, this constructor builds the same
View's crop closure once and keeps its entire factory equation. That exact
closure produces the retained paid moving path. The unchanged source cell,
models and six-channel Query supply productive observations whose actual
roots are compared to the original parent's direct Queries.
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

/-- The same View's actual full crop, its paid observations and productive original source-root queries.

The complete crop-closure factory equation retains its accepted parent,
original budget and exact fit certificates. The payment and source-query
family consume the same original source preparation. These existing
Sigma/product owners add no replacement path, cell, model or preparation.
-/
@[expose] def AffineFullCrop :=
  Σ physical : {value : PreparedTraceBudget.Trace.CropComparisons
      (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet, center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)
      0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl) //
    value = view.cropComparisons center 0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl)
      (of_decide_eq_true rfl)},
    PaidFullCrop (parameter := parameter) (frame := frame) (basis := basis) (row := row) (accuracy := accuracy)
      view center old parts physical.val firstQuery lastQuery prepared allocation ×
    PreparedParent.RootedQueries (frame := frame) prepared

/-- Attach the original source roots to one actual full-parent crop inside its selected withParent callback.

One crop closure is constructed, retained with Eq.refl, and executed once
by the existing paid observer. The productive callback keeps the same
original source Query and models; every invocation retains its own actual
bundle, direct Query and internally derived six-channel root comparison.
-/
def observeAffineFullCrop : AffineFullCrop (parameter := parameter) (frame := frame) (basis := basis)
    (row := row) (accuracy := accuracy) view center old parts firstQuery lastQuery prepared allocation :=
  let physical := view.cropComparisons center 0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (of_decide_eq_true rfl)
  let paid := observePaidFullCrop view center old parts physical firstQuery lastQuery prepared allocation
  let queries : PreparedParent.RootedQueries (frame := frame) prepared :=
    fun fraction inside => PreparedParent.RootedQuery.build prepared fraction inside
  ⟨⟨physical, rfl⟩, paid, queries⟩

namespace AffineFullCrop

variable {view center old parts firstQuery lastQuery prepared allocation}
variable (cropped : AffineFullCrop (parameter := parameter) (frame := frame) (basis := basis)
  (row := row) (accuracy := accuracy) view center old parts firstQuery lastQuery prepared allocation)

/-- Read the complete same-View crop closure without a new selector or closure construction. -/
abbrev physical := cropped.1.val

/-- Read the same once-executed crop, both observation executions and internally completed source payment. -/
abbrev paid := cropped.2.1

/-- Read the productive callback for the same original spatial source and all six actual root attachments. -/
abbrev queries := cropped.2.2

/-- The retained entire crop closure has its exact original same-View factory, beyond its endpoint list. -/
theorem physical_eq : cropped.physical =
    view.cropComparisons center 0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl) :=
  cropped.1.property

/-- The retained moving path is the original affine queryPath on the same original parent, budget, fits and Queries.

This complete value identity is derived from both original factory
certificates. No path or geometric support is inferred from vertex equality,
sheet labels or an endpoint matrix action.
-/
theorem queryPath_eq : cropped.paid.observed.crop =
    Riemann.Paths.PreparedTraceEdges.PreparedTraceBudget.queryPath
      (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet)
      budget fits.1 fits.2.1 0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
      firstQuery lastQuery := by
  have factory := congrArg (fun physical : PreparedTraceBudget.Trace.CropComparisons
    (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within
      current inherited request cached ordered small sheet, center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)
    0 1 (of_decide_eq_true rfl) (of_decide_eq_true rfl) => physical.2 firstQuery lastQuery) cropped.physical_eq
  exact cropped.paid.observed.crop_eq.trans factory

/-- The actual affine crop primitive increment pays the same retained original row-cell integral sample. -/
theorem integral_le : Norm.Basic.normSq
    ((cropped.paid.observed.sampled.last.value - cropped.paid.observed.sampled.first.value) -
      (row.cell prepared.preparation.models).integralSample) ≤
    8 * accuracy.tolerance + 16 * targets.endpoint + 8 * prepared.preparation.cell.primitives.bound :=
  cropped.paid.integral_le

end AffineFullCrop

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

end
