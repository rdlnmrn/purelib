module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Comparison
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Observations
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Endpoints
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Finite full-parent crop increments on the same old observations

Only the full parent has both old moving endpoint observations. The actual
selected View identifies their original root names with the supplied zero
and unit Queries. One new observation spine executes the supplied crop;
two actual comparison caches pay the change of its primitive increment.
Strict-fraction old observations and primitive constant normalization are
not asserted by this construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest CachedSource Subdivision)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
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

/-- The same old spine and three old heads, one executed full crop, its new spine and both actual comparisons.

The complete source/moving/reset observation payload is retained literally.
The new crop and new observation each have their original factory
equation. Both comparisons retain the original possible readings and
states; no desired increment bound is an input.
-/
@[expose] def FullCrop :=
  Σ originals : {value : Primitive.Spine (row.expression parameter) accuracy trace.path × view.Observations old //
    value = (old, parts)},
  Σ cropped : {value : OwnerPath (Paths.polynomial parameter)
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet).point 0)
      firstQuery.owner
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet).point 1)
      lastQuery.owner // value = physical.2 firstQuery lastQuery},
  Σ sampled : {value : Primitive.Spine (row.expression parameter) accuracy cropped.val //
    value = Primitive.Spine.build (accuracy := accuracy) cropped.val (Trace.defined row cropped.val)},
    Primitive.Vertex.EndpointComparisons originals.val.2.moving.before.first originals.val.2.moving.before.last
      sampled.val.first sampled.val.last

/-- The original source suffix and actual zero Query read the same original root name. -/
private theorem source_query_name_eq : ownerName view.source.owner = ownerName firstQuery.owner :=
  view.source_name_eq.trans
    ((PreparedEdge.rootName_zero_eq_cached
      (edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet)).symm.trans firstQuery.name_eq)

/-- The original moving suffix and actual unit Query read the same transported root name. -/
private theorem moving_query_name_eq : ownerName view.moving.owner = ownerName lastQuery.owner :=
  (view.movingQuery_name_eq (curve := Fibre.frameCurve frame) (differential := basis)
    (sheet := sheet)).symm.trans lastQuery.name_eq

/-- Execute the supplied full-parent crop once and compare its new observations with both actual old moving endpoints.

The selected View's original source and moving name readbacks derive the
two root relations to the supplied literal Queries. Point equalities
reindex only their coordinates. The original old requests are unchanged;
the new spine is a separate explicit observation execution.
-/
def observeFullCrop : FullCrop (parameter := parameter) (frame := frame) (basis := basis)
    (row := row) (accuracy := accuracy) view center old parts physical firstQuery lastQuery :=
  let originals := (old, parts)
  let cropped := physical.2 firstQuery lastQuery
  let sampled := Primitive.Spine.build (accuracy := accuracy) cropped (Trace.defined row cropped)
  have firstName := source_query_name_eq (frame := frame) (basis := basis) view firstQuery
  have lastName := moving_query_name_eq (frame := frame) (basis := basis) view lastQuery
  let compared := Primitive.Vertex.compareEndpointsAt
    originals.2.moving.before.first originals.2.moving.before.last sampled.first sampled.last
    (view.source_point.trans (PreparedEdge.point_zero
      (edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet)).symm)
    (view.moving_point.trans (PreparedEdge.point_one
      (edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet)).symm)
    (NamedEquivalent.transport rfl firstName (NamedEquivalent.refl (ownerName view.source.owner)))
    (NamedEquivalent.transport rfl lastName (NamedEquivalent.refl (ownerName view.moving.owner)))
  ⟨⟨originals, rfl⟩, ⟨cropped, rfl⟩, ⟨sampled, rfl⟩, compared⟩

namespace FullCrop

variable {view center old parts physical firstQuery lastQuery}
variable (compared : FullCrop (parameter := parameter) (frame := frame) (basis := basis)
  (row := row) (accuracy := accuracy) view center old parts physical firstQuery lastQuery)

/-- Read the complete unchanged original old row observation spine. -/
abbrev original := compared.1.val.1

/-- Read the same complete actual source/moving/reset old-head payload. -/
abbrev heads := compared.1.val.2

/-- Read the actual once-executed query crop with both original supplied endpoint Owners. -/
abbrev crop := compared.2.1.val

/-- Read the separate new observation spine on this same executed full-parent crop. -/
abbrev sampled := compared.2.2.1.val

/-- Read both complete original endpoint-observation comparison caches without reconstructing either. -/
abbrev comparisons := compared.2.2.2

/-- Both whole old caches remain the same original inputs. -/
theorem originals_eq : (compared.original, compared.heads) = (old, parts) := compared.1.property

/-- The crop is the one execution of the supplied actual crop operation on these same Queries. -/
theorem crop_eq : compared.crop = physical.2 firstQuery lastQuery := compared.2.1.property

/-- The new observation spine has its original factory on that same retained crop. -/
theorem sampled_eq : compared.sampled =
    Primitive.Spine.build (accuracy := accuracy) compared.crop (Trace.defined row compared.crop) :=
  compared.2.2.1.property

/-- The actual new full-crop primitive increment differs from the old moving increment by a finite paid bound. -/
theorem increment_le : Norm.Basic.normSq
    ((compared.sampled.last.value - compared.sampled.first.value) -
      (compared.heads.moving.before.last.value - compared.heads.moving.before.first.value)) ≤
    4 * accuracy.tolerance := compared.comparisons.increment_le

/-- Read the entire old moving-source Vertex at its exact original cached parent Owner index. -/
def sourceVertex : PreparedParent.SourceVertex (frame := frame) (basis := basis) row
    (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
      center⟩ : CenteredEdge (Fibre.frameCurve frame) basis) accuracy :=
  Primitive.Vertex.castOwner view.source_point view.source_owner_heq compared.heads.moving.before.first

/-- Read the distinct old moving-target Vertex at the same original parent's transported Owner index. -/
def targetVertex : PreparedParent.TargetVertex (frame := frame) (basis := basis) row
    (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
      center⟩ : CenteredEdge (Fibre.frameCurve frame) basis) accuracy :=
  Primitive.Vertex.castOwner view.moving_point
    (view.movingOwner_heq.symm.trans (heq_of_eq view.movingOwner_eq)) compared.heads.moving.before.last

/-- The source reindex keeps the whole original moving Vertex, including its denotation and selected request. -/
private theorem packaged_sourceVertex_heq : HEq compared.sourceVertex compared.heads.moving.before.first :=
  Primitive.Vertex.castOwner_heq _ _ _

/-- The source reindex keeps the whole original moving Vertex, including its denotation and selected request. -/
theorem sourceVertex_heq : HEq compared.sourceVertex compared.heads.moving.before.first :=
  packaged_sourceVertex_heq compared

/-- The target reindex keeps the whole distinct original moving Vertex and all of its actual observation data. -/
private theorem packaged_targetVertex_heq : HEq compared.targetVertex compared.heads.moving.before.last :=
  Primitive.Vertex.castOwner_heq _ _ _

/-- The target reindex keeps the whole distinct original moving Vertex and all of its actual observation data. -/
theorem targetVertex_heq : HEq compared.targetVertex compared.heads.moving.before.last :=
  packaged_targetVertex_heq compared

/-- The source reindex retains the actual original old moving reading. -/
private theorem packaged_sourceVertex_value :
    compared.sourceVertex.value = compared.heads.moving.before.first.value :=
  Primitive.Vertex.castOwner_value _ _ _

/-- The source reindex retains the actual original old moving reading. -/
theorem sourceVertex_value : compared.sourceVertex.value = compared.heads.moving.before.first.value :=
  packaged_sourceVertex_value compared

/-- The target reindex retains the separate original old moving reading. -/
private theorem packaged_targetVertex_value :
    compared.targetVertex.value = compared.heads.moving.before.last.value :=
  Primitive.Vertex.castOwner_value _ _ _

/-- The target reindex retains the separate original old moving reading. -/
theorem targetVertex_value : compared.targetVertex.value = compared.heads.moving.before.last.value :=
  packaged_targetVertex_value compared

variable {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage}
variable {patch : PreparedPatch
  (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
    center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)}
variable {covered : (patch.neighborhood count).box.Contains
  ((edgeOfStep (Fibre.frameCurve frame) basis segment within
    current inherited request cached ordered small sheet).point 1)}
variable {prepared : PreparedParent patch count floor covered targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}

/-- The same source-model payment composes with the actual full-crop observation comparison.

The retained source comparison cache refers to the two original moving
Vertices under exact point/Owner reindices. Its existing integral theorem
supplies the old payment internally. Neither that final estimate nor any
primitive normalization or strict-fraction old observation is an input.
-/
theorem integral_le
    (retained : PreparedParent.Comparisons (frame := frame) (basis := basis)
      row prepared compared.sourceVertex compared.targetVertex allocation) :
    Norm.Basic.normSq ((compared.sampled.last.value - compared.sampled.first.value) -
      (row.cell prepared.preparation.models).integralSample) ≤
      8 * accuracy.tolerance + 16 * targets.endpoint + 8 * prepared.preparation.cell.primitives.bound := by
  have oldBound := PreparedParent.increment_le (frame := frame) (basis := basis) retained
  rewrite [compared.sourceVertex_value, compared.targetVertex_value] at oldBound
  have difference : (compared.sampled.last.value - compared.sampled.first.value) -
      (row.cell prepared.preparation.models).integralSample =
      ((compared.sampled.last.value - compared.sampled.first.value) -
        (compared.heads.moving.before.last.value - compared.heads.moving.before.first.value)) +
      ((compared.heads.moving.before.last.value - compared.heads.moving.before.first.value) -
        (row.cell prepared.preparation.models).integralSample) := by ring1
  rewrite [difference]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct compared.increment_le oldBound)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end FullCrop

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

end
