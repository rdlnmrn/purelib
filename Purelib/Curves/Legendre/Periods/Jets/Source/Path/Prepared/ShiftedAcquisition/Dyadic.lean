module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Partition
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Dyadic
import Purelib.Data.Rat.Interval.ConvexCombination

/-! # Actual shifted children at their original dyadic parameters

The original acquired Mesh edge word and SAME centered Parents give an
exact bounded-index transport. Normalizing a point inside that original
coarse interval reads the identical physical point of the original affine
parent. No center, Mesh, query, Step or acquisition is built by these laws.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Algebra
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- Transport a raw Mesh coordinate to the SAME actual centered parent occurrence. -/
@[expose] def dyadicIndex (index : Fin retained.acquired.mesh.edges.length) :
    Fin retained.parents.covered.parents.length :=
  Parents.parentIndex basis parent.edge.sheet count retained.acquired retained.parents index

/-- The selected actual child's original parameter edge is the SAME retained raw Mesh edge. -/
theorem dyadicEdge_eq (index : Fin retained.acquired.mesh.edges.length) :
    (retained.childAt (retained.dyadicIndex index)).parameterEdge =
      retained.acquired.mesh.edges[index.val]'index.isLt :=
  Parents.parameterEdge_at basis parent.edge.sheet count retained.acquired retained.parents index

/-- A normalized parameter in the SAME raw Mesh interval reads the identical original affine-parent point.

Both original endpoints are retained through dyadicEdge_eq. The original
parameterAt readback and segmentParameter interpolation identify the point;
this scalar operation makes no signed-sheet or observation claim.
-/
theorem dyadicPoint_eq (index : Fin retained.acquired.mesh.edges.length) (time : Rational)
    (inside :
      (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter ≤ time ∧
        time ≤ (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter) :
    (retained.childAt (retained.dyadicIndex index)).edge.point
      (segmentParameter (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
        (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter time) = parent.edge.point time := by
  let edge := retained.acquired.mesh.edges[index.val]'index.isLt
  let child := retained.childAt (retained.dyadicIndex index)
  have left_eq : child.edge.left.parameter = edge.left.parameter :=
    congrArg (fun value : ClearSheetContinuation.Subdivision.ParameterEdge => value.left.parameter)
      (retained.dyadicEdge_eq index)
  have right_eq : child.edge.request.endpoint.parameter = edge.right.parameter :=
    congrArg (fun value : ClearSheetContinuation.Subdivision.ParameterEdge => value.right.parameter)
      (retained.dyadicEdge_eq index)
  let fraction := segmentParameter edge.left.parameter edge.right.parameter time
  have actual : child.edge.point fraction = parent.edge.point
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request fraction) :=
    retained.originalPoint_eq (child := child) (retained.dyadicIndex index) rfl fraction
  have interpolates := segmentParameter_interpolates edge.left.parameter edge.right.parameter time
    ⟨(Data.Rat.Fraction.Order.Basic.min_le_left _ _).trans inside.1,
      inside.2.trans (Data.Rat.Fraction.Order.Basic.le_max_right _ _)⟩
  have parameter_eq : PreparedSheetContinuation.parameterAt child.edge.left child.edge.request fraction = time :=
    (PreparedSheetContinuation.parameterAt_eq_affine child.edge.left child.edge.request fraction).trans
      ((congrArg₂ (fun first last : Rational => first + fraction * (last - first)) left_eq right_eq).trans
        interpolates)
  exact actual.trans (congrArg parent.edge.point parameter_eq)

/-- An actual globally allocated prepared child reads the same raw dyadic physical point in every coefficient channel.

Only the supplied whole preparation and its exact original child occurrence
are used. Its patch and Targets remain its original owners; this projection
constructs no source, observation or polynomial model.
-/
theorem dyadicCellPoint_eq (index : Fin retained.acquired.mesh.edges.length)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (selected : child = retained.childAt (retained.dyadicIndex index))
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (prepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (channel : Fin 6) (time : Rational)
    (inside :
      (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter ≤ time ∧
        time ≤ (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter) :
    (prepared.preparation.cell.models.cell channel).point
      (segmentParameter (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
        (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter time) = parent.edge.point time := by
  let fraction := segmentParameter (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
    (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter time
  exact (prepared.preparation.cell.models.cell_point channel fraction).trans
    ((prepared.queryPoint_eq fraction).trans
      ((congrArg (fun child => child.edge.point fraction) selected).trans
        (retained.dyadicPoint_eq index time inside)))

variable {targetParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {targetCover : CoveredParents count targetParents} {targetFloor : Nat}
    {targetStart targetFinish : LiftedPoint 2} {targetPath : LiftedPath 2 targetStart targetFinish}
    {targetStage : Nat} {targetTargets : CellEndpoints.Targets targetPath targetStage}
    (prepared : PreparedParents targetCover targetFloor targetTargets)
    (positions : Fin retained.parents.covered.parents.length → Fin targetParents.length)

/-- Read actual globally allocated cells through the SAME original dyadic, parent and global occurrence indices. -/
@[expose] def dyadicCells (channel : Fin 6) (index : Fin retained.acquired.mesh.edges.length) :=
  (prepared.entry (positions (retained.dyadicIndex index))).preparation.cell.models.cell channel

/-- Dyadic indexing preserves the actual target-child integral sum in its original local-parent occurrence order.

Only the proven complete parent/Mesh length equality transports a bounded
index. The actual globally allocated preparation and original positions
remain identical; no source, cell, integral or occurrence factory runs.
-/
theorem dyadicCells_sum (channel : Fin 6) :
    FiniteSum.Fin.sumFin (fun index => (retained.dyadicCells prepared positions channel index).integralSample) =
      FiniteSum.Fin.sumFin (fun index => ((prepared.entry (positions index)).preparation.cell.models.cell
        channel).integralSample) := by
  have exact_cast {first last : Nat} (same : first = last) (values : Fin last → Canonical) :
      FiniteSum.Fin.sumFin (fun index : Fin first => values (Fin.cast same index)) =
        FiniteSum.Fin.sumFin values := by
    cases same
    rfl
  exact exact_cast
    (Parents.length_eq_edges basis parent.edge.sheet count retained.acquired retained.parents).symm
    (fun index => ((prepared.entry (positions index)).preparation.cell.models.cell channel).integralSample)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
