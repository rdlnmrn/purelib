module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Dyadic
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Restriction
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Cells
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Literal target restriction geometry on one retained acquired parent

The same acquired mesh, centered child, global preparation and cached
restriction remain inputs. Their scalar endpoints, query parameter and
physical displacement readbacks are independent of the shifted parameter.
Applying the same operations to each actual acquisition therefore retains
both parameter owners in a common-dyadic Taylor comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Meshes

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (index : Fin retained.acquired.mesh.edges.length) (additional : Nat)
    (inner : Fin (dyadicEdges additional
      (retained.acquired.mesh.edges[index.val]'index.isLt).left
      (retained.acquired.mesh.edges[index.val]'index.isLt).right).length)

/-- The exact cached fine-local query maps to its SAME original coarse-local parameter.

No positivity of physical displacement or nonconstant parameter leg is
needed. The original normalization handles either orientation and stationary
scalar endpoints; actual dyadic progress is retained separately by the mesh.
-/
theorem dyadicRestriction_parameter (input : Rational) :
    Cell.Restriction.parameter
      (ParameterEdge.intervals (retained.acquired.mesh.edges[index.val]'index.isLt) additional inner).start
      (ParameterEdge.intervals (retained.acquired.mesh.edges[index.val]'index.isLt) additional inner).finish input =
      segmentParameter (retained.acquired.mesh.edges[index.val]'index.isLt).left.parameter
        (retained.acquired.mesh.edges[index.val]'index.isLt).right.parameter
        (Cell.Restriction.parameter
          ((dyadicEdges additional
            (retained.acquired.mesh.edges[index.val]'index.isLt).left
            (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt).left.parameter
          ((dyadicEdges additional
            (retained.acquired.mesh.edges[index.val]'index.isLt).left
            (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt).right.parameter input) :=
  segmentParameter_affine _ _ _ _ input

variable {child : CenteredEdge (Fibre.frameCurve target) basis}
    (selected : child = retained.childAt (retained.dyadicIndex index))
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (prepared : PreparedParent newPatch newCount newFloor newCovered newTargets) (channel : Fin 6)
    (restrictions : ParameterEdge.Restrictions (prepared.preparation.cell.models.cell channel)
      (retained.acquired.mesh.edges[index.val]'index.isLt) additional)

include selected in
/-- The SAME target restriction starts at its actual original fine edge's physical left endpoint. -/
theorem dyadicRestriction_start :
    (Cell.Restriction.model (prepared.preparation.cell.models.cell channel) (restrictions.cache inner)).start =
      parent.edge.point ((dyadicEdges additional
        (retained.acquired.mesh.edges[index.val]'index.isLt).left
        (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt).left.parameter := by
  let coarse := retained.acquired.mesh.edges[index.val]'index.isLt
  let fine := (dyadicEdges additional coarse.left coarse.right)[inner.val]'inner.isLt
  have coarseBounds := dyadicEdges_bounds retained.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
    (show (0 : Rational) ≤ 1 by decide +kernel) _ (List.getElem_mem index.isLt)
  have bounds := dyadicEdges_bounds additional coarse.left coarse.right coarseBounds.2.1 fine
    (List.getElem_mem inner.isLt)
  exact (Cell.Restriction.model_start _ (restrictions.cache inner)).trans
    (retained.dyadicCellPoint_eq index selected prepared channel fine.left.parameter
      ⟨bounds.1, bounds.2.1.trans bounds.2.2⟩)

include selected in
/-- The SAME target restriction finishes at that actual fine edge's physical right endpoint. -/
theorem dyadicRestriction_finish :
    (Cell.Restriction.model (prepared.preparation.cell.models.cell channel) (restrictions.cache inner)).finish =
      parent.edge.point ((dyadicEdges additional
        (retained.acquired.mesh.edges[index.val]'index.isLt).left
        (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt).right.parameter := by
  let coarse := retained.acquired.mesh.edges[index.val]'index.isLt
  let fine := (dyadicEdges additional coarse.left coarse.right)[inner.val]'inner.isLt
  have coarseBounds := dyadicEdges_bounds retained.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
    (show (0 : Rational) ≤ 1 by decide +kernel) _ (List.getElem_mem index.isLt)
  have bounds := dyadicEdges_bounds additional coarse.left coarse.right coarseBounds.2.1 fine
    (List.getElem_mem inner.isLt)
  exact (Cell.Restriction.model_finish _ (restrictions.cache inner)).trans
    (retained.dyadicCellPoint_eq index selected prepared channel fine.right.parameter
      ⟨bounds.1.trans bounds.2.1, bounds.2.2⟩)

variable {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2}
    {oldPath : LiftedPath 2 oldStart oldFinish} {oldStage : Nat}
    {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (old : PreparedParent patch count oldFloor covered oldTargets)

include selected old in
/-- The actual retained restriction has its original parent displacement scaled by its SAME oriented fine width.

This is a scalar Gaussian equality on the existing model. Neither the
polynomial, local allowance, stored Cached table nor either preparation
owner is changed, including constant physical parents and zero widths.
-/
theorem dyadicRestriction_displacement :
    let fine := (dyadicEdges additional
      (retained.acquired.mesh.edges[index.val]'index.isLt).left
      (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt
    (Cell.Restriction.model (prepared.preparation.cell.models.cell channel) (restrictions.cache inner)).displacement =
      (Cast.Path.ofCoordinate fine.right.parameter - Cast.Path.ofCoordinate fine.left.parameter) *
        ((finishPoint parent).coordinate - (startPoint parent).coordinate) := by
  let fine := (dyadicEdges additional
    (retained.acquired.mesh.edges[index.val]'index.isLt).left
    (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt
  let original := old.preparation.cell.models.cell channel
  have originalPoint (time : Rational) : original.point time = parent.edge.point time :=
    (old.preparation.cell.models.cell_point channel time).trans (old.queryPoint_eq time)
  have start := retained.dyadicRestriction_start index additional inner selected prepared channel restrictions
  have finish := retained.dyadicRestriction_finish index additional inner selected prepared channel restrictions
  have endpoints :
      (Cell.Restriction.model (prepared.preparation.cell.models.cell channel) (restrictions.cache inner)).displacement =
        original.point fine.right.parameter - original.point fine.left.parameter :=
    congrArg₂ (fun finish start : Canonical => finish - start)
      (finish.trans (originalPoint fine.right.parameter).symm)
      (start.trans (originalPoint fine.left.parameter).symm)
  have affine : original.point fine.right.parameter - original.point fine.left.parameter =
      (Cast.Path.ofCoordinate fine.right.parameter - Cast.Path.ofCoordinate fine.left.parameter) *
        original.displacement := by
    unfold CellModel.point
    ring1
  exact endpoints.trans (affine.trans
    (congrArg (fun displacement : Canonical =>
      (Cast.Path.ofCoordinate fine.right.parameter - Cast.Path.ofCoordinate fine.left.parameter) * displacement)
      (old.cell_displacement channel)))

include selected old in
/-- The same literal target restriction cost is fine width squared times the original physical parent cost. -/
theorem dyadicRestriction_normSq :
    let fine := (dyadicEdges additional
      (retained.acquired.mesh.edges[index.val]'index.isLt).left
      (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt
    Norm.Basic.normSq (Cell.Restriction.model
        (prepared.preparation.cell.models.cell channel) (restrictions.cache inner)).displacement =
      (fine.right.parameter - fine.left.parameter) ^ 2 * cost parent := by
  let fine := (dyadicEdges additional
    (retained.acquired.mesh.edges[index.val]'index.isLt).left
    (retained.acquired.mesh.edges[index.val]'index.isLt).right)[inner.val]'inner.isLt
  have scalar : Norm.Basic.normSq
      (Cast.Path.ofCoordinate fine.right.parameter - Cast.Path.ofCoordinate fine.left.parameter) =
      (fine.right.parameter - fine.left.parameter) ^ 2 := by
    simp only [Norm.Basic.normSq, Basic.sub_re, Basic.sub_im, Cast.ofCoordinate_re, Cast.ofCoordinate_im]
    ring1
  exact (congrArg Norm.Basic.normSq
    (retained.dyadicRestriction_displacement index additional inner selected prepared channel restrictions old)).trans
      ((Norm.Basic.normSq_mul _ _).trans
        (congrArg (fun width : Rational => width * cost parent) scalar))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
