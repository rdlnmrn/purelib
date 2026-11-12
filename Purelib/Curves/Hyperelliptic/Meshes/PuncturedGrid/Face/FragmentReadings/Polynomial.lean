module

public import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Tactic.Ring

/-! # Full-polynomial comparison on the original entered split pieces

The covered parent, its original patch and root lineage determine the sign.
Only the genuine supplied polynomial primitive changes with the numerator.
Both that primitive and the face primitives keep their actual constants.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.FragmentBounds

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedParentSplitting (PreparedSplitMesh)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.GridPrimitiveAccuracy (shared_local_increment_bound)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece SegmentSplit GridCuts)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint atPoint_coordinate)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {genus columns rows : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face} {sheet : Fin 2}
    {geometry : Geometry columns rows}
    {patch : RectangularPatch models.bounds (models.frame.owners sheet) geometry}
    {differential : Differential genus} {numerator : CoefficientPolynomial}
    (bounds : FragmentBounds patch differential (numeratorPolynomial := numerator))
    {parent : CenteredEdge curve differential} {count sourceIndex : Nat}
    (sourcePatch : PreparedPatch parent)
    (finishInside : (sourcePatch.neighborhood count).box.Contains (parent.edge.point 1))
    (sourcePrimitive : PrimitiveModel (sourcePatch.neighborhood count) sourceIndex numerator)

include finishInside in
/-- The SAME original covering patch contains every admitted rational point of its original parent. -/
private theorem patch_contains (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (sourcePatch.neighborhood count).box.Contains (parent.edge.point fraction) := by
  rewrite [Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent fraction, point_eq_line]
  exact Purelib.Geometry.Rational.Box.contains_line (sourcePatch.start_inside count) finishInside inside

include finishInside in
/-- A supplied full-numerator source primitive has the internally derived signed comparison on every actual piece. -/
theorem polynomial_increment_le (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    {index : Nat}
    (primitives : Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator)
    (reached : ParentReached face.cell.box (models.frame.owners sheet) parent) :
    normSq ((primitives.value piece.column piece.row piece.lastPoint -
        primitives.value piece.column piece.row piece.firstPoint) -
      (sourcePrimitive.primitive.value.eval piece.lastPoint - sourcePrimitive.primitive.value.eval piece.firstPoint)) ≤
      bounds.residualCharge piece
        (quarterRadius (sourcePatch.neighborhood count).base.model.bound sourceIndex) index := by
  have firstEq : piece.firstPoint = parent.edge.point piece.interval.lower :=
    piece.first_eq.trans (Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent _).symm
  have lastEq : piece.lastPoint = parent.edge.point piece.interval.upper :=
    piece.last_eq.trans (Riemann.Integration.PreparedParentSplitting.prepared_point_eq parent _).symm
  have firstInside : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  have lastInside : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  have original := TransportedFaceInverseModels.TransportedCell.prepared_subedge_primitive_increment_le
    (pairs := 0) (patch.transported.cell piece.column piece.row) differential parent
    piece.interval.lower piece.interval.upper firstInside (firstEq ▸ piece.first_inside) sourcePatch count index
    sourceIndex
    (by
      intro otherCount otherPatch otherInside otherSample roots otherIndex
      exact (patch.transported.cell piece.column piece.row).prepared_query_aligned
        (entered := Riemann.Paths.PreparedPathTrace.TracedPath.build
          (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
            (ambient := face.cell.box) face.cell.box.anchor) (.nil face.cell.box.anchor) _)
        face.cell.box.contains_anchor differential (BranchIsolation.degreePositive curve)
        (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
        parent reached piece.interval.lower firstInside (firstEq ▸ piece.first_inside) index
        otherPatch otherInside otherSample roots otherIndex)
    (primitives.dense piece.column piece.row)
    (patch.primitive_coefficient_eq (pairs := 0)
      (entered := Riemann.Paths.PreparedPathTrace.TracedPath.build
        (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
          (ambient := face.cell.box) face.cell.box.anchor) (.nil face.cell.box.anchor) _)
      face.cell.box.contains_anchor differential (BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
      primitives piece.column piece.row)
    sourcePrimitive (bounds.atCell piece.column piece.row) (lastEq ▸ piece.last_inside)
    (patch_contains sourcePatch finishInside piece.interval.lower firstInside)
    (patch_contains sourcePatch finishInside piece.interval.upper lastInside)
  rewrite [PrimitiveOverlapBounds.weight_zero, ← firstEq, ← lastEq] at original
  exact original.trans_eq (by
    rewrite [Model.refine_bound,
      Riemann.Normalization.OwnerSeededInverseRoot.SeededNeighborhood.refine, Model.refine_bound]
    rfl)

include finishInside in
/-- The actual shared mesh value and genuine polynomial source primitive obey the retained grid-plus-model charge. -/
theorem shared_polynomial_increment_le
    {globalBounds : PrimitiveOverlapBounds face.clearance numerator} {tolerance : Rational}
    (accuracy : Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds columns tolerance)
    {primitives : Primitives (Transitions.oriented (patch.sheets.refine accuracy.index).transitions
      (patch.sheets.refine accuracy.index).gauge) numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {cuts : GridCuts geometry} {parents : List (CenteredEdge curve differential)} {extra : List Canonical}
    {mesh : PreparedSplitMesh cuts parents extra}
    (readings : SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    (member : Riemann.Integration.PreparedParentSplitting.ParentSplits.Member split mesh.splits)
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)) (present : piece ∈ split.pieces)
    (reached : ParentReached face.cell.box (models.frame.owners sheet) parent) :
    normSq (((atPoint readings) piece.lastPoint - (atPoint readings) piece.firstPoint) -
      (sourcePrimitive.primitive.value.eval piece.lastPoint - sourcePrimitive.primitive.value.eval piece.firstPoint)) ≤
      32 * accuracy.globalBound + 2 * bounds.residualCharge piece
        (quarterRadius (sourcePatch.neighborhood count).base.model.bound sourceIndex) accuracy.index := by
  let contact := mesh.contact member piece present
  have ownership := shared_local_increment_bound accuracy readings patch.cell_refines piece.column piece.row
    contact.first contact.last (contact.first_eq.symm ▸ piece.first_inside)
    (contact.last_eq.symm ▸ piece.last_inside)
  have analytic := bounds.polynomial_increment_le sourcePatch finishInside sourcePrimitive piece primitives reached
  have actualFirst : readings.values contact.first = atPoint readings piece.firstPoint :=
    (atPoint_coordinate readings contact.first).symm.trans (congrArg (atPoint readings) contact.first_eq)
  have actualLast : readings.values contact.last = atPoint readings piece.lastPoint :=
    (atPoint_coordinate readings contact.last).symm.trans (congrArg (atPoint readings) contact.last_eq)
  rewrite [contact.first_eq, contact.last_eq, actualFirst, actualLast] at ownership
  let localValue := primitives.value piece.column piece.row piece.lastPoint -
    primitives.value piece.column piece.row piece.firstPoint
  let original := sourcePrimitive.primitive.value.eval piece.lastPoint -
    sourcePrimitive.primitive.value.eval piece.firstPoint
  have triangle := Norm.Bounds.normSq_add_le_two
    (((atPoint readings) piece.lastPoint - (atPoint readings) piece.firstPoint) - localValue)
    (localValue - original)
  have identity : (((atPoint readings) piece.lastPoint - (atPoint readings) piece.firstPoint) - localValue) +
      (localValue - original) =
        ((atPoint readings) piece.lastPoint - (atPoint readings) piece.firstPoint) - original := by
    ring1
  rewrite [identity] at triangle
  simp only [Norm.Basic.normSq_eq_canonical] at triangle ownership analytic
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact triangle.trans ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct ownership analytic)
    (by decide : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.FragmentBounds
