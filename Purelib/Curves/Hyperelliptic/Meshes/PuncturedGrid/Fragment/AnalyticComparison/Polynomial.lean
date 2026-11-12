module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Paths.RectangularSegmentSplitting.Comparison
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring

/-! # Actual polynomial-numerator primitives across one retained fragment

The original sample/Entry split derives the sign at independent model
stages. Both actual primitive banks and their constants remain unchanged.
The source inverse is supplied as its retained cache; no source polynomial,
Point, Query or numerical primitive bank is prepared by the comparison.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.GridPrimitiveAccuracy (shared_local_increment_bound)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry (allCells)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint atPoint_coordinate)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target : Rational} {request : LocalRequest parent count target}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable (assigned : SheetEntry fragment domains request)
variable {numerator : CoefficientPolynomial} {sourceIndex faceIndex : Nat}
variable (sourceInverse : Model curve.polynomial request.neighborhood.base.box)
variable (sourceFactory : sourceInverse = request.neighborhood.base.refine sourceIndex)
variable (primitive : PrimitiveModel request.neighborhood sourceIndex numerator)
variable (primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine faceIndex).transitions
  (assigned.domain.patch.sheets.refine faceIndex).gauge) numerator)

/-- The exact scalar analytic charge uses both actual model bounds and the full numerator ceiling. -/
@[expose] def numeratorPieceCharge
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (bounds : PrimitiveOverlapBounds
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator) : Rational :=
  12 * (left.bound + sourceInverse.bound) * (bounds.numeratorUpper * bounds.inverseUpper) *
    normSq (piece.lastPoint - piece.firstPoint)

/-- Actual supplied primitive coefficients and the derived same-sign transition bound oriented partial increments. -/
private theorem numerator_partial_increment_le
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (leftFactory : left = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2))
    (bounds : PrimitiveOverlapBounds
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator)
    (transition : {value : EdgeTransition left sourceInverse piece.firstPoint piece.lastPoint //
      value = pieceTransitionOn assigned piece member faceIndex sourceIndex
        left leftFactory sourceInverse sourceFactory})
    {first last : Rational} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((primitives.value piece.column piece.row
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) first) -
      primitives.value piece.column piece.row
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) last)) -
      (primitive.primitive.value.eval
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) first) -
      primitive.primitive.value.eval
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) last))) ≤
      numeratorPieceCharge assigned sourceInverse piece left bounds * (first - last) ^ 2 := by
  have leftCoefficient : ∀ point, (primitives.cells piece.column piece.row).coefficient.eval point =
      numerator.eval point * left.value.eval point := by
    intro point
    exact (assigned.domain.patch.primitive_coefficient_eq (pairs := 0)
      (entered := Riemann.Paths.PreparedPathTrace.TracedPath.build
        (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
          (ambient := fragment.face.located.face.cell.box) fragment.face.located.face.cell.box.anchor)
        (.nil fragment.face.located.face.cell.box.anchor) _)
      fragment.face.located.face.cell.box.contains_anchor source (BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
        (fragment.face.located.face.cell.anchor_mem fragment.face.located.face.member)).toLoop
      primitives piece.column piece.row point).trans
      (congrArg (fun value : Canonical => numerator.eval point * value)
        (congrArg (fun model => model.value.eval point) leftFactory.symm))
  have rightCoefficient : ∀ point, primitive.coefficient.eval point =
      numerator.eval point * sourceInverse.value.eval point := by
    intro point
    exact (primitive.coefficient_eq point).trans
      (congrArg (fun value : Canonical => numerator.eval point * value)
        (congrArg (fun model => model.value.eval point) sourceFactory.symm))
  have original := PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le (pairs := 0) transition.val bounds
    (primitives.dense piece.column piece.row) (primitive.primitive.onBox request.neighborhood.base.box)
    leftCoefficient rightCoefficient firstInside lastInside
  have sign : transition.val.sign = 1 :=
    (congrArg EdgeTransition.sign transition.property).trans
      (pieceTransitionOn_sign assigned piece member faceIndex sourceIndex
        left leftFactory sourceInverse sourceFactory)
  rewrite [sign, Data.Gaussian.Basic.one_mul] at original
  simpa only [← Norm.Basic.normSq_eq_canonical, Primitives.dense, Primitives.value,
    DensePrimitive.onBox, PrimitiveOverlapBounds.weight_zero, numeratorPieceCharge] using original

/-- The actual source primitive, old target primitive and retained transition pay the exact full-piece charge. -/
private theorem numerator_increment_le
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (leftFactory : left = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2))
    (bounds : PrimitiveOverlapBounds
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator)
    (transition : {value : EdgeTransition left sourceInverse piece.firstPoint piece.lastPoint //
      value = pieceTransitionOn assigned piece member faceIndex sourceIndex
        left leftFactory sourceInverse sourceFactory}) :
    normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (primitive.primitive.value.eval piece.lastPoint - primitive.primitive.value.eval piece.firstPoint)) ≤
      numeratorPieceCharge assigned sourceInverse piece left bounds := by
  have original := numerator_partial_increment_le assigned sourceInverse sourceFactory primitive primitives
    piece member left leftFactory bounds transition
    (first := 1) (last := 0) ⟨of_decide_eq_true rfl, Basic.le_refl 1⟩
      ⟨Basic.le_refl 0, of_decide_eq_true rfl⟩
  rewrite [line_one, line_zero] at original
  have unit : ((1 : Rational) - 0) ^ 2 = 1 := of_decide_eq_true rfl
  exact original.trans_eq (by rewrite [unit, Data.Rat.Fraction.Field.mul_one_direct]; rfl)

/-- One actual target-cell model, full numerator bounds, genuine signed transition and exact analytic charge.

The source inverse and primitive are the supplied caches. The target inverse
is computed once for this new comparison at its actual face stage, then
retained with its whole factory. It is not a rebuilt target primitive bank.
-/
abbrev NumeratorPieceComparison
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) :=
  (left : {value : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row) //
    value = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2)}) ×
  (bounds : {value : PrimitiveOverlapBounds
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator // value = PrimitiveOverlapBounds.build
        (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
        numerator}) ×
  (_transition : {value : EdgeTransition left.val sourceInverse piece.firstPoint piece.lastPoint //
    value = pieceTransitionOn assigned piece member faceIndex sourceIndex
      left.val left.property sourceInverse sourceFactory}) ×
  (charge : {value : Rational // value = numeratorPieceCharge assigned sourceInverse piece left.val bounds.val}) ×
  {_value : Unit // normSq ((primitives.value piece.column piece.row piece.lastPoint -
    primitives.value piece.column piece.row piece.firstPoint) -
    (primitive.primitive.value.eval piece.lastPoint - primitive.primitive.value.eval piece.firstPoint)) ≤ charge.val}

/-- Bind each actual given-model transition and full-numerator bound once before its exact increment certificate. -/
def compareNumeratorPiece
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) :
    NumeratorPieceComparison assigned sourceInverse sourceFactory primitive primitives piece member :=
  let left : {value : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row) //
      value = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2)} :=
    ⟨(assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2), rfl⟩
  let bounds : {value : PrimitiveOverlapBounds
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator // value = PrimitiveOverlapBounds.build
        (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
        numerator} :=
    ⟨PrimitiveOverlapBounds.build
      (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
      numerator, rfl⟩
  let transition : {value : EdgeTransition left.val sourceInverse piece.firstPoint piece.lastPoint //
      value = pieceTransitionOn assigned piece member faceIndex sourceIndex
        left.val left.property sourceInverse sourceFactory} :=
    ⟨pieceTransitionOn assigned piece member faceIndex sourceIndex
      left.val left.property sourceInverse sourceFactory, rfl⟩
  let charge : {value : Rational // value = numeratorPieceCharge assigned sourceInverse piece left.val bounds.val} :=
    ⟨numeratorPieceCharge assigned sourceInverse piece left.val bounds.val, rfl⟩
  ⟨left, bounds, transition, charge,
    ⟨(), numerator_increment_le assigned sourceInverse sourceFactory primitive primitives
      piece member left.val left.property bounds.val transition⟩⟩

namespace NumeratorPieceComparison

variable {assigned sourceInverse sourceFactory primitive primitives}
variable {piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last}
variable {member : piece ∈ assigned.split.pieces}
variable (kept : NumeratorPieceComparison assigned sourceInverse sourceFactory primitive primitives piece member)

/-- Read the same retained target inverse polynomial used by this actual comparison. -/
@[expose] def left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row) := kept.1.val

/-- Read the full-numerator bound at this actual cell and unchanged face clearance. -/
@[expose] def bounds : PrimitiveOverlapBounds
    (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
    numerator := kept.2.1.val

/-- Read the genuine signed transition between the same target and supplied source model. -/
@[expose] def transition : EdgeTransition kept.left sourceInverse piece.firstPoint piece.lastPoint := kept.2.2.1.val

/-- Read the actual once computed analytic charge. -/
@[expose] def charge : Rational := kept.2.2.2.1.val

/-- The target inverse cache is its original actual refinement at the retained face stage. -/
theorem left_eq : kept.left =
    (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (faceIndex + 2) := kept.1.property

/-- The full bounds cache is exactly the original constructor on the actual cell and numerator. -/
theorem bounds_eq : kept.bounds = PrimitiveOverlapBounds.build
    (fragment.face.located.face.clearance.restrict (assigned.domain.patch.cell_refines piece.column piece.row))
    numerator := kept.2.1.property

/-- The complete signed transition retains its actual one given-model factory. -/
theorem transition_eq : kept.transition = pieceTransitionOn assigned piece member faceIndex sourceIndex
    kept.left kept.left_eq sourceInverse sourceFactory := kept.2.2.1.property

/-- The complete charge retains both original model bounds and the full numerator factors. -/
theorem charge_eq : kept.charge = numeratorPieceCharge assigned sourceInverse piece kept.left kept.bounds :=
  kept.2.2.2.1.property

/-- Both original primitive increments obey their internally derived actual analytic charge. -/
theorem accurate : normSq ((primitives.value piece.column piece.row piece.lastPoint -
    primitives.value piece.column piece.row piece.firstPoint) -
    (primitive.primitive.value.eval piece.lastPoint - primitive.primitive.value.eval piece.firstPoint)) ≤ kept.charge :=
  kept.2.2.2.2.property

end NumeratorPieceComparison

namespace NumeratorFragmentComparison

variable {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance numerator}
variable {tolerance : Rational} (accuracy : GridPrimitiveAccuracy globalBounds assigned.domain.steps tolerance)
variable (targetPrimitives : Primitives
  (Transitions.oriented (assigned.domain.patch.sheets.refine accuracy.index).transitions
    (assigned.domain.patch.sheets.refine accuracy.index).gauge) numerator)
variable {anchors : PrimitiveAnchors targetPrimitives} {offsets : Offsets anchors.edges} {points : List Canonical}
variable (mesh : CommonMesh assigned.domain.geometry (allCells assigned.domain.geometry) points)
variable (included : ∀ point ∈ assigned.split.points, point ∈ points)
variable (readings : SharedPrimitiveValues anchors offsets mesh.surface)

/-- Actual indexed per-piece comparisons, with every original member and occurrence retained separately. -/
abbrev Pieces := DependentProduct assigned.split.pieces fun position =>
  NumeratorPieceComparison (faceIndex := accuracy.index) assigned sourceInverse sourceFactory primitive
    targetPrimitives (assigned.split.pieces[position.val]'position.isLt) (List.getElem_mem position.isLt)

/-- Materialize each genuine per-piece comparison once, consuming the SAME supplied source inverse and primitive. -/
def comparePieces : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives :=
  DependentProduct.ofFn assigned.split.pieces fun position =>
    compareNumeratorPiece (faceIndex := accuracy.index) assigned sourceInverse sourceFactory primitive targetPrimitives
      (assigned.split.pieces[position.val]'position.isLt) (List.getElem_mem position.isLt)

/-- Read the retained comparison at its exact original bounded occurrence without running its producer. -/
@[expose] def pieceAt (bank : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives)
    (position : Fin assigned.split.pieces.length) :
    NumeratorPieceComparison (faceIndex := accuracy.index) assigned sourceInverse sourceFactory primitive
      targetPrimitives (assigned.split.pieces[position.val]'position.isLt) (List.getElem_mem position.isLt) :=
  DependentProduct.get assigned.split.pieces bank position

include included in
/-- One given shared-mesh increment pays its actual selected-cell ownership and the retained analytic piece charge. -/
private theorem shared_piece_le
    (bank : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives)
    (position : Fin assigned.split.pieces.length) :
    normSq ((atPoint readings (assigned.split.pieces[position.val]'position.isLt).lastPoint -
      atPoint readings (assigned.split.pieces[position.val]'position.isLt).firstPoint) -
      (primitive.primitive.value.eval (assigned.split.pieces[position.val]'position.isLt).lastPoint -
        primitive.primitive.value.eval (assigned.split.pieces[position.val]'position.isLt).firstPoint)) ≤
      32 * accuracy.globalBound +
        2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives bank position).charge := by
  let piece := assigned.split.pieces[position.val]'position.isLt
  have member : piece ∈ assigned.split.pieces := List.getElem_mem position.isLt
  have ends := assigned.split.points_mem member
  let firstVertex := mesh.lookup piece.firstPoint (included _ ends.1) piece.column piece.row
    (allCells_mem assigned.domain.geometry _ _) piece.first_inside
  let lastVertex := mesh.lookup piece.lastPoint (included _ ends.2) piece.column piece.row
    (allCells_mem assigned.domain.geometry _ _) piece.last_inside
  have firstEq : mesh.surface.mesh.coordinate firstVertex.index = piece.firstPoint := firstVertex.coordinate_eq
  have lastEq : mesh.surface.mesh.coordinate lastVertex.index = piece.lastPoint := lastVertex.coordinate_eq
  have firstInside : (assigned.domain.geometry.box piece.column piece.row).Contains
      (mesh.surface.mesh.coordinate firstVertex.index) :=
    Eq.mpr (congrArg (assigned.domain.geometry.box piece.column piece.row).Contains firstEq) piece.first_inside
  have lastInside : (assigned.domain.geometry.box piece.column piece.row).Contains
      (mesh.surface.mesh.coordinate lastVertex.index) :=
    Eq.mpr (congrArg (assigned.domain.geometry.box piece.column piece.row).Contains lastEq) piece.last_inside
  have ownership := shared_local_increment_bound accuracy readings assigned.domain.patch.cell_refines
    piece.column piece.row firstVertex.index lastVertex.index
    firstInside lastInside
  rewrite [← atPoint_coordinate readings firstVertex.index, ← atPoint_coordinate readings lastVertex.index,
    firstEq, lastEq, ← Norm.Basic.normSq_eq_canonical] at ownership
  have analytic := (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives bank position).accurate
  have split := Norm.Bounds.normSq_sub_le_via
    (atPoint readings piece.lastPoint - atPoint readings piece.firstPoint)
    (targetPrimitives.value piece.column piece.row piece.lastPoint -
      targetPrimitives.value piece.column piece.row piece.firstPoint)
    (primitive.primitive.value.eval piece.lastPoint - primitive.primitive.value.eval piece.firstPoint)
  exact (split.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct ownership analytic) (by decide +kernel))).trans_eq (by ring1)

include included in
/-- The original whole fragment pays the literal indexed piece count and every actual retained local charge. -/
private theorem shared_increment_le
    (bank : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives) :
    normSq ((atPoint readings fragment.located.last - atPoint readings fragment.located.first) -
      (primitive.primitive.value.eval fragment.located.last - primitive.primitive.value.eval fragment.located.first)) ≤
      (assigned.split.count : Rational) * sumFin (fun position : Fin assigned.split.pieces.length =>
        32 * accuracy.globalBound +
          2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives bank position).charge) :=
  assigned.split.increment_difference_le (atPoint readings) primitive.primitive.value.eval
    (fun position : Fin assigned.split.pieces.length => 32 * accuracy.globalBound +
      2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives bank position).charge)
    (fun position => shared_piece_le assigned sourceInverse sourceFactory primitive accuracy targetPrimitives
      mesh included readings bank position)

/-- The complete given geometric/root, source and numerical inputs, without copying fields into another bank. -/
abbrev Originals :=
  {value : LocalRequest parent count target × SheetEntry fragment domains request ×
      {model : Model curve.polynomial request.neighborhood.base.box //
        model = request.neighborhood.base.refine sourceIndex} ×
      PrimitiveModel request.neighborhood sourceIndex numerator ×
      GridPrimitiveAccuracy globalBounds assigned.domain.steps tolerance ×
      Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine accuracy.index).transitions
        (assigned.domain.patch.sheets.refine accuracy.index).gauge) numerator ×
      PrimitiveAnchors targetPrimitives × Offsets anchors.edges ×
      CommonMesh assigned.domain.geometry (allCells assigned.domain.geometry) points ×
      SharedPrimitiveValues anchors offsets mesh.surface ×
      {_value : Unit // ∀ point ∈ assigned.split.points, point ∈ points} //
    value = (request, assigned, ⟨sourceInverse, sourceFactory⟩, primitive, accuracy,
      targetPrimitives, anchors, offsets, mesh, readings, ⟨(), included⟩)}

/-- One full-numerator fragment comparison on the SAME given primitive and shared-mesh caches.

Both source and target constants remain. Every real per-piece transition,
bound, source model index and mesh index is retained, with the original
fragment's actual count and exact finite error allowance.
-/
abbrev Cache :=
  Originals assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings ×
  (Σ pieces : {value : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives //
      value = comparePieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives},
  Σ value : {value : Canonical //
      value = atPoint readings fragment.located.last - atPoint readings fragment.located.first},
  Σ bound : {value : Rational // value = (assigned.split.count : Rational) *
      sumFin (fun position : Fin assigned.split.pieces.length => 32 * accuracy.globalBound +
        2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives pieces.val position).charge)},
  {_value : Unit // normSq (value.val -
    (primitive.primitive.value.eval fragment.located.last - primitive.primitive.value.eval fragment.located.first)) ≤
      bound.val})

include included in
/-- Compare the genuine supplied numerator primitives on every original piece, then fold only their retained charges. -/
def build : Cache assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings :=
  let originals : Originals assigned sourceInverse sourceFactory primitive accuracy targetPrimitives
      mesh included readings :=
    ⟨(request, assigned, ⟨sourceInverse, sourceFactory⟩, primitive, accuracy,
      targetPrimitives, anchors, offsets, mesh, readings, ⟨(), included⟩), rfl⟩
  let pieces : {value : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives //
      value = comparePieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives} :=
    ⟨comparePieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives, rfl⟩
  let value : {value : Canonical //
      value = atPoint readings fragment.located.last - atPoint readings fragment.located.first} :=
    ⟨atPoint readings fragment.located.last - atPoint readings fragment.located.first, rfl⟩
  let bound : {value : Rational // value = (assigned.split.count : Rational) *
      sumFin (fun position : Fin assigned.split.pieces.length => 32 * accuracy.globalBound +
        2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives pieces.val position).charge)} :=
    ⟨(assigned.split.count : Rational) *
      sumFin (fun position : Fin assigned.split.pieces.length => 32 * accuracy.globalBound +
        2 * (pieceAt assigned sourceInverse sourceFactory primitive
          accuracy targetPrimitives pieces.val position).charge),
      rfl⟩
  ⟨originals, pieces, value, bound,
    ⟨(), shared_increment_le assigned sourceInverse sourceFactory primitive accuracy targetPrimitives
      mesh included readings pieces.val⟩⟩

namespace Cache

variable {assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings}
variable (kept : Cache assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings)

/-- Read each same retained piece comparison in the actual original indexed product. -/
@[expose] def pieces : Pieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives := kept.2.1.val

/-- Read the actual shared endpoint increment without evaluating the original source primitive polynomial. -/
@[expose] def value : Canonical := kept.2.2.1.val

/-- Read the once computed indexed piece allowance. -/
@[expose] def bound : Rational := kept.2.2.2.1.val

/-- Every whole geometric/root and numerical input remains the exact original given object. -/
theorem originals_eq : kept.1.val = (request, assigned, ⟨sourceInverse, sourceFactory⟩, primitive,
    accuracy, targetPrimitives, anchors, offsets, mesh, readings, ⟨(), included⟩) := kept.1.property

/-- The whole comparison product retains its actual single materialization factory. -/
theorem pieces_eq : kept.pieces =
    comparePieces assigned sourceInverse sourceFactory primitive accuracy targetPrimitives := kept.2.1.property

/-- The endpoint value reads exactly the same original shared cache and keeps its separate literal endpoint roles. -/
theorem value_eq : kept.value = atPoint readings fragment.located.last - atPoint readings fragment.located.first :=
  kept.2.2.1.property

/-- The complete bound keeps the actual piece count and every actual indexed ownership and analytic charge. -/
theorem bound_eq : kept.bound = (assigned.split.count : Rational) *
    sumFin (fun position : Fin assigned.split.pieces.length => 32 * accuracy.globalBound +
      2 * (pieceAt assigned sourceInverse sourceFactory primitive
        accuracy targetPrimitives kept.pieces position).charge) :=
  kept.2.2.2.1.property

/-- The actual full-numerator fragment source increment and shared endpoint increment obey the derived finite bound. -/
theorem accurate : normSq (kept.value -
    (primitive.primitive.value.eval fragment.located.last - primitive.primitive.value.eval fragment.located.first)) ≤
      kept.bound := kept.2.2.2.2.property

/-- A bound check retains the same actual cache and either its strict payment or its computed-bound insufficiency. -/
abbrev Payment (requested : Rational) :=
  {value : Cache assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings ×
      Rational // value = (kept, requested)} ×
  ({_value : Unit // kept.bound < requested ∧ normSq (kept.value -
      (primitive.primitive.value.eval fragment.located.last -
        primitive.primitive.value.eval fragment.located.first)) < requested} ⊕
    {_value : Unit // ¬kept.bound < requested})

/-- Check the retained actual bound without altering either source-model stage or face-mesh index.

An unpaid result certifies only failure of this strict bound test. It does
not give a lower bound on the actual error or prove impossibility.
-/
def pay (requested : Rational) : kept.Payment requested :=
  if admitted : kept.bound < requested then
    ⟨⟨(kept, requested), rfl⟩, Sum.inl ⟨(), admitted, kept.accurate.trans_lt admitted⟩⟩
  else ⟨⟨(kept, requested), rfl⟩, Sum.inr ⟨(), admitted⟩⟩

end Cache
end NumeratorFragmentComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
