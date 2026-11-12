module
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathTrace

public import Purelib.Riemann.Readings.UniformPreparedRequests.Face
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

/-! # Actual parent primitive comparisons on a contained regular-face segment

The original request, cached point owner, Entry, domain and SegmentSplit
are the numerical parents. A complete indexed grid edge is not a premise.
The same operation serves the retained standard-period SheetEntry and an
actual paid regular-cell leaf, without replacing their geometric owners.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.Rat
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget (sumFin_le)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece SegmentSplit)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {target : Fraction.Rational}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face} {first last : Canonical}

/-- The original two retained inverse-model residuals pay the actual oriented piece displacement. -/
@[expose] def facePieceCharge (request : LocalRequest parent count target) {sheet : Fin 2}
    (domain : PeriodDomain models sheet) (bounds : FragmentBounds domain.patch differential)
    (piece : SegmentPiece domain.geometry first last) (index : Nat) : Fraction.Rational :=
  12 * (quarterRadius (domain.patch.transported.cell piece.column piece.row).model.bound (index + 2) +
    quarterRadius request.neighborhood.base.model.bound request.request.index) *
      (bounds.numerator piece.column piece.row * bounds.inverse) * normSq (piece.lastPoint - piece.firstPoint)

/-- The original initial comparison propagates through the retained analytic split without per-piece sign inputs. -/
theorem facePiece_nearest (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood first) (entry : Entry models first sample.owner)
    (domain : PeriodDomain models entry.sheet) (split : SegmentSplit domain.cuts first last)
    (fraction : Fraction.Rational) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointEq : parent.edge.point fraction = first)
    (firstInside : request.neighborhood.box.Contains first) (lastInside : request.neighborhood.box.Contains last)
    (piece : SegmentPiece domain.geometry first last) (member : piece ∈ split.pieces)
    (leftIndex rightIndex : Nat) :
    normSq (((domain.patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2)).value.eval
      piece.firstPoint - (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) ≤
    normSq (((domain.patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2)).value.eval
      piece.firstPoint + (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) :=
  SplitSigns.split_nearest domain.patch differential split request.neighborhood firstInside lastInside
    leftIndex rightIndex
    (fun column row inside => request.face_entry_nearest fraction fractionInside pointEq firstInside sample entry
      (domain.patch.transported.cell column row) inside leftIndex (rightIndex + 2)) piece member

/-- The actual original face-cell and request primitive increments satisfy the derived piece charge.

The same retained entry and split pay the sign. Original coefficient laws,
primitive polynomials, oriented endpoints and displacement remain unchanged.
-/
theorem facePiece_increment_le (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood first) (entry : Entry models first sample.owner)
    (domain : PeriodDomain models entry.sheet) (split : SegmentSplit domain.cuts first last)
    (fraction : Fraction.Rational) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointEq : parent.edge.point fraction = first)
    (firstInside : request.neighborhood.box.Contains first) (lastInside : request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential) (piece : SegmentPiece domain.geometry first last)
    (member : piece ∈ split.pieces) {index : Nat}
    (primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine index).transitions
      (domain.patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential)) :
    normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
        (request.request.model.primitive.value.eval piece.lastPoint -
          request.request.model.primitive.value.eval piece.firstPoint)) ≤
      request.facePieceCharge domain bounds piece index := by
  have ends := SplitSigns.piece_neighborhood piece firstInside lastInside
  let cell := domain.patch.transported.cell piece.column piece.row
  let left := cell.model.refine (index + 2)
  let right := request.neighborhood.base.refine request.request.index
  let edge : EdgeTransition left right piece.firstPoint piece.lastPoint :=
    ⟨piece.first_inside, piece.last_inside, request.neighborhood.box_refines.contains ends.1,
      request.neighborhood.box_refines.contains ends.2,
      ⟨left.value.eval piece.firstPoint, rfl, right.value.eval piece.firstPoint, rfl,
        ⟨false, right.value.eval piece.firstPoint, rfl, by
          have scalar := request.facePiece_nearest sample entry domain split fraction fractionInside pointEq
            firstInside lastInside piece member index request.request.index
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩⟩
  have estimate := EdgeTransition.primitive_increment_le (pairs := 0)
    edge (bounds.atCell piece.column piece.row)
    (primitives.dense piece.column piece.row) (request.request.model.primitive.onBox request.neighborhood.base.box)
    (domain.patch.primitive_coefficient_eq (pairs := 0)
      (entered := TracedPath.build
        (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
          (ambient := face.cell.box) face.cell.box.anchor)
        (.nil face.cell.box.anchor) _)
      face.cell.box.contains_anchor differential
      (BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt bank _
        (face.cell.anchor_mem face.member)).toLoop
      primitives piece.column piece.row)
    request.request.model.coefficient_eq
    (first := 1) (last := 0) ⟨of_decide_eq_true rfl, le_rfl⟩ ⟨le_rfl, of_decide_eq_true rfl⟩
  rewrite [PrimitiveOverlapBounds.weight_zero] at estimate
  have sign : edge.sign = 1 := rfl
  rewrite [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one,
    InverseModelEdgeTransition.line_zero] at estimate
  simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  have unit : ((1 : Fraction.Rational) - 0) ^ 2 = 1 := of_decide_eq_true rfl
  have scale := estimate.trans_eq (by
    change 12 * (left.bound + right.bound) *
      (bounds.numerator piece.column piece.row * bounds.inverse) *
      normSq (piece.lastPoint - piece.firstPoint) * (1 - 0) ^ 2 =
        request.facePieceCharge domain bounds piece index
    rewrite [unit, Fraction.Field.mul_one_direct]
    dsimp only [left, right, cell, facePieceCharge, SeededNeighborhood.refine]
    rewrite [Model.refine_bound, Model.refine_bound]
    rfl)
  simpa only [Primitives.dense, Primitives.value,
    Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive.onBox] using scale

/-- Sum the actual cellwise primitive discrepancies with the computed finite count and charge list.

Constants cancel inside each actual primitive increment. The left list is
still the ordered local-cell increment list, not an identified global
primitive or period. The original request's right list telescopes exactly.
-/
theorem faceSplit_increment_le (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood first) (entry : Entry models first sample.owner)
    (domain : PeriodDomain models entry.sheet) (split : SegmentSplit domain.cuts first last)
    (fraction : Fraction.Rational) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointEq : parent.edge.point fraction = first)
    (firstInside : request.neighborhood.box.Contains first) (lastInside : request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential) {index : Nat}
    (primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine index).transitions
      (domain.patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential)) :
    normSq (gaussianSum (split.pieces.map fun piece =>
      primitives.value piece.column piece.row piece.lastPoint -
        primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval last - request.request.model.primitive.value.eval first)) ≤
    (split.pieces.length : Fraction.Rational) *
      coordinateSum (split.pieces.map fun piece => request.facePieceCharge domain bounds piece index) := by
  let left := fun piece : SegmentPiece domain.geometry first last =>
    primitives.value piece.column piece.row piece.lastPoint - primitives.value piece.column piece.row piece.firstPoint
  let right := fun piece : SegmentPiece domain.geometry first last =>
    request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
      piece.firstPoint
  let error := fun piece => left piece - right piece
  let charge := fun piece : SegmentPiece domain.geometry first last =>
    request.facePieceCharge domain bounds piece index
  have pointwise : ∀ piece ∈ split.pieces, normSq (error piece) ≤ charge piece := by
    intro piece member
    exact request.facePiece_increment_le sample entry domain split fraction fractionInside pointEq firstInside
      lastInside bounds piece member primitives
  have normBound : gaussianNormSqSum (split.pieces.map error) ≤ coordinateSum (split.pieces.map charge) := by
    rewrite [← Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum_eq_coordinateSum_map]
    rewrite [Algebra.FiniteSum.Rational.Squares.coordinateSum_map_eq_sumFin,
      Algebra.FiniteSum.Rational.Squares.coordinateSum_map_eq_sumFin]
    exact sumFin_le (fun position => pointwise (split.pieces[position.val]'position.isLt)
      (List.getElem_mem position.isLt))
  have total := Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (split.pieces.map error)
  rewrite [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.List.Map.length_map] at total
  have paid := total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normBound
    (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := split.pieces.length) (Nat.zero_le _)))
  have telescope := split.telescope request.request.model.primitive.value.eval
  have difference := Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub split.pieces left right
  change gaussianSum (split.pieces.map error) = gaussianSum (split.pieces.map left) -
    gaussianSum (split.pieces.map right) at difference
  change gaussianSum (split.pieces.map right) = _ at telescope
  have sumEq := difference.trans (congrArg (gaussianSum (split.pieces.map left) - ·) telescope)
  exact (congrArg normSq sumEq).symm.trans_le paid

end Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

end
