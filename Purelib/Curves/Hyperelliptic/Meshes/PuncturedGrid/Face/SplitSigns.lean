module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Normalization.InverseModelBackwardSigns

/-!
# One request sign through all analytic cells of a face segment

The finite ordered split carries the initial sign across each actual piece.
At a junction, both transported cells belong to the same face occurrence.
Two proof-only Newton steps permit the cocycle comparison; backwards sign
preservation then reads the original requested index, including zero and one.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
public section
open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Geometry
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularSegmentSplitting
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {columns rows : Nat} {geometry : Geometry
    columns rows}
  {patch : RectangularPatch models.bounds (models.frame.owners sheet)
    geometry}
  {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {count : Nat} {neighborhood :
    ContinuedNeighborhood curve.polynomial count}

/-- Every emitted piece remains in the same original request neighborhood. -/
theorem piece_neighborhood (piece : RectangularSegmentSplitting.SegmentPiece geometry first last)
    (firstInside : neighborhood.box.Contains first) (lastInside : neighborhood.box.Contains last) :
    neighborhood.box.Contains piece.firstPoint ∧ neighborhood.box.Contains piece.lastPoint := by
  rw [piece.first_eq, piece.last_eq, PreparedSegmentCuts.point_eq_line,
    PreparedSegmentCuts.point_eq_line]
  exact ⟨Rational.Box.contains_line firstInside lastInside
      ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩,
    Rational.Box.contains_line firstInside lastInside
      ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩⟩

open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
/-- Every original containing face cell has the same nearest sign as the retained request neighborhood after the
two-step cocycle floor.

Every retained grid cell containing the point compares its refined inverse-root
model with the supplied neighborhood at the two displayed reading stages. -/
private def NearestAt (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count) (leftIndex rightIndex : Nat)
      (point : InverseRootPolynomial.Gaussian) : Prop :=
  ∀ column row, (geometry.box column row).Contains point →
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine (leftIndex +
      2)).value.eval point -
      (neighborhood.base.refine (rightIndex + 2)).value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine (leftIndex +
      2)).value.eval point +
      (neighborhood.base.refine (rightIndex + 2)).value.eval point)

/-- Transport the original initial nearest-sign comparison along the retained ordered finite segment-piece walk.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
private theorem nearest_walk (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood
      curve.polynomial count)
    (firstInside : neighborhood.box.Contains first) (lastInside : neighborhood.box.Contains last)
    (leftIndex rightIndex : Nat) {available : List PreparedAxisPartitions.Interval} :
    ∀ (pieces : List (RectangularSegmentSplitting.SegmentPiece geometry first last)) {lower upper :
      InverseRootPolynomial.Coordinate}
      (walk : AxisWalks.IncreasingWalk available lower upper)
      (_ordered : pieces.map SegmentPiece.interval = walk.edges)
      (_initial : NearestAt patch neighborhood leftIndex
        rightIndex (point first last lower)),
      ∀ piece ∈ pieces,
        Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell piece.column piece.row).model.refine
          (leftIndex + 2)).value.eval piece.firstPoint -
          (neighborhood.base.refine (rightIndex + 2)).value.eval piece.firstPoint) ≤
        Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell piece.column piece.row).model.refine
          (leftIndex + 2)).value.eval piece.firstPoint +
          (neighborhood.base.refine (rightIndex + 2)).value.eval piece.firstPoint)
  | [], _, _, _, _, _, _, member => (List.not_mem_nil member).elim
  | head :: tail, _, _, .nil _, ordered, _, _, _ => by cases ordered
  | head :: tail, _, _, .cons interval _ walk, ordered, initial, piece, member => by
      have equations := List.cons.inj ordered
      have firstEq : head.firstPoint = point first last interval.lower := by rw [head.first_eq, equations.1]
      have lastEq : head.lastPoint = point first last interval.upper := by rw [head.last_eq, equations.1]
      have atFirst := initial head.column head.row (firstEq ▸ head.first_inside)
      dsimp only [id_eq] at atFirst
      rw [← firstEq] at atFirst
      rcases Membership.mem_cons.mp member with rfl | member
      · exact atFirst
      · have contained := piece_neighborhood head firstInside
          lastInside
        have atLast := Model.nearest_finish ((patch.transported.cell head.column head.row).model.refine (leftIndex + 2))
          (neighborhood.base.refine (rightIndex + 2)) head.first_inside head.last_inside
          (neighborhood.box_refines.contains contained.1) (neighborhood.box_refines.contains contained.2) atFirst
        have next : NearestAt patch neighborhood leftIndex
          rightIndex (point first last interval.upper) := by
          rw [← lastEq]
          intro column row inside
          exact ((Model.overlapRefine (patch.transported.cell column row).model) leftIndex).nearest_trans
            ((Model.overlapRefine (patch.transported.cell head.column head.row).model) leftIndex)
            ((Model.overlapRefine neighborhood.base.model) rightIndex) inside head.last_inside
            (neighborhood.box_refines.contains contained.2)
            (SheetGauge.cells_nearest _ _ differential inside head.last_inside leftIndex leftIndex) atLast
        exact nearest_walk patch differential
          neighborhood firstInside lastInside leftIndex rightIndex tail walk equations.2 next piece member

/-- All containing cells of the retained split use the original sign. Only the initial endpoint alignment is required;
no per-piece sign or root agreement is supplied. -/
theorem split_nearest (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) {cuts : RectangularSegmentSplitting.GridCuts geometry}
      (split : RectangularSegmentSplitting.SegmentSplit cuts first last)
    (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count)
    (firstInside : neighborhood.box.Contains first) (lastInside : neighborhood.box.Contains last)
    (leftIndex rightIndex : Nat)
    (initial : ∀ column row, (geometry.box column row).Contains first →
      Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine (leftIndex +
        2)).value.eval first -
        (neighborhood.base.refine (rightIndex + 2)).value.eval first) ≤
      Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine (leftIndex +
        2)).value.eval first +
        (neighborhood.base.refine (rightIndex + 2)).value.eval first))
    (piece : RectangularSegmentSplitting.SegmentPiece geometry first last) (member : piece ∈ split.pieces) :
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell piece.column piece.row).model.refine (leftIndex +
      2)).value.eval piece.firstPoint -
      (neighborhood.base.refine rightIndex).value.eval piece.firstPoint) ≤
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell piece.column piece.row).model.refine (leftIndex +
      2)).value.eval piece.firstPoint +
      (neighborhood.base.refine rightIndex).value.eval piece.firstPoint) := by
  have started : NearestAt patch neighborhood leftIndex
    rightIndex (point first last 0) := by
    rw [PreparedSegmentCuts.point_zero]
    exact initial
  have later := nearest_walk patch differential neighborhood
    firstInside lastInside leftIndex rightIndex split.pieces
    split.partition.walk (split.intervals_eq.trans split.partition.walk_edges.symm) started piece member
  have nearest : Data.Gaussian.Basic.Canonical.normSq
      (((patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint -
        (neighborhood.base.refine rightIndex).step.step.value.eval piece.firstPoint) ≤
      Data.Gaussian.Basic.Canonical.normSq
      (((patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint +
        (neighborhood.base.refine rightIndex).step.step.value.eval piece.firstPoint) := by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine,
      Model.refine] using later
  have scalar := OverlapReady.nearest_before_two_steps
    ((Model.overlapRefine (patch.transported.cell piece.column piece.row).model) leftIndex)
    (neighborhood.base.refine rightIndex) piece.first_inside
    (neighborhood.box_refines.contains (piece_neighborhood
      piece firstInside lastInside).1) nearest
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, Model.overlapRefine] using scalar

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
