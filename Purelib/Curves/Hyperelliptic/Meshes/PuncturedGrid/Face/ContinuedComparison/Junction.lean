module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison.Entry
public import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot

/-! # Original cell transitions across a retained signed face junction

Two actual Point/Entry caches may belong to distinct old faces and
sheets. The literal retained OwnerJoin aligns their original cell models;
the resulting transition does not identify their primitive constants.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {start finish : Canonical} {leftCount rightCount : Nat}
variable {leftPatch : ContinuedNeighborhood curve.polynomial leftCount}
variable {rightPatch : ContinuedNeighborhood curve.polynomial rightCount}
variable (leftPoint : ContinuedNeighborhood.Point leftPatch start)
variable (rightPoint : ContinuedNeighborhood.Point rightPatch start)
variable (leftPointInside : leftPatch.box.Contains start)
variable (leftEntry : Entry leftModels start leftPoint.owner) (rightEntry : Entry rightModels start rightPoint.owner)
variable (joined : OwnerJoin leftPoint.owner rightPoint.owner)
variable (differential : Differential genus)
variable {leftBox rightBox : Box}
variable (leftCell : TransportedCell leftModels.bounds (leftModels.frame.owners leftEntry.sheet) leftBox)
variable (rightCell : TransportedCell rightModels.bounds (rightModels.frame.owners rightEntry.sheet) rightBox)
variable (leftStart : leftBox.Contains start) (rightStart : rightBox.Contains start)

include leftPointInside joined differential leftStart rightStart in
/-- Both actual old-face cell refinements have the same sign through the retained junction Point and literal join.

Each Entry aligns its own original transported cell. The actual join
changes the second original root name, and the existing overlap cocycle
composes through the SAME supplied Point neighborhood. No Point, row,
Entry, join or desired model-sign certificate is acquired or supplied.
-/
private theorem junction_nearest (leftIndex rightIndex : Nat) :
    Norm.Basic.normSq ((leftCell.model.refine (leftIndex + 2)).value.eval start -
      (rightCell.model.refine (rightIndex + 2)).value.eval start) ≤
    Norm.Basic.normSq ((leftCell.model.refine (leftIndex + 2)).value.eval start +
      (rightCell.model.refine (rightIndex + 2)).value.eval start) := by
  have roots : NamedEquivalent (ownerName leftPoint.owner) leftPoint.certificate.value.name :=
    NamedEquivalent.refl _
  have first := entry_aligned leftEntry leftCell differential leftStart leftIndex
    leftPatch leftPointInside leftPoint roots 0
  have last := entry_aligned rightEntry rightCell differential rightStart rightIndex
    leftPatch leftPointInside leftPoint (joined.equivalent.symm.trans roots) 0
  let reversed : SignAlignment ((rightCell.model.refine (rightIndex + 2)).value.eval start)
      ((leftPatch.base.refine 2).value.eval start) :=
    ⟨false, (leftPatch.base.refine 2).value.eval start, rfl, by
      simpa only [SeededNeighborhood.refine, Model.overlapRefine, Norm.Basic.normSq_eq_canonical] using last⟩
  have back : Norm.Basic.normSq ((leftPatch.base.refine 2).value.eval start -
      (rightCell.model.refine (rightIndex + 2)).value.eval start) ≤
      Norm.Basic.normSq ((leftPatch.base.refine 2).value.eval start +
        (rightCell.model.refine (rightIndex + 2)).value.eval start) := by
    have scalar := (InverseModelRefinementSigns.SignAlignment.reverse reversed).nearest
    dsimp only [InverseModelRefinementSigns.SignAlignment.reverse, reversed] at scalar
    simp only [Norm.Basic.normSq_eq_canonical] at scalar ⊢
    exact scalar
  have scalar := OverlapReady.nearest_trans (Model.overlapRefine leftCell.model leftIndex)
    (Model.overlapRefine leftPatch.base.model 0) (Model.overlapRefine rightCell.model rightIndex)
    leftStart (leftPatch.box_refines.contains leftPointInside) rightStart
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using first)
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using back)
  simpa only [SeededNeighborhood.refine, Model.overlapRefine] using scalar

/-- Construct the original unflipped transition at actual common endpoints from the retained signed junction.

The two model refinements and their start evaluations are new numerical
work. The original Point, Entry and join caches are not reacquired.
The four geometric endpoint incidences belong to these original cell
boxes; the end need not be an original full grid-edge vertex.
-/
def junctionTransition (leftIndex rightIndex : Nat) (leftFinish : leftBox.Contains finish)
    (rightFinish : rightBox.Contains finish) :
    EdgeTransition (leftCell.model.refine (leftIndex + 2)) (rightCell.model.refine (rightIndex + 2)) start finish :=
  let first := (leftCell.model.refine (leftIndex + 2)).value.eval start
  let last := (rightCell.model.refine (rightIndex + 2)).value.eval start
  ⟨leftStart, leftFinish, rightStart, rightFinish,
    ⟨first, rfl, last, rfl, ⟨false, last, rfl, by
        have nearest := junction_nearest leftPoint rightPoint leftPointInside leftEntry rightEntry joined
          differential leftCell rightCell leftStart rightStart leftIndex rightIndex
        simpa only [Norm.Basic.normSq_eq_canonical] using nearest⟩⟩⟩

/-- The actual transition derived from the literal junction selects the original unflipped sign. -/
theorem junctionTransition_sign (leftIndex rightIndex : Nat) (leftFinish : leftBox.Contains finish)
    (rightFinish : rightBox.Contains finish) :
    (junctionTransition leftPoint rightPoint leftPointInside leftEntry rightEntry joined differential
      leftCell rightCell leftStart rightStart leftIndex rightIndex leftFinish rightFinish).sign = 1 := by rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison

end
