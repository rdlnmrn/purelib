module
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.TransportNegation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-!
# Opposite-sheet models at arbitrary common face points

A proof-only opposite cell at the first cell's box carries the anchor sign
to the requested point. The existing same-sheet comparison identifies it
with the second retained cell. The conclusion reads only the original two
polynomial caches, even when their boxes and refinement indices differ.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CellNegation
public section
open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Polynomial.Geometry.ClearPath
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlap
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial
open Purelib.Riemann.Normalization.TransportedFaceInverseModels
open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
open Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge (cells_nearest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.TransportNegation (compareOppositeCellTrace)
open Purelib.Data.Gaussian.Basic.Canonical

/-- A retained flipped overlap sample proves that the original model values are nearest with opposite signs.

The retained sign bit selects the same negated model value. Scalar transports compare the original cached values and
their two quadrances without changing the model or its overlap witness. -/
private theorem opposite_of_flipped {polynomial : InverseRootPolynomial.Polynomial} {leftBox rightBox :
  InverseRootPolynomial.Box}
    {left : InverseRootPolynomial.Model polynomial leftBox} {right : InverseRootPolynomial.Model polynomial rightBox}
      {point : InverseRootPolynomial.Gaussian}
    (sample : InverseModelOverlap.OverlapSample left right point) (flipped : sample.alignment.flip = true) :
    Data.Gaussian.Norm.Basic.normSq (left.value.eval point + right.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (left.value.eval point - right.value.eval point) := by
  have nearest := sample.alignment.nearest
  have difference : sample.leftValue - -sample.rightValue = sample.leftValue + sample.rightValue := by ring1
  rewrite [sample.alignment.value_eq, flipped, if_pos (Eq.refl true), difference,
    ← Data.Gaussian.Basic.Canonical.sub_eq_add_neg,
    sample.leftValue_eq, sample.rightValue_eq] at nearest
  rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact nearest

/-- An original negative-sign model comparison at the segment start holds at every common contained endpoint.

The retained sign bit selects the same negated model value. Scalar transports compare the original cached values and
their two quadrances without changing the model or its overlap witness. -/
private theorem opposite_finish {polynomial : InverseRootPolynomial.Polynomial} {leftBox rightBox :
  InverseRootPolynomial.Box}
    (left : InverseRootPolynomial.Model polynomial leftBox) (right : InverseRootPolynomial.Model polynomial rightBox)
      {start finish : InverseRootPolynomial.Gaussian}
    (leftStart : leftBox.Contains start) (leftFinish : leftBox.Contains finish)
    (rightStart : rightBox.Contains start) (rightFinish : rightBox.Contains finish)
    (nearest : Data.Gaussian.Norm.Basic.normSq (left.value.eval start + right.value.eval start) ≤
      Data.Gaussian.Norm.Basic.normSq (left.value.eval start - right.value.eval start)) :
    Data.Gaussian.Norm.Basic.normSq (left.value.eval finish + right.value.eval finish) ≤
      Data.Gaussian.Norm.Basic.normSq (left.value.eval finish - right.value.eval finish) := by
  let edge : InverseModelEdgeTransition.EdgeTransition left right start finish :=
    ⟨leftStart, leftFinish, rightStart, rightFinish,
      ⟨left.value.eval start, rfl, right.value.eval start, rfl,
        ⟨true, -(right.value.eval start), rfl, by
          have difference : left.value.eval start - -(right.value.eval start) = left.value.eval start + right.value.eval
            start := by ring1
          rewrite [difference, ← Data.Gaussian.Basic.Canonical.sub_eq_add_neg]
          rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
            Data.Gaussian.Norm.Basic.normSq_eq_canonical] at nearest
          exact nearest⟩⟩⟩
  exact opposite_of_flipped (OverlapSample.build left right
    finish) edge.flip_eq_finish.symm

/-- An original opposite-sign comparison followed by a same-sign comparison gives an opposite-sign comparison between
the retained outer models.

The retained sign bit selects the same negated model value. Scalar transports compare the original cached values and
their two quadrances without changing the model or its overlap witness. -/
private theorem opposite_trans {polynomial : InverseRootPolynomial.Polynomial} {firstBox middleBox lastBox :
  InverseRootPolynomial.Box}
    (first : InverseRootPolynomial.OverlapReady polynomial firstBox) (middle : InverseRootPolynomial.OverlapReady
      polynomial middleBox)
    (last : InverseRootPolynomial.OverlapReady polynomial lastBox) {point : InverseRootPolynomial.Gaussian}
    (firstInside : firstBox.Contains point) (middleInside : middleBox.Contains point) (lastInside : lastBox.Contains
      point)
    (firstMiddle : Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point + middle.model.value.eval
      point) ≤
      Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point - middle.model.value.eval point))
    (middleLast : Data.Gaussian.Norm.Basic.normSq (middle.model.value.eval point - last.model.value.eval point)
      ≤
      Data.Gaussian.Norm.Basic.normSq (middle.model.value.eval point + last.model.value.eval point)) :
    Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point + last.model.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point - last.model.value.eval point) := by
  let negative : InverseModelOverlap.OverlapSample first.model middle.model point :=
    ⟨first.model.value.eval point, rfl, middle.model.value.eval point, rfl,
      ⟨true, -(middle.model.value.eval point), rfl, by
        have difference : first.model.value.eval point - -(middle.model.value.eval point) = first.model.value.eval point
          + middle.model.value.eval point := by ring1
        rewrite [difference, ← Data.Gaussian.Basic.Canonical.sub_eq_add_neg]
        rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
          Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstMiddle
        exact firstMiddle⟩⟩
  let positive : InverseModelOverlap.OverlapSample middle.model last.model point :=
    ⟨middle.model.value.eval point, rfl, last.model.value.eval point, rfl,
      ⟨false, last.model.value.eval point, rfl, by
        rewrite [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
          Data.Gaussian.Norm.Basic.normSq_eq_canonical] at middleLast
        exact middleLast⟩⟩
  let direct := OverlapSample.build first.model last.model point
  exact opposite_of_flipped direct
    (OverlapReady.cocycle first middle last firstInside middleInside lastInside negative positive direct)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}

/-- The actual opposite face occurrences fix the sign on every common point of two retained cells. Auxiliary acquisition
is confined to this proof. -/
theorem opposite_cells_nearest {leftBox rightBox : InverseRootPolynomial.Box}
    (left : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet) leftBox)
    (right : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners (BranchCutLifts.otherSheet
      sheet)) rightBox)
    (differential : Differentials.Basic.Differential genus) {point : InverseRootPolynomial.Gaussian}
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point + (right.model.refine
      (rightIndex + 2)).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point -
        (right.model.refine (rightIndex + 2)).value.eval point) := by
  let auxiliary := TransportedCell.acquire left.geometry (models.frame.owners (BranchCutLifts.otherSheet sheet))
  let frame := OwnerFrame.build left.traced.finishOwner.parameterNonzero
  let opposite := TransportNegation.compareOppositeCellTrace left auxiliary.traced
    (Polynomial.Geometry.ClearPath.InBox.ofWithin auxiliary.route.path auxiliary.route.within
      face.cell.box.contains_anchor) frame
  let neighborhood := Neighborhood.build auxiliary.traced 0
  have anchor := TransportNegation.opposite_anchor_nearest
    left auxiliary.traced opposite neighborhood (leftIndex + 2) 2
  have first := opposite_finish (left.model.refine
    (leftIndex + 2)) (auxiliary.model.refine 2)
    leftBox.contains_anchor leftInside leftBox.contains_anchor leftInside anchor
  have second := SheetGauge.cells_nearest auxiliary right differential leftInside rightInside 0 rightIndex
  exact opposite_trans ((Model.overlapRefine left.model)
    leftIndex) ((Model.overlapRefine auxiliary.model) 0)
    ((Model.overlapRefine right.model) rightIndex) leftInside leftInside rightInside first second

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CellNegation
