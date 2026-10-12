module
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
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
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Grid.Signs

public section

/-!
# The rectangular gauge follows the actual face occurrence

All cells have been transported from the same face owner. At any overlap,
their models agree with a common actual path endpoint, so the comparison
bit is unflipped. Every checked rectangular gauge with unflipped origin is
therefore unflipped everywhere, including generated nonuniform banks.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial

open Purelib.Riemann.Normalization.InverseModelRefinementSigns

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood

open Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}

/-- Two independently acquired cells compare through the same actual face trace. The trace, frame and endpoint
neighborhood are proof-only. No caller-supplied root identification or sign assumption remains.

Both retained models compare with the same endpoint neighborhood through their supplied indices. Reversing that exact
unflipped comparison and composing the nearestness bounds preserves the chosen face owner. -/
theorem cells_nearest {leftBox rightBox : InverseRootPolynomial.Box}
    (left : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet) leftBox)
    (right : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet) rightBox)
    (differential : Differentials.Basic.Differential genus) {point : InverseRootPolynomial.Gaussian}
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point - (right.model.refine
      (rightIndex + 2)).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq ((left.model.refine (leftIndex + 2)).value.eval point +
        (right.model.refine (rightIndex + 2)).value.eval point) := by
  let route := Route.build face.clearance face.cell.box.anchor point
    face.cell.box.contains_anchor (left.geometry.refines.contains leftInside)
  let traced := TracedPath.build route.path route.within (models.frame.owners sheet)
  have inside := Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within face.cell.box.contains_anchor
  let frame := OwnerFrame.build traced.finishOwner.parameterNonzero
  let neighborhood := Neighborhood.build traced 0
  have first := ContinuedComparison.trace_nearest left differential traced inside frame leftInside neighborhood
    leftIndex 0
  have second := ContinuedComparison.trace_nearest right differential traced inside frame rightInside neighborhood
    rightIndex 0
  let reversed : InverseModelOverlap.SignAlignment ((right.model.refine (rightIndex + 2)).value.eval point)
      ((neighborhood.patch.base.refine 2).value.eval point) :=
    ⟨false, (neighborhood.patch.base.refine 2).value.eval point, rfl, by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using second⟩
  have back : Data.Gaussian.Norm.Basic.normSq
      ((neighborhood.patch.base.refine 2).value.eval point - (right.model.refine (rightIndex + 2)).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq
      ((neighborhood.patch.base.refine 2).value.eval point + (right.model.refine (rightIndex + 2)).value.eval point) :=
        by
    have scalar := (SignAlignment.reverse reversed).nearest
    dsimp only [SignAlignment.reverse, reversed] at scalar
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar ⊢
    exact scalar
  have scalar := OverlapReady.nearest_trans
    ((Model.overlapRefine left.model) leftIndex)
    ((Model.overlapRefine neighborhood.patch.base.model) 0)
    ((Model.overlapRefine right.model) rightIndex) leftInside
    (neighborhood.patch.box_refines.contains neighborhood.center_inside) rightInside
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using first)
    (by simpa only [SeededNeighborhood.refine, Model.overlapRefine] using back)
  simpa only [SeededNeighborhood.refine, Model.overlapRefine] using scalar

variable {columns rows : Nat} {geometry : Geometry columns rows}

/-- The stored horizontal transition, not just a freshly recomputed bit, is unflipped on the common physical occurrence.

Both adjacent cells read the shared physical grid vertex. Their retained nearestness certificate selects the unflipped
horizontal transition stored by the patch. -/
theorem horizontal_false (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) (column : Fin columns) (row : Fin (rows + 1)) :
    patch.sheets.transitions.horizontal column row = false := by
  let point := geometry.vertex column.castSucc.succ row.castSucc
  have nearest : Data.Gaussian.Norm.Basic.normSq ((patch.models.ready column.castSucc row).model.value.eval
    point -
      (patch.models.ready column.succ row).model.value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq ((patch.models.ready column.castSucc row).model.value.eval point +
      (patch.models.ready column.succ row).model.value.eval point) := by
    rw [patch.value_eq, patch.value_eq]
    exact cells_nearest _ _ differential
      (geometry.lowerRight_mem column.castSucc row)
      (geometry.lowerLeft_mem column.succ row) 0 0
  rw [patch.sheets.transitions.horizontal_eq]
  change (SignAlignment.build ((patch.models.ready column.castSucc row).model.value.eval point)
    ((patch.models.ready column.succ row).model.value.eval point)).flip = false
  unfold SignAlignment.build
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at nearest
  rw [dif_pos nearest]

/-- The same identification holds for vertical transitions, including those not used by the spanning-tree gauge
constructor.

The shared grid vertex identifies the two retained cell models. Their actual nearestness certificate selects the
unflipped stored vertical transition. -/
theorem vertical_false (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) (column : Fin (columns + 1)) (row : Fin rows) :
    patch.sheets.transitions.vertical column row = false := by
  let point := geometry.vertex column.castSucc row.castSucc.succ
  have nearest : Data.Gaussian.Norm.Basic.normSq ((patch.models.ready column row.castSucc).model.value.eval
    point -
      (patch.models.ready column row.succ).model.value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq ((patch.models.ready column row.castSucc).model.value.eval point +
      (patch.models.ready column row.succ).model.value.eval point) := by
    rw [patch.value_eq, patch.value_eq]
    exact cells_nearest _ _ differential
      (geometry.upperLeft_mem column row.castSucc)
      (geometry.lowerLeft_mem column row.succ) 0 0
  rw [patch.sheets.transitions.vertical_eq]
  change (SignAlignment.build ((patch.models.ready column row.castSucc).model.value.eval point)
    ((patch.models.ready column row.succ).model.value.eval point)).flip = false
  unfold SignAlignment.build
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at nearest
  rw [dif_pos nearest]

/-- Every checked gauge with the retained origin agrees with the actual source occurrence throughout the rectangle. No
canonical scan equality is required, and zero-row or zero-column grids are covered by the same proof.

Fixed-bound finite induction follows the stored vertical transitions in the first column, then the stored horizontal
transitions in each row. The argument includes empty-row and empty-column rectangles. -/
theorem gauge_false (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (differential : Differentials.Basic.Differential genus) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    patch.sheets.gauge.values column row = false := by
  have firstColumn (row : Fin (rows + 1)) : patch.sheets.gauge.values 0 row = false := by
    induction row using Data.Fin.induction with
    | zero => exact patch.origin
    | succ row ih =>
        rw [patch.sheets.gauge.vertical]
        change (patch.sheets.gauge.values 0 row.castSucc ^^ patch.sheets.transitions.vertical 0 row) = false
        rw [ih, vertical_false patch differential]
        rfl
  induction column using Data.Fin.induction with
  | zero => exact firstColumn row
  | succ column ih =>
      rw [patch.sheets.gauge.horizontal]
      change (patch.sheets.gauge.values column.castSucc row ^^ patch.sheets.transitions.horizontal column row) = false
      rw [ih, horizontal_false patch differential]
      rfl

/-- Every oriented request reads the actual transported model at every cell, not merely the origin. The equation remains
pointwise, so generated coefficient representations and noncanonical gauge caches are admissible.

The gauge equation is specialized to the displayed cell before applying the retained refinement readback. Every point
and refinement index uses the same transported cell cache. -/
theorem oriented_value (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) (index : Nat) (column : Fin (columns + 1)) (row : Fin (rows
      + 1))
    (point : InverseRootPolynomial.Gaussian) :
    ((Transitions.oriented
      (patch.sheets.refine index).transitions (patch.sheets.refine index).gauge).ready column row).model.value.eval
        point =
      ((patch.transported.cell column row).model.refine (index + 2)).value.eval point := by
  rw [Transitions.oriented,
    Bank.orient_value]
  change RectangularSheetGauge.signedValue (patch.sheets.gauge.values column row)
    (((patch.models.refine index).ready column row).model.value.eval point) = _
  rw [gauge_false patch differential]
  exact patch.refine_value index column row point

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
