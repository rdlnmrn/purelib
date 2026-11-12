module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.Points
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Fin

/-! # Original rectangular gauge on the actual continued face sheet

Every shared corner is compared to one genuinely continued Point. Its
original Entry selects the retained source sheet. The exact overlap cocycle
then fixes each cached transition bit, and the original gauge equations
propagate the source sign without rebuilding a gauge or a model.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (Acquisition TracedPoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseModelRefinementSigns
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.RectangularRefinementSigns

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
    {models : FaceModels frames face} {columns rows : Nat} {geometry : Geometry columns rows}

/-- Cut the actual selected sheet equality before comparing the original dependent model owners. -/
private theorem nearest_on_sheet {count : Nat} {point : Canonical}
    {patch : ContinuedNeighborhood curve.polynomial count}
    (actual : ContinuedNeighborhood.Point patch point) (insideFace : face.cell.box.Contains point)
    (acquired : Acquisition models insideFace actual.owner) (sheet : Fin 2)
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (same : acquired.entry.sheet = sheet) (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (basis : Differential genus) (insideCell : (geometry.box column row).Contains point)
    (insideActual : patch.box.Contains point) :
    normSq ((rectangles.models.ready column row).model.value.eval point -
      (patch.base.refine 2).value.eval point) ≤
      normSq ((rectangles.models.ready column row).model.value.eval point +
        (patch.base.refine 2).value.eval point) := by
  cases same
  let result : {value : Unit //
      normSq ((rectangles.models.ready column row).model.value.eval point -
        (patch.base.refine 2).value.eval point) ≤
      normSq ((rectangles.models.ready column row).model.value.eval point +
        (patch.base.refine 2).value.eval point)} :=
    withRectangularPointComparison actual insideFace acquired rectangles column row basis insideCell insideActual
      (fun _ _ _ _ near => ⟨(), near⟩)
  exact result.property

/-- An original Point acquisition fixes the unflipped raw model sign throughout its actual retained cell.

The full acquisition and Point remain the supplied caches. The finite
covered-path proof in the original comparison is erased; it does not add
an executable Point, model, root reading or selection to this theorem.
-/
theorem rectangular_point_nearest {count : Nat} {point : Canonical}
    {patch : ContinuedNeighborhood curve.polynomial count}
    (actual : ContinuedNeighborhood.Point patch point) (insideFace : face.cell.box.Contains point)
    (acquired : Acquisition models insideFace actual.owner)
    (rectangles : RectangularPatch models.bounds (models.frame.owners acquired.entry.sheet) geometry)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (basis : Differential genus)
    (insideCell : (geometry.box column row).Contains point) (insideActual : patch.box.Contains point) :
    normSq ((rectangles.models.ready column row).model.value.eval point -
      (patch.base.refine 2).value.eval point) ≤
      normSq ((rectangles.models.ready column row).model.value.eval point +
        (patch.base.refine 2).value.eval point) :=
  nearest_on_sheet actual insideFace acquired acquired.entry.sheet rectangles rfl column row basis
    insideCell insideActual

/-- A shared original corner compares both retained raw models to one genuine Point on the supplied face sheet.

The source sheet is an original Owner index. Its new corner trace and
Point, and the actual selector acquisition, occur only in this proof.
Their Entry uniqueness determines the sheet rather than assuming it from
coordinates or a local chart label.
-/
private theorem raw_overlap_unflipped {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (firstColumn lastColumn : Fin (columns + 1)) (firstRow lastRow : Fin (rows + 1))
    (basis : Differential genus) (point : Canonical)
    (firstInside : (geometry.box firstColumn firstRow).Contains point)
    (lastInside : (geometry.box lastColumn lastRow).Contains point) :
    (OverlapSample.build (rectangles.models.ready firstColumn firstRow).model
      (rectangles.models.ready lastColumn lastRow).model point).alignment.flip = false := by
  have insideFace := (rectangles.cell_refines firstColumn firstRow).contains firstInside
  let frame := OwnerFrame.build (face.clearance.eval_ne_zero insideFace)
  let common := TracedPoint.build models sheet point insideFace 0 frame
  let acquired := Acquisition.build models insideFace common.sample.owner
  have same : acquired.entry.sheet = sheet :=
    (acquired.entry.sheet_unique common.entry insideFace).trans common.entry_sheet
  have firstNear := nearest_on_sheet common.sample insideFace acquired sheet rectangles same firstColumn firstRow
    basis firstInside common.neighborhood.center_inside
  have lastNear := nearest_on_sheet common.sample insideFace acquired sheet rectangles same lastColumn lastRow
    basis lastInside common.neighborhood.center_inside
  let middle : OverlapReady curve.polynomial common.neighborhood.patch.base.box :=
    ⟨common.neighborhood.patch.base.refine 2,
      OverlapReady.two_steps_small common.neighborhood.patch.base.model⟩
  let first : OverlapSample (rectangles.models.ready firstColumn firstRow).model middle.model point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq ((rectangles.models.ready firstColumn firstRow).model.value.eval point -
        middle.model.value.eval point) ≤
        Canonical.normSq ((rectangles.models.ready firstColumn firstRow).model.value.eval point +
          middle.model.value.eval point)
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using firstNear⟩⟩
  let reverse : OverlapSample (rectangles.models.ready lastColumn lastRow).model middle.model point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq ((rectangles.models.ready lastColumn lastRow).model.value.eval point -
        middle.model.value.eval point) ≤
        Canonical.normSq ((rectangles.models.ready lastColumn lastRow).model.value.eval point +
          middle.model.value.eval point)
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using lastNear⟩⟩
  let last : OverlapSample middle.model (rectangles.models.ready lastColumn lastRow).model point :=
    ⟨_, rfl, _, rfl, SignAlignment.reverse reverse.alignment⟩
  exact (OverlapReady.cocycle (rectangles.models.ready firstColumn firstRow) middle
    (rectangles.models.ready lastColumn lastRow) firstInside
    (common.neighborhood.patch.box_refines.contains common.neighborhood.center_inside) lastInside first last
    (OverlapSample.build (rectangles.models.ready firstColumn firstRow).model
      (rectangles.models.ready lastColumn lastRow).model point)).trans rfl

/-- Each actual cached horizontal transition has no flip on the retained original source sheet. -/
theorem rectangular_horizontal_false {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (basis : Differential genus) (column : Fin columns) (row : Fin (rows + 1)) :
    rectangles.sheets.transitions.horizontal column row = false := by
  have original := rectangles.sheets.transitions.horizontal_eq column row
  have canonical := InverseModelEdgeTransition.OverlapSample.flip_eq_build
    (rectangles.models.horizontalEdge column row).sample
    (geometry.lowerRight_mem column.castSucc row) (geometry.lowerLeft_mem column.succ row)
  exact original.trans (canonical.trans
    (raw_overlap_unflipped rectangles column.castSucc column.succ row row basis _
      (geometry.lowerRight_mem column.castSucc row) (geometry.lowerLeft_mem column.succ row)))

/-- Each actual cached vertical transition has no flip on the retained original source sheet. -/
theorem rectangular_vertical_false {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (basis : Differential genus) (column : Fin (columns + 1)) (row : Fin rows) :
    rectangles.sheets.transitions.vertical column row = false := by
  have original := rectangles.sheets.transitions.vertical_eq column row
  have canonical := InverseModelEdgeTransition.OverlapSample.flip_eq_build
    (rectangles.models.verticalEdge column row).sample
    (geometry.upperLeft_mem column row.castSucc) (geometry.lowerLeft_mem column row.succ)
  exact original.trans (canonical.trans
    (raw_overlap_unflipped rectangles column column row.castSucc row.succ basis _
      (geometry.upperLeft_mem column row.castSucc) (geometry.lowerLeft_mem column row.succ)))

/-- The SAME retained gauge has the original source sign at every literal cell index.

Only the existing horizontal/vertical equations and source origin are
used. Pointwise finite induction avoids a new scan, array replacement or
whole-function extensionality certificate.
-/
theorem rectangular_gauge_false {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (basis : Differential genus) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    rectangles.sheets.gauge.values column row = false := by
  have firstColumn : ∀ index : Fin (rows + 1), rectangles.sheets.gauge.values 0 index = false := by
    intro index
    induction index using Data.Fin.induction with
    | zero => exact rectangles.origin
    | succ index ih =>
        exact (rectangles.sheets.gauge.vertical 0 index).trans
          ((congrArg₂ Bool.xor ih (rectangular_vertical_false rectangles basis 0 index)).trans rfl)
  induction column using Data.Fin.induction with
  | zero => exact firstColumn row
  | succ column ih =>
      exact (rectangles.sheets.gauge.horizontal column row).trans
        ((congrArg₂ Bool.xor ih (rectangular_horizontal_false rectangles basis column row)).trans rfl)

/-- Later requests reuse the SAME pointwise source gauge rather than selecting another sign. -/
theorem rectangular_refine_gauge_false {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (basis : Differential genus) (index : Nat) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (rectangles.sheets.refine index).gauge.values column row = false :=
  (congrArg (fun values => values column row) (rectangles.sheets.refine_values index)).trans
    (rectangular_gauge_false rectangles basis column row)

/-- The actual oriented later model reads its SAME original refined polynomial value without a hidden sign. -/
theorem rectangular_oriented_value {sheet : Fin 2}
    (rectangles : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (basis : Differential genus) (index : Nat) (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (point : Canonical) :
    ((RectangularSheetGauge.Transitions.oriented
      (rectangles.sheets.refine index).transitions
      (rectangles.sheets.refine index).gauge).ready column row).model.value.eval point =
      ((rectangles.models.refine index).ready column row).model.value.eval point := by
  have original := RectangularSheetGauge.Bank.orient_value (rectangles.models.refine index)
    (rectangles.sheets.refine index).gauge.values column row point
  exact original.trans ((congrArg
    (fun flip => signedValue flip (((rectangles.models.refine index).ready column row).model.value.eval point))
    (rectangular_refine_gauge_false rectangles basis index column row)).trans rfl)

/-- Construct the actual unflipped oriented-model overlap with an independently retained later source model.

The source readback keeps its absolute original index 2+sourceDepth. Both
model evaluations are retained once in the original OverlapSample; all
Point, selector, gauge and root-comparison work proving the sign is erased.
An earlier fixed source is not retagged by this operation.
-/
def orientedOverlap {count : Nat} {point : Canonical}
    {patch : ContinuedNeighborhood curve.polynomial count}
    (actual : ContinuedNeighborhood.Point patch point) (insideFace : face.cell.box.Contains point)
    (entry : Entry models point actual.owner)
    (rectangles : RectangularPatch models.bounds (models.frame.owners entry.sheet) geometry)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (basis : Differential genus)
    (insideCell : (geometry.box column row).Contains point) (insideActual : patch.box.Contains point)
    (index sourceDepth : Nat) (source : Model curve.polynomial patch.base.box)
    (sourceEq : source.value.eval point = (patch.base.refine (2 + sourceDepth)).value.eval point) :
    {sample : OverlapSample
      ((RectangularSheetGauge.Transitions.oriented
        (rectangles.sheets.refine index).transitions
        (rectangles.sheets.refine index).gauge).ready column row).model source point //
      sample.alignment.flip = false} :=
  let middle : OverlapReady curve.polynomial patch.base.box :=
    ⟨patch.base.refine 2, OverlapReady.two_steps_small patch.base.model⟩
  let original : OverlapSample (rectangles.models.ready column row).model middle.model point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq ((rectangles.models.ready column row).model.value.eval point -
        middle.model.value.eval point) ≤
        Canonical.normSq ((rectangles.models.ready column row).model.value.eval point +
          middle.model.value.eval point)
      let acquired := Acquisition.build models insideFace actual.owner
      have same := acquired.entry.sheet_unique entry insideFace
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        nearest_on_sheet actual insideFace acquired entry.sheet rectangles same column row basis
          insideCell insideActual⟩⟩
  let left := ((RectangularSheetGauge.Transitions.oriented
    (rectangles.sheets.refine index).transitions
    (rectangles.sheets.refine index).gauge).ready column row).model
  let refined := OverlapSample.ofRefined original insideCell (patch.box_refines.contains insideActual)
    (rectangles.models.ready column row).small middle.small index sourceDepth left source
    ((rectangular_oriented_value rectangles basis index column row point).trans
      (congrArg (fun value : Model curve.polynomial (geometry.box column row) => value.value.eval point)
        (RectangularRefinementSigns.Bank.refine_model rectangles.models index column row)))
    (sourceEq.trans (congrArg (fun value : Model curve.polynomial patch.base.box => value.value.eval point)
      (patch.base.model.refine_add 2 sourceDepth)).symm)
  ⟨refined, rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
