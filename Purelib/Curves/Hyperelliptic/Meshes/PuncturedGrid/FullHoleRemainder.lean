module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

/-! The full hole-side remainder is exactly the hole part of the original
physical correction, with the actual normalized endpoint chords removed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection
  componentTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues (PhysicalComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor (componentValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition (fullHoleEvaluation omittedHoleEvaluation
  fullHoleEvaluation_partition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters (sideSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters (componentPerimeter)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_add sumFin_neg sumFin_swap sumFin_zero)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {target : Purelib.Data.Rat.Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

/-- The original physical-component projection preserves subtraction. -/
private theorem component_sub {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor base.faces face side) (component : PhysicalComponentValues.PhysicalComponent
      base.faces)
    (a b : Data.Gaussian.Basic.Canonical) : SideNeighbor.componentValue neighbor component (a - b) =
      SideNeighbor.componentValue neighbor component a - SideNeighbor.componentValue neighbor component b := by
  cases neighbor with
  | exterior _ => cases component <;> first | rfl | exact (Data.Gaussian.Basic.sub_self _).symm
  | neighbor _ _ _ location =>
    cases location with
    | regular _ _ => cases component <;> exact (Data.Gaussian.Basic.sub_self _).symm
    | hole found _ =>
      cases component with
      | exterior => exact (sub_self _).symm
      | hole hole =>
        change (if hole = found then a - b else 0) =
          (if hole = found then a else 0) - (if hole = found then b else 0)
        by_cases same : hole = found
        · simp only [if_pos same, -eq_self, -iff_self]; rfl
        · simp only [if_neg same, -eq_self, -iff_self]; rfl

/-- The original physical-component projection preserves the sum over both retained sheets. -/
private theorem component_sum {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor base.faces face side) (component : PhysicalComponentValues.PhysicalComponent
      base.faces)
    (values : Fin 2 → Data.Gaussian.Basic.Canonical) : SideNeighbor.componentValue neighbor component
      (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun sheet => SideNeighbor.componentValue neighbor component
      (values sheet)) := by
  cases neighbor with
  | exterior _ => cases component <;> first | rfl | exact FiniteSum.Fin.sumFin_zero.symm
  | neighbor _ _ _ location =>
    cases location with
    | regular _ _ => cases component <;> first | rfl | exact FiniteSum.Fin.sumFin_zero.symm
    | hole found _ =>
      cases component with
      | exterior => exact FiniteSum.Fin.sumFin_zero.symm
      | hole hole =>
        change (if hole = found then FiniteSum.Fin.sumFin values else 0) =
          FiniteSum.Fin.sumFin (fun sheet => if hole = found then values sheet else 0)
        by_cases same : hole = found
        · rewrite [if_pos same]
          exact (FiniteSum.Fin.sumFin_congr (fun sheet => if_pos same)).symm
        · rewrite [if_neg same]
          exact (FiniteSum.Fin.sumFin_congr (fun sheet => if_neg same)).trans
            FiniteSum.Fin.sumFin_zero |>.symm

/-- The original physical-component projection sends zero to zero. -/
private theorem component_zero {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor base.faces face side) (component : PhysicalComponentValues.PhysicalComponent
      base.faces) :
    SideNeighbor.componentValue neighbor component (0 : Data.Gaussian.Basic.Canonical) = 0 := by
  cases neighbor with
  | exterior _ => cases component <;> rfl
  | neighbor _ _ _ location =>
    cases location with
    | regular _ _ => cases component <;> rfl
    | hole _ _ => cases component with
      | exterior => rfl
      | hole _ => exact ite_self _

/-- The original physical-component projection preserves negation. -/
private theorem component_neg {face : PuncturedGridFaces.RegularFace base.bank.toBranchCellBank} {side :
  GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor base.faces face side) (component : PhysicalComponentValues.PhysicalComponent
      base.faces) (v : Data.Gaussian.Basic.Canonical) :
    SideNeighbor.componentValue neighbor component (-v) = -SideNeighbor.componentValue neighbor component v := by
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_sub neighbor component 0 v
  simpa only [zero_sub, Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_zero, -eq_self, -iff_self]
    using equal

/-- The complete two-sheet side remainder of one physical component equals its original perimeter-minus-triangle
correction. -/
theorem component_remainder (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : PuncturedFaces.NeighborBank base.faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (component : PhysicalComponentValues.PhysicalComponent base.faces) :
    SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
      (fun side p => FiniteSum.Fin.sumFin (fun sheet => HoleAreaRemainder.sideAreaRemainder perimeters p sheet side))
        component =
      PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left right component := by
  simp only [SelectedPhysicalComponents.componentEvaluation, SelectedSides.value, if_pos (rfl : true = true),
    HoleAreaRemainder.sideAreaRemainder,
    FiniteSum.Fin.sumFin_sub, Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_sub,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_sum,
    Numerics.normalized_bottom_chord cache,
    Numerics.normalized_left_chord cache,
    TriangleReadings.normalized_right_chord left right,
    TriangleReadings.normalized_top_chord left right,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_neg,
    FiniteSum.Fin.sumFin_neg, Data.Gaussian.Basic.sub_zero,
    PhysicalComponentCorrection.physicalComponentCorrection, FacePerimeters.componentPerimeter, FacePerimeters.sideSum,
      PhysicalComponentCorrection.componentTriangleArea,
    FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rw [FiniteSum.Fin.sumFin_swap (fun sheet p => SideNeighbor.componentValue (neighbors.entries.get p).right component
    (TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex p sheet false))),
    FiniteSum.Fin.sumFin_swap (fun sheet p => SideNeighbor.componentValue (neighbors.entries.get p).top component
      (TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex p sheet true)))]
  ring1

/-- The complete physical hole-side remainder equals the sum of the original indexed hole-component corrections.

The equality retains the normalized endpoint chords and all actual side and sheet occurrences. -/
theorem fullHoleEvaluation_eq_correction (perimeters : Matched.FacePerimeters (request := request)
  cache.normalize i j)
    (neighbors : PuncturedFaces.NeighborBank base.faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    HoleSelectionPartition.fullHoleEvaluation neighbors (fun side p => FiniteSum.Fin.sumFin (fun sheet =>
      HoleAreaRemainder.sideAreaRemainder perimeters p sheet side)) =
      FiniteSum.Fin.sumFin (fun hole => PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors
        left right (.hole hole)) := by
  rw [HoleSelectionPartition.fullHoleEvaluation_partition neighbors (fun _ => true)]
  simp only [HoleSelectionPartition.omittedHoleEvaluation, if_neg (by decide : true ≠ false), FiniteSum.Fin.sumFin_zero,
    sub_self, add_zero, -eq_self, -iff_self]
  exact FiniteSum.Fin.sumFin_congr (fun hole =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder.component_remainder perimeters neighbors left right
    (.hole hole))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FullHoleRemainder
