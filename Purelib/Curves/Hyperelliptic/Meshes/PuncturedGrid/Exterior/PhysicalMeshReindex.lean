module
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshPerimeters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateFacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CorrectionReindex
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly

public section

/-! Identify retained conjugated perimeter areas with the actual normal-form
exterior component, including every face, sheet, side and orientation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage : Nat}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget}

/-- The original source-forward sign equals the orientation of its retained physical side occurrence. -/
private theorem sourceForward_oriented (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (value : Gaussian.Basic.Canonical) :
    (if occurrence.sourceForward then value else -value) =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence value := by
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only
      [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceForward,
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented,
      side, backward,
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .left),
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .left),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .left)),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .left)),
      if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self] <;>
      first | rfl | ring1

section PhysicalMeshRequest
variable (request : PhysicalMeshRequest basis initial)

/-- A whole-face conjugate perimeter bank for each original pair of basis rows.

Each entry retains the same surface request and primitive cache, so occurrence readback selects its actual face and
sheet. -/
@[expose] def FacePerimeterBank (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    ConjugateFacePerimeters request.surface cache first
      second))

namespace FacePerimeterBank

/-- Build each original row-pair perimeter bank from the supplied common primitive cache and retained surface request.
-/
@[expose] def build (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage) : request.FacePerimeterBank cache :=
  Data.Vector.DependentVector.ofFn fun first => Data.Vector.DependentVector.ofFn fun second =>
    ConjugateFacePerimeters.build request.surface cache first
      second

variable {request} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  (faces : request.FacePerimeterBank cache)

/-- Read the existing whole-face assembly at the occurrence's actual owner. -/
@[expose] def occurrence (first second : Fin genus) (i : Fin (basis.preparations.get first).occurrences.length) :
    request.OccurrencePerimeter cache first second i :=
  let side := ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence
  let pair := (faces.get first).get second
  ⟨(pair.assemblies.get side.position).get side.sheet, (pair.perimeters.get side.position).get side.sheet⟩

/-- Select the retained whole-face perimeter at every original occurrence, keeping its basis rows, face and sheet. -/
@[expose] def occurrences : request.Perimeters cache :=
  Data.Vector.DependentVector.ofFn fun first => Data.Vector.DependentVector.ofFn fun second =>
    Data.Vector.DependentVector.ofFn fun i => faces.occurrence first second i

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.FacePerimeterBank
  in
/-- The selected occurrence perimeter reads the original whole-face area at its actual face, sheet and side. -/
private theorem occurrence_area (first second : Fin genus) (i : Fin (basis.preparations.get first).occurrences.length) :
    (faces.occurrence first second i).area =
      let side := ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence
      ((faces.get first).get second).area side.position side.sheet side.side := by
  unfold OccurrencePerimeter.area
    occurrence
  dsimp only
  cases ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence.side <;> rfl

/-- The physical occurrence area is exactly the exterior component selected
by the original face-neighbor classification; no equality is a caller input. -/
theorem area_eq_component (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces) (first second :
  Fin genus) :
    faces.occurrences.area first second =
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
        (fun side position => FiniteSum.Fin.sumFin (fun sheet => ((faces.get first).get second).area position sheet
          side)) .exterior := by
  apply Eq.trans _ ((basis.preparations.get first).oriented_sum_eq_component neighbors
    (fun position sheet side => ((faces.get first).get second).area position sheet side))
  unfold Perimeters.area
  apply FiniteSum.Fin.sumFin_congr
  intro i
  have areaEq := faces.occurrence_area first second i
  have oriented := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.sourceForward_oriented
    ((basis.preparations.get first).occurrences[i.val]'i.isLt)
    (faces.occurrence first second i).area
  have result := oriented.trans (congrArg
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
      ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence) areaEq)
  simpa only
    [occurrences,
    Data.Vector.DependentVector.ofFn_get, -eq_self, -iff_self] using result

end FacePerimeterBank
end PhysicalMeshRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
