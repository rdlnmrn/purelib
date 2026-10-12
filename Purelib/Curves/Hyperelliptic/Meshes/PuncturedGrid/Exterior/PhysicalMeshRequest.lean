module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

@[expose] public section

/-! Select exterior owner budgets from the actual complete-surface partitions,
then refine that same surface before acquiring the common numerical bank. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (PhysicalBasisRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
  (PhysicalBasisPieceCounts)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
  (pieceCount)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {coarse : (sheet : Fin 2) → RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {surfaceTarget target : Rational}
  {minimum floor : Nat}

namespace PhysicalMeshRequest

/-- These are coarse perimeter interval counts, not counts of fine vertices. -/
def physicalMeshPieceCounts (preparations : BasisArcRequest.BasisArcPreparations regular domains)
    (coarse : (sheet : Fin 2) → RegularDomainMeshes.RegularMeshes domains sheet) :
      PhysicalBasisRequest.PhysicalBasisPieceCounts preparations :=
  fun first _ i =>
    let occurrence := (preparations.get first).occurrences[i.val]'i.isLt
    SharedPhysicalPerimeterReadings.pieceCount (occurrence := occurrence)
      ((coarse occurrence.sideOccurrence.sheet).entries.get occurrence.sideOccurrence.position)
      occurrence.sideOccurrence.side

/-- Requested refinement preserves exactly the intervals used to budget owners. -/
theorem physicalMesh_pieceCount (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget)
    (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    SharedPhysicalPerimeterReadings.pieceCount (occurrence := occurrence)
      ((request.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position)
      occurrence.sideOccurrence.side =
    SharedPhysicalPerimeterReadings.pieceCount (occurrence := occurrence)
      ((coarse occurrence.sideOccurrence.sheet).entries.get occurrence.sideOccurrence.position)
      occurrence.sideOccurrence.side := by
  rw [RegularMeshes.Request.mesh_eq,
    EnergyRequest.mesh_eq]
  cases occurrence.sideOccurrence.side <;> rfl

end PhysicalMeshRequest

namespace PhysicalMeshRequest.PhysicalBasisRequest

/-- Prepare the exterior basis request using the actual coarse surface piece counts and the original surface depth as
its floor. -/
def forSurface (preparations : BasisArcRequest.BasisArcPreparations regular domains)
    (surface : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget)
    (target : Fraction.Rational) (positive : 0 < target) (minimum floor : Nat) :
    PhysicalBasisRequest regular domains target minimum floor :=
  PhysicalBasisRequest.build
    preparations (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.physicalMeshPieceCounts
      preparations coarse) target positive minimum floor surface.depth

end PhysicalMeshRequest.PhysicalBasisRequest

set_option genInjectivity false in
/-- The complete surface and all exterior occurrences share one physical depth and one numerical stage. Piece-count
readbacks identify the actual budgets. -/
structure PhysicalMeshRequest (basis : PhysicalBasisRequest regular domains target minimum floor)
    (initial : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget) where
  /-- The retained complete-surface request refined to the exterior basis depth. -/ surface :
    TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget
  /-- The surface and exterior basis requests use the same physical depth. -/ depth_eq : surface.depth =
    basis.physicalDepth
  /-- Every exterior occurrence budget uses the actual retained refined-surface piece count. -/ pieceCounts_eq : ∀ first
    second i,
    let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
    basis.pieceCounts first second i = SharedPhysicalPerimeterReadings.pieceCount (occurrence := occurrence)
      ((surface.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position)
      occurrence.sideOccurrence.side
  /-- The original surface request's stage is paid by the retained refined request. -/ initial_le : initial.index ≤
    surface.index
  /-- The common numerical stage for both retained requests. -/ index : Nat
  /-- The common stage is the exact maximum of the basis and surface stages. -/ index_eq : index = max basis.index
    surface.index
  /-- The retained exterior basis request is paid at the common stage. -/ basis_le : basis.index ≤ index
  /-- The retained complete-surface request is paid at the common stage. -/ surface_le : surface.index ≤ index

constructive_injectivity PhysicalMeshRequest

namespace PhysicalMeshRequest

/-- Refine the original surface to the paid exterior basis depth and retain the exact piece-count readbacks with one
common numerical stage. -/
def build (preparations : BasisArcRequest.BasisArcPreparations regular domains)
    (initial : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget)
    (target : Fraction.Rational) (positive : 0 < target) (minimum floor : Nat) :
    PhysicalMeshRequest
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.PhysicalBasisRequest.forSurface
      preparations initial target positive minimum floor) initial := by
  let basis := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.PhysicalBasisRequest.forSurface
    preparations initial target positive minimum floor
  have later : initial.depth ≤ basis.physicalDepth :=
    PhysicalBasisRequest.build_physicalFloor_le preparations
      (physicalMeshPieceCounts preparations
      coarse)
      target positive minimum floor initial.depth
  let surface := initial.atDepth basis.physicalDepth later
  refine ⟨surface, rfl, ?_, initial.atDepth_index_ge _ later,
    max basis.index surface.index, rfl, Nat.Order.le_max_left _ _, Nat.Order.le_max_right _ _⟩
  intro first second i
  exact (physicalMesh_pieceCount surface
    ((preparations.get first).occurrences[i.val]'i.isLt)).symm

end PhysicalMeshRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
