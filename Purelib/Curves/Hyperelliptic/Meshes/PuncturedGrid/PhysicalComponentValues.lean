module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

@[expose] public section

/-! Exact component selection from the retained geometric side classification. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {face : Meshes.PuncturedGridFaces.RegularFace bank} {side :
    Meshes.GridLiftedDualSteps.GridSide}

set_option genInjectivity false in
/-- An original physical boundary component: the exterior or a retained hole-list position.

Hole components retain their bounded position in the original physical-hole
list. The exterior constructor identifies the original ambient boundary. -/
inductive PhysicalComponent (faces : Meshes.PuncturedGridFaces.PuncturedFaces bank) where
  /-- The original physical exterior boundary. -/ | exterior
  /-- The physical hole at its retained original list position. -/ | hole (position : Fin faces.holes.length)

constructive_injectivity PhysicalComponent

set_option backward.match.sparseCases false in
/-- Select a side contribution precisely when its original geometric neighbor belongs to the requested physical
component.

Exterior sides contribute only to the exterior component. A side classified at
a retained hole contributes only at that same bounded hole position; all other
original neighbor/component combinations contribute zero. -/
def SideNeighbor.componentValue (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side)
    (component : Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent faces) (value :
      Gaussian.Basic.Canonical) : Gaussian :=
  match neighbor, component with
  | .exterior _, .exterior => value
  | .neighbor _ _ _ (.hole position _), .hole selected => if selected = position then value else 0
  | _, _ => 0

/-- The retained physical side contribution splits exactly into its exterior and individual hole contributions.

The original neighbor classification selects either the exterior or one hole.
The finite sum over the original hole positions recovers precisely that retained
contribution, with no enumeration or witness replacement. -/
theorem SideNeighbor.physical_components (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face
  side) (value : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      neighbor value = Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor
      .exterior value +
      FiniteSum.Fin.sumFin (fun hole =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor (.hole hole)
        value) := by
  cases neighbor with
  | exterior equal =>
      simp only
        [NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue,
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue,
        FiniteSum.Fin.sumFin_zero, add_zero, -eq_self, -iff_self]
      rfl
  | neighbor cell member matching location =>
    cases location with
    | regular position equal =>
        simp only
          [NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue,
          Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue,
          FiniteSum.Fin.sumFin_zero, add_zero, -eq_self, -iff_self]
        rfl
    | hole position equal =>
      simp only
        [NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue,
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue]
      rw [zero_add]
      exact (FiniteSum.Fin.sumFin_ite_eq position (fun _ => value)).symm

/-- A nonzero selected term identifies the actual adjacent hole geometry.

Only the original hole classification at the selected position can contribute
a nonzero value. Its retained cell identity transports the original side match
to the requested physical hole box. -/
theorem SideNeighbor.hole_component_supported (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces
  face side)
    (hole : Fin faces.holes.length) (value : Gaussian.Basic.Canonical)
    (nonzero : Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor (.hole
      hole) value ≠ 0) :
    side.Matches face.cell.box (faces.holes[hole.val]'hole.isLt).cell.box := by
  cases neighbor with
  | exterior equal => exact False.elim (nonzero rfl)
  | neighbor cell member matching location =>
    cases location with
    | regular position equal => exact False.elim (nonzero rfl)
    | hole position equal =>
      by_cases same : hole = position
      · subst hole
        rw [← equal] at matching
        exact matching
      · apply False.elim
        apply nonzero
        simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue, if_neg same,
          -eq_self, -iff_self]
        rfl

/-- A nonzero exterior contribution certifies that the original face side lies on the physical exterior. -/
theorem SideNeighbor.exterior_component_supported (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor
  faces face side)
    (value : Gaussian.Basic.Canonical) (nonzero :
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior value ≠
      0) :
    side.Exterior face.cell.box (Hyperelliptic.Branches.Cuts.Ambient curve) := by
  cases neighbor with
  | exterior equal => exact equal
  | neighbor cell member matching location =>
    cases location <;> exact False.elim (nonzero rfl)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
