module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The retained physical correction splits into its actual hole and ambient components. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- The physical-side sum partitions into the retained exterior component and all original hole components. -/
private theorem component_sum {count : Nat} {Face : Fin count → Meshes.PuncturedGridFaces.RegularFace bank} {side :
  Meshes.GridLiftedDualSteps.GridSide}
    (neighbors : (index : Fin count) → Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces (Face index) side)
    (values : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index =>
      NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      (neighbors index) (values index)) =
      FiniteSum.Fin.sumFin (fun index =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors index)
        .exterior (values index)) +
      FiniteSum.Fin.sumFin (fun hole => FiniteSum.Fin.sumFin (fun index =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors index) (.hole
        hole) (values index))) := by
  rw [FiniteSum.Fin.sumFin_congr (fun index =>
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.physical_components (neighbors index)
    (values index)),
    FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_swap
      (fun index hole => Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
        (neighbors index) (.hole hole) (values index))]

/-- The oriented right-minus-left-minus-top-plus-bottom perimeter of one original physical boundary component. -/
def FacePerimeters.componentPerimeter (perimeters :
  Matched.FacePerimeters (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (component :
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent faces) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
    (neighbors.entries.get p).right component
    (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right p)) -
    FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
      p).left component (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
      .left p)) -
    (FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
      p).top component (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
      .top p)) -
      FiniteSum.Fin.sumFin (fun p =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
        p).bottom component (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
        perimeters .bottom p)))

/-- The complete physical perimeter is the exterior component plus every original hole component. -/
theorem FacePerimeters.physicalPerimeter_components (perimeters :
  Matched.FacePerimeters (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) :
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors =
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters.componentPerimeter perimeters
      neighbors .exterior +
      FiniteSum.Fin.sumFin (fun hole =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters.componentPerimeter perimeters
        neighbors (.hole hole)) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter
  rw [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
    p).right),
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
      p).left),
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
      p).top),
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
      p).bottom)]
  simp only [componentPerimeter, FiniteSum.Fin.sumFin_sub]
  ring1

/-- Sum the original physical right and top triangle areas belonging to the specified boundary component on both sheets.
-/
def componentTriangleArea (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (component : Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent faces) :
      Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun sheet =>
    FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
      p).right component
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex p sheet false))) +
    FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
      p).top component
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex p sheet true))))

/-- The physical triangle sum partitions into the original exterior and hole components. -/
theorem physicalTriangleArea_components (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right =
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.componentTriangleArea neighbors left right
      .exterior +
      FiniteSum.Fin.sumFin (fun hole =>
        Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.componentTriangleArea neighbors left right (.hole
        hole)) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea
  rw [FiniteSum.Fin.sumFin_swap]
  simp only [FiniteSum.Fin.sumFin_add]
  rw [FiniteSum.Fin.sumFin_congr (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
        p).right)
        (fun p => Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex p sheet false))),
    FiniteSum.Fin.sumFin_congr (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.component_sum (fun p => (neighbors.entries.get
        p).top)
        (fun p => Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex p sheet true)))]
  simp only [FiniteSum.Fin.sumFin_add]
  rw [FiniteSum.Fin.sumFin_swap (fun sheet hole => FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
        p).right (.hole hole) (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left
        right (mesh.triangleIndex p sheet false)))),
    FiniteSum.Fin.sumFin_swap (fun sheet hole => FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue (neighbors.entries.get
        p).top (.hole hole) (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left
        right (mesh.triangleIndex p sheet true))))]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.componentTriangleArea,
    FiniteSum.Fin.sumFin_add]
  ring1

/-- The normalized physical perimeter of one component minus its original triangle area. -/
def physicalComponentCorrection (perimeters : Matched.FacePerimeters
  (request := request) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (component : Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.PhysicalComponent faces) :
      Gaussian.Basic.Canonical :=
  Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters.componentPerimeter perimeters neighbors
    component - Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.componentTriangleArea neighbors left
    right component

/-- The complete physical correction is the original exterior correction plus the sum of all hole corrections. -/
theorem physicalCorrection_components (perimeters :
  Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors -
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right =
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors
        left right .exterior +
        FiniteSum.Fin.sumFin (fun hole =>
          Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection perimeters
          neighbors left right (.hole hole)) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters.physicalPerimeter_components
    perimeters, Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalTriangleArea_components]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection,
    FiniteSum.Fin.sumFin_sub]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
