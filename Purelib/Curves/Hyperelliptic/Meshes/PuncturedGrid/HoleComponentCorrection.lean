module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Hole corrections read the actual adjacent boxes, without depending on
which certified side-classification witnesses were retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection

attribute [local congr] FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
  (physicalComponentCorrection componentTriangleArea physicalCorrection_components)

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

/-- Keep the original side contribution exactly when its regular box matches the specified original hole box. -/
def holeSideValue (hole : Fin faces.holes.length) (side : Meshes.GridLiftedDualSteps.GridSide)
    (position : Fin faces.regulars.length) (value : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  if side.Matches faces.regulars[position.val].cell.box faces.holes[hole.val].cell.box then value else 0

/-- The original hole perimeter correction minus its actual adjacent triangle areas on both sheets.

Selection uses the retained regular and hole boxes directly, preserving orientation independently of side-classification
witnesses. -/
def holeCorrection (perimeters : Matched.FacePerimeters (request :=
  request) cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (hole : Fin faces.holes.length) : Gaussian.Basic.Canonical :=
  (FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole .right p
    (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right p)) -
    FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole .left p
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left p)) -
    (FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole .top p
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top p)) -
      FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole
        .bottom p (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom
        p)))) -
  FiniteSum.Fin.sumFin (fun sheet =>
    FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole .right
      p (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex p sheet false))) +
    FiniteSum.Fin.sumFin (fun p => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole .top p
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex p sheet true))))

/-- The direct original-box hole correction equals the corresponding certified physical-component correction.

Each original side classification selects precisely the contribution from its
actual adjacent hole box. The retained perimeter and triangle-area sums therefore
agree with the direct box selectors at the same bounded hole position. -/
theorem holeCorrection_eq_component (perimeters :
  Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (hole : Fin faces.holes.length) :
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left
      right (.hole hole) = Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeCorrection perimeters left
      right hole := by
  simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection,
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.FacePerimeters.componentPerimeter,
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.componentTriangleArea,
    Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.SideNeighbor.hole_value_eq,
      Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeCorrection,
      Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue, -eq_self, -iff_self]
  rfl

/-- The complete physical correction is its retained exterior component plus the original-box corrections for every
hole. -/
theorem physicalCorrection_eq_holes (perimeters :
  Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors -
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right =
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors
        left right .exterior +
        FiniteSum.Fin.sumFin (fun hole => Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeCorrection
          perimeters left right hole) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalCorrection_components]
  rw [FiniteSum.Fin.sumFin_congr (fun hole =>
    Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeCorrection_eq_component perimeters neighbors left
    right hole)]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection
