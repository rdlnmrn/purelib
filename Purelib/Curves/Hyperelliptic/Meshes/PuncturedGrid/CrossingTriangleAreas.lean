module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerTotal
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCornerFormula
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The fixed-corner sum is an exact sum of the retained source triangle areas. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor

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

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
/-- The original upper triangle area for a matched horizontal crossing, or zero for a separated outcome. -/
@[expose] def HorizontalOutcome.triangleArea (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
      Gaussian.Basic.Canonical :=
  match outcome with
  | .matched _ => Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
    (mesh.triangleIndex firstPosition firstSheet true)
  | .separated _ => 0

/-- The normalized horizontal corner jump is the negative of its retained source triangle area. -/
theorem HorizontalOutcome.cornerJump_eq_triangleArea (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    outcome.cornerJump cache.normalize i j =
      -Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.HorizontalOutcome.triangleArea outcome left right := by
  cases outcome with
  | matched joined =>
    exact Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.normalized_horizontal_jump left right
      firstPosition nextPosition firstSheet joined.crossing.next.sheet
  | separated obstruction => exact (neg_zero).symm

/-- The original lower triangle area for a matched vertical crossing, or zero for a separated outcome. -/
@[expose] def VerticalOutcome.triangleArea (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
      Gaussian.Basic.Canonical :=
  match outcome with
  | .matched _ => Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
    (mesh.triangleIndex firstPosition firstSheet false)
  | .separated _ => 0

/-- The normalized vertical corner jump is its retained source triangle area. -/
theorem VerticalOutcome.cornerJump_eq_triangleArea (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    outcome.cornerJump cache.normalize i j =
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.VerticalOutcome.triangleArea outcome left right := by
  cases outcome with
  | matched joined =>
    exact Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.normalized_vertical_jump left right
      firstPosition nextPosition firstSheet joined.crossing.next.sheet
  | separated obstruction => rfl

/-- The horizontal outcome selects exactly the original upper triangle when its two face boxes match. -/
theorem HorizontalOutcome.triangleArea_eq_if (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.HorizontalOutcome.triangleArea outcome left right =
      if Meshes.GridLiftedDualSteps.GridSide.Matches .top faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box then
        Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex firstPosition firstSheet true) else 0 := by
  cases outcome with
  | matched joined =>
    rw [if_pos (Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.HorizontalCrossing.physical_match joined)];
      rfl
  | separated obstruction =>
      have different : ¬ Meshes.GridLiftedDualSteps.GridSide.Matches .top faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box := by
        intro matching
        cases obstruction with
        | lower different => exact different matching.1
        | upper different => exact different matching.2.1
        | boundary different => exact different matching.2.2
      rw [if_neg different]
      rfl

/-- The vertical outcome selects exactly the original lower triangle when its two face boxes match. -/
theorem VerticalOutcome.triangleArea_eq_if (outcome :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request first nextPosition)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.VerticalOutcome.triangleArea outcome left right =
      if Meshes.GridLiftedDualSteps.GridSide.Matches .right faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box then
        Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex firstPosition firstSheet false) else 0 := by
  cases outcome with
  | matched joined =>
    rw [if_pos (Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.VerticalCrossing.physical_match joined)];
      rfl
  | separated obstruction =>
      have different : ¬ Meshes.GridLiftedDualSteps.GridSide.Matches .right faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box := by
        intro matching
        cases obstruction with
        | lower different => exact different matching.1
        | upper different => exact different matching.2.1
        | boundary different => exact different matching.2.2
      rw [if_neg different]
      rfl

/-- Actual source triangle occurrences selected by retained regular crossings. -/
@[expose] def CrossingBank.triangleArea (retained : Matched.CrossingBank
  request mesh)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
      Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.VerticalOutcome.triangleArea (((retained.vertical.get
      a).get b).get c) left right))) +
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.HorizontalOutcome.triangleArea (((retained.horizontal.get
      a).get b).get c) left right)))

/-- The complete normalized crossing-bank corner jump is the sum of its actual retained source triangle areas. -/
theorem CrossingBank.cornerJump_eq_triangleArea (retained :
  Matched.CrossingBank request mesh)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    retained.cornerJump cache.normalize i j =
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea retained left right := by
  have vertical := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b => FiniteSum.Fin.sumFin_congr (fun c =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.VerticalOutcome.cornerJump_eq_triangleArea
        (((retained.vertical.get a).get b).get c) left right)))
  have horizontal := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b => FiniteSum.Fin.sumFin_congr (fun c =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.HorizontalOutcome.cornerJump_eq_triangleArea
        (((retained.horizontal.get a).get b).get c) left right)))
  unfold Matched.CrossingBank.cornerJump
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea
  rw [vertical, horizontal]
  simp only [FiniteSum.Fin.sumFin_neg, -eq_self, -iff_self]
  ring1

/-- Sum the original triangle areas whose right or top neighbor is a regular face, preserving both sheets. -/
@[expose] def regularTriangleArea (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
      Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      (neighbors.entries.get position).right
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex position sheet false)) +
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      (neighbors.entries.get position).top
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex position sheet true))))

/-- The crossing-bank triangle sum equals the original regular-neighbor triangle sum. -/
theorem CrossingBank.triangleArea_eq_regular (retained :
  Matched.CrossingBank request mesh)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea retained left right =
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.regularTriangleArea neighbors left right := by
  have vertical := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b => FiniteSum.Fin.sumFin_congr (fun c =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.VerticalOutcome.triangleArea_eq_if
        (((retained.vertical.get a).get b).get c) left right)))
  have horizontal := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b => FiniteSum.Fin.sumFin_congr (fun c =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.HorizontalOutcome.triangleArea_eq_if
        (((retained.horizontal.get a).get b).get c) left right)))
  unfold Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea
  rw [vertical, horizontal]
  have verticalMatch (a : Fin faces.regulars.length) (b : Fin 2) :=
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.sum_matching
      (neighbors.entries.get a).right
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex a b false))
  have horizontalMatch (a : Fin faces.regulars.length) (b : Fin 2) :=
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.sum_matching
      (neighbors.entries.get a).top
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex a b true))
  have verticalRows := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b =>
      (by simpa only [List.get_eq_getElem, -eq_self, -iff_self] using verticalMatch a b)))
  have horizontalRows := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun b =>
      (by simpa only [List.get_eq_getElem, -eq_self, -iff_self] using horizontalMatch a b)))
  rw [verticalRows, horizontalRows]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.regularTriangleArea, FiniteSum.Fin.sumFin_add,
    -eq_self, -iff_self]
  rfl

/-- The complementary source triangles touch a hole or the outer frame. -/
@[expose] def physicalTriangleArea (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
      Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      (neighbors.entries.get position).right
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex position sheet false)) +
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      (neighbors.entries.get position).top
      (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
      (mesh.triangleIndex position sheet true))))

/-- Sum both original triangle areas on every regular face and both sheets. -/
@[expose] def fullTriangleArea (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get i) mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get
  j) mesh) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right (mesh.triangleIndex
      position sheet false) +
    Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right (mesh.triangleIndex
      position sheet true)))

/-- The complete original triangle sum partitions into regular-neighbor and physical-boundary triangle sums. -/
theorem fullTriangleArea_partition (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea left right =
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.regularTriangleArea neighbors left right +
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right := by
  have equal := FiniteSum.Fin.sumFin_congr (fun position =>
    FiniteSum.Fin.sumFin_congr (fun sheet =>
      congrArg₂ (fun a b : Gaussian.Basic.Canonical => a + b)
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.value_split
          (neighbors.entries.get position).right
          (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex position sheet false)))
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.value_split
          (neighbors.entries.get position).top
          (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
          (mesh.triangleIndex position sheet true)))))
  unfold Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea
  rw [equal]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.regularTriangleArea,
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea, FiniteSum.Fin.sumFin_add, -eq_self,
    -iff_self]
  ring1

/-- The retained local and corner requests pay the original local-total comparison with physical perimeters and actual
crossing triangles. -/
theorem CrossingRequests.TotalRequest.local_physical_triangle_paid
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      ((target / 4) / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (((target / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j (target / 4))
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea retained left right) ≤ target
        := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.cornerJump_eq_triangleArea retained left
    right]
  exact Hyperelliptic.Meshes.PuncturedGrid.LocalCornerFormula.CrossingRequests.TotalRequest.local_physical_corner_paid
    exterior total corner samples original normalized neighbors positive later cornerLater

/-- The complete original triangle comparison retains the physical perimeter minus its physical-boundary triangle
correction within the paid target. -/
theorem CrossingRequests.TotalRequest.local_full_triangle_paid
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      ((target / 4) / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (((target / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j (target / 4))
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea left right -
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right)) ≤ target
        := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingRequests.TotalRequest.local_physical_triangle_paid
    exterior total corner left right samples original normalized neighbors positive later cornerLater
  rw [Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.CrossingBank.triangleArea_eq_regular retained neighbors
    left right] at estimate
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea left right -
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) =
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
        Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.regularTriangleArea neighbors left right := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea_partition neighbors left right]
    ring1
  rw [equal]
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
