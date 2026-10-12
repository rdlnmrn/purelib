module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! All regular face exteriors split into paired crossings and retained physical sides. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

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

namespace FacePerimeters

/-- Sum the actual retained perimeter contribution on a specified side over both sheets of one original regular face. -/
@[expose] def sideSum (perimeters : Matched.FacePerimeters (request :=
  request) cache i j)
    (side : Meshes.GridLiftedDualSteps.GridSide) (position : Fin faces.regulars.length) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun sheet => match side with
    | .bottom => ((perimeters.perimeters.get position).get sheet).bottom
    | .right => ((perimeters.perimeters.get position).get sheet).right
    | .top => ((perimeters.perimeters.get position).get sheet).top
    | .left => ((perimeters.perimeters.get position).get sheet).left)

/-- The signed total of original side contributions adjacent to regular faces. -/
@[expose] def regularPerimeter (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun p =>
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
    (neighbors.entries.get p).right (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
    perimeters .right p)) -
    FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      (neighbors.entries.get p).left (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
      perimeters .left p)) -
    (FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      (neighbors.entries.get p).top (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
      perimeters .top p)) -
      FiniteSum.Fin.sumFin (fun p =>
        Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        (neighbors.entries.get p).bottom
        (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom p)))

/-- The signed total of original side contributions facing holes or the physical exterior. -/
@[expose] def physicalPerimeter (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun p =>
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
    (neighbors.entries.get p).right (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
    perimeters .right p)) -
    FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      (neighbors.entries.get p).left (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
      perimeters .left p)) -
    (FiniteSum.Fin.sumFin (fun p =>
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      (neighbors.entries.get p).top (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum
      perimeters .top p)) -
      FiniteSum.Fin.sumFin (fun p =>
        NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
        (neighbors.entries.get p).bottom
        (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom p)))

/-- The sum of all retained regular-face exterior values over both sheets. -/
@[expose] def exteriorTotal (perimeters : Matched.FacePerimeters
  (request := request) cache i j) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get p).get sheet).exterior))

/-- The complete retained exterior total splits exactly into regular-neighbor and physical-boundary contributions. -/
theorem exterior_split (perimeters : Matched.FacePerimeters (request
  := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) :
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters =
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.regularPerimeter perimeters neighbors +
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors
      := by
  have face_eq : ∀ p : Fin faces.regulars.length,
      FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get p).get sheet).exterior) =
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom p +
        Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right p -
        Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top p -
          Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left p := by
    intro p
    rw [FiniteSum.Fin.sumFin_congr (fun sheet => ((perimeters.perimeters.get p).get sheet).exterior_eq)]
    simp only [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub,
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum, -eq_self, -iff_self]
    rfl
  have split (side : Meshes.GridLiftedDualSteps.GridSide) : FiniteSum.Fin.sumFin
    (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side) =
      FiniteSum.Fin.sumFin (fun p =>
        Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get p) side)
        (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p)) +
        FiniteSum.Fin.sumFin (fun p =>
          NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
          (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
            (neighbors.entries.get p) side)
          (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p)) := by
      rw [FiniteSum.Fin.sumFin_congr (fun p =>
        Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.value_split
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get p) side)
        (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p)),
          FiniteSum.Fin.sumFin_add]
  unfold Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal
  rw [FiniteSum.Fin.sumFin_congr face_eq]
  simp only [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rw [split .bottom, split .right, split .top, split .left]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.regularPerimeter,
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter,
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at, -eq_self,
      -iff_self]
  ring1

end FacePerimeters

/-- The actual paired crossing perimeter equals the retained regular-neighbor perimeter selected by the original
neighbor bank. -/
theorem CrossingBank.pairedPerimeter_eq_regular (retained :
  Matched.CrossingBank request mesh)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter retained perimeters =
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.regularPerimeter perimeters neighbors :=
      by
  have horizontal : ∀ firstPosition : Fin faces.regulars.length,
      FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun nextPosition =>
        Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
        (((retained.horizontal.get firstPosition).get sheet).get nextPosition))) =
      FiniteSum.Fin.sumFin (fun nextPosition => if Meshes.GridLiftedDualSteps.GridSide.Matches .top
        faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box then
          Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top
            firstPosition - Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
            .bottom nextPosition else 0) := by
    intro firstPosition
    rw [FiniteSum.Fin.sumFin_swap]
    exact FiniteSum.Fin.sumFin_congr (fun nextPosition =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums.CrossingBank.horizontal_pair_sum
        retained perimeters firstPosition nextPosition)
  have vertical : ∀ firstPosition : Fin faces.regulars.length,
      FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun nextPosition =>
        Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
        (((retained.vertical.get firstPosition).get sheet).get nextPosition))) =
      FiniteSum.Fin.sumFin (fun nextPosition => if Meshes.GridLiftedDualSteps.GridSide.Matches .right
        faces.regulars[firstPosition.val].cell.box
        faces.regulars[nextPosition.val].cell.box then
          Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right
            firstPosition - Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
            .left nextPosition else 0) := by
    intro firstPosition
    rw [FiniteSum.Fin.sumFin_swap]
    exact FiniteSum.Fin.sumFin_congr (fun nextPosition =>
      Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums.CrossingBank.vertical_pair_sum
        retained perimeters firstPosition nextPosition)
  unfold Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter
  rw [FiniteSum.Fin.sumFin_congr vertical, FiniteSum.Fin.sumFin_congr horizontal]
  rw [Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.NeighborBank.pair_sum
    neighbors .right (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
    .right) (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left),
    Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.NeighborBank.pair_sum
      neighbors .top (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top)
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom)]
  rfl

/-- The complete original exterior total is the paired crossing perimeter plus its retained physical-boundary
contribution. -/
theorem CrossingBank.exterior_eq_paired_add_physical (retained :
  Matched.CrossingBank request mesh)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) :
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters =
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter retained perimeters +
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors
      := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.CrossingBank.pairedPerimeter_eq_regular retained
    perimeters neighbors]
  exact Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exterior_split perimeters neighbors

namespace CrossingRequests

/-- The original exterior total minus physical sides and retained crossing endpoints meets the paid crossing bound at
every sufficient stage. -/
theorem TotalRequest.exterior_bound {retained : Matched.CrossingBank
  request mesh} {target : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent target floor)
    {samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache} (accounting : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.Accounting
      samples)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors -
      accounting.endpoints) ≤ target := by
  have equal : Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters -
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors =
    Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter retained perimeters := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.CrossingBank.exterior_eq_paired_add_physical retained
      perimeters neighbors]
    ring1
  rw [equal]
  exact Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest.pairedPerimeter_bound
    total accounting perimeters later

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
