module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! The adjacent retained face side is the actual inward hole edge at the
requested root sheet, even when their clearance payloads differ. -/

section

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.GridSide.Matches

/-- Matching sides identify the opposite-side start with the original side finish. -/
theorem opposite_start {side : Meshes.GridLiftedDualSteps.GridSide} {first last : Rational.Box}
  (matching : side.Matches first last) :
    side.opposite.start last = side.finish first := by
  cases side with
  | bottom => exact Gaussian.Basic.ext matching.2.1.symm matching.2.2.symm
  | right => exact Gaussian.Basic.ext matching.2.2.symm matching.2.1.symm
  | top => exact Gaussian.Basic.ext matching.1.symm matching.2.2.symm
  | left => exact Gaussian.Basic.ext matching.2.2.symm matching.1.symm

/-- Matching sides identify the opposite-side finish with the original side start. -/
theorem opposite_finish {side : Meshes.GridLiftedDualSteps.GridSide} {first last : Rational.Box}
  (matching : side.Matches first last) :
    side.opposite.finish last = side.start first := by
  cases side with
  | bottom => exact Gaussian.Basic.ext matching.1.symm matching.2.2.symm
  | right => exact Gaussian.Basic.ext matching.2.2.symm matching.1.symm
  | top => exact Gaussian.Basic.ext matching.2.1.symm matching.2.2.symm
  | left => exact Gaussian.Basic.ext matching.2.2.symm matching.2.1.symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.GridSide.Matches

end

end

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

/-- The actual original grid edge traversing the specified side of a retained branch hole. -/
@[expose] def side (hole : BranchHole bank) : (side :
  GridSide) →
    Geometry.Grid.Walks.Edge bank.grid (side.start hole.cell.box) (side.finish hole.cell.box)
  | .bottom => hole.cell.bottomSide hole.member
  | .right => hole.cell.rightSide hole.member
  | .top => hole.cell.topSide hole.member
  | .left => hole.cell.leftSide hole.member

end Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole

section

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Two original grid edges with equal endpoints have the same indexed lift at the requested start sheet.

The supplied endpoint reference loops identify the existing cached root transport. -/
public theorem same_endpoints {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient :
  Rational.Box}
    {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {frames : RootFrames grid}
    (edges : SquareRoot.Grid.RootEdgeBank frames) (vertices : SquareRoot.Grid.LiftedVertices.VertexBank
      grid)
    {start finish otherStart otherFinish : Gaussian.Basic.Canonical}
    (first : Geometry.Grid.Walks.Edge grid start finish) (last : Geometry.Grid.Walks.Edge grid otherStart otherFinish)
    (startEq : otherStart = start) (finishEq : otherFinish = finish)
    (firstReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial start)
    (lastReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial finish) (sheet : Fin 2) :
    edges.indexedEdge vertices last sheet = edges.indexedEdge vertices first sheet := by
  cases startEq
  cases finishEq
  exact edges.indexedEdge_eq vertices last first firstReference lastReference sheet

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

end

section

variable {base : Meshes.FramedPuncturedGrid curve branches higher} {lifted : Meshes.LiftedPuncturedGrid base}
  {hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank} {side : Meshes.GridLiftedDualSteps.GridSide}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace

set_option genInjectivity false in
/-- The actual adjacent regular-face lift at a requested inward-hole start sheet.

It retains the original face occurrence and equality with the cached reversed hole edge. -/
structure LiftedSide (adjacent :
  Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole side) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (requested : Fin 2) where
  /-- The retained adjacent face occurrence selected at the requested side-start sheet. -/ selected : lifted.mesh.AtSide
    adjacent.position side.opposite requested
  /-- The selected opposite face side is the cached inward-oriented hole edge. -/ edge_eq :
    selected.located.lifted.quad.edge side.opposite.kind =
    lifted.edges.indexedEdge lifted.vertices (hole.side side).reverse requested

constructive_injectivity LiftedSide

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid
namespace HoleAdjacentFace.LiftedSide

/-- Selection consumes the existing two face lifts and cached root maps.
The requested sheet is the start of the inward-oriented hole edge. -/
@[expose] def build (adjacent :
  Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole side) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (requested : Fin 2) :
      HoleAdjacentFace.LiftedSide adjacent lifted
      requested := by
  let selected := lifted.mesh.locateAtSide adjacent.position side.opposite requested
  refine ⟨selected, ?_⟩
  rw [selected.located.lifted.side_edge_eq, selected.start_eq]
  exact SquareRoot.Grid.RootEdgeBank.same_endpoints lifted.edges lifted.vertices (hole.side
    side).reverse
    (base.faces.regulars[adjacent.position.val].side side.opposite)
    (GridSide.Matches.opposite_start adjacent.matching)
    (GridSide.Matches.opposite_finish adjacent.matching)
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank
      (side.finish hole.cell.box) (hole.side side).vertices.2).toLoop
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank
      (side.start hole.cell.box) (hole.side side).vertices.1).toLoop requested

/-- Equal selected face sheets imply equal requested inward-hole start sheets. -/
theorem sheet_injective {adjacent :
  Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole side} {first last
  : Fin 2}
    (left : HoleAdjacentFace.LiftedSide adjacent
      lifted first) (right :
      HoleAdjacentFace.LiftedSide adjacent lifted
      last)
    (equal : left.selected.sheet = right.selected.sheet) : first = last :=
  left.selected.start_eq.symm.trans
    ((left.selected.located.lifted.sideStartSheet_eq right.selected.located.lifted equal side.opposite).trans
      right.selected.start_eq)

/-- Reading in inward-hole start-sheet order retains both original face
occurrences exactly once; no arbitrary equality of local sheet labels is used. -/
theorem sum_selected {adjacent :
  Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid.HoleAdjacentFace base hole side}
    (sides : (sheet : Fin 2) →
      HoleAdjacentFace.LiftedSide adjacent lifted
      sheet) (values : Fin 2 → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun sheet => values (sides sheet).selected.sheet) =
      FiniteSum.Fin.sumFin values := by
  have different : (sides 0).selected.sheet ≠ (sides 1).selected.sheet :=
    fun equal => (by decide : (0 : Fin 2) ≠ 1) ((sides 0).sheet_injective (sides 1) equal)
  have unequal : (sides 0).selected.sheet.val ≠ (sides 1).selected.sheet.val :=
    fun equal => different (Fin.ext equal)
  have firstBound := (sides 0).selected.sheet.isLt
  have lastBound := (sides 1).selected.sheet.isLt
  simp only [FiniteSum.Fin.sumFin_succ]
  change values (sides 0).selected.sheet + (values (sides 1).selected.sheet + 0) = values 0 + (values 1 + 0)
  by_cases first : (sides 0).selected.sheet.val = 0
  · have last : (sides 1).selected.sheet.val = 1 := by omega
    rw [show (sides 0).selected.sheet = 0 from Fin.ext first,
      show (sides 1).selected.sheet = 1 from Fin.ext last]
  · have first : (sides 0).selected.sheet.val = 1 := by omega
    have last : (sides 1).selected.sheet.val = 0 := by omega
    rw [show (sides 0).selected.sheet = 1 from Fin.ext first,
      show (sides 1).selected.sheet = 0 from Fin.ext last]
    ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace.LiftedSide

end
