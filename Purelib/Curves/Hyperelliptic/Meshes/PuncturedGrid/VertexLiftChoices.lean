module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.GridLiftedMesh

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Integration.PuncturedVertexConnections
import Batteries.Logic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.Gaussian

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Meshes

public section

/-!
# Cached actual lifts at a specified grid-vertex sheet

The requested corner is chosen by rational endpoint comparisons, and its
sheet selects one of the two retained root-backed face lifts. Exact bank
positions and the canonical lookup equation are retained for coincidence
steps. No root owners or continuation calculations are reconstructed.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide (start kind)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)

section

namespace Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

/-- The next side in the original counterclockwise rectangle boundary order. -/
@[expose] def next : GridSide → GridSide
  | .bottom => .right
  | .right => .top
  | .top => .left
  | .left => .bottom

/-- The next side starts at the original side's finishing corner. -/
theorem start_next (side : GridSide) (box :
  Rational.Box) : side.next.start box = side.finish box := by cases side <;> rfl

/-- Distinct oriented sides of a proper rectangle have distinct starting corners. -/
theorem start_injective {box : Rational.Box}
  (proper : box.Proper) {first last : GridSide}
    (equal : first.start box = last.start box) : first = last := by
  have x := congrArg (fun vertex : Data.Gaussian.Basic.Canonical => vertex.re) equal
  have y := congrArg (fun vertex : Data.Gaussian.Basic.Canonical => vertex.im) equal
  cases first <;> cases last <;>
    dsimp only [start, kind, Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates] at x y
  all_goals first
    | rfl
    | exact (ne_of_lt proper.1 x).elim
    | exact (ne_of_lt proper.1 x.symm).elim
    | exact (ne_of_lt proper.2 y).elim
    | exact (ne_of_lt proper.2 y.symm).elim

set_option genInjectivity false in
/-- The retained oriented side starting at the displayed original rectangle corner. -/
structure AtCorner (box : Rational.Box)
  (point : Data.Gaussian.Basic.Canonical) where
  /-- The retained oriented side whose starting corner is the displayed point. -/ side : GridSide
  /-- The retained side starts at exactly the displayed original point. -/ start_eq : side.start box = point

constructive_injectivity Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.AtCorner

open Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide (AtCorner)

/-- Select the original side at a certified grid-cell corner by exact coordinate comparisons. -/
@[expose] def atCorner {polynomial :
  ClearPath.GaussianPolynomial} {ambient : Rational.Box}
    (cell : ClearGrid.Cell polynomial ambient) (point : Data.Gaussian.Basic.Canonical) (corner : cell.IsCorner point) :
      AtCorner cell.box point :=
  if left : cell.box.xLower = point.re then
    if lower : cell.box.yLower = point.im then
      ⟨.bottom, congrArg₂ Components.Basic.point left lower⟩
    else ⟨.left, congrArg₂ Components.Basic.point left (corner.2.resolve_left lower)⟩
  else if lower : cell.box.yLower = point.im then
    ⟨.right, congrArg₂ Components.Basic.point (corner.1.resolve_left left) lower⟩
  else ⟨.top, congrArg₂ Components.Basic.point (corner.1.resolve_left left) (corner.2.resolve_left lower)⟩

end Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {face : RegularFace bank} {sheet : Fin 2}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- The next lifted side starts on the original side's finishing sheet. -/
theorem startSheet_next (lifted : LiftedFace
  vertices edges face sheet) (side : GridSide) :
    lifted.sideStartSheet side.next = lifted.sideFinishSheet side := by cases side <;> rfl

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {point : Purelib.Data.Gaussian.Basic.Canonical} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    base.bank.grid} {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

namespace Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident

/-- Select the original side beginning at the retained regular incidence point. -/
@[expose] def corner (regular :
  RegularIncident base point) : GridSide.AtCorner regular.incident.cell.box point :=
  GridSide.atCorner regular.incident.cell point regular.incident.corner

/-- The retained regular-face list position reads back the original incident cell. -/
theorem indexed_cell (regular :
  RegularIncident base point) :
    base.faces.regulars[regular.located.index.val].cell = regular.incident.cell :=
  (congrArg RegularFace.cell regular.located.indexed).trans regular.located.cell_eq

/-- The retained incidence side begins at the original point even through its exact list-position readback. -/
theorem corner_start (regular :
  RegularIncident base point) :
    regular.corner.side.start base.faces.regulars[regular.located.index.val].cell.box = point := by
  rw [regular.indexed_cell]
  exact regular.corner.start_eq

set_option genInjectivity false in
/-- The cached original lifted face at a retained regular corner and requested sheet.

Its lookup equality fixes the exact occurrence selected from the original lifted mesh. -/
structure Lifted (regular :
  RegularIncident base point) (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (requested : Fin 2) where
  /-- The cached original lifted mesh occurrence at this side and requested sheet. -/ value : mesh.AtSide
    regular.located.index regular.corner.side requested
  /-- The cached occurrence is exactly the original mesh lookup at the retained face position and corner side. -/
    value_eq : value = mesh.locateAtSide regular.located.index regular.corner.side requested

constructive_injectivity Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Lifted

/-- Cache the original mesh lookup at the retained regular corner and requested sheet. -/
@[expose] def lift (regular :
  RegularIncident base point) (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (requested : Fin 2) : regular.Lifted mesh requested :=
  ⟨mesh.locateAtSide regular.located.index regular.corner.side requested, rfl⟩

end Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident

section

variable {regular : RegularIncident base point} {requested : Fin 2}

namespace Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Lifted

/-- Every side starting at the retained corner has the requested original lifted sheet there. -/
theorem startSheet_at (lifted :
  regular.Lifted mesh requested) (side : GridSide)
    (atPoint : side.start regular.incident.cell.box = point) :
    lifted.value.located.lifted.sideStartSheet side = requested := by
  have same := GridSide.start_injective regular.incident.cell.box_proper (atPoint.trans regular.corner.start_eq.symm)
  rw [same]
  exact lifted.value.start_eq

/-- Every side finishing at the retained corner has the requested original lifted sheet there. -/
theorem finishSheet_at (lifted :
  regular.Lifted mesh requested) (side : GridSide)
    (atPoint : side.finish regular.incident.cell.box = point) :
    lifted.value.located.lifted.sideFinishSheet side = requested := by
  rw [← lifted.value.located.lifted.startSheet_next]
  exact lifted.startSheet_at side.next ((side.start_next _).trans atPoint)

end Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Lifted

end

end

end
