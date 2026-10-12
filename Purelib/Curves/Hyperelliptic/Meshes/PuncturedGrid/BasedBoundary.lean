module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.Topology.Polygon.Stokes
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Joining
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundary

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-!
# One based walk for the lifted exterior and branch-hole tours

All tours are joined at sheet zero of the retained ambient anchor.  Each
branch-hole tour keeps its actual two laps; in even degree the second
exterior tour is brought to that same owner along a checked connector.
Connector/return pairs cancel exactly for arbitrary shared-vertex values.

The resulting walk is a based representative of the boundary sum, not a
claim that these connectors are disjoint cuts or that this ordered word is
already the fundamental-polygon A/B relation.
-/

section

open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append sumValues_map sumValues_congr)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- An original lifted grid walk from the retained ambient anchor on sheet zero back to that same indexed owner. -/
abbrev BasedLoop (lifted : Meshes.LiftedPuncturedGrid base) :=
  RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 0 (Cuts.Ambient curve).anchor 0

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBoundary

/-- Construct a winding-one reference from the original retained branch bank at the requested grid vertex. -/
public def reference (_lifted : Meshes.LiftedPuncturedGrid base) (point : Data.Gaussian.Basic.Canonical) (member :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point) :
    OwnerLoopMonodromy.WindingOneLoop curve.polynomial point :=
  BranchCellBank.referenceAt base.bank.toBranchCellBank point member |>.toLoop

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBoundary

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The canonical bridge between the two actual exterior base owners. Only cached grid transports are queried; a
nontrivial path changes sheets. -/
def exteriorSheetBridge (lifted : Meshes.LiftedPuncturedGrid base) :
    RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 0 (Cuts.Ambient curve).anchor 1 :=
  base.bank.toBranchCellBank.connectSheets lifted.edges _ _
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0 1

/-- Retain the original exterior tours based at the ambient sheet-zero anchor.

Odd degree uses one double lap; even degree brings the original second-sheet lap back through the retained sheet bridge.
-/
def basedExteriorLoops (lifted : Meshes.LiftedPuncturedGrid base) :
  List lifted.BasedLoop :=
  match curve.degreeShape with
  | .odd degree =>
      [⟨base.bank.exterior.append base.bank.exterior,
        ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩, ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩,
        lifted.exterior_double_return_odd degree 0⟩]
  | .even degree =>
      let zero : lifted.BasedLoop := ⟨base.bank.exterior,
        ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩, ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩,
        lifted.exterior_return_even degree 0⟩
      let one : RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 1 (Cuts.Ambient curve).anchor 1 :=
        ⟨base.bank.exterior,
        ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩, ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩,
        lifted.exterior_return_even degree 1⟩
      let bridge := lifted.exteriorSheetBridge
      [zero, bridge.conjugate one (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBoundary.reference lifted)]

open Purelib.Riemann.Meshes.LiftedPuncturedGrid (basedExteriorLoops)

/-- The retained based exterior loops have exactly the original two-sheet exterior area. -/
theorem basedExteriorLoops_area (lifted : Meshes.LiftedPuncturedGrid
  base) (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    CellBoundary.sumValues (fun loop => loop.area lifted.vertices primitive) lifted.basedExteriorLoops =
      lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior := by
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [basedExteriorLoops, shape, CellBoundary.sumValues, LiftedWalk.area]
      rw [lifted.edges.indexedEdges_append, lifted.exterior_swap_odd degree, BranchCutLifts.otherSheet_zero,
        Stokes.edgeListArea_append]
      change _ + _ + 0 = _ + _
      ring1
  | even _ =>
      simp only [basedExteriorLoops, shape, CellBoundary.sumValues]
      rw [LiftedWalk.conjugate_area]
      simp only [LiftedWalk.area, RootEdgeBank.twoSheetArea]
      ring1

/-- Accept any generated or retained connector satisfying the actual sheet equation, then append the original two-lap
hole tour and its exact return. -/
def basedHoleOfConnector (lifted : Meshes.LiftedPuncturedGrid base)
  (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (connector : RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 0 hole.cell.box.anchor 0) :
      lifted.BasedLoop :=
  let loop : RootEdgeBank.LiftedWalk lifted.edges hole.cell.box.anchor 0 hole.cell.box.anchor 0 :=
    ⟨hole.doubleBoundary, Cell.anchor_mem hole.cell hole.member, Cell.anchor_mem hole.cell hole.member,
      hole.doubleBoundary_return lifted.edges 0⟩
  connector.conjugate loop (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBoundary.reference lifted)

open Purelib.Riemann.Meshes.LiftedPuncturedGrid (basedHoleOfConnector)

/-- The retained based hole loop has exactly its original two-sheet inward boundary area after connector cancellation.
-/
theorem basedHoleOfConnector_area (lifted : Meshes.LiftedPuncturedGrid
  base) (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (connector : RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 0 hole.cell.box.anchor 0)
    (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    (lifted.basedHoleOfConnector hole connector).area lifted.vertices primitive =
      lifted.edges.twoSheetArea lifted.vertices primitive hole.inwardBoundary := by
  rw [basedHoleOfConnector, LiftedWalk.conjugate_area]
  exact hole.liftedBoundary_area lifted.vertices lifted.edges primitive

/-- Construct a based original hole tour using the retained grid's sheet-zero connector and exact return. -/
def basedHole (lifted : Meshes.LiftedPuncturedGrid base) (hole :
  PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) : lifted.BasedLoop :=
  let connector := base.bank.toBranchCellBank.connectSheets lifted.edges _ _
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ (Cell.anchor_mem hole.cell hole.member) 0 0
  lifted.basedHoleOfConnector hole connector

/-- The constructed based hole tour preserves the original two-sheet inward boundary area. -/
theorem basedHole_area (lifted : Meshes.LiftedPuncturedGrid base)
  (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    (lifted.basedHole hole).area lifted.vertices primitive = lifted.edges.twoSheetArea lifted.vertices primitive
      hole.inwardBoundary := by
  let connector : RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor 0 hole.cell.box.anchor 0 :=
    base.bank.toBranchCellBank.connectSheets lifted.edges _ _
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ (Cell.anchor_mem hole.cell hole.member) 0 0
  exact lifted.basedHoleOfConnector_area hole connector primitive

/-- The original based exterior tours followed by the retained hole tours in their original bank order. -/
def basedLoops (lifted : Meshes.LiftedPuncturedGrid base) : List
  lifted.BasedLoop :=
  lifted.basedExteriorLoops ++ base.faces.holes.map lifted.basedHole

/-- The materialized input loops and the final joined walk can both be retained by callers. No owner acquisition or root
preparation is repeated. -/
def joinBasedLoops (lifted : Meshes.LiftedPuncturedGrid base) (loops :
  List lifted.BasedLoop) : lifted.BasedLoop :=
  LiftedWalk.concatenate lifted.edges (Cuts.Ambient curve).anchor ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0
    loops

/-- Join the retained original exterior and hole tours into one walk at the ambient sheet-zero anchor. -/
def basedBoundary (lifted : Meshes.LiftedPuncturedGrid base) :
  lifted.BasedLoop := lifted.joinBasedLoops lifted.basedLoops

open Purelib.Riemann.Meshes.LiftedPuncturedGrid (basedBoundary)

/-- The retained joined boundary word closes at the exact original indexed ambient sheet-zero anchor. -/
theorem basedBoundary_closed (lifted : Meshes.LiftedPuncturedGrid
  base) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (lifted.edges.indexedEdges lifted.vertices
      lifted.basedBoundary.walk 0)
      (lifted.vertices.index (Cuts.Ambient curve).anchor ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0)
      (lifted.vertices.index (Cuts.Ambient curve).anchor ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ 0) :=
  lifted.basedBoundary.endpoints lifted.vertices

open Purelib.Riemann.Meshes.LiftedPuncturedGrid (joinBasedLoops basedLoops)

/-- The original mesh boundary sum is carried by one actual based walk, with all added connector/return contributions
exactly cancelled. -/

theorem boundary_eq_basedBoundary (lifted : Meshes.LiftedPuncturedGrid
  base) (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive lifted.mesh.triangulation.boundary = lifted.basedBoundary.area lifted.vertices
      primitive := by
  rw [basedBoundary, joinBasedLoops,
    LiftedWalk.concatenate_area, basedLoops, CellBoundary.sumValues_append,
    lifted.basedExteriorLoops_area, CellBoundary.sumValues_map, lifted.boundary_eq_exterior_and_holes]
  exact congrArg (fun holes => lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior + holes)
    (CellBoundary.sumValues_congr _ _ _ (fun hole _ => (lifted.basedHole_area hole primitive).symm))

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end
