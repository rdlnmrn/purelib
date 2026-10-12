module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! The corrected B prefix survives subdivision as a literal indexed-word
concatenation, on the same arriving sheet in the enlarged grid. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {sheet : Fin 2}

/-- The original root-closed branch loop has raw winding four. -/
private theorem Inclusion.PairedWords.loop_winding (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    Paths.PreparedPathWinding.ClearPath.rawWinding (bank.liftedLoop index sheet).walk.path = 4 := by
  change Paths.PreparedPathWinding.ClearPath.rawWinding ((bank.rows.get index).reference.walk.castEndpoints _ _).path =
    4
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding]
  exact (bank.rows.get index).reference.winding

/-- Transporting exact retained endpoint indices preserves the original walk's raw winding. -/
private theorem Inclusion.PairedWords.cast_winding {first last nextFirst nextLast : Fin lifted.vertices.count}
    (walk : SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges first last)
    (firstEq : first = nextFirst) (lastEq : last = nextLast) :
    Paths.PreparedPathWinding.ClearPath.rawWinding (walk.castVertices firstEq lastEq).walk.path =
      Paths.PreparedPathWinding.ClearPath.rawWinding walk.walk.path := by
  cases firstEq
  cases lastEq
  rfl

/-- The original concatenated closed branch pair has raw winding eight. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.closed_winding
    {first last : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
    (pair : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
      sheet) : Paths.PreparedPathWinding.ClearPath.rawWinding pair.closed.walk.path = 8 := by
  rw [pair.closed_eq]
  change Paths.PreparedPathWinding.ClearPath.rawWinding (pair.outward.walk.append pair.returning.walk).path = 8
  rw [Geometry.Grid.Winding.Walk.append_winding, pair.outward_eq, pair.returning_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedWords.cast_winding,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedWords.loop_winding,
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedWords.loop_winding]
  rfl

variable {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)

/-- Subdivision of the original closed branch pair returns to its starting sheet in the retained enlarged grid. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_target
    {first last : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
    (pair : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
      sheet) (newSheet : Fin 2) :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges (included.resplit pair.closed.walk
      (lifted.vertices.coordinate_onGrid _)) newSheet = newSheet :=
  SquareRoot.Grid.EdgeBank.RootEdgeBank.target_even edges
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
    (lifted.vertices.coordinate_onGrid _)).toLoop _
    (included.vertex (lifted.vertices.coordinate_onGrid _)) 1
    ((included.resplit_winding _ _).trans (pair.closed_winding.trans (by decide))) newSheet

namespace Paired.PeriodPrograms.Prepared

variable {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet} {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

/-- The literal reference pair precedes the original A prefix even after
subdivision. Root closure of the pair proves the prefix's starting sheet. -/
theorem resplit_b_indexed
    (index : Fin genus) (newSheet : Fin 2) :
    edges.indexedEdges vertices (included.resplit (prepared.bWalk index).closed.walk
      (lifted.vertices.coordinate_onGrid _)) newSheet =
      edges.indexedEdges vertices (included.resplit (paired.row index).row.b.closed.walk
        (lifted.vertices.coordinate_onGrid _)) newSheet ++
      edges.indexedEdges vertices (included.resplit (paired.row index).prior.walk
        (lifted.vertices.coordinate_onGrid _)) newSheet := by
  rw [prepared.b_walk_eq, (paired.row index).row.corrected_eq]
  change edges.indexedEdges vertices (included.resplit
    ((paired.row index).row.b.closed.walk.append (paired.row index).prior.walk) _) newSheet = _
  rw [included.resplit_append _ _ (lifted.vertices.coordinate_onGrid _) _, edges.indexedEdges_append,
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_target included
      edges]

/-- The subdivided original corrected B word retains the reference area, preceding A-prefix area and their actual
cross-area term. -/
theorem resplit_b_area
    (index : Fin genus) (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
      Gaussian.Basic.Canonical) :
    let reference := edges.indexedEdges vertices (included.resplit (paired.row index).row.b.closed.walk
      (lifted.vertices.coordinate_onGrid _)) newSheet
    let priorWord := edges.indexedEdges vertices (included.resplit (paired.row index).prior.walk
      (lifted.vertices.coordinate_onGrid _)) newSheet
    Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (included.resplit (prepared.bWalk
      index).closed.walk
      (lifted.vertices.coordinate_onGrid _)) newSheet) =
      Topology.Mesh.RetracingWords.wordArea value reference + Topology.Mesh.RetracingWords.wordArea value priorWord +
        Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value reference)
          (Topology.Surface.Sewing.SewingRetraction.wordValue value priorWord) := by
  intro reference priorWord
  rw [prepared.resplit_b_indexed included edges vertices]
  exact Topology.Mesh.RetracingWords.wordArea_append value reference priorWord

end Paired.PeriodPrograms.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
