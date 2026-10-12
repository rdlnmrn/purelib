module
import Purelib.Data.List.Append
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

public section

/-! The original branch excursion on an enlarged grid has exactly the
old-cell hole area and two explicit opposite-sheet stem defects. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Curves
open Purelib.Data
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} (bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted)
  {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)

include reference

/-- The original branch-loop subdivision is chain-comparable to its actual resplit stem based around the original cell
boundary. -/
theorem resplit_loop_comparison (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      (included.resplit (bank.rows.get index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      ((included.resplit (bank.rows.get index).stem ((base.bank.cell index).anchor_mem (base.bank.cell_mem
        index))).based
        (included.resplit (bank.rows.get index).boundary ((base.bank.cell index).anchor_mem (base.bank.cell_mem
          index)))) := by
  rw [(bank.rows.get index).reference_eq]
  exact included.resplit_based edges vertices reference _ _
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank) _

omit reference in
/-- Combine the two original stem-hole cross terms into the retained opposite-sheet stem-total remainder. -/
private theorem cross_remainder (stem hole other : Gaussian.Basic.Canonical) :
    Path.BoundaryRibbon.area stem hole + Path.BoundaryRibbon.area (stem + hole) (-other) = Path.BoundaryRibbon.area
      (stem + hole) (-(stem + other)) := by
  apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re,
    Gaussian.Basic.neg_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Both cancellation obligations survive subdivision: the area difference
of the two forward stems and their total increment, with its full multiplier.
The retained hole is the original enclosing cell, not the smaller Newton hole. -/
theorem resplit_loop_area (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (newSheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    let stem := included.resplit (bank.rows.get index).stem ((base.bank.cell index).anchor_mem (base.bank.cell_mem
      index))
    let hole := included.resplit (bank.rows.get index).boundary ((base.bank.cell index).anchor_mem (base.bank.cell_mem
      index))
    let outward := edges.indexedEdges vertices stem newSheet
    let other := edges.indexedEdges vertices stem (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet)
    let boundary := edges.indexedEdges vertices hole (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges stem newSheet)
    Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) =
      Topology.Mesh.RetracingWords.wordArea value boundary + (Topology.Mesh.RetracingWords.wordArea value outward -
        Topology.Mesh.RetracingWords.wordArea value other) +
        Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value outward +
          Topology.Surface.Sewing.SewingRetraction.wordValue value boundary)
          (-(Topology.Surface.Sewing.SewingRetraction.wordValue value outward +
            Topology.Surface.Sewing.SewingRetraction.wordValue value other)) := by
  intro stem hole outward other boundary
  have comparison := bank.resplit_loop_comparison included edges vertices reference index
  have returned : SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges (stem.based hole) newSheet =
    Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet :=
    (comparison.targets newSheet).symm.trans (bank.resplit_branch_target included edges index newSheet)
  rw [Geometry.Grid.Walks.Walk.based, SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges,
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges] at returned
  have arrival : SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges hole (SquareRoot.Grid.EdgeBank.RootEdgeBank.target
    edges stem newSheet) = SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges stem
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet) := by
    apply edges.target_injective reference stem.reverse
    rw [returned, edges.target_reverse reference stem]
  have same := comparison.areas value anti newSheet
  change _ = Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (stem.based hole) newSheet)
    at same
  dsimp only [-eq_self, -iff_self, SquareRoot.Grid.RootEdgeBank.chainArea] at same
  rw [same, Geometry.Grid.Walks.Walk.based, edges.indexedEdges_append, edges.indexedEdges_append, arrival,
    edges.indexedEdges_reverse vertices reference, ← Data.List.Append.append_assoc,
    Topology.Mesh.RetracingWords.wordArea_append, Topology.Mesh.RetracingWords.wordArea_append,
      Topology.Surface.Sewing.SewingRetraction.wordValue_append]
  erw [Topology.Mesh.RetracingWords.wordArea_reverse value anti,
    Topology.Surface.Sewing.SewingRetraction.wordValue_reverse value anti]
  change Topology.Mesh.RetracingWords.wordArea value outward + Topology.Mesh.RetracingWords.wordArea value boundary +
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value outward)
    (Topology.Surface.Sewing.SewingRetraction.wordValue value boundary) +
    -Topology.Mesh.RetracingWords.wordArea value other + Path.BoundaryRibbon.area
      (Topology.Surface.Sewing.SewingRetraction.wordValue value outward +
      Topology.Surface.Sewing.SewingRetraction.wordValue value boundary)
      (-Topology.Surface.Sewing.SewingRetraction.wordValue value other) = _
  have cross := Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.cross_remainder
    (Topology.Surface.Sewing.SewingRetraction.wordValue value outward)
    (Topology.Surface.Sewing.SewingRetraction.wordValue value boundary)
    (Topology.Surface.Sewing.SewingRetraction.wordValue value other)
  rw [← cross]
  ring1

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- Consume the exact internal-area term of the transported corrected
pairing. Every retained label occurs with its actual alternating sheet. -/
theorem resplit_internal_area
    (labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches))
    (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    let branchArea := fun (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (incoming : Fin 2) =>
      let stem := included.resplit (bank.rows.get index).stem ((base.bank.cell index).anchor_mem (base.bank.cell_mem
        index))
      let hole := included.resplit (bank.rows.get index).boundary ((base.bank.cell index).anchor_mem (base.bank.cell_mem
        index))
      let outward := edges.indexedEdges vertices stem incoming
      let other := edges.indexedEdges vertices stem (Hyperelliptic.Branches.BranchCutLifts.otherSheet incoming)
      let boundary := edges.indexedEdges vertices hole (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges stem
        incoming)
      Topology.Mesh.RetracingWords.wordArea value boundary + (Topology.Mesh.RetracingWords.wordArea value outward -
        Topology.Mesh.RetracingWords.wordArea value other) +
        Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value outward +
          Topology.Surface.Sewing.SewingRetraction.wordValue value boundary)
          (-(Topology.Surface.Sewing.SewingRetraction.wordValue value outward +
            Topology.Surface.Sewing.SewingRetraction.wordValue value other))
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
      value labels =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (labels.map (fun pair => branchArea pair.1 newSheet + branchArea pair.2
          (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet))) := by
  intro branchArea
  have branch (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (incoming : Fin 2) :
      Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get index).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming) =
          branchArea index incoming :=
    bank.resplit_loop_area included edges vertices reference index incoming value anti
  induction labels with
  | nil => rfl
  | cons pair rest ih =>
      change (_ + _) + Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges
        vertices bank newSheet value rest =
        (_ + _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (rest.map (fun pair => branchArea pair.1 newSheet + branchArea pair.2
            (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet)))
      rw [branch, branch, ih]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

end
