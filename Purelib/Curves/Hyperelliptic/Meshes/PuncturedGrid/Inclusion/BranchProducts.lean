module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Exact concatenation and sheet parity for the original branch products
after grid enlargement. No newly selected branch loops are substituted. -/

namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
  {first second : ClearGrid polynomial ambient} (included :
    CoordinateInclusion first second)

/-- Enlarging the grid and resplitting the actual concatenated walk preserves its exact two original path factors. -/
theorem resplit_append {start middle finish : Data.Gaussian.Basic.Canonical}
    (left : Walks.Walk first start middle) (right : Walks.Walk first middle finish)
    (middleMember : FromStates.ContainsVertex first middle) (finishMember : FromStates.ContainsVertex first finish) :
    included.resplit (left.append right) finishMember =
      (included.resplit left middleMember).append (included.resplit right finishMember) := by
  induction left with
  | nil => rfl
  | cons edge tail ih =>
      change (Walks.splitSegment second edge.segment (included.vertex edge.vertices.1) (included.vertex
        edge.vertices.2)).append
        (included.resplit (tail.append right) finishMember) =
          ((Walks.splitSegment second edge.segment (included.vertex edge.vertices.1) (included.vertex
            edge.vertices.2)).append
            (included.resplit tail middleMember)).append (included.resplit right finishMember)
      rw [ih, Walk.append_assoc]

/-- Resplitting commutes with erased transport of the actual original walk endpoints. -/
theorem resplit_castEndpoints {start finish nextStart nextFinish : Data.Gaussian.Basic.Canonical}
    (walk : Walks.Walk first start finish) (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (member : FromStates.ContainsVertex first finish) :
    included.resplit (walk.castEndpoints startEq finishEq) (finishEq ▸ member) =
      (included.resplit walk member).castEndpoints startEq finishEq := by
  cases startEq
  cases finishEq
  rfl

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} (bank :
    BasedBranchBank lifted)
  {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)} (included :
    Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)

/-- The actual winding-one branch loop still exchanges sheets after its edges are subdivided, for either incoming
new-grid sheet. -/
theorem resplit_branch_target (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit (bank.rows.get index).reference.walk (FramedBranchCellBank.baseMember
      base.bank)) sheet =
      BranchCutLifts.otherSheet sheet :=
  RootEdgeBank.target_odd edges _ (included.vertex (FramedBranchCellBank.baseMember base.bank)) 0
    ((included.resplit_winding _ (FramedBranchCellBank.baseMember base.bank)).trans
      ((bank.rows.get index).reference.winding.trans (by decide))) sheet

/-- The enlarged-grid indexed branch product retains the first actual loop and continues the original tail on its
exchanged arriving sheet. -/
theorem resplit_product_cons (index : BranchIsolation.Data.Index branches)
    (rest : List (BranchIsolation.Data.Index branches)) (sheet : Fin 2) :
    edges.indexedEdges vertices (included.resplit (bank.loopProduct (index :: rest)) (FramedBranchCellBank.baseMember
      base.bank)) sheet =
      edges.indexedEdges vertices (included.resplit (bank.rows.get index).reference.walk
        (FramedBranchCellBank.baseMember base.bank)) sheet ++
        edges.indexedEdges vertices (included.resplit (bank.loopProduct rest) (FramedBranchCellBank.baseMember
          base.bank))
          (BranchCutLifts.otherSheet sheet) := by
  change edges.indexedEdges vertices (included.resplit
    ((bank.rows.get index).reference.walk.append (bank.loopProduct rest)) (FramedBranchCellBank.baseMember base.bank))
      sheet = _
  rw [included.resplit_append _ _ (FramedBranchCellBank.baseMember base.bank) (FramedBranchCellBank.baseMember
    base.bank),
    edges.indexedEdges_append, bank.resplit_branch_target]

/-- A pair returns to its incoming sheet before the remaining ordered product. The full edge lists, not just their
integrals, are identified. -/
theorem resplit_product_pair (first last : BranchIsolation.Data.Index branches)
    (rest : List (BranchIsolation.Data.Index branches)) (sheet : Fin 2) :
    edges.indexedEdges vertices (included.resplit (bank.loopProduct (first :: last :: rest))
      (FramedBranchCellBank.baseMember base.bank)) sheet =
      edges.indexedEdges vertices (included.resplit (bank.rows.get first).reference.walk
        (FramedBranchCellBank.baseMember base.bank)) sheet ++
        (edges.indexedEdges vertices (included.resplit (bank.rows.get last).reference.walk
          (FramedBranchCellBank.baseMember base.bank))
          (BranchCutLifts.otherSheet sheet) ++
        edges.indexedEdges vertices (included.resplit (bank.loopProduct rest) (FramedBranchCellBank.baseMember
          base.bank)) sheet) := by
  rw [bank.resplit_product_cons, bank.resplit_product_cons, BranchCutLifts.otherSheet_other]

/-- Keep the entire excursion area and its cross term with the remaining branches. This is the area decomposition used
by the corrected pairing, without treating a one-branch loop as root-closed or area-zero. -/
theorem resplit_product_area (index : BranchIsolation.Data.Index branches)
    (rest : List (BranchIsolation.Data.Index branches)) (sheet : Fin 2)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) :
    let first := edges.indexedEdges vertices (included.resplit (bank.rows.get index).reference.walk
      (FramedBranchCellBank.baseMember base.bank)) sheet
    let tail := edges.indexedEdges vertices (included.resplit (bank.loopProduct rest) (FramedBranchCellBank.baseMember
      base.bank))
      (BranchCutLifts.otherSheet sheet)
    RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (index :: rest)) (FramedBranchCellBank.baseMember base.bank)) sheet) =
      RetracingWords.wordArea value first + RetracingWords.wordArea value tail +
        BoundaryRibbon.area (SewingRetraction.wordValue value first) (SewingRetraction.wordValue value tail) := by
  intro first tail
  rw [bank.resplit_product_cons]
  exact RetracingWords.wordArea_append value first tail

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
