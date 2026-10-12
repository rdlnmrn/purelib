module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.CellBoundary
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Integration.Path

open Purelib.Integration.Path.Paired

open Purelib.Polynomial.Geometry.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! The original physical exterior and original corrected A/B walks on
one enlarged root bank. All regular, branch, terminal and reference areas
remain explicit in the full ordered-period identity. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea (resplitInternalArea resplitReadings)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)

include reference

/-- The actual kept circuit product and original ordered branch-loop product have the same indexed chain comparison on
the enlarged grid. -/
theorem Ordered.resplit_comparison (ordered : BasedBranchBank.Ordered bank sheet) :
    ChainComparison edges vertices
      (included.resplit ordered.prepared.partition.kept.product (FramedBranchCellBank.baseMember base.bank))
      (included.resplit (bank.loopProduct ordered.prepared.labels) (FramedBranchCellBank.baseMember base.bank)) := by
  have stems : CellCircuits.ResplitAscendingStems included edges vertices ordered.prepared.ordered.tree := by
    rw [ordered.prepared.ordered.tree_eq]
    exact Window.resplit_ascending_stems included edges vertices ordered.window
  have same := (CircuitPartition.resplit_kept_stems ordered.prepared.partition stems).canonicalize_comparison reference
    (FramedBranchCellBank.baseMember base.bank)
  exact same.trans (ChainComparison.of_eq
    (congrArg (fun walk => included.resplit walk (FramedBranchCellBank.baseMember base.bank))
      ((bank.canonicalized_product ordered.prepared.partition).trans
        (congrArg bank.loopProduct ordered.prepared.labels_eq.symm))))

/-- The actual enlarged-grid exterior area splits into the original ordered branch area and all retained regular and
connector corrections. -/
theorem Ordered.resplit_exterior_branch_areas (ordered : BasedBranchBank.Ordered bank sheet) {newSheet : Fin 2}
    (compiled : CircuitPartition.ResplitCompiled included edges vertices (FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    edges.chainArea vertices value (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank))
      newSheet =
      RetracingWords.wordArea value (edges.indexedEdges vertices
        (included.resplit (bank.loopProduct ordered.prepared.labels) (FramedBranchCellBank.baseMember base.bank))
          newSheet) +
        AreaTerm.total value compiled.areaTerms := by
  rw [ordered.resplit_exterior_areas included edges vertices reference compiled value anti, compiled.word_eq]
  exact congrArg (fun branchArea => branchArea + AreaTerm.total value compiled.areaTerms)
    ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.Ordered.resplit_comparison included edges
      vertices reference ordered).areas value anti newSheet)

omit reference in
/-- Resplitting an ordered sequence of actual branch pairs returns to its original starting root sheet. -/
private theorem pairs_target (labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches))
    (newSheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit (bank.loopProduct (labels.flatMap (fun pair => [pair.1, pair.2])))
      (FramedBranchCellBank.baseMember base.bank))
      newSheet = newSheet := by
  induction labels with
  | nil => rfl
  | cons pair tail ih =>
      change RootEdgeBank.target edges (included.resplit
        ((bank.rows.get pair.1).reference.walk.append ((bank.rows.get pair.2).reference.walk.append
          (bank.loopProduct (tail.flatMap (fun pair => [pair.1, pair.2]))))) (FramedBranchCellBank.baseMember
            base.bank)) newSheet = newSheet
      rw [included.resplit_append _ _ (FramedBranchCellBank.baseMember base.bank) (FramedBranchCellBank.baseMember
        base.bank),
        included.resplit_append _ _ (FramedBranchCellBank.baseMember base.bank) (FramedBranchCellBank.baseMember
          base.bank),
        RootEdgeBank.target_append edges, RootEdgeBank.target_append edges, bank.resplit_branch_target,
          bank.resplit_branch_target,
        BranchCutLifts.otherSheet_other]
      exact ih

namespace Ordered.Paired.Prepared

variable {paired : Paired ordered}
  (prepared : Prepared paired)

/-- The corrected ordered A/B pairing now consumes the original physical exterior on this very grid. This is the
complete area identity, not a claim that its physical or regular residual terms vanish. -/
theorem resplit_exterior_area_formula (newSheet : Fin 2)
    (compiled : CircuitPartition.ResplitCompiled included edges vertices (FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    let ending := edges.indexedEdges vertices
      (included.resplit (bank.loopProduct paired.split.ending.labels) (FramedBranchCellBank.baseMember base.bank))
        newSheet
    edges.chainArea vertices value (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank))
      newSheet +
      FiniteSum.Fin.sumFin (fun index : Fin genus => BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) =
      PairedArea.resplitInternalArea included edges vertices bank newSheet value paired.split.pairs +
        RetracingWords.wordArea value ending +
        BoundaryRibbon.area (Increments.total (PairedArea.resplitReadings included edges vertices bank newSheet value
          paired.split.pairs))
          (SewingRetraction.wordValue value ending + SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
              (FramedBranchCellBank.baseMember base.bank))
            (BranchCutLifts.otherSheet newSheet))) +
        (CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value occurrence.word) compiled.regulars +
          AreaTerm.total value compiled.connectorTerms) := by
  intro ending
  have split := congrArg bank.loopProduct paired.split.labels_eq
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.Ordered.resplit_exterior_branch_areas included
    edges vertices reference ordered compiled value anti,
    split, bank.loopProduct_append, included.resplit_append _ _ (FramedBranchCellBank.baseMember base.bank)
      (FramedBranchCellBank.baseMember base.bank),
    edges.indexedEdges_append, Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.pairs_target included
      edges]
  have formula := prepared.resplit_area_formula included edges vertices newSheet value ending
  calc
    _ = (RetracingWords.wordArea value (edges.indexedEdges vertices
        (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
          (FramedBranchCellBank.baseMember base.bank))
        newSheet ++ ending) +
        FiniteSum.Fin.sumFin (fun index : Fin genus => BoundaryRibbon.area
          (SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
          (SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet)))) +
        AreaTerm.total value compiled.areaTerms := by ring1
    _ = _ := by
      rw [formula, compiled.area_split]

end Ordered.Paired.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
