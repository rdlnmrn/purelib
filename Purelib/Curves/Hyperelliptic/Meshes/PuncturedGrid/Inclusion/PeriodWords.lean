module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SegmentWalkGroups
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates

public section

/-! Original corrected-path grouping survives both scheduled refinement and
splitting on an enlarged grid. The actual parent roots certify every join. -/

section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathSources
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid
open Purelib.Riemann.Topology.PreparedRecastRootChains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open
  LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords (PathSourceWords)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments (IncludedFragments)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {original : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)} {point : Purelib.Data.Gaussian.Basic.Canonical}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval point)} {source :
    Differential genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
    curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve branches higher}
  {period : PeriodWalk original point owner source} {differential :
    Fin genus}
  {minimum : Nat} {target : Rational}
  {split : IncludedFragments (base := base)
    period differential minimum target}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets
    domains split.cells split.comparison.request.requests}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodWords

/-- The retained refined and recast parent bank consists of sources for the original closed period path. -/
theorem path_sources (split : PeriodFragments.IncludedFragments (base := base) period differential minimum target) :
    PreparedPathSources.PathSources 0 period.closed.walk.path
      (split.comparison.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
  have initial : PreparedPathSources.PathSources 0 period.closed.walk.path period.initial.state.parents := by
    rw [period.initial_eq, RootClosedWalk.initial_parents]
    exact PathSources.ofPreparedPath source 0 period.closed.traced.prepared
  apply (initial.recast (PeriodMatrix.standardDifferential differential)).refine
  apply DirectedRefinement.recast
  rw [split.comparison.cover.retained.current_eq]
  exact RootClosedState.statesDirected
    period.initial (PreparedRefinementProgramCore.standardDifferentials genus) _

/-- The displayed source path is the retained program's path, not a freshly prepared Newton-grid loop with merely
matching coordinates. -/
theorem source_words (sources : SheetEntries.LiftedSources mesh entries) :
    SourceWords.PathSourceWords period.closed.walk.path (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName owner)
      (LiftedSources.pieces sources) :=
  PathSourceWords.ofParents (path_sources split)
    (LiftedSources.parentGroups sources)
    (RootChain.recast
      (PeriodMatrix.standardDifferential differential) split.comparison.cover.retained.current.roots)

/-- The actual moving source fragments group along the original period walk resplit on the enlarged grid.

Both endpoint names retain the same original root owner, with stationary pieces removed by their certified source-word
transport. -/
theorem walk_groups (sources : SheetEntries.LiftedSources mesh entries)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex original point) (included :
      Extension.CoordinateInclusion original base.bank.grid) :
    Fragment.WalkGroups (included.resplit period.closed.walk member)
      (OwnerTraceReadings.ownerName owner) (OwnerTraceReadings.ownerName owner)
      (LiftedFragment.movingPieces
        (LiftedSources.pieces sources)) :=
  (source_words sources).moving.walk_groups
    (fun _ present => (LiftedFragment.movingPieces_mem present).2)
    (included.path _ (period.closed.walk.vertices member))

/-- Flattening the certified source spine preserves the shared reading exactly, before any routed-edge or seam error is
paid. -/
theorem source_sum (sources : SheetEntries.LiftedSources mesh entries)
    {points : List Data.Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
    {budgets : CommonMeshes.FaceMeshBudgets (PeriodMatrix.standardDifferential differential) points tolerance domains}
    {numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) numericalIndex domains}
    {shared : CommonMeshes.FaceSharedMeshes budgets numerics} (reading : SheetEntries.SharedSum shared entries) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((LiftedSources.pieces sources).map
      (fun piece => piece.value shared)) = reading.value := by
  rw [← LiftedSources.values_eq_pieces sources shared]
  exact sources.sum_eq reading

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodWords

end
