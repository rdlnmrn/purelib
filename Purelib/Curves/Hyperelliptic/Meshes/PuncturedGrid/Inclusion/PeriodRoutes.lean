module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
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
import Purelib.Topology.Polygon.Stokes

public section

/-! Routed edge sums of retained periods on an enlarged grid. Original
fragment ownership and the selected grid-frame sheet are both checked. -/

section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments (IncludedFragments)

open
  LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Riemann.Periods
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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
  {split : IncludedFragments period
    differential minimum target}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets
    domains split.cells split.comparison.request.requests}
  {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {numericalIndex
    : Nat}
  {budgets : FaceMeshBudgets
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) points tolerance domains}
  {numerics : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes

/-- The retained period fragments' canonical route sum equals the whole enlarged-grid walk sum on the sheet selected by
the actual incoming owner. -/
theorem routed_sum (sources : SheetEntries.LiftedSources mesh entries)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex original point) (included :
      Extension.CoordinateInclusion original base.bank.grid)
    (faces : FramedPuncturedGrid.OwnerWalkFaces mesh (included.resplit period.closed.walk member) owner)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((LiftedSources.pieces sources).map (fun piece =>
      RouteContacts.routeValue piece (RouteWords.canonicalRoute piece) shared)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces mesh (included.resplit
        period.closed.walk member) faces.sheet).values
        (fun _ route => FaceSharedMeshes.edgeIncrement shared route)) :=
  (LiftedFragment.movingPieces_sum (LiftedSources.pieces sources) shared).symm.trans
    (OwnerWalkFaces.grouped_read faces (PeriodWords.walk_groups sources member included) rfl shared)

/-- Select the canonical routes once and pay every original fragment. The bound compares the actual original shared
reading to the whole routed grid walk. It does not infer cancellation from coordinate closure. -/
theorem routed_accurate (sources : SheetEntries.LiftedSources mesh entries)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex original point) (included :
      Extension.CoordinateInclusion original base.bank.grid)
    (faces : FramedPuncturedGrid.OwnerWalkFaces mesh (included.resplit period.closed.walk member) owner)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    let request := RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute allowance positive
    ∀ (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (summary : SheetEntries.SharedSum shared entries),
      request.index ≤ numericalIndex →
      (∀ piece ∈ (LiftedSources.pieces sources), piece.first ∈ points ∧ piece.last ∈ points) →
      Data.Gaussian.Norm.Basic.normSq (summary.value -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces mesh (included.resplit
          period.closed.walk member) faces.sheet).values
          (fun _ route => FaceSharedMeshes.edgeIncrement shared route))) < allowance := by
  intro request shared summary later endpoints
  have bound := request.requests.accurate positive shared (request.index_eq ▸ later) endpoints
  have values := RouteRequests.build_values
    (Aggregate.perTerm allowance (LiftedSources.pieces sources).length)
    (Aggregate.perTerm_positive positive _) RouteWords.canonicalRoute (LiftedSources.pieces sources) shared
  change request.requests.values shared = _ at values
  rw [values, PeriodWords.source_sum sources summary,
    routed_sum sources member included faces shared] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes

end
