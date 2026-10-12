module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SegmentWalkGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalStandardFaces
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-! Complete original A/B fragment words read the same standard routed
increments, with the initial sheet justified by the actual retained owner. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
open Purelib.LinearAlgebra.Alternating
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels
open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational} {first last : Purelib.Data.Gaussian.Basic.Canonical} {walk
    : Purelib.Polynomial.Geometry.Grid.Walks.Walk base.bank.grid first last}
  {owner : Owner (curve.polynomial.eval first)}
  {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {index : Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.OwnerWalkFaces

/-- Equal grid vertices read the same retained frame-owner name on a fixed sheet. -/
private theorem frameNames_eq (frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid) {first last :
  Data.Gaussian.Basic.Canonical}
    (equal : first = last) (firstMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (lastMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last) (sheet : Fin 2) :
    OwnerTraceReadings.ownerName ((frames.frameAt first firstMember).owners sheet) = OwnerTraceReadings.ownerName
      ((frames.frameAt last lastMember).owners sheet) := by
  cases equal
  rfl

/-- The retained owner classification supplies the initial root for the entire standard walk fold. No incoming
sheet-alignment premise is left. -/
theorem grouped_read (faces : FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
    {firstName lastName : Gaussian.Name.Basic.Named}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (groups : Fragment.WalkGroups walk firstName lastName pieces)
    (rootEq : OwnerTraceReadings.ownerName owner = firstName) (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
      :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => RouteContacts.routeValue piece
      (RouteWords.canonicalRoute piece) shared)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces mesh walk faces.sheet).values
        (fun _ route => FaceSharedMeshes.edgeIncrement shared route)) := by
  let vertex := vertices.index first faces.first faces.sheet
  have coordinate : vertices.coordinate vertex = first := vertices.coordinate_index _ faces.first _
  have names : OwnerTraceReadings.ownerName (vertices.owner frames vertex) = OwnerTraceReadings.ownerName
    ((frames.frameAt first faces.first).owners faces.sheet) := by
    change OwnerTraceReadings.ownerName ((frames.frameAt (vertices.coordinate vertex) (vertices.coordinate_onGrid
      vertex)).owners (vertices.sheet vertex)) = _
    rw [show vertices.sheet vertex = faces.sheet from vertices.sheet_index _ faces.first _]
    exact frameNames_eq frames
      coordinate _ faces.first faces.sheet
  obtain ⟨aligned⟩ := faces.aligned
  have root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
    firstName := by
    rw [names, ← rootEq]
    exact aligned.symm
  obtain ⟨_, _, _, _, total⟩ := Fragment.WalkGroups.read groups vertex coordinate root shared
  simpa only [vertex, vertices.sheet_index, -eq_self, -iff_self] using total

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.OwnerWalkFaces

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.StandardBoundaryReadings

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
open Purelib.LinearAlgebra.Alternating
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings (StandardBoundaryReadings)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Rational} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {extraPoints : List Purelib.Data.Gaussian.Basic.Canonical}

/-- The retained moving A fragments form the original A walk, with both root names preserved. -/
theorem a_walkGroups (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains
  extraPoints) :
    Fragment.WalkGroups row.pair.aWalk row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.aWord.pieces) := by
  have words := (congrArg (fun source : PreparedOwnerClosedBridges.OwnerClosedCyclePair curve =>
    SourceWords.TourSourceWords source.aTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.aWord.pieces)) row.source_eq).mpr readings.a_movingSourceWords
  have groups := TourSourceWords.walk_groups words (fun _ member => (LiftedFragment.movingPieces_mem member).2)
    row.pair.aOnGrid
  exact (congrArg (fun walk => Fragment.WalkGroups walk row.period.tours.root row.period.tours.root
    (LiftedFragment.movingPieces readings.aWord.pieces)) row.pair.aWalk_eq).mpr groups

/-- The retained moving B fragments form the original B walk, with both root names preserved. -/
theorem b_walkGroups (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains
  extraPoints) :
    Fragment.WalkGroups row.pair.bWalk row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.bWord.pieces) := by
  have words := (congrArg (fun source : PreparedOwnerClosedBridges.OwnerClosedCyclePair curve =>
    SourceWords.TourSourceWords source.bTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.bWord.pieces)) row.source_eq).mpr readings.b_movingSourceWords
  have groups := TourSourceWords.walk_groups words (fun _ member => (LiftedFragment.movingPieces_mem member).2)
    row.pair.bOnGrid
  exact (congrArg (fun walk => Fragment.WalkGroups walk row.period.tours.root row.period.tours.root
    (LiftedFragment.movingPieces readings.bWord.pieces)) row.pair.bWalk_eq).mpr groups

/-- Equality of the full original A route sum with the standard lookup. -/
theorem a_standard_routes_sum (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target
  domains extraPoints) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces lifted.mesh row.pair.aWalk
      row.pair.aFaces.sheet).values
      (fun _ route => FaceSharedMeshes.edgeIncrement readings.original.shared.meshes route)) = readings.aRoutes.sum :=
        by
  have total := Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.OwnerWalkFaces.grouped_read
    row.pair.aFaces
    (a_walkGroups readings)
    (row.pair.source.aRoot_eq.trans (congrArg OwnerClosedCyclePair.root row.source_eq)) readings.original.shared.meshes
  exact total.symm.trans readings.a_moving_sum

/-- The B fold uses its retained incoming owner and all four original legs. -/
theorem b_standard_routes_sum (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target
  domains extraPoints) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces lifted.mesh row.pair.bWalk
      row.pair.bFaces.sheet).values
      (fun _ route => FaceSharedMeshes.edgeIncrement readings.original.shared.meshes route)) = readings.bRoutes.sum :=
        by
  have total := Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.OwnerWalkFaces.grouped_read
    row.pair.bFaces
    (b_walkGroups readings)
    (row.pair.source.bRoot_eq.trans (congrArg OwnerClosedCyclePair.root row.source_eq)) readings.original.shared.meshes
  exact total.symm.trans readings.b_moving_sum

/-- For canonical A face lookup, the cached boundary reading equals the complete retained A route sum. -/
theorem a_routes_value (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains
  extraPoints)
    (canonical : row.pair.aFaces.geometry = SkeletonFaceAssignments.walkFaces lifted.mesh row.pair.aWalk
      row.pair.aFaces.sheet) :
    readings.a.value = readings.aRoutes.sum := by
  rw [readings.a.value_eq, readings.a.values_eq, canonical]
  exact
    a_standard_routes_sum
    readings

/-- For canonical B face lookup, the cached boundary reading equals the complete retained B route sum. -/
theorem b_routes_value (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains
  extraPoints)
    (canonical : row.pair.bFaces.geometry = SkeletonFaceAssignments.walkFaces lifted.mesh row.pair.bWalk
      row.pair.bFaces.sheet) :
    readings.b.value = readings.bRoutes.sum := by
  rw [readings.b.value_eq, readings.b.values_eq, canonical]
  exact
    b_standard_routes_sum
    readings

/-- The actual row producer uses the canonical lookup; its boundary reader therefore needs no caller-provided transport
equality. -/
theorem a_routes_value_ofPeriod
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (RootClosedPeriodBank.ofData curve branches).rows index)
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints) : readings.a.value = readings.aRoutes.sum :=
  a_routes_value readings
    (IntersectionRow.ofPeriod_a_canonical normal period periodEq)

/-- The actual period-row producer supplies canonical B lookup, so its cached reading equals the route sum without an
extra transport premise. -/
theorem b_routes_value_ofPeriod
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (RootClosedPeriodBank.ofData curve branches).rows index)
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints) : readings.b.value = readings.bRoutes.sum :=
  b_routes_value readings
    (IntersectionRow.ofPeriod_b_canonical normal period periodEq)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.StandardBoundaryReadings
