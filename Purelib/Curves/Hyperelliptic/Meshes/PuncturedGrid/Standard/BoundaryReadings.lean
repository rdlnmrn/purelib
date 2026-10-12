module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedTourSources
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SourceAncestry
import Init.Data.List.Basic
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-!
# Original standard periods and routed boundary words in one numerical bank

The original A/B requests and their actual retained face words read the same
fine meshes and primitive data. Corner and integration errors are selected
below the request. The remaining difference between the two fine-mesh path
sums is retained explicitly; it is not erased by root or coordinate closure.
-/

section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open
  LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open
  RegularPrimitiveSplits.SheetEntries.LiftedSources
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
open
  WordPoints.ClearGrid.RegularPrimitiveSplits.SheetEntries.LiftedSources
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedTourSources
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
open Purelib.Riemann.Topology.PreparedRecastRootChains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods (RequestedSharedReadings)

open
  LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm countCoordinate countCoordinate_eq)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)

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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings

set_option genInjectivity false in
/-- The complete grid-coordinate bank is included before any mesh is built, so every retained routed corner has a
certified fine-mesh reading. -/
structure StandardBoundaryReadings (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin
  genus)
    (minimum : Nat) (target : Fraction.Rational) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars)
    (extraPoints : List Data.Gaussian.Basic.Canonical) : Type 3 where
  /-- The original complete standard-boundary tolerance is strictly positive. -/ positive : 0 < target
  /-- The cached combined number of original A and B routed face occurrences. -/ count : Nat
  /-- The count is exactly the sum of the original two routed face-word lengths. -/ count_eq : count =
    row.pair.aFaces.geometry.indexed.length + row.pair.bFaces.geometry.indexed.length
  /-- The original A/B period readings sharing one numerical bank and the complete retained grid-coordinate and
    extra-point list. -/ original : RequestedStandardPeriods.RequestedSharedReadings row differential minimum
    (Aggregate.perTerm (target / 16) count) domains
    (List.ofFn lifted.vertices.coordinate ++ extraPoints)
  /-- The retained requested lower bound on the common numerical stage. -/ numericalFloor : Nat
  /-- The actual original shared bank stage pays that retained numerical floor. -/ numericalFloor_le : numericalFloor ≤
    original.shared.numericalIndex
  /-- The actual rooted original A fragment word with both retained endpoint owners. -/ aWord : LiftedSources.Rooted
    original.assignments.a lifted.mesh
    original.comparison.a.cover.retained.current.state.start.coordinate row.period.tours.root
    original.comparison.a.cover.retained.current.state.finish.coordinate row.period.tours.root
  /-- The actual rooted original B fragment word with both retained endpoint owners. -/ bWord : LiftedSources.Rooted
    original.assignments.b lifted.mesh
    original.comparison.b.cover.retained.current.state.start.coordinate row.period.tours.root
    original.comparison.b.cover.retained.current.state.finish.coordinate row.period.tours.root
  /-- The original A parent chain's directed source refinement after recasting to the retained differential. -/
    a_ancestry : PreparedDirectedRootRefinements.DirectedRefinement
    (row.period.aInitial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential
      differential)))
    (original.comparison.a.cover.retained.current.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential)))
  /-- The original B parent chain's directed source refinement after recasting to the retained differential. -/
    b_ancestry : PreparedDirectedRootRefinements.DirectedRefinement
    (row.period.bInitial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential
      differential)))
    (original.comparison.b.cover.retained.current.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential)))
  /-- The retained canonical-route requests for every original A fragment. -/ aRouteRequest : RouteWords.RouteRequest
    aWord.pieces (target / 16)
  /-- The retained canonical-route requests for every original B fragment. -/ bRouteRequest : RouteWords.RouteRequest
    bWord.pieces (target / 16)
  /-- The cached original A route readings on the shared numerical mesh bank. -/ aRoutes : aRouteRequest.Readings
    original.shared.meshes
  /-- The cached original B route readings on the shared numerical mesh bank. -/ bRoutes : bRouteRequest.Readings
    original.shared.meshes
  /-- The cached A route values equal the actual retained canonical fragment readings in original order. -/ aRoutes_eq :
    aRoutes.values = aWord.pieces.map (fun piece => RouteContacts.routeValue piece (RouteWords.canonicalRoute piece)
    original.shared.meshes)
  /-- The cached B route values equal the actual retained canonical fragment readings in original order. -/ bRoutes_eq :
    bRoutes.values = bWord.pieces.map (fun piece => RouteContacts.routeValue piece (RouteWords.canonicalRoute piece)
    original.shared.meshes)
  /-- The actual closed original A chart transition bank on those same cached meshes. -/ aSeams :
    SeamReadings.ClosedSeams original.shared.meshes aWord.pieces
  /-- The actual closed original B chart transition bank on those same cached meshes. -/ bSeams :
    SeamReadings.ClosedSeams original.shared.meshes bWord.pieces
  /-- The original A root junctions remain valid across the complete word and its closing repetition. -/ a_junctions :
    WordJunctions.Junctions (aWord.pieces ++ aWord.pieces)
  /-- The original B root junctions remain valid across the complete word and its closing repetition. -/ b_junctions :
    WordJunctions.Junctions (bWord.pieces ++ bWord.pieces)
  /-- The actual original A routed face-word readings on the shared mesh bank. -/ a : PathFaces.MeshWordReadings
    original.shared.meshes row.pair.aFaces.geometry
  /-- The actual original B routed face-word readings on the shared mesh bank. -/ b : PathFaces.MeshWordReadings
    original.shared.meshes row.pair.bFaces.geometry
  /-- The original triangle readings evaluated from the same retained shared primitive bank. -/ triangles :
    TrianglePrimitiveReadings.TriangleReadings original.shared.numerics lifted.mesh
  /-- The original A route-spine chart request at one sixteenth of the retained complete target. -/ aCharts :
    RouteChartRequests.RouteChartRequest row.pair.aFaces.geometry.routeSpine
    (PeriodMatrix.standardDifferential differential) domains (target / 16)
  /-- The original B route-spine chart request at one sixteenth of the retained complete target. -/ bCharts :
    RouteChartRequests.RouteChartRequest row.pair.bFaces.geometry.routeSpine
    (PeriodMatrix.standardDifferential differential) domains (target / 16)
  /-- The common original bank stage pays every retained A route chart request. -/ aCharts_later : aCharts.index ≤
    original.shared.numericalIndex
  /-- The common original bank stage pays every retained B route chart request. -/ bCharts_later : bCharts.index ≤
    original.shared.numericalIndex
  /-- The original signed A correction-face chart request at the retained local target. -/ aFaceRequest :
    SignedFaceChartRequests.SignedFaceChartRequest lifted.mesh row.coordinates.routes.a.correction
    (PeriodMatrix.standardDifferential differential) domains (target / 16)
  /-- The original signed B correction-face chart request at the retained local target. -/ bFaceRequest :
    SignedFaceChartRequests.SignedFaceChartRequest lifted.mesh row.coordinates.routes.b.correction
    (PeriodMatrix.standardDifferential differential) domains (target / 16)
  /-- The common original bank stage pays the retained signed A face request. -/ aFaces_later : aFaceRequest.index ≤
    original.shared.numericalIndex
  /-- The common original bank stage pays the retained signed B face request. -/ bFaces_later : bFaceRequest.index ≤
    original.shared.numericalIndex
  /-- The original A mesh word bound is less than one sixteenth of the complete target. -/ a_small : a.bound < target /
    16
  /-- The original B mesh word bound is less than one sixteenth of the complete target. -/ b_small : b.bound < target /
    16

constructive_injectivity StandardBoundaryReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings

/-- The retained per-fragment ownership allowance pays the complete original scalar ownership error. -/
theorem ownership_allowance {inner : Fraction.Rational} (positive : 0 < inner) (pieces : Nat) :
    16 * (Aggregate.perTerm (inner / 4) pieces / 64) ≤ inner := by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have divided : 16 * (Aggregate.perTerm (inner / 4) pieces / 64) = Aggregate.perTerm (inner / 4) pieces / 4 := by
    generalize Aggregate.perTerm (inner / 4) pieces = allowance
    simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
    calc
      _ = allowance * (16 * (64 : Fraction.Rational)⁻¹) := by ring1
      _ = _ := by
        rw [show (16 : Fraction.Rational) * (64 : Fraction.Rational)⁻¹ = (4 : Fraction.Rational)⁻¹ by decide +kernel]
  exact divided.trans_le ((Fraction.Order.Field.divide_le_self
    (Aggregate.perTerm_positive quarterPositive pieces).le (by decide)).trans
      ((Aggregate.perTerm_le quarterPositive.le pieces).trans
        (Fraction.Order.Field.divide_le_self positive.le (by decide))))

/-- Exact ownership of an acquired standard boundary reading. -/
@[expose] def SharedAt {extraPoints : List Data.Gaussian.Basic.Canonical}
    (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row
      differential minimum target domains extraPoints)
    {stage : Nat} (numerics : PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential differential) stage domains) (numericalFloor : Nat) : Prop :=
  readings.original.shared.numericalIndex = stage ∧
    HEq readings.original.shared.numerics numerics ∧ readings.numericalFloor = numericalFloor

set_option genInjectivity false in
/-- The acquisition closure retains the already prepared paths, routes and chart requests. A later supplied numerical
bank is used without rebuilding those preparations or replacing its primitive values. -/
structure Preparation (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus) (minimum
  : Nat)
    (target : Fraction.Rational) (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (extraPoints : List Data.Gaussian.Basic.Canonical) (numericalFloor : Nat) : Type 3 where
  /-- The retained common stage paying all original path, route, chart and scalar preparations. -/ index : Nat
  /-- Acquire the prepared original boundary readings from the supplied later numerical bank, retaining exact bank and
    floor identity. -/ readWith : ∀ {stage : Nat} (numerics : PrimitiveData.FacePrimitiveBank
    (PeriodMatrix.standardDifferential differential) stage domains), index ≤ stage →
    { readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row
      differential minimum target domains extraPoints //
      SharedAt readings
        numerics numericalFloor }

constructive_injectivity Preparation

/-- Prepare both original standard words and all route, chart and face requests once.

The returned acquisition closure consumes a supplied later numerical bank and preserves every original path, source
ancestry and stage floor. -/
@[expose] def prepare (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus) (minimum
  : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars)
    (extraPoints : List Gaussian := []) (numericalFloor : Nat := 0) :
    Preparation row
      differential minimum target domains extraPoints numericalFloor := by
  let count := row.pair.aFaces.geometry.indexed.length + row.pair.bFaces.geometry.indexed.length
  have smallPositive : 0 < target / 16 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let inner := Aggregate.perTerm (target / 16) count
  have innerPositive : 0 < inner := Aggregate.perTerm_positive smallPositive count
  let preparation := RequestedPreparation.build row differential minimum inner innerPositive domains
  let aSources := LiftedSources.build lifted.mesh preparation.assignments.a
  let bSources := LiftedSources.build lifted.mesh preparation.assignments.b
  let aWord := Rooted.build aSources
    (ParentCoordinates.recast
      (PeriodMatrix.standardDifferential differential)
      (ParentCoordinates.ofSwitched preparation.comparison.a.cover.retained.current.state.chain))
    (RootChain.recast (PeriodMatrix.standardDifferential differential)
      preparation.comparison.a.cover.retained.current.roots)
  let bWord := Rooted.build bSources
    (ParentCoordinates.recast
      (PeriodMatrix.standardDifferential differential)
      (ParentCoordinates.ofSwitched preparation.comparison.b.cover.retained.current.state.chain))
    (RootChain.recast (PeriodMatrix.standardDifferential differential)
      preparation.comparison.b.cover.retained.current.roots)
  let aRouteRequest := RouteRequest.build aWord.pieces RouteWords.canonicalRoute (target / 16) smallPositive
  let bRouteRequest := RouteRequest.build bWord.pieces RouteWords.canonicalRoute (target / 16) smallPositive
  let aCharts := RouteChartRequest.build row.pair.aFaces.geometry.routeSpine
    (PeriodMatrix.standardDifferential differential) domains (target / 16) smallPositive
  let bCharts := RouteChartRequest.build row.pair.bFaces.geometry.routeSpine
    (PeriodMatrix.standardDifferential differential) domains (target / 16) smallPositive
  let aFaces := SignedFaceChartRequest.build lifted.mesh row.coordinates.routes.a.correction
    (PeriodMatrix.standardDifferential differential) domains (target / 16) smallPositive
  let bFaces := SignedFaceChartRequest.build lifted.mesh row.coordinates.routes.b.correction
    (PeriodMatrix.standardDifferential differential) domains (target / 16) smallPositive
  let extraFloor := max numericalFloor
    (max (max (max aRouteRequest.index bRouteRequest.index) (max aCharts.index bCharts.index)) (max aFaces.index
      bFaces.index))
  refine ⟨max extraFloor (FaceScalarBudgets.index preparation.scalars), ?_⟩
  intro stage numerics later
  let original := preparation.readWith innerPositive
    (List.ofFn lifted.vertices.coordinate ++ extraPoints) numerics ((Data.Nat.Order.le_max_right _ _).trans later)
  have extraLater : extraFloor ≤ original.shared.numericalIndex := (Data.Nat.Order.le_max_left _ _).trans later
  have ownLater : max (max (max aRouteRequest.index bRouteRequest.index) (max aCharts.index bCharts.index))
      (max aFaces.index bFaces.index) ≤ original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_right _ _).trans extraLater
  have routeLater : max aRouteRequest.index bRouteRequest.index ≤ original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans ownLater)
  have chartLater : max aCharts.index bCharts.index ≤ original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans ownLater)
  have faceLater : max aFaces.index bFaces.index ≤ original.shared.numericalIndex :=
    (Data.Nat.Order.le_max_right _ _).trans ownLater
  have aIncluded : ∀ piece ∈ aWord.pieces, piece.first ∈ original.shared.points ∧ piece.last ∈ original.shared.points :=
    by
    intro piece member
    have ends := Rooted.endpoints_mem aWord member
    rw [original.shared.points_eq]
    exact ⟨List.mem_append_left _ (List.mem_append_left _ ends.1), List.mem_append_left _ (List.mem_append_left _
      ends.2)⟩
  have bIncluded : ∀ piece ∈ bWord.pieces, piece.first ∈ original.shared.points ∧ piece.last ∈ original.shared.points :=
    by
    intro piece member
    have ends := Rooted.endpoints_mem bWord member
    rw [original.shared.points_eq]
    exact ⟨List.mem_append_left _ (List.mem_append_right _ ends.1), List.mem_append_left _ (List.mem_append_right _
      ends.2)⟩
  let aRoutes := aRouteRequest.readings original.shared.meshes ((Data.Nat.Order.le_max_left _ _).trans routeLater)
    aIncluded
  let bRoutes := bRouteRequest.readings original.shared.meshes ((Data.Nat.Order.le_max_right _ _).trans routeLater)
    bIncluded
  have included : ∀ vertex, lifted.vertices.coordinate vertex ∈ original.shared.points := by
    intro vertex
    rw [original.shared.points_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (Permutation.ofFn_mem _ vertex))
  let a := MeshWordReadings.build original.shared.meshes included row.pair.aFaces.geometry
  let b := MeshWordReadings.build original.shared.meshes included row.pair.bFaces.geometry
  have aSmall : a.bound < target / 16 := by
    rw [a.bound_eq, a.count_eq]
    exact Aggregate.count_mul_allowance_lt (Nat.le_add_right _ _) smallPositive
      (ownership_allowance
      innerPositive original.pieces)
  have bSmall : b.bound < target / 16 := by
    rw [b.bound_eq, b.count_eq]
    exact Aggregate.count_mul_allowance_lt (Nat.le_add_left _ _) smallPositive
      (ownership_allowance
      innerPositive original.pieces)
  have aJunctions := RootedWord.closed_junctions aWord.rooted
    (congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
      original.comparison.a.cover.retained.current.closed)
  have bJunctions := RootedWord.closed_junctions bWord.rooted
    (congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
      original.comparison.b.cover.retained.current.closed)
  let aSeams := ClosedSeams.build original.shared.meshes aWord.pieces
    (aWord.rooted.castFinish
      (congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
        original.comparison.a.cover.retained.current.closed))
  let bSeams := ClosedSeams.build original.shared.meshes bWord.pieces
    (bWord.rooted.castFinish
      (congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
        original.comparison.b.cover.retained.current.closed))
  let readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row
    differential minimum target domains extraPoints := by
    refine ⟨positive, count, rfl, original, numericalFloor,
    (Data.Nat.Order.le_max_left _ _).trans extraLater, aWord, bWord, ?_, ?_, aRouteRequest, bRouteRequest, aRoutes,
      bRoutes,
    aRoutes.values_eq.trans (RouteRequests.build_values ..),
    bRoutes.values_eq.trans (RouteRequests.build_values ..), aSeams, bSeams, aJunctions, bJunctions, a, b,
    TriangleReadings.build original.shared.numerics lifted.mesh, aCharts, bCharts,
    (Data.Nat.Order.le_max_left _ _).trans chartLater, (Data.Nat.Order.le_max_right _ _).trans chartLater,
    aFaces, bFaces, (Data.Nat.Order.le_max_left _ _).trans faceLater, (Data.Nat.Order.le_max_right _ _).trans faceLater,
      aSmall, bSmall⟩
    · apply DirectedRefinement.recast
      rw [original.comparison.a.cover.retained.current_eq]
      exact RootClosedState.statesDirected row.period.aInitial (PreparedRefinementProgramCore.standardDifferentials
        genus) _
    · apply DirectedRefinement.recast
      rw [original.comparison.b.cover.retained.current_eq]
      exact RootClosedState.statesDirected row.period.bInitial (PreparedRefinementProgramCore.standardDifferentials
        genus) _
  exact ⟨readings, rfl, HEq.rfl, rfl⟩

/-- Prepare the original complete A/B boundary schedule and acquire one shared primitive bank at its retained paid
stage. -/
@[expose] def build (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus) (minimum :
  Nat)
    (target : Fraction.Rational) (positive : 0 < target) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars)
    (extraPoints : List Gaussian := []) (numericalFloor : Nat := 0) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential
      minimum target domains extraPoints :=
  let prepared := prepare
    row differential minimum target positive domains extraPoints numericalFloor
  (prepared.readWith (FacePrimitiveBank.build
    (PeriodMatrix.standardDifferential differential) prepared.index domains) le_rfl).val

/-- The original boundary builder preserves exactly the supplied numerical stage floor. -/
theorem build_numericalFloor (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus)
  (minimum : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars)
    (extraPoints : List Data.Gaussian.Basic.Canonical) (numericalFloor : Nat) :
    (build row differential
      minimum target positive domains extraPoints numericalFloor).numericalFloor = numericalFloor := rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings

variable {extraPoints : List Purelib.Data.Gaussian.Basic.Canonical}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings

/-- The retained original A word still groups into the four actual source paths, with ordered locations on every
original segment. -/
theorem a_sources (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    PreparedTourSources.TourSources row.period.tours.aTour
      (readings.original.comparison.a.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) :=
  TourSources.refine
    (TourSources.recast
      (SourceAncestry.a_initial_sources row)
      (PeriodMatrix.standardDifferential differential)) readings.a_ancestry

/-- The B word retains its own actual connector and both boundary paths. -/
theorem b_sources (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    PreparedTourSources.TourSources row.period.tours.bTour
      (readings.original.comparison.b.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) :=
  TourSources.refine
    (TourSources.recast
      (SourceAncestry.b_initial_sources row)
      (PeriodMatrix.standardDifferential differential)) readings.b_ancestry

/-- All original A segment groups are certified on the actual cached flat word, with the original root joins and
four-leg traversal order. -/
theorem a_sourceWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SourceWords.TourSourceWords row.period.tours.aTour row.period.tours.root row.period.tours.root readings.aWord.pieces
      := by
  have words := TourSourceWords.ofParents readings.a_sources
    (LiftedSources.parentGroups readings.aWord.sources)
    (RootChain.recast
      (PeriodMatrix.standardDifferential differential)
      readings.original.comparison.a.cover.retained.current.roots)
  exact (congrArg (SourceWords.TourSourceWords row.period.tours.aTour row.period.tours.root row.period.tours.root)
    readings.aWord.pieces_eq).mpr words

/-- The retained B fragment word has the same exact source-group readback. -/
theorem b_sourceWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SourceWords.TourSourceWords row.period.tours.bTour row.period.tours.root row.period.tours.root readings.bWord.pieces
      := by
  have words := TourSourceWords.ofParents readings.b_sources
    (LiftedSources.parentGroups readings.bWord.sources)
    (RootChain.recast
      (PeriodMatrix.standardDifferential differential)
      readings.original.comparison.b.cover.retained.current.roots)
  exact (congrArg (SourceWords.TourSourceWords row.period.tours.bTour row.period.tours.root row.period.tours.root)
    readings.bWord.pieces_eq).mpr words

/-- The actual A word retains its source segments and root joins after stationary increments are removed. -/
theorem a_movingSourceWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SourceWords.TourSourceWords row.period.tours.aTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.aWord.pieces) := readings.a_sourceWords.moving

/-- Removing stationary occurrences preserves the exact cached A route sum. -/
theorem a_moving_sum (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((LiftedFragment.movingPieces readings.aWord.pieces).map
      (fun piece => RouteContacts.routeValue piece (RouteWords.canonicalRoute piece) readings.original.shared.meshes)) =
        readings.aRoutes.sum := by
  rw [LiftedFragment.movingPieces_sum, readings.aRoutes.sum_eq, readings.aRoutes_eq]

/-- The actual B word retains its source segments and root joins after stationary increments are removed. -/
theorem b_movingSourceWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SourceWords.TourSourceWords row.period.tours.bTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.bWord.pieces) := readings.b_sourceWords.moving

/-- Removing stationary occurrences preserves the exact cached B route sum. -/
theorem b_moving_sum (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((LiftedFragment.movingPieces readings.bWord.pieces).map
      (fun piece => RouteContacts.routeValue piece (RouteWords.canonicalRoute piece) readings.original.shared.meshes)) =
        readings.bRoutes.sum := by
  rw [LiftedFragment.movingPieces_sum, readings.bRoutes.sum_eq, readings.bRoutes_eq]

/-- The actual moving A word is grouped into the complete adjacent axis intervals used by the original four-leg grid
split. -/
theorem a_axisWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SegmentAxisGroups.AxisTourWords row.period.tours.aTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.aWord.pieces) := by
  apply TourSourceWords.group_axes readings.a_movingSourceWords (fun _ member => (LiftedFragment.movingPieces_mem
    member).2)
  rw [← row.source_eq]
  exact row.pair.aOnGrid

/-- The actual moving B word is grouped into the complete adjacent axis intervals used by the original four-leg grid
split. -/
theorem b_axisWords (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    SegmentAxisGroups.AxisTourWords row.period.tours.bTour row.period.tours.root row.period.tours.root
      (LiftedFragment.movingPieces readings.bWord.pieces) := by
  apply TourSourceWords.group_axes readings.b_movingSourceWords (fun _ member => (LiftedFragment.movingPieces_mem
    member).2)
  rw [← row.source_eq]
  exact row.pair.bOnGrid

/-- An adjacent A pair inherits its root junction from the actual retained word, after any prefix and across original
parent boundaries. -/
theorem a_pair_junction (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (before after) (left right) (equal : readings.aWord.pieces = before ++ left :: right :: after) :
    WordJunctions.Junction left right :=
  Junctions.at_pair before after ((congrArg WordJunctions.Junctions equal).mp (RootedWord.junctions
    readings.aWord.rooted))

/-- The same actual-word readback for the retained B path. -/
theorem b_pair_junction (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (before after) (left right) (equal : readings.bWord.pieces = before ++ left :: right :: after) :
    WordJunctions.Junction left right :=
  Junctions.at_pair before after ((congrArg WordJunctions.Junctions equal).mp (RootedWord.junctions
    readings.bWord.rooted))

/-- The actual cached original A fragment word closes with its retained coordinate and root owner. -/
theorem a_rooted_closed (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    LiftedFragment.RootedWord readings.aWord.pieces
      readings.original.comparison.a.cover.retained.current.state.start.coordinate row.period.tours.root
      readings.original.comparison.a.cover.retained.current.state.start.coordinate row.period.tours.root := by
  have word := readings.aWord.rooted
  have closed := congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
    readings.original.comparison.a.cover.retained.current.closed
  exact word.castFinish closed

/-- The actual cached original B fragment word closes with its retained coordinate and root owner. -/
theorem b_rooted_closed (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    LiftedFragment.RootedWord readings.bWord.pieces
      readings.original.comparison.b.cover.retained.current.state.start.coordinate row.period.tours.root
      readings.original.comparison.b.cover.retained.current.state.start.coordinate row.period.tours.root := by
  have word := readings.bWord.rooted
  have closed := congrArg (fun point : Lifted.Basic.LiftedPoint 2 => point.coordinate)
    readings.original.comparison.b.cover.retained.current.closed
  exact word.castFinish closed

/-- The original A seam sum reads the same cached shared period value after exact same-chart cancellation. -/
theorem a_seam_sum_eq (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    readings.aSeams.sum = readings.original.shared.a.value :=
  readings.aSeams.original_eq.trans (readings.aWord.sum_eq readings.original.shared.a)

/-- The original B seam sum reads the same cached shared period value after exact same-chart cancellation. -/
theorem b_seam_sum_eq (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    readings.bSeams.sum = readings.original.shared.b.value :=
  readings.bSeams.original_eq.trans (readings.bWord.sum_eq readings.original.shared.b)

/-- Every actual retained A seam point belongs to the original shared point bank. -/
theorem a_seam_point (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (seam) (member : seam ∈ readings.aSeams.entries) : seam.left.last ∈ readings.original.shared.points := by
  have present := (Rooted.endpoints_mem readings.aWord (readings.aSeams.entries_mem seam member).1).2
  exact (congrArg (fun bank : List Data.Gaussian.Basic.Canonical => seam.left.last ∈ bank)
    readings.original.shared.points_eq).mpr
    (List.mem_append_left _ (List.mem_append_left _ present))

/-- Every actual retained B seam point belongs to the original shared point bank. -/
theorem b_seam_point (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (seam) (member : seam ∈ readings.bSeams.entries) : seam.left.last ∈ readings.original.shared.points := by
  have present := (Rooted.endpoints_mem readings.bWord (readings.bSeams.entries_mem seam member).1).2
  exact (congrArg (fun bank : List Data.Gaussian.Basic.Canonical => seam.left.last ∈ bank)
    readings.original.shared.points_eq).mpr
    (List.mem_append_left _ (List.mem_append_right _ present))

/-- The exact element type of the supplied original list. -/
@[expose] def elementType {α : Type 2} (_ : List α) : Type 2 := α

/-- The exact type of the original retained A contact seams. -/
@[expose] def AContactSeam (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) : Type 2 :=
  elementType
    readings.aSeams.entries

/-- The exact type of the original retained B contact seams. -/
@[expose] def BContactSeam (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) : Type 2 :=
  elementType
    readings.bSeams.entries

/-- The original quantitative comparison request between two retained A seams. -/
@[expose] def AContactRequest (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (first last :
      AContactSeam
      readings) (allowance : Fraction.Rational) : Type 2 :=
  Seam.Request first last allowance

/-- The original quantitative comparison request between two retained B seams. -/
@[expose] def BContactRequest (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (first last :
      BContactSeam
      readings) (allowance : Fraction.Rational) : Type 2 :=
  Seam.Request first last allowance

/-- Membership in the actual retained original A seam list. -/
@[expose] def AContactMember (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (seam : AContactSeam
      readings) : Prop := seam ∈ readings.aSeams.entries

/-- Membership in the actual retained original B seam list. -/
@[expose] def BContactMember (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (seam : BContactSeam
      readings) : Prop := seam ∈ readings.bSeams.entries

/-- The original shared numerical stage pays the retained A contact request. -/
@[expose] def AContactLater (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    {first last :
      AContactSeam
      readings} {allowance : Fraction.Rational}
    (request :
      AContactRequest
      readings first last allowance) : Prop :=
  request.budget.index ≤ readings.original.shared.numericalIndex

/-- The original shared numerical stage pays the retained B contact request. -/
@[expose] def BContactLater (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    {first last :
      BContactSeam
      readings} {allowance : Fraction.Rational}
    (request :
      BContactRequest
      readings first last allowance) : Prop :=
  request.budget.index ≤ readings.original.shared.numericalIndex

/-- The original paid contact request bounds the actual difference between two retained A seam values. -/
theorem a_contact_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (first last :
      AContactSeam
      readings) (firstMem :
      AContactMember
      readings first)
    (lastMem :
      AContactMember
      readings last)
    {allowance : Fraction.Rational} (request :
      AContactRequest
      readings first last allowance)
    (later : AContactLater
      readings request) :
    Data.Gaussian.Norm.Basic.normSq (last.value - first.value) < allowance :=
  request.accurate later (readings.a_seam_point first firstMem) (readings.a_seam_point last lastMem)

/-- The original paid contact request bounds the actual difference between two retained B seam values. -/
theorem b_contact_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (first last :
      BContactSeam
      readings) (firstMem :
      BContactMember
      readings first)
    (lastMem :
      BContactMember
      readings last)
    {allowance : Fraction.Rational} (request :
      BContactRequest
      readings first last allowance)
    (later : BContactLater
      readings request) :
    Data.Gaussian.Norm.Basic.normSq (last.value - first.value) < allowance :=
  request.accurate later (readings.b_seam_point first firstMem) (readings.b_seam_point last lastMem)

/-- The cached original A shared reading approximates every later original period sample within one sixteenth of the
complete target. -/
theorem a_original_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.original.shared.a.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target / 16 :=
  (readings.original.a_accurate stage later).trans_le (Aggregate.perTerm_le
    (Fraction.Order.Field.div_pos_direct readings.positive (by decide)).le readings.count)

/-- The cached original B shared reading approximates every later original period sample within one sixteenth of the
complete target. -/
theorem b_original_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.original.shared.b.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target / 16 :=
  (readings.original.b_accurate stage later).trans_le (Aggregate.perTerm_le
    (Fraction.Order.Field.div_pos_direct readings.positive (by decide)).le readings.count)

/-- The complete original A route sum approximates its cached shared reading within the retained paid local target. -/
theorem a_routes_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    Data.Gaussian.Norm.Basic.normSq (readings.original.shared.a.value - readings.aRoutes.sum) < target / 16 :=
      by
  have estimate := readings.aRoutes.accurate
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (readings.aWord.values
    readings.original.shared.meshes) - readings.aRoutes.sum) < target / 16 at estimate
  rw [readings.aWord.sum_eq readings.original.shared.a] at estimate
  exact estimate

/-- The complete original B route sum approximates its cached shared reading within the retained paid local target. -/
theorem b_routes_accurate (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints) :
    Data.Gaussian.Norm.Basic.normSq (readings.original.shared.b.value - readings.bRoutes.sum) < target / 16 :=
      by
  have estimate := readings.bRoutes.accurate
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (readings.bWord.values
    readings.original.shared.meshes) - readings.bRoutes.sum) < target / 16 at estimate
  rw [readings.bWord.sum_eq readings.original.shared.b] at estimate
  exact estimate

/-- Combine the paid original corner, routing and period errors while retaining the actual mesh-minus-route discrepancy
explicitly. -/
private theorem compose {corner mesh routed original sample : Data.Gaussian.Basic.Canonical} {target :
  Fraction.Rational}
    (positive : 0 < target) (cornerSmall : Data.Gaussian.Norm.Basic.normSq (corner - mesh) < target / 16)
    (routeSmall : Data.Gaussian.Norm.Basic.normSq (original - routed) < target / 16)
    (originalSmall : Data.Gaussian.Norm.Basic.normSq (original - sample) < target / 16) :
    Data.Gaussian.Norm.Basic.normSq (corner - sample) < 4 * Data.Gaussian.Norm.Basic.normSq (mesh -
      routed) + target := by
  have reverseSmall : Data.Gaussian.Norm.Basic.normSq (routed - original) < target / 16 := by
    rw [show routed - original = -(original - routed) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact routeSmall
  have left := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (corner - mesh) (mesh - routed)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_right_direct cornerSmall (Data.Gaussian.Norm.Basic.normSq (mesh -
        routed))))
  have right := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (routed - original) (original - sample)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct reverseSmall originalSmall))
  have identity : corner - sample = ((corner - mesh) + (mesh - routed)) + ((routed - original) + (original - sample)) :=
    by ring1
  rw [identity]
  have paid := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct left right))
  have allowance : 12 * (target / 16) ≤ target := by
    have order := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (12 : Fraction.Rational) ≤ 16)
      (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)).le
    exact (by ring1 : 12 * (target / 16) = (target / 16) * 12).trans_le
      (order.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  exact paid.trans_le ((by
      ring1 : _ = 4 * Data.Gaussian.Norm.Basic.normSq (mesh - routed) + 12 * (target / 16)).trans_le
    (add_le_add le_rfl allowance))

/-- The original A triangle boundary approximates the retained period sample with all numerical errors paid and the
actual mesh-versus-route discrepancy explicit. -/
theorem a_boundary_error (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (row.pair.aFaces.geometry.values fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) <
        4 * Data.Gaussian.Norm.Basic.normSq (readings.a.value - readings.aRoutes.sum) + target := by
  rw [← readings.a.cornerValue_eq_triangles readings.triangles]
  exact compose
    readings.positive (readings.a.accurate.trans_lt readings.a_small) readings.a_routes_accurate
    (readings.a_original_accurate stage later)

/-- The original B triangle boundary approximates the retained period sample with all numerical errors paid and the
actual mesh-versus-route discrepancy explicit. -/
theorem b_boundary_error (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
  target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (row.pair.bFaces.geometry.values fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) <
        4 * Data.Gaussian.Norm.Basic.normSq (readings.b.value - readings.bRoutes.sum) + target := by
  rw [← readings.b.cornerValue_eq_triangles readings.triangles]
  exact compose
    readings.positive (readings.b.accurate.trans_lt readings.b_small) readings.b_routes_accurate
    (readings.b_original_accurate stage later)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings

end
