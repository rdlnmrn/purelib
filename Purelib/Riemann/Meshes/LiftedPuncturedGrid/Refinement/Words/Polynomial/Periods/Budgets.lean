module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial.Periods
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial.Budgets

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Comparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # Canonical cochain observations on the one supplied next-budget pipeline

The existing canonical input, request and comparison families are consumed
unchanged. A given certified next-budget cache can select fresh source
requirements before observations, then the one original pipeline and
canonical suffix share every actual numerical value and factory.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment (SplitSheets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.Closed
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Topology.Polygon.Stokes (triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original clearance}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet annulusSheet stripSheet freshSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})}
    {strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {rowIndex : Fin genus} {source : retained.PairCompilation oldBank newBank periods annuli strips rowIndex}
    {freshOrdered : BasedBranchBank.Ordered newBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    {fresh : Paired.PeriodPrograms.Prepared freshPaired} {basis : fresh.GeometricBasis}
    {boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences retained.fine.mesh.triangulation.faces)}
    {factory : boundary = retained.fine.boundaryComponents}
    (coordinates : PairCoordinates source basis boundary factory)

    (domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars)
    (minimum : Nat)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open LiftedSources (Rooted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (RouteRequest canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (anchor)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

variable {points : List Canonical} {oldTolerance : Rational} {oldStage : Nat}
    {referenceBudgets : FaceMeshBudgets (standardDifferential rowIndex) points oldTolerance domains}
    {referencePrimitives : FacePrimitiveBank (standardDifferential rowIndex) oldStage domains}
    {referenceLater : referenceBudgets.index ≤ oldStage}
    (reference : FaceSharedMeshes.Acquisition referenceBudgets referencePrimitives referenceLater)
    {pointPrefix extraPoints : List Canonical}
    {sampleCount : Nat} {requestTarget : Rational}
    {axes : PrimitiveAxes retained.fineBase.bank.grid}
    {parents : List (CenteredEdge curve (standardDifferential rowIndex))}
    {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := retained.fineBase) axes splits}
    {parentRequests : RequestedParents sampleCount requestTarget parents}
    {entries : SplitSheets domains fragments parentRequests}
    (pointFactory : points = pointPrefix ++ (List.ofFn retained.fine.vertices.coordinate ++
      (Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints)))
    {vertex : Fin original.vertices.count}
    {period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) (standardDifferential rowIndex)}
    (faces : PeriodFaces retained vertex period)
    {sourceSheet : Fin 2} (ancestry : PathSources sourceSheet period.closed.walk.path parents)
    {roots : RootChain parents (ownerName
      (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex))}
    {point : LiftedPoint 2} {geometry : CenteredPathChain parents (start := point) (finish := point)}
    {included : ∀ value ∈ Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries,
      value ∈ points}
    (word : Fragment.SplitSheets.Closed reference.shared entries geometry roots included)
    (rooted : Rooted entries retained.fine.mesh (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)))
    {previousRouteTarget previousChartTarget : Rational}
    (routing : RouteRequest rooted.pieces previousRouteTarget)
    (routingFactory : routing = RouteRequest.build rooted.pieces canonicalRoute previousRouteTarget routing.positive)
    (charts : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential rowIndex)
      domains previousChartTarget)
    (polynomial : Ordinary curve.polynomial)
    (wordTarget cochainTarget : Rational) (wordPositive : 0 < wordTarget) (cochainPositive : 0 < cochainTarget)
    (minimumFloor modelStage : Nat)

namespace ComparisonRequests

namespace CanonicalPreparation

/-- Every original retained subtype factory identifies the SAME complete canonical comparison cache.

Dependency is eliminated one actual field at a time. The point-list and
source/route certificates are those of the same supplied input product;
no producer is unfolded or executed to identify its output.
-/
theorem eq_of_factories
    (first last : CanonicalPreparation (pointPrefix := pointPrefix) (extraPoints := extraPoints)
      (sourceSheet := sourceSheet) coordinates domains minimum reference faces word rooted routing charts
      polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage) : first = last := by
  rcases first with ⟨firstInputs, firstRequests, firstPrepared, firstRouted, firstMesh, firstChart, firstValue⟩
  rcases last with ⟨lastInputs, lastRequests, lastPrepared, lastRouted, lastMesh, lastChart, lastValue⟩
  have inputsEq : firstInputs = lastInputs :=
    Subtype.ext (firstInputs.property.1.trans lastInputs.property.1.symm)
  cases inputsEq
  have requestsEq : firstRequests = lastRequests :=
    Subtype.ext (firstRequests.property.trans lastRequests.property.symm)
  cases requestsEq
  have preparedEq : firstPrepared = lastPrepared :=
    Subtype.ext (firstPrepared.property.trans lastPrepared.property.symm)
  cases preparedEq
  have routedEq : firstRouted = lastRouted := Subtype.ext (firstRouted.property.trans lastRouted.property.symm)
  cases routedEq
  have meshEq : firstMesh = lastMesh := Subtype.ext (firstMesh.property.trans lastMesh.property.symm)
  cases meshEq
  have chartEq : firstChart = lastChart := Subtype.ext (firstChart.property.trans lastChart.property.symm)
  cases chartEq
  have valueEq : firstValue = lastValue := Subtype.ext (firstValue.property.trans lastValue.property.symm)
  cases valueEq
  rfl

end CanonicalPreparation

/-- Fill the original canonical comparison with one GIVEN next-budget cache and pre-observation request products.

The original given-budget word worker produces one P primitive/shared
bank, triangle readings and six comparison products. The original
fromPreparation suffix then adds route, mesh, Some-chart and scalar caches
once. All convenience-producer equations occur only in erased proofs.
-/
def prepareCanonicalWithBudgets
    (originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
      (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts)
    (needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive //
      value = canonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive})
    (cochainRequests : {value : ComparisonRequests coordinates (standardDifferential rowIndex) domains
        (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage
        (some polynomial) //
      value = coordinates.requestComparison (standardDifferential rowIndex) domains
        (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage
        (some polynomial)})
    (nextBudgets : PolynomialPreparation.Budgets word polynomial.val
      (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)) :
    {result : CanonicalPreparation (pointPrefix := pointPrefix) (extraPoints := extraPoints)
        (sourceSheet := sourceSheet) coordinates domains minimum reference faces word rooted routing charts
        polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage //
      result = prepareCanonical (pointFactory := originals.property.2.1)
        (routingFactory := originals.property.2.2.1) (ancestry := originals.property.2.2.2)
        coordinates domains minimum reference faces word rooted routing charts polynomial wordTarget cochainTarget
        wordPositive cochainPositive minimumFloor modelStage ∧
      HEq result.prepared.cochainRequests cochainRequests.val ∧
      result.prepared.numerical.meshBudgets = nextBudgets.val} :=
  let built := prepareWordWithBudgets coordinates (standardDifferential rowIndex) domains
    (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage word polynomial
    (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
    (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
    minimumFloor modelStage cochainRequests nextBudgets
  let prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
      (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage word polynomial
      (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
      minimumFloor modelStage //
      value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32)
        (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage word polynomial
        (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
        (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
        minimumFloor modelStage} := ⟨built.val, built.property.1⟩
  let result := fromPreparation coordinates domains minimum reference faces word rooted routing charts polynomial
    wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage originals needed prepared
  have forwarded : result.prepared = built.val :=
    fromPreparation_prepared coordinates domains minimum reference faces word rooted routing charts polynomial
      wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage originals needed prepared
  have requestsEq : result.prepared.cochainRequests = cochainRequests.val :=
    (congrArg (fun actual => actual.cochainRequests) forwarded).trans built.property.2.1
  have budgetsEq : result.prepared.numerical.meshBudgets = nextBudgets.val :=
    (congrArg (fun actual => actual.numerical.meshBudgets) forwarded).trans built.property.2.2
  have factory := CanonicalPreparation.eq_of_factories
    (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := reference)
    (faces := faces) (word := word) (rooted := rooted) (routing := routing) (charts := charts)
    (polynomial := polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget)
    (wordPositive := wordPositive) (cochainPositive := cochainPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) result
    (prepareCanonical (pointFactory := originals.property.2.1) (routingFactory := originals.property.2.2.1)
      (ancestry := originals.property.2.2.2) coordinates domains minimum reference faces word rooted routing charts
      polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage)
  ⟨result, factory, heq_of_eq requestsEq, budgetsEq⟩

end ComparisonRequests

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

end
