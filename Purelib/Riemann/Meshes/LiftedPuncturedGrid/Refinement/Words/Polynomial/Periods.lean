module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods.Sources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.Refinement
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Tactic.Ring
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Comparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # Paid canonical cochains on one retained ordinary-numerator bank

The actual old shared point bank contains all vertices of the same fine
grid by its original whole point-list factory. Existing route/contact
caches select genuinely new small requests before the one shared pipeline;
the returned products retain the old/fresh periods, coordinates, word,
all model and primitive owners, and every actual comparison cache.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
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
      (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints)))
    {vertex : Fin original.vertices.count}
    {period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) (standardDifferential rowIndex)}
    (faces : PeriodFaces retained vertex period)
    {sourceSheet : Fin 2} (ancestry : PathSources sourceSheet period.closed.walk.path parents)
    {roots : RootChain parents (ownerName
      (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex))}
    {point : LiftedPoint 2} {geometry : CenteredPathChain parents (start := point) (finish := point)}
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries,
      value ∈ points}
    (word : SplitSheets.Closed reference.shared entries geometry roots included)
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

/-- The whole original A-period transport reads the literal source cochain in the retained paired comparison.

The actual source closed-walk factory and original anchor/Owner transport
supply the word identity. This is a reading law on a given cochain, with
no new period, Frame selection, root comparison or geometric realization.
-/
theorem a_period_difference
    (aFaces : PeriodFaces retained (anchor original oldSheet) (periods.aWalk rowIndex))
    (valuation : Topology.Polygon.Stokes.OrientedEdge retained.fine.vertices.count → Canonical) :
    wordValue valuation aFaces.view.geometry.indexed - coordinates.a.coordinates.periodValue valuation =
      coordinates.aDifference valuation := by
  have originalValue := periods.a_refined_value retained rowIndex aFaces valuation
  have actualSource := congrArg (fun walk => wordValue valuation
    (retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit walk (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet))
        source.aClosed_walk
  exact congrArg (fun amount : Canonical => amount - coordinates.a.coordinates.periodValue valuation)
    (originalValue.trans actualSource.symm)

/-- The full corrected-B transport reads the SAME source cochain, including every earlier-A occurrence.

The whole retained corrected walk is used through its original factory.
No replacement by the reference B bridge or independent homology claim
enters the scalar reading identity.
-/
theorem b_period_difference
    (bFaces : PeriodFaces retained (anchor original oldSheet) (periods.bWalk rowIndex))
    (valuation : Topology.Polygon.Stokes.OrientedEdge retained.fine.vertices.count → Canonical) :
    wordValue valuation bFaces.view.geometry.indexed - coordinates.b.coordinates.periodValue valuation =
      coordinates.bDifference valuation := by
  have originalValue := periods.b_refined_value retained rowIndex bFaces valuation
  have actualSource := congrArg (fun walk => wordValue valuation
    (retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit walk (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet))
        source.bClosed_walk
  exact congrArg (fun amount : Canonical => amount - coordinates.b.coordinates.periodValue valuation)
    (originalValue.trans actualSource.symm)

namespace ComparisonRequests

/-- Real route/chart allocations and their common floor, chosen before any new observation.

The original whole raw route and chart objects supply their literal
contact geometries. New positive budgets, including the genuine P source
and numerical floors, are selected without reconstructing those contacts.
The word tolerance uses only the fixed retained global-grid word count.
-/
@[expose] def CanonicalRequests : Type _ :=
  {value : Rational × Rational × Nat // value = (wordTarget, cochainTarget, faces.view.geometry.indexed.length)} ×
  (Σ raw : {value : RouteRequest rooted.pieces (cochainTarget / 32) //
    value = routing.retarget (cochainTarget / 32)
      (PeriodCanonical.cochainShare_positive cochainPositive)},
  Σ route : {value : RouteRequest rooted.pieces (cochainTarget / 32) (some polynomial) //
    value = raw.val.onNumerator polynomial},
  Σ chart : {value : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential rowIndex)
      domains (cochainTarget / 32) (some polynomial) //
    value = charts.rebudget (cochainTarget / 32)
      (PeriodCanonical.cochainShare_positive cochainPositive) (some polynomial)},
  {value : Nat // value = max minimum (max route.val.index chart.val.index)})

/-- Retarget the given route/contact budgets and retain the joint Some chart floor. -/
def canonicalRequests : CanonicalRequests domains minimum faces rooted routing charts polynomial
    wordTarget cochainTarget cochainPositive :=
  let sharePositive := PeriodCanonical.cochainShare_positive cochainPositive
  let raw : {value : RouteRequest rooted.pieces (cochainTarget / 32) //
      value = routing.retarget (cochainTarget / 32) sharePositive} :=
    ⟨routing.retarget (cochainTarget / 32) sharePositive, rfl⟩
  let route : {value : RouteRequest rooted.pieces (cochainTarget / 32) (some polynomial) //
      value = raw.val.onNumerator polynomial} := ⟨raw.val.onNumerator polynomial, rfl⟩
  let chart : {value : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential rowIndex)
      domains (cochainTarget / 32) (some polynomial) //
      value = charts.rebudget (cochainTarget / 32) sharePositive (some polynomial)} :=
    ⟨charts.rebudget (cochainTarget / 32) sharePositive (some polynomial), rfl⟩
  let stage : {value : Nat // value = max minimum (max route.val.index chart.val.index)} :=
    ⟨max minimum (max route.val.index chart.val.index), rfl⟩
  ⟨⟨(wordTarget, cochainTarget, faces.view.geometry.indexed.length), rfl⟩, raw, route, chart, stage⟩

namespace CanonicalRequests

variable {domains minimum faces rooted routing charts polynomial wordTarget cochainTarget cochainPositive}
variable (needed : CanonicalRequests domains minimum faces rooted routing charts polynomial
  wordTarget cochainTarget cochainPositive)

/-- Read the actual independently supplied targets and fixed global-grid word count. -/
@[expose] def allocation := needed.1.val

/-- The targets and count are the original retained input data. -/
theorem allocation_eq : needed.allocation = (wordTarget, cochainTarget, faces.view.geometry.indexed.length) :=
  needed.1.property

/-- Read the actual raw route request with genuinely reselected small budgets. -/
@[expose] def rawRoute : RouteRequest rooted.pieces (cochainTarget / 32) := needed.2.1.val

/-- The whole raw route is the retained numerical retargeting of the supplied contacts. -/
theorem rawRoute_eq : needed.rawRoute = routing.retarget (cochainTarget / 32)
    (PeriodCanonical.cochainShare_positive cochainPositive) := needed.2.1.property

/-- Read the certified full-numerator request on those SAME raw route/contact caches. -/
@[expose] def route : {value : RouteRequest rooted.pieces (cochainTarget / 32) (some polynomial) //
    value = needed.rawRoute.onNumerator polynomial} := needed.2.2.1

/-- Read the actual Some chart-change request on the supplied ordered chart-contact spine. -/
@[expose] def chart : RouteChartRequest faces.view.geometry.routeSpine (standardDifferential rowIndex)
    domains (cochainTarget / 32) (some polynomial) := needed.2.2.2.1.val

/-- The whole Some chart request has its one retained-geometry numerical factory. -/
theorem chart_eq : needed.chart = charts.rebudget (cochainTarget / 32)
    (PeriodCanonical.cochainShare_positive cochainPositive) (some polynomial) :=
  needed.2.2.2.1.property

/-- Read the actual route/chart/caller minimum computed before the one shared bank. -/
@[expose] def stage : Nat := needed.2.2.2.2.val

/-- The selected floor retains the literal caller and actual pre-bank request maxima. -/
theorem stage_eq : needed.stage = max minimum (max needed.route.val.index needed.chart.index) :=
  needed.2.2.2.2.property

/-- The actual route request is paid by the pre-bank common floor. -/
theorem route_le : needed.route.val.index ≤ needed.stage :=
  ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans_eq needed.stage_eq.symm

/-- The actual Some chart request is paid by the pre-bank common floor. -/
theorem chart_le : needed.chart.index ≤ needed.stage :=
  ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans_eq needed.stage_eq.symm

/-- The caller's independent numerical minimum remains in the actual common floor. -/
theorem minimum_le : minimum ≤ needed.stage :=
  (Data.Nat.Order.le_max_left _ _).trans_eq needed.stage_eq.symm

end CanonicalRequests

/-- The exact retained canonical numerical inputs and their whole source/point factories.

Every value is an original nominal owner or cache. The subtype records the
literal same-fine point choice, canonical raw-request factory and actual
directed source grouping, without replacing those inputs by membership or
numerical agreement assumptions.
-/
@[expose] def CanonicalInputs : Type _ :=
  {value : Paired.PeriodPrograms.Prepared paired × Paired.PeriodPrograms.Prepared freshPaired ×
      fresh.GeometricBasis ×
      PairCoordinates source basis boundary factory ×
      FaceSharedMeshes.Acquisition referenceBudgets referencePrimitives referenceLater ×
      List Canonical × List Canonical ×
      PeriodFaces retained vertex period ×
      RootChain parents (ownerName (original.vertices.owner original.frames vertex))
        (ownerName (original.vertices.owner original.frames vertex)) ×
      SplitSheets.Closed reference.shared entries geometry roots included ×
      Rooted entries retained.fine.mesh (original.vertices.coordinate vertex)
        (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
        (ownerName (original.vertices.owner original.frames vertex)) ×
      RouteRequest rooted.pieces previousRouteTarget ×
      RouteChartRequest faces.view.geometry.routeSpine (standardDifferential rowIndex)
        domains previousChartTarget //
    value = (periods, fresh, basis, coordinates, reference, pointPrefix, extraPoints,
      faces, roots, word, rooted, routing, charts) ∧
      points = pointPrefix ++ (List.ofFn retained.fine.vertices.coordinate ++
        (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints)) ∧
      routing = RouteRequest.build rooted.pieces canonicalRoute previousRouteTarget routing.positive ∧
      PathSources sourceSheet period.closed.walk.path parents}

namespace CanonicalPreparation

/-- The retained post-bank route, mesh, chart and canonical scalar observations. -/
@[expose] def ReadingsTail
    (originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts)
    (needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive //
    value = canonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive})
    (prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
      (cochainTarget / 32)
        (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage
      word polynomial (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
      minimumFloor modelStage //
    value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32)
      (PeriodCanonical.cochainShare_positive cochainPositive)
      needed.val.stage word polynomial
      (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
      minimumFloor modelStage}) : Type _ :=
  Σ _routed : {value : RouteRequest.PolynomialReadings prepared.val.numerical.sharedMeshes
      prepared.val.numerical.word rooted needed.val.rawRoute needed.val.route
      (needed.val.route_le.trans (prepared.val.cochainRequests.minimum_le.trans prepared.val.cochainRequests_le)) //
    value = RouteRequest.compareClosed prepared.val.numerical.sharedMeshes prepared.val.numerical.word rooted
      needed.val.rawRoute needed.val.route
      (needed.val.route_le.trans (prepared.val.cochainRequests.minimum_le.trans prepared.val.cochainRequests_le))},
  Σ _mesh : {value : MeshWordReadings prepared.val.numerical.sharedMeshes faces.view.geometry //
    value = MeshWordReadings.build prepared.val.numerical.sharedMeshes
      (FaceSharedMeshes.Acquisition.vertices_mem (bank := retained.fineBase.bank.toBranchCellBank)
      retained.fine.vertices pointPrefix
      (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints)
      originals.property.2.1) faces.view.geometry},
  Σ _chart : {value : needed.val.chart.Comparisons prepared.val.numerical.primitiveBank prepared.val.triangles //
    value = needed.val.chart.compare prepared.val.numerical.primitiveBank prepared.val.triangles},
  {value : Canonical// value = wordValue
    (CanonicalEdgeValues.edgeValuation retained.fine.mesh prepared.val.triangles.values) faces.view.geometry.indexed}

/-- The single retained polynomial preparation and its post-bank observations. -/
@[expose] def BankTail
    (originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts)
    (needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive //
    value = canonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive}) : Type _ :=
  Σ prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
      (cochainTarget / 32)
        (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage
      word polynomial (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
      minimumFloor modelStage //
    value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32)
      (PeriodCanonical.cochainShare_positive cochainPositive)
      needed.val.stage word polynomial
      (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
      (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
      minimumFloor modelStage},
  ReadingsTail (pointPrefix := pointPrefix) (extraPoints := extraPoints) (sourceSheet := sourceSheet) (coordinates
    := coordinates) (domains := domains) (minimum := minimum) (reference := reference) (faces := faces) (word :=
    word) (rooted := rooted) (routing := routing) (charts := charts) (polynomial := polynomial) (wordTarget :=
    wordTarget) (cochainTarget := cochainTarget) (wordPositive := wordPositive) (cochainPositive :=
    cochainPositive) (minimumFloor := minimumFloor) (modelStage := modelStage) originals needed prepared

end CanonicalPreparation

/-- The SAME old/fresh canonical inputs and one shared-bank preparation with every actual chart/routing cache.

The original numerical execution, literal point factory and both public
targets are retained. The
post-bank fields contain real route, mesh and Some chart observations on
one numerical bank, together with the actual canonical scalar reading.
-/
@[expose] def CanonicalPreparation : Type _ :=
  Σ originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts,
  Σ needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive //
    value = canonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive},
  CanonicalPreparation.BankTail (pointPrefix := pointPrefix) (extraPoints := extraPoints) (sourceSheet :=
    sourceSheet) (coordinates := coordinates) (domains := domains) (minimum := minimum) (reference := reference)
    (faces := faces) (word := word) (rooted := rooted) (routing := routing) (charts := charts) (polynomial :=
    polynomial) (wordTarget := wordTarget) (cochainTarget := cochainTarget) (wordPositive := wordPositive)
    (cochainPositive := cochainPositive) (minimumFloor := minimumFloor) (modelStage := modelStage) originals needed

/-- Consume the retained whole inputs, pre-bank requests and single-bank preparation before actual cochain readings.

The original route, mesh, Some chart and scalar suffix runs once on the
supplied bank. Whole point-list coverage comes from the given original
input factory; no numerical bank, source, period or query is prepared to
recover that ownership.
-/
@[expose] def fromPreparation
    (originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
      (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts)
    (needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive //
      value = canonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive})
    (prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
        (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive)
        needed.val.stage word polynomial
        (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
        (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
        minimumFloor modelStage //
      value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32)
        (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage word polynomial
        (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
        (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
        minimumFloor modelStage}) :
    CanonicalPreparation (pointPrefix := pointPrefix) (extraPoints := extraPoints)
      (sourceSheet := sourceSheet) coordinates domains minimum reference faces word rooted routing charts
      polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage := by
  have vertexMember : ∀ vertex, retained.fine.vertices.coordinate vertex ∈ points :=
    FaceSharedMeshes.Acquisition.vertices_mem (bank := retained.fineBase.bank.toBranchCellBank)
      retained.fine.vertices pointPrefix
      (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints) originals.property.2.1
  have routeLater : needed.val.route.val.index ≤ prepared.val.numerical.faceStage :=
    needed.val.route_le.trans (prepared.val.cochainRequests.minimum_le.trans prepared.val.cochainRequests_le)
  let routed : {value : RouteRequest.PolynomialReadings prepared.val.numerical.sharedMeshes
      prepared.val.numerical.word rooted needed.val.rawRoute needed.val.route routeLater //
      value = RouteRequest.compareClosed prepared.val.numerical.sharedMeshes prepared.val.numerical.word rooted
        needed.val.rawRoute needed.val.route routeLater} :=
    ⟨RouteRequest.compareClosed prepared.val.numerical.sharedMeshes prepared.val.numerical.word rooted
      needed.val.rawRoute needed.val.route routeLater, rfl⟩
  let mesh : {value : MeshWordReadings prepared.val.numerical.sharedMeshes faces.view.geometry //
      value = MeshWordReadings.build prepared.val.numerical.sharedMeshes vertexMember
        faces.view.geometry} :=
    ⟨MeshWordReadings.build prepared.val.numerical.sharedMeshes vertexMember faces.view.geometry, rfl⟩
  let chart : {value : needed.val.chart.Comparisons prepared.val.numerical.primitiveBank prepared.val.triangles //
      value = needed.val.chart.compare prepared.val.numerical.primitiveBank prepared.val.triangles} :=
    ⟨needed.val.chart.compare prepared.val.numerical.primitiveBank prepared.val.triangles, rfl⟩
  let value : {value : Canonical // value = wordValue
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh prepared.val.triangles.values)
      faces.view.geometry.indexed} :=
    ⟨wordValue (CanonicalEdgeValues.edgeValuation retained.fine.mesh prepared.val.triangles.values)
      faces.view.geometry.indexed, rfl⟩
  exact ⟨originals, needed, prepared, routed, mesh, chart, value⟩

include ancestry routingFactory pointFactory in
/-- Construct one actually paid route/mesh/chart/cochain bank after all genuine request floors are known.

The old closed word uses the given original numerical execution on this
SAME fine grid; its whole point factory supplies vertex membership. Only real new
requests and ordinary-P observations are produced. All old physical
leaves, roots, source/query owners, offsets and cache identities remain
those of the given old word and whole original period view.
-/
def prepareCanonical : CanonicalPreparation (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains minimum reference faces word rooted routing
    charts polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage := by
  let sharePositive := PeriodCanonical.cochainShare_positive cochainPositive
  let selected := PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length
  have selectedPositive := PeriodCanonical.wordAllowance_positive wordPositive cochainPositive
    faces.view.geometry.indexed.length
  let originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts :=
    ⟨(periods, fresh, basis, coordinates, reference, pointPrefix, extraPoints,
      faces, roots, word, rooted, routing, charts),
      rfl, pointFactory, routingFactory, ancestry⟩
  let needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive //
      value = canonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive} :=
    ⟨canonicalRequests domains minimum faces rooted routing charts polynomial
      wordTarget cochainTarget cochainPositive, rfl⟩
  let prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
      (cochainTarget / 32) sharePositive needed.val.stage word polynomial selected selectedPositive
      minimumFloor modelStage //
      value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32) sharePositive
        needed.val.stage word polynomial selected selectedPositive minimumFloor modelStage} :=
    ⟨prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32) sharePositive
      needed.val.stage word polynomial selected selectedPositive minimumFloor modelStage, rfl⟩
  exact fromPreparation coordinates domains minimum reference faces word rooted routing charts polynomial
    wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage originals needed prepared

namespace CanonicalPreparation

variable {coordinates domains minimum reference faces word rooted routing charts
  polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage}
variable (kept : CanonicalPreparation (pointPrefix := pointPrefix) (extraPoints := extraPoints)
    (sourceSheet := sourceSheet) coordinates domains minimum reference faces word rooted routing charts
  polynomial wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage)

include kept

/-- Read the complete original/fresh period preparations, basis, coordinates, shared bank and physical/source inputs. -/
@[expose] def originals := kept.1.val

/-- Every whole original and fresh input remains the literal supplied data. -/
theorem originals_eq : kept.originals =
    (periods, fresh, basis, coordinates, reference, pointPrefix, extraPoints,
      faces, roots, word, rooted, routing, charts) :=
  kept.1.property.1

/-- The literal same-fine vertex and source point choice belongs to the actual original numerical inputs. -/
theorem points_eq : points = pointPrefix ++ (List.ofFn retained.fine.vertices.coordinate ++
    (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints)) := kept.1.property.2.1

/-- Every fine-grid vertex belongs to the actual reference point bank by its retained whole factory. -/
theorem vertices_mem (vertex : Fin retained.fine.vertices.count) : retained.fine.vertices.coordinate vertex ∈ points :=
  FaceSharedMeshes.Acquisition.vertices_mem (bank := retained.fineBase.bank.toBranchCellBank)
    retained.fine.vertices pointPrefix
    (RegularPrimitiveSplits.SheetEntries.points entries ++ extraPoints) kept.points_eq vertex

/-- Every original analytic source endpoint belongs to that SAME reference point bank. -/
theorem child_points_mem (value : Canonical)
    (member : value ∈ RegularPrimitiveSplits.SheetEntries.points entries) : value ∈ points := by
  rewrite [kept.points_eq]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))

/-- The original raw canonical request keeps its whole producer identity. -/
theorem routing_factory : routing =
    RouteRequest.build rooted.pieces canonicalRoute previousRouteTarget routing.positive := kept.1.property.2.2.1

/-- The actual retained child parents keep their original directed period-source grouping. -/
theorem source_path : PathSources sourceSheet period.closed.walk.path parents := kept.1.property.2.2.2

/-- Read the actual pre-bank route/chart requests and common floor, without preparing them again. -/
@[expose] def requests := kept.2.1.val

/-- The pre-bank request product retains its one actual retained-geometry factory. -/
theorem requests_eq : kept.requests = canonicalRequests domains minimum faces rooted routing charts polynomial
    wordTarget cochainTarget cochainPositive := kept.2.1.property

/-- Read the single ordinary-numerator pipeline and all actual source-model/primitive/six-comparison caches. -/
@[expose] def prepared := kept.2.2.1.val

/-- The original single-bank producer was called with the actual pre-bank route/chart floor. -/
theorem prepared_eq : kept.prepared = prepareWord coordinates (standardDifferential rowIndex) domains
    (cochainTarget / 32)
      (PeriodCanonical.cochainShare_positive cochainPositive) kept.requests.stage
    word polynomial (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
    (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
    minimumFloor modelStage := kept.2.2.1.property

/-- The actual route request is paid by this SAME retained primitive bank. -/
theorem route_le : kept.requests.route.val.index ≤ kept.prepared.numerical.faceStage :=
  kept.requests.route_le.trans (kept.prepared.cochainRequests.minimum_le.trans kept.prepared.cochainRequests_le)

/-- The actual Some chart request is paid by this SAME retained primitive bank. -/
theorem chart_le : kept.requests.chart.index ≤ kept.prepared.numerical.faceStage :=
  kept.requests.chart_le.trans (kept.prepared.cochainRequests.minimum_le.trans kept.prepared.cochainRequests_le)

/-- Read the one actual whole-word route cache on the retained closed physical word. -/
@[expose] def routed := kept.2.2.2.1.val

/-- The actual route comparison retains its single original factory on the SAME numerical word. -/
theorem routed_eq : kept.routed = RouteRequest.compareClosed kept.prepared.numerical.sharedMeshes
    kept.prepared.numerical.word rooted kept.requests.rawRoute kept.requests.route kept.route_le :=
  kept.2.2.2.1.property

/-- Read the actual shared-mesh and fixed-corner period readings without a second numerical fold. -/
@[expose] def mesh := kept.2.2.2.2.1.val

/-- The retained period readings use genuine vertex membership derived from the original SAME-fine point factory. -/
theorem mesh_eq : kept.mesh = MeshWordReadings.build kept.prepared.numerical.sharedMeshes kept.vertices_mem
    faces.view.geometry := kept.2.2.2.2.1.property

/-- Read the once-executed ordered Some chart comparisons and their literal cached residuals. -/
@[expose] def chart := kept.2.2.2.2.2.1.val

/-- The chart products retain their single post-bank factory on the exact shared numerical bank. -/
theorem chart_eq : kept.chart = kept.requests.chart.compare kept.prepared.numerical.primitiveBank
    kept.prepared.triangles := kept.2.2.2.2.2.1.property

/-- Read the retained canonical cochain value on the selected original period word. -/
@[expose] def value : Canonical := kept.2.2.2.2.2.2.val

/-- The actual canonical scalar reads the SAME triangle bank and selected period-face word. -/
theorem value_eq : kept.value = wordValue
    (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values)
    faces.view.geometry.indexed := kept.2.2.2.2.2.2.property

/-- The unchanged literal fragment count determines the genuine new mesh tolerance, independently of its stage. -/
theorem mesh_bound_lt : kept.mesh.bound < cochainTarget / 32 := by
  rewrite [kept.mesh.bound_eq, kept.mesh.count_eq]
  exact PeriodCanonical.meshCharge_lt wordPositive cochainPositive faces.view.geometry.indexed.length
    (Fragment.SplitSheets.fragmentCount entries)

/-- The retained raw route has the exact smaller-target canonical factory, derived from its whole old factory. -/
theorem rawRoute_factory : kept.requests.rawRoute = RouteRequest.build rooted.pieces canonicalRoute
    (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive) :=
  kept.requests.rawRoute_eq.trans (routing.retarget_factory routing.positive canonicalRoute kept.routing_factory
    (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive))

/-- The actual ordered gap sum and the SAME selected period mesh reading satisfy their new paid route allowance. -/
theorem routed_gap_lt : normSq
    (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - kept.mesh.value) < cochainTarget / 32 := by
  have actual := PeriodFaces.polynomial_routed_gap_lt (period := period) (kept := faces) (ancestry := kept.source_path)
    (roots := roots) (nextShared := kept.prepared.numerical.sharedMeshes) (closed := kept.prepared.numerical.word)
    (word := rooted)
    (positive := PeriodCanonical.cochainShare_positive cochainPositive)
    (routing := kept.requests.rawRoute) (routingFactory := kept.rawRoute_factory) (requested := kept.requests.route)
    (readings := kept.routed)
  have same : kept.mesh.value = gaussianSum (faces.view.geometry.values
      (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement kept.prepared.numerical.sharedMeshes route)) :=
    kept.mesh.value_eq.trans (congrArg gaussianSum kept.mesh.values_eq)
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq
    (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - amount) < cochainTarget / 32) same) actual

/-- Actual Some chart products and the fixed-grid mesh allocation bound the canonical-versus-mesh difference. -/
theorem canonical_mesh_lt : normSq (kept.value - kept.mesh.value) <
    2 * (cochainTarget / 32 + cochainTarget / 32) := by
  have actual := PeriodCanonical.comparison_bound kept.mesh kept.requests.chart kept.chart_le
    kept.prepared.triangles kept.chart
  have paid := actual.trans (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
    (Arithmetic.add_lt_add_left_direct kept.mesh_bound_lt (cochainTarget / 32)))
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq (amount - kept.mesh.value) <
    2 * (cochainTarget / 32 + cochainTarget / 32)) kept.value_eq) paid

/-- The actual gap, mesh and chart caches derive the complete signed gap-to-canonical bound internally. -/
theorem gap_bound : normSq
    (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - kept.value) <
      2 * (cochainTarget / 32 + 2 * (cochainTarget / 32 + cochainTarget / 32)) := by
  have reversed : normSq (kept.mesh.value - kept.value) <
      2 * (cochainTarget / 32 + cochainTarget / 32) := by
    rewrite [show kept.mesh.value - kept.value = -(kept.value - kept.mesh.value) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact kept.canonical_mesh_lt
  rewrite [show gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes
      entries geometry roots
      kept.prepared.numerical.word) - kept.value =
      (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
        kept.prepared.numerical.word) - kept.mesh.value) + (kept.mesh.value - kept.value) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_lt_add_right_direct kept.routed_gap_lt _).trans
        (Arithmetic.add_lt_add_left_direct reversed _)))

/-- The actual ordered P-gap sum meets its independent public canonical-cochain target. -/
theorem gap_lt : normSq
    (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - kept.value) < cochainTarget :=
  kept.gap_bound.trans (PeriodCanonical.three_error_lt cochainPositive)

/-- The same one-bank preparation meets its independently supplied public ordinary-model word target. -/
theorem model_lt : normSq
    (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) -
      (PathModel.mk (PolynomialWork.Models.cells parentRequests.covered kept.prepared.numerical.work
        kept.prepared.numerical.models)).integralSample) < wordTarget :=
  kept.prepared.gaps_accurate.trans_le
    (PeriodCanonical.wordAllowance_le wordTarget cochainTarget faces.view.geometry.indexed.length)

/-- The SAME retained six-cache products pay actual A's fresh-basis cochain discrepancy. -/
theorem a_difference_lt (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.aDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values)) < cochainTarget / 32 :=
  kept.prepared.a_accurate degree

/-- The SAME retained six-cache products pay full corrected B's fresh-basis cochain discrepancy. -/
theorem b_difference_lt (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.bDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values)) < cochainTarget / 32 :=
  kept.prepared.b_accurate degree

/-- The actual original A-period gap sum meets the fresh canonical period combination on the SAME P bank.

The two whole original-owner identities identify the chosen period cache;
they do not assert a numerical or root comparison. They are reflexive for
the original A-period caller. All four numerical charges are derived from
the retained route, mesh, chart and six paired comparison caches.
-/
theorem a_cochain_lt (vertexFactory : vertex = anchor original oldSheet)
    (periodFactory : HEq period (periods.aWalk rowIndex))
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - coordinates.a.coordinates.periodValue
        (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values)) < cochainTarget := by
  cases vertexFactory
  have samePeriod : period = periods.aWalk rowIndex := eq_of_heq periodFactory
  cases samePeriod
  let valuation := CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values
  have actualValue : kept.value - coordinates.a.coordinates.periodValue valuation =
      coordinates.aDifference valuation :=
    (congrArg (fun amount : Canonical => amount - coordinates.a.coordinates.periodValue valuation)
      kept.value_eq).trans (coordinates.a_period_difference faces valuation)
  have paired : normSq (kept.value - coordinates.a.coordinates.periodValue valuation) < cochainTarget / 32 :=
    Eq.mpr (congrArg (fun amount : Canonical => normSq amount < cochainTarget / 32) actualValue)
      (kept.a_difference_lt degree)
  rewrite [show gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes
      entries geometry roots
      kept.prepared.numerical.word) - coordinates.a.coordinates.periodValue valuation =
      (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
        kept.prepared.numerical.word) - kept.value) + (kept.value - coordinates.a.coordinates.periodValue valuation)
        by ring1]
  have total := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_lt_add_right_direct kept.gap_bound _).trans
        (Arithmetic.add_lt_add_left_direct paired _)))
  exact total.trans (PeriodCanonical.four_error_lt cochainPositive)

/-- The full original corrected-B gap sum meets its fresh canonical period combination on that SAME P bank.

The literal whole B preparation and its original vertex identity preserve
the full ordered corrected word. All retained stationary, repeated and
closing occurrences and nonzero primitive jumps remain in the bound.
-/
theorem b_cochain_lt (vertexFactory : vertex = anchor original oldSheet)
    (periodFactory : HEq period (periods.bWalk rowIndex))
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
      kept.prepared.numerical.word) - coordinates.b.coordinates.periodValue
        (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values)) < cochainTarget := by
  cases vertexFactory
  have samePeriod : period = periods.bWalk rowIndex := eq_of_heq periodFactory
  cases samePeriod
  let valuation := CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.prepared.triangles.values
  have actualValue : kept.value - coordinates.b.coordinates.periodValue valuation =
      coordinates.bDifference valuation :=
    (congrArg (fun amount : Canonical => amount - coordinates.b.coordinates.periodValue valuation)
      kept.value_eq).trans (coordinates.b_period_difference faces valuation)
  have paired : normSq (kept.value - coordinates.b.coordinates.periodValue valuation) < cochainTarget / 32 :=
    Eq.mpr (congrArg (fun amount : Canonical => normSq amount < cochainTarget / 32) actualValue)
      (kept.b_difference_lt degree)
  rewrite [show gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes
      entries geometry roots
      kept.prepared.numerical.word) - coordinates.b.coordinates.periodValue valuation =
      (gaussianSum (SplitSheets.Closed.gaps kept.prepared.numerical.sharedMeshes entries geometry roots
        kept.prepared.numerical.word) - kept.value) + (kept.value - coordinates.b.coordinates.periodValue valuation)
        by ring1]
  have total := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_lt_add_right_direct kept.gap_bound _).trans
        (Arithmetic.add_lt_add_left_direct paired _)))
  exact total.trans (PeriodCanonical.four_error_lt cochainPositive)

end CanonicalPreparation

/-- The given-preparation worker forwards the SAME original complete single-bank preparation. -/
theorem fromPreparation_prepared
    (originals : CanonicalInputs (pointPrefix := pointPrefix) (extraPoints := extraPoints)
      (sourceSheet := sourceSheet) coordinates domains reference faces word rooted routing charts)
    (needed : {value : CanonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive //
      value = canonicalRequests domains minimum faces rooted routing charts polynomial
        wordTarget cochainTarget cochainPositive})
    (prepared : {value : WordPreparation coordinates (standardDifferential rowIndex) domains
        (cochainTarget / 32) (PeriodCanonical.cochainShare_positive cochainPositive)
        needed.val.stage word polynomial
        (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
        (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
        minimumFloor modelStage //
      value = prepareWord coordinates (standardDifferential rowIndex) domains (cochainTarget / 32)
        (PeriodCanonical.cochainShare_positive cochainPositive) needed.val.stage word polynomial
        (PeriodCanonical.wordAllowance wordTarget cochainTarget faces.view.geometry.indexed.length)
        (PeriodCanonical.wordAllowance_positive wordPositive cochainPositive faces.view.geometry.indexed.length)
        minimumFloor modelStage}) :
    (fromPreparation coordinates domains minimum reference faces word rooted routing charts polynomial
      wordTarget cochainTarget wordPositive cochainPositive minimumFloor modelStage
      originals needed prepared).prepared = prepared.val := by
  unfold fromPreparation CanonicalPreparation.prepared
  rfl

end ComparisonRequests

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates
