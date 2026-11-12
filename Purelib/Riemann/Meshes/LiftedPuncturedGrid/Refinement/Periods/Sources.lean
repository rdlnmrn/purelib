module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes.Sources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.Polynomial
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Retained source groups on the original period-face word

Actual source ancestry and signed root data feed the given whole-owner
period view. The canonical-route factory and its retained Some numerical
request then align the cached routed sum with that same mesh reading.
No model, source, owner, Frame selection, bank or period is reconstructed.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PeriodFaces

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Fragment.RegularFaces (RegularPrimitiveSplits)
open Fragment.RootedWords (LiftedFragment)
open Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries renaming LiftedSources -> SourceSpine
open Fragment.RouteWords (RouteRequest RouteRequests canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus patchCount sampleCount : Nat} {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {base : FramedPuncturedGrid curve branches higher} {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial patchCount)}
    {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original clearance} {vertex : Fin original.vertices.count}
    {source : Differential genus}
    {period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
      (original.vertices.owner original.frames vertex) source}
    (kept : PeriodFaces retained vertex period)
    {domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars}
    {axes : PrimitiveAxes retained.fineBase.bank.grid} {parents : List (CenteredEdge curve source)}
    {splits : PrimitiveSplits axes parents} {fragments : RegularPrimitiveSplits (base := retained.fineBase) axes splits}
    {requestTarget : Rational} {requests : RequestedParents sampleCount requestTarget parents}
    {entries : SplitSheets domains fragments requests} {sheet : Fin 2}
    (sources : SourceSpine retained.fine.mesh entries)
    (ancestry : PathSources sheet period.closed.walk.path parents)
    (roots : RootChain parents (ownerName (original.vertices.owner original.frames vertex))
      (ownerName (original.vertices.owner original.frames vertex)))
    {points : List Canonical} {tolerance : Rational} {index : Nat} {numerator : CoefficientPolynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : FaceSharedMeshes budgets numerics)

include ancestry roots in
/-- The actual canonical-route source sum is the same selected period mesh reading on the given numerator bank.

The original whole Frame/Owner view supplies its actual sheet and exact
face-word geometry. Genuine source and root certificates supply every
ordered group, including the separate stationary-sum transport. No sheet
or root identity is inferred from equal coordinates.
-/
theorem routed_source_sum :
    gaussianSum ((LiftedSources.pieces sources).map (fun piece => RouteContacts.routeValue piece
      (canonicalRoute piece) shared)) =
      gaussianSum (kept.view.geometry.values (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement shared
          route)) := by
  have geometric : SkeletonFaceAssignments.walkFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)) kept.view.sheet =
      kept.view.geometry :=
    (congrArg (SkeletonFaceAssignments.walkFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)))
      kept.view_sheet).trans kept.view_geometry.symm
  have meshSum := congrArg (fun assigned : PathFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)).path =>
      gaussianSum (assigned.values (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route)))
          geometric
  exact (Inclusion.PeriodRoutes.routed_sum_of_sources (period := period) sources ancestry roots
    (original.vertices.coordinate_onGrid vertex) retained.included kept.view shared).trans meshSum

section Polynomial

open Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources (Rooted)

variable {ordinary : Ordinary curve.polynomial}
    {nextBudgets : FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains}
    {nextNumerics : FacePrimitiveBank source index (numerator := ordinary.numerator) domains}
    (nextShared : FaceSharedMeshes nextBudgets nextNumerics)
    {point : LiftedPoint 2} {geometry : CenteredPathChain parents (start := point) (finish := point)}
    {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (closed : SplitSheets.Closed nextShared entries geometry roots included)
    (word : Rooted entries retained.fine.mesh (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)) (original.vertices.coordinate vertex)
      (ownerName (original.vertices.owner original.frames vertex)))
    {allowance : Rational} (positive : 0 < allowance)
    (routing : RouteRequest word.pieces allowance)
    (routingFactory : routing = RouteRequest.build word.pieces canonicalRoute allowance positive)
    (requested : {value : RouteRequest word.pieces allowance (some ordinary) // value = routing.onNumerator ordinary})
    {later : requested.val.index ≤ index}
    (readings : RouteRequest.PolynomialReadings nextShared closed word routing requested later)

include ancestry routingFactory positive in
/-- The retained genuine-P route cache reads the SAME original period-face word, with both whole request factories.

Only the given cached right increments and actual raw/Some request
identities are consumed. Whole source-list equality is proof transport;
no route, SourceSpine, query, owner or observation is reconstructed.
-/
theorem polynomial_routed_value_eq : readings.value =
    gaussianSum (kept.view.geometry.values
      (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement nextShared route)) := by
  have requestsEq : requested.val.requests = routing.requests.onNumerator ordinary
      (perTerm_positive routing.positive word.pieces.length) :=
    (congrArg (fun actual : RouteRequest word.pieces allowance (some ordinary) => actual.requests)
      requested.property).trans (routing.onNumerator_requests ordinary)
  have numeratorValues : requested.val.requests.values nextShared = routing.requests.values nextShared :=
    (congrArg (fun actual : RouteRequests (perTerm allowance word.pieces.length) word.pieces (some ordinary) =>
      actual.values nextShared) requestsEq).trans
        (RouteRequests.onNumerator_values ordinary (perTerm_positive routing.positive word.pieces.length)
          nextShared routing.requests)
  have chosen : routing.requests.values nextShared =
      word.pieces.map (fun piece => RouteContacts.routeValue piece (canonicalRoute piece) nextShared) :=
    (congrArg (fun actual : RouteRequest word.pieces allowance => actual.requests.values nextShared)
      routingFactory).trans
        (RouteRequests.build_values (perTerm allowance word.pieces.length)
          (perTerm_positive positive word.pieces.length) canonicalRoute word.pieces nextShared)
  have supplied : gaussianSum (word.pieces.map (fun piece => RouteContacts.routeValue piece
      (canonicalRoute piece) nextShared)) =
      gaussianSum ((LiftedSources.pieces word.sources).map (fun piece => RouteContacts.routeValue piece
        (canonicalRoute piece) nextShared)) :=
    congrArg (fun pieces : List (LiftedFragment axes domains retained.fine.mesh source sampleCount requestTarget) =>
      gaussianSum (pieces.map (fun piece => RouteContacts.routeValue piece (canonicalRoute piece) nextShared)))
      word.pieces_eq
  exact (readings.value_eq.trans (congrArg gaussianSum
    (readings.routed_values_eq.trans (numeratorValues.trans chosen)))).trans
      (supplied.trans (routed_source_sum (period := period) kept word.sources ancestry roots nextShared))

include ancestry routingFactory positive readings in
/-- The actual ordered outgoing-gap sum and selected original period mesh reading meet the literal route allowance.

Every comparison and occurrence comes from the retained numerical word.
This is the paid routing contribution; mesh-corner, actual Some chart,
source-programme and canonical-cycle certificates remain distinct.
-/
theorem polynomial_routed_gap_lt : normSq
    (gaussianSum (SplitSheets.Closed.gaps nextShared entries geometry roots closed) -
      gaussianSum (kept.view.geometry.values
        (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement nextShared route))) < allowance :=
  Eq.mp (congrArg (fun actual : Canonical => normSq
    (gaussianSum (SplitSheets.Closed.gaps nextShared entries geometry roots closed) - actual) < allowance)
      (polynomial_routed_value_eq (period := period) (kept := kept) (ancestry := ancestry) (roots := roots)
        (nextShared := nextShared) (closed := closed) (word := word) (positive := positive)
        (routing := routing) (routingFactory := routingFactory) (requested := requested) (readings := readings)))
    readings.accurate

end Polynomial

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PeriodFaces
