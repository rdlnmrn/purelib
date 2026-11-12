module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
public import Purelib.Riemann.Paths.PreparedPathSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SegmentWalkGroups
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Actual source groups for a given resplit period on one numerator bank

The same retained source spine, genuine parent ancestry and signed root
chain determine the moving groups on the actual resplit walk. The given
whole-owner face assignment supplies its real initial sheet. The scalar
identity reads one literal numerator bank without preparing a period,
source, root frame, selector, numerical bank or homotopy.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords (PathSourceWords)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries
open Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  renaming LiftedSources -> SourceSpine
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {original : ClearGrid curve.polynomial (Ambient curve)}
    {base : FramedPuncturedGrid curve branches higher} {point : Canonical}
    {owner : Owner (curve.polynomial.eval point)} {source periodSource : Differential genus}
    {period : PeriodWalk original point owner periodSource}
    {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
    {mesh : LiftedMesh vertices edges base.faces} {domains : FaceDomainBank frames base.faces.regulars}
    {axes : PrimitiveAxes base.bank.grid} {parents : List (CenteredEdge curve source)}
    {splits : PrimitiveSplits axes parents} {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {target : Rational} {requests : Riemann.Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SplitSheets domains fragments requests} {sheet : Fin 2}
    (sources : SourceSpine mesh entries) (ancestry : PathSources sheet period.closed.walk.path parents)
    (roots : RootChain parents (ownerName owner) (ownerName owner))
    (member : ContainsVertex original point) (included : CoordinateInclusion original base.bank.grid)

include ancestry roots in
/-- The actual retained source fragments group on the original period's resplit walk with both signed root endpoints.

Whole parent ancestry and the SAME supplied root chain produce the source
words. The period construction and recast source parents may use independent
differentials; the grouping retains their original common path and root owners.
Moving-group transport removes only certified stationary pieces
from this proof view; the original source spine and numerical occurrence
lists remain unchanged.
-/
theorem groups : WalkGroups (included.resplit period.closed.walk member) (ownerName owner) (ownerName owner)
    (LiftedFragment.movingPieces (LiftedSources.pieces sources)) :=
  (PathSourceWords.ofParents ancestry (LiftedSources.parentGroups sources) roots).moving.walk_groups
    (fun _ present => (LiftedFragment.movingPieces_mem present).2)
    (included.path _ (period.closed.walk.vertices member))

variable {points : List Canonical} {tolerance : Rational} {index : Nat} {numerator : CoefficientPolynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := numerator) domains}

include ancestry roots in
/-- The actual canonical-route source sum is the SAME resplit walk reading on the literal supplied numerator bank.

The face assignment is the given whole-owner selection, not a sheet
label inferred from coordinates. This scalar readback preserves the
stationary sum and every ordered moving occurrence. Point membership,
finite numerical payment and canonical period comparison remain distinct
certificates; none is postulated by the equality.
-/
theorem routed_sum_of_sources
    (faces : OwnerWalkFaces mesh (included.resplit period.closed.walk member) owner)
    (shared : FaceSharedMeshes budgets numerics) :
    gaussianSum ((LiftedSources.pieces sources).map (fun piece => RouteContacts.routeValue piece
      (RouteWords.canonicalRoute piece) shared)) =
      gaussianSum ((SkeletonFaceAssignments.walkFaces mesh (included.resplit period.closed.walk member)
        faces.sheet).values (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route)) :=
  (LiftedFragment.movingPieces_sum (LiftedSources.pieces sources) shared).symm.trans
    (Standard.GroupedReadings.OwnerWalkFaces.grouped_read faces
      (groups (period := period) sources ancestry roots member included) rfl shared)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
