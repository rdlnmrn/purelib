module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.List.Permutation
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.GeneratorValuations
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation
import Purelib.Topology.Surface.Cut.SourceUniqueness
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

public section

/-! The annular inner occurrences are the original physical hole occurrences
in the same cut polygon. Equality holds before reading primitive values. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback.InnerOccurrences

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.SourceUniqueness
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Word.GeneratorValuations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance (InnerOccurrences)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge SourceContact)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts (nodup_ofFn_injective)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius}
    {lifted : LiftedPuncturedGrid grid.punctured}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
    AnnularFaces grid index}
  {region : Lifted annulus lifted}

/-- Every retained source occurrence projecting to the original physical inner hole word has positive source
orientation. -/
private theorem positive_sources
    (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      region.hole.liftedBoundary lifted.vertices lifted.edges) :
    ∀ source ∈ sources, SourceEdge.Positive source lifted.mesh.triangulation.faces := by
  intro source member
  apply BranchHoleSourceComparison.physicalSource_positive lifted source
  apply SimpleBoundaryCycles.mem_flatten.mpr
  refine ⟨_, Data.List.Membership.mem_append.mpr (Or.inr (Map.mem_map_of_mem region.hole_mem)), ?_⟩
  exact projected ▸ Map.mem_map_of_mem member

/-- The retained inner source occurrences equal those of any physical cut word with the same original hole projection.
-/
theorem sources_eq_physical (inner : CutBalance.InnerOccurrences region)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted (region.hole.liftedBoundary lifted.vertices lifted.edges)) :
    inner.word.sources.sources = physical.sources.sources := by
  have projected := inner.word.sources.sources_project.trans (inner.project.trans region.inner_eq)
  exact SourceEdge.list_eq_of_project_eq lifted.mesh.orientedEdges_unique
    (LiftedMesh.corners_injective lifted.mesh)
    _ _ (positive_sources _ projected)
      (positive_sources _
      physical.sources_project)
    (projected.trans physical.sources_project.symm)

/-- Physical source uniqueness and complete, nonduplicated face coverage identify the actual cut edges, not just their
projected coordinates. -/
theorem edges_eq_physical (inner : CutBalance.InnerOccurrences region)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted (region.hole.liftedBoundary lifted.vertices lifted.edges)) :
    inner.word.edges = physical.edges := by
  have unique := Permutation.nodup lifted.cutPolygon.coverage.symm
    (BoundaryCounts.nodup_ofFn_injective (fun index : Fin lifted.mesh.triangles.length => index) (fun _ _ same => same))
  exact PathSources.edges_eq_of_sources_eq
    unique inner.word.sources physical.sources
      (sources_eq_physical inner physical)

/-- Reading any primitive bank on the retained inner edges gives exactly the area of the original physical cut word. -/
theorem area_eq_physical (inner : CutBalance.InnerOccurrences region)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted (region.hole.liftedBoundary lifted.vertices lifted.edges))
    (primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive inner.word.edges = Stokes.edgeListArea primitive physical.edges :=
  congrArg (Stokes.edgeListArea primitive)
    (edges_eq_physical inner physical)

/-- Reuse the retained inner edges and source owners as a physical word. The independently located word appears only in
the erased membership proof. -/
@[expose] def toPhysical (inner : CutBalance.InnerOccurrences region) :
    BranchHoleCutWords.PhysicalCutWord lifted (region.hole.liftedBoundary lifted.vertices lifted.edges) where
  edges := inner.word.edges
  physical := by
    let canonical := BranchHoleCutWords.holeCutWord lifted region.hole region.hole_mem
    intro edge member
    exact canonical.physical edge
      (edges_eq_physical inner canonical ▸
      member)
  project := inner.project.trans region.inner_eq
  sources := inner.word.sources

/-- The existing physical-generator valuation now consumes the retained annular occurrences directly, without a new path
or primitive preparation. -/
theorem generator_sum (inner : CutBalance.InnerOccurrences region)
    (values : PrimitiveSewing.PrimitiveValues lifted.cutPolygon.patch.cut.count) :
    SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun index =>
      values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).finish -
        values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators index).start))
      (region.hole.liftedBoundary lifted.vertices lifted.edges) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (inner.word.edges.map fun edge =>
        values edge.finish - values edge.start) :=
  PhysicalCutWord.generator_sum (toPhysical
    inner) values

/-- The existing physical cancellation request pays the retained annular inner increments on the actual sewn bank. This
is an integral estimate, not a claim that its raw area vanishes. -/
theorem requested_increment_accurate (inner : CutBalance.InnerOccurrences region)
    {domains : DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
    {differential : Differentials.Basic.Differential genus}
    {contacts : List (SewnPrimitiveContacts.SourceContact lifted.mesh.triangulation.faces)}
    {covered : ContactBanks.ContactPreparations contacts differential domains}
    {error : Fraction.Rational} {floor stage : Nat}
    (requested : BranchHoleCutCancellation.BranchHoleCutRequest region.hole covered error floor)
    (later : requested.contactRequest.index ≤ stage)
    {shared : PrimitiveData.FacePrimitiveBank differential stage domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (inner.word.edges.map fun edge =>
        surface.sewn.values edge.finish - surface.sewn.values edge.start)) < error := by
  rw [edges_eq_physical inner requested.cut]
  exact requested.accurate later triangles surface

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback.InnerOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback.PairedSewnRequest.AnnularSample

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.SourceUniqueness
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Word.GeneratorValuations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests (PairedSewnRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests (AnnularSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error
    radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {lifted : LiftedPuncturedGrid request.grid.punctured}
  {differential other : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.grid.faces.regulars} {stage floor : Nat}
  {shared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {surface : CachedSample lifted.cutPolygon.patch
    readings.values}
  {otherShared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential other) stage domains}
  {otherReadings : TriangleReadings
    otherShared lifted.mesh}
  {otherSurface : CachedSample lifted.cutPolygon.patch
    otherReadings.values}

variable {annulus : SewnAnnulus surface} {prepared :
  OuterPreparation annulus.source.region}
  {requested : PairedSewnRequest request prepared differential
    other domains floor}

/-- Read the cached annular inner area on the actual physical cut word. The same two sewn scalar banks supply both
coordinates. -/
theorem innerArea_eq_physical (sample : PairedCutRequests.AnnularSample annulus prepared requested otherSurface)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted
      (annulus.source.region.hole.liftedBoundary lifted.vertices lifted.edges)) :
    sample.innerArea = Stokes.edgeListArea (fun vertex =>
      (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)) physical.edges :=
  sample.innerArea_eq.trans (Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback.InnerOccurrences.area_eq_physical
    sample.balance.inner physical _)

/-- The physical inner contribution is identified exactly; the other three correction terms are still present and
require their own accounting. -/
theorem correction_eq_physical (sample : PairedCutRequests.AnnularSample annulus prepared requested otherSurface)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted
      (annulus.source.region.hole.liftedBoundary lifted.vertices lifted.edges)) :
    sample.correction = Stokes.edgeListArea (fun vertex =>
      (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)) physical.edges +
      sample.paired.jumpSum + sample.paired.defectSum + sample.outer.correction := by
  rw [sample.correction_eq,
    innerArea_eq_physical
    sample physical]

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback.PairedSewnRequest.AnnularSample
