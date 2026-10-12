module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.GeneratorValuations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
public import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathRequests

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word.GeneratorValuations

public section

/-!
# Fully requested branch-hole increments on the actual sewn cut

The original eight edges are located in the retained one-sided cut boundary.
One common index pays their two-sheet cancellation and every inherited
sewing error. Existing contact preparations and assembly profiles are reused.
The resulting cut edges need not have equal consecutive endpoints.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord holeCutWord)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison (hole_sources_eq)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation (PairedWalkRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Topology.Surface.Sewing.SewnPathRequests (PathRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Differential genus} {contacts : List
    (SourceContact lifted.mesh.triangulation.faces)}

set_option genInjectivity false in
/-- A paid original branch-hole increment request on the actual sewn cut boundary.

The retained eight cut occurrences share the paired two-sheet source cache and covered sewing contacts; their finite sum
includes all inherited offsets. -/
structure BranchHoleCutRequest (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (covered : ContactBanks.ContactPreparations contacts differential domains) (target :
      InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained two-sheet cancellation request on the actual original inward hole boundary. -/ paired :
    WalkCancellation.PairedWalkRequest (mesh := lifted.mesh) domains differential hole.inwardBoundary (target / 4)
  /-- The actual one-sided cut occurrences projecting to the original lifted hole word. -/ cut :
    BranchHoleCutWords.PhysicalCutWord lifted (hole.liftedBoundary lifted.vertices lifted.edges)
  /-- The cut occurrences use exactly the paired request's retained source list. -/ cut_sources : cut.sources.sources =
    paired.sources
  /-- The retained sewing-path budget for these actual eight cut occurrences. -/ path : SewnPathRequests.PathRequest
    lifted.cutPolygon.patch.assembly 8 (target / 4)
  /-- Every original assembly contact is present in the supplied retained contact bank. -/ coverage : ∀ contact ∈
    SewnPrimitiveContacts.sourceContacts lifted.cutPolygon.patch.assembly, contact ∈ contacts
  /-- The covered contact request paying both the caller floor and original paired cancellation stage. -/ contactRequest
    : ContactPreparations.Request covered path.tolerance (max floor paired.index)

constructive_injectivity BranchHoleCutRequest

namespace BranchHoleCutRequest

variable {hole : BranchHole base.bank.toBranchCellBank}
  {covered : ContactPreparations contacts differential
    domains} {target : Coordinate} {floor : Nat}

/-- Several holes share the expensive contact budgets. Only the requested floor is adjusted; the cached budget vector
and its maximum are retained. -/
@[expose] def ofCachedContacts
    (paired : WalkCancellation.PairedWalkRequest (mesh := lifted.mesh) domains differential hole.inwardBoundary (target
      / 4))
    (cut : BranchHoleCutWords.PhysicalCutWord lifted (hole.liftedBoundary lifted.vertices lifted.edges))
    (matching : cut.sources.sources = paired.sources)
    (path : SewnPathRequests.PathRequest lifted.cutPolygon.patch.assembly 8 (target / 4))
    (coverage : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts lifted.cutPolygon.patch.assembly, contact ∈ contacts)
    (cached : ContactPreparations.Request covered path.tolerance 0) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest hole covered target floor
      :=
  ⟨paired, cut, matching, path, coverage,
    { positive := cached.positive
      budgets := cached.budgets
      maximum := cached.maximum
      maximum_eq := cached.maximum_eq
      index := max (max floor paired.index) cached.maximum
      index_eq := rfl }⟩

/-- Accuracy selection preserves the paired source cache, the shared contact geometry and the already computed assembly
profile. -/
@[expose] def ofPaired (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (paired : WalkCancellation.PairedWalkRequest (mesh := lifted.mesh) domains differential hole.inwardBoundary (target
      / 4))
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch lifted.cutBoundaryPairs
      differential domains)
    (floor : Nat) : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest hole
      prepared.prepared target floor :=
  let cut := BranchHoleCutWords.holeCutWord lifted hole retained
  let path := PathRequest.ofProfile prepared.profile prepared.profile_eq 8 (target / 4) paired.positive
  ofCachedContacts paired cut
    (BranchHoleSourceComparison.hole_sources_eq hole retained paired cut.sources.sources cut.sources_project)
    path prepared.sewing_mem (ContactPreparations.Request.build prepared.prepared path.tolerance path.tolerance_positive
      0) floor

/-- Prepare the original hole's paired cancellation and reuse the retained boundary contacts to pay its complete
cut-word increment. -/
@[expose] def build (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch lifted.cutBoundaryPairs
      differential domains)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest hole prepared.prepared
      target floor :=
  ofPaired hole retained
    (BranchHoleCancellation.cancellationRequest hole lifted.mesh domains differential (target / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide))) prepared floor

/-- The retained cut-hole contact stage meets the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest
  hole covered target floor) : floor ≤ request.contactRequest.index :=
  (Data.Nat.Order.le_max_left _ _).trans request.contactRequest.floor_le

/-- Every stage paying the retained cut-hole contacts also pays its original paired cancellation request. -/
theorem paired_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest
  hole covered target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index) : request.paired.index ≤ index :=
  (Data.Nat.Order.le_max_right _ _).trans (request.contactRequest.floor_le.trans later)

/-- The retained cut occurrences project exactly to the original lifted branch-hole boundary. -/
theorem cut_project (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest
  hole covered target floor) :
    request.cut.edges.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) =
      hole.liftedBoundary lifted.vertices lifted.edges :=
  request.cut.project

/-- The actual retained branch-hole cut word has exactly eight occurrences. -/
theorem cut_length (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest
  hole covered target floor) : request.cut.edges.length = 8 :=
  request.cut.length_eq.trans (hole.liftedBoundary_length lifted.vertices lifted.edges)

/-- These are the sewn cut values, including all ancestor offsets. The proof pays their full finite sum without assuming
a closed cut-vertex path. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest
  hole covered target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank differential index domains} (triangles :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.cut.edges.map fun
      edge => surface.sewn.values edge.finish - surface.sewn.values edge.start)) < target := by
  have localAccuracy := request.contactRequest.localAccuracy_of_coverage request.coverage le_rfl later triangles
    surface.sewn.readings
  have sewing := request.path.cached_accurate surface localAccuracy request.cut.sources request.cut_length.le
  have original : Data.Gaussian.Norm.Basic.normSq ((CachedSample.pathSample surface request.cut.sources)).value
    < target / 4 := by
    rw [PathSources.Sample.value_eq_sources, request.cut_sources]
    exact request.paired.accurate triangles (request.paired_later later)
  have bound := ((CachedSample.pathSample surface request.cut.sources)).sum_magnitude_bound original.le
  apply bound.trans_lt
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_right_direct sewing (target / 4))
  apply paid.trans_eq
  rw [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The physical-loop value used by the standard/chord chain comparison is small for the actual retained cut-generator
increments. -/
theorem generator_accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation.BranchHoleCutRequest hole covered target floor)
  {index : Nat}
    (later : request.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank differential index domains} (triangles :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue
      lifted.cutBoundaryPairs (fun column =>
      surface.sewn.values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators
        column).finish -
        surface.sewn.values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators
          column).start))
          (hole.liftedBoundary lifted.vertices lifted.edges)) < target := by
  rw [request.cut.generator_sum surface.sewn.values]
  exact request.accurate later triangles surface

end BranchHoleCutRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation
