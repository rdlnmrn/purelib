module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedSources
import Purelib.Topology.Surface.Sewing.SewnPairedPathRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.State.Raw
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! One path-area tolerance and two actual contact preparations pay the
paired annular cut-path sewing error at a cached common stage. -/

namespace Purelib.Riemann.Branches.NewtonPairedCutRequests

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation (Comparison)
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation (CutComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : AnnularFaces grid index} {lifted :
    LiftedPuncturedGrid grid.punctured} {region :
    Lifted annulus lifted}
  {prepared : OuterPreparation region}
    {differential : Fin genus}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars} {tolerance : Rational} {other : Fin genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- Two original differential comparisons with one paid paired-area budget and a common contact stage.

Both retained cut comparisons preserve their original inputs; their contact requests share the exact path tolerance and
both reference floors. -/
structure PairedCutRequest (left : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared
  differential domains tolerance)
    (right : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance) (error : Fraction.Rational) (floor : Nat) where
  /-- The retained cut comparison for the first original differential comparison. -/ first : CutComparison prepared
    differential domains tolerance
  /-- The retained cut comparison for the second original differential comparison. -/ second : CutComparison prepared
    other domains tolerance
  /-- The first retained comparison preserves its exact original input. -/ first_eq : first.original = left
  /-- The second retained comparison preserves its exact original input. -/ second_eq : second.original = right
  /-- The shared paired-area budget for the original outer-boundary count and scalar bound. -/ budget :
    Sewing.SewnPathAreaRequests.PathAreaRequest lifted.cutPolygon.patch.assembly region.outer.length
    (3 * tolerance + 4 * (target / 16)) error
  /-- The first retained contact request at the shared tolerance and combined reference floor. -/ firstContact :
    Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request first.covered budget.path.tolerance
    (max floor (max left.reference.index right.reference.index))
  /-- The second retained contact request at the shared tolerance and combined reference floor. -/ secondContact :
    Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request second.covered budget.path.tolerance
    (max floor (max left.reference.index right.reference.index))
  /-- The retained common contact stage. -/ stage : Nat
  /-- The common stage is exactly the maximum of the two retained contact indices. -/ stage_eq : stage = max
    firstContact.index secondContact.index

constructive_injectivity PairedCutRequest

namespace PairedCutRequest

variable {left :
  Comparison prepared
  differential domains tolerance}
  {right : Comparison
    prepared other domains tolerance} {error : Rational} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
/-- Prepare both original differential comparisons under one paired-area budget and common stage floor.

The final stage is the maximum of the two retained contact indices, preserving both original reference stages and source
owners. -/
@[expose] def build (left : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared
  differential domains tolerance)
    (right : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance) (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    PairedCutRequest left right error floor :=
  let first := CutComparison.ofComparison left
  let second := CutComparison.ofComparison right
  let budget := Sewing.SewnPathAreaRequests.PathAreaRequest.ofProfile first.profile first.profile_eq region.outer.length
    (3 * tolerance + 4 * (target / 16)) error left.reference.bound_nonnegative positive
  let firstContact := Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build first.covered
    budget.path.tolerance
    budget.path.tolerance_positive (max floor (max left.reference.index right.reference.index))
  let secondContact := Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build second.covered
    budget.path.tolerance
    budget.path.tolerance_positive (max floor (max left.reference.index right.reference.index))
  ⟨first, second, rfl, rfl, budget, firstContact, secondContact,
    max firstContact.index secondContact.index, rfl⟩

/-- A stage meeting the common request meets the first retained contact request. -/
theorem first_later (request : PairedCutRequest left right error floor) {stage : Nat}
    (later : request.stage ≤ stage) : request.firstContact.index ≤ stage :=
  (Nat.Order.le_max_left _ _).trans (request.stage_eq ▸ later)

/-- A stage meeting the common request meets the second retained contact request. -/
theorem second_later (request : PairedCutRequest left right error floor) {stage : Nat}
    (later : request.stage ≤ stage) : request.secondContact.index ≤ stage :=
  (Nat.Order.le_max_right _ _).trans (request.stage_eq ▸ later)

/-- A stage meeting the common request meets both original comparison reference stages. -/
theorem references_later (request : PairedCutRequest left right error floor) {stage : Nat}
    (later : request.stage ≤ stage) : left.reference.index ≤ stage ∧ right.reference.index ≤ stage := by
  have common := (Nat.Order.le_max_right floor _).trans
    (request.firstContact.floor_le.trans (request.first_later later))
  exact ⟨(Nat.Order.le_max_left _ _).trans common, (Nat.Order.le_max_right _ _).trans common⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Surface in
/-- The retained paired request bounds the difference between sewn and original paired increment areas.

Both readings use the same original source word, while separate contact accuracy and scalar magnitude bounds supply the
shared paired-area estimate. -/
theorem accurate (request : PairedCutRequest left right error floor) {stage : Nat}
    (later : request.stage ≤ stage)
    {firstBank : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    {secondBank : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential other) stage domains}
    (firstReadings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh)
    (secondReadings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh)
    (firstSurface : Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch firstReadings.values)
    (secondSurface : Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch secondReadings.values) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (request.first.word.edges.map (fun edge =>
      (⟨firstSurface.sewn.values edge.finish - firstSurface.sewn.values edge.start,
        secondSurface.sewn.values edge.finish - secondSurface.sewn.values edge.start⟩ : PrimitivePoint))) -
      PairedIncrementArea.area (prepared.sources.map (fun source =>
        (⟨Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
          Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ : PrimitivePoint)))) < error
          := by
  have firstAccurate := request.firstContact.localAccuracy_of_coverage
    (fun _ member => request.first.contacts.entries_eq.symm ▸ member) le_rfl
    (request.first_later later) firstReadings firstSurface.sewn.readings
  have secondAccurate := request.secondContact.localAccuracy_of_coverage
    (fun _ member => request.second.contacts.entries_eq.symm ▸ member) le_rfl
    (request.second_later later) secondReadings secondSurface.sewn.readings
  have references := request.references_later later
  have bounded : ∀ source ∈ request.first.word.sources.sources,
      PrimitiveAreaBounds.PrimitivePoint.Bounded
        (⟨Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
          Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ : PrimitivePoint)
        (3 * tolerance + 4 * (target / 16)) := by
    intro source member
    rw [request.first.word.sources_eq, prepared.sources_eq] at member
    have firstScalar := left.reference.source_bound left.shared references.1 firstReadings
      (Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values)
      (Map.mem_map_of_mem member)
    have secondScalar := right.reference.source_bound right.shared references.2 secondReadings
      (Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values)
      (Map.mem_map_of_mem member)
    rw [Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
    exact ⟨firstScalar, secondScalar⟩
  have estimate := Sewing.SewnPairedPathRequests.paired_cached_accurate request.budget firstSurface secondSurface
    firstAccurate secondAccurate request.first.word.sources
    (request.first.word_count.trans request.first.count_eq) bounded
  rw [request.first.word.sources_eq] at estimate
  exact estimate

end PairedCutRequest
end Purelib.Riemann.Branches.NewtonPairedCutRequests
