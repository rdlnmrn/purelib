module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalRequests
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Data

/-! Aggregate the physical-hole cancellation on the exact cached annular
sample, with a proved readback to the original excision-entry list. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalAggregate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
  (PairedAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Term Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (SewnSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {comparison :
    PairedComparison
    prepared first second domains}

namespace SewnSample

variable {stage : Nat} {cache :
  Numerics domains stage}
  {left : TriangleReadings (cache.get first)
    lifted.mesh} {right : TriangleReadings
    (cache.get second) lifted.mesh}
  {source :
    PairedComparison.Sample
    comparison left right}
  {leftSurface : CachedSample lifted.cutPolygon.patch left.values}
  {rightSurface : CachedSample lifted.cutPolygon.patch
    right.values}

/-- The retained sewn annular terms project to exactly the original excision entry list. -/
theorem physical_entries (sample : PairedComparison.SewnSample source leftSurface rightSurface) :
    sample.terms.map (fun term => term.source.source.source.entry) = excision.entries := by
  have mapFirst := congrArg (List.map (fun term : PairedComparison.Term left right => term.source.source.entry))
    sample.terms_eq
  have mapSecond := congrArg (List.map (fun entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains
    => entry.source.entry)) source.terms_eq
  have mapThird := congrArg (List.map (fun entry : AnnularEntry.Prepared request.single.grid lifted => entry.entry))
    comparison.entries_eq
  rw [List.Map.map_map] at mapFirst mapSecond mapThird
  exact mapFirst.trans (mapSecond.trans (mapThird.trans prepared.entries_eq))

/-- The physical-hole sum of the retained sewn terms equals the sum on the original excision entries. -/
theorem physical_sum (sample : PairedComparison.SewnSample source leftSurface rightSurface) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map (fun term => AnnularEntry.physicalHoleArea
      term.source.source.source.entry left right)) =
      CellBoundary.sumValues (fun entry => AnnularEntry.physicalHoleArea entry left right) excision.entries := by
  have equal := congrArg (CellBoundary.sumValues (fun entry => AnnularEntry.physicalHoleArea entry left right))
    (physical_entries sample)
  refine Eq.trans ?_ equal
  induction sample.terms with
  | nil => rfl
  | cons term tail ih =>
    exact congrArg (AnnularEntry.physicalHoleArea term.source.source.source.entry left right + ·) ih

/-- The retained selected areas plus their actual physical-hole polygons sum to the original aggregate selected area and
hole sum. -/
theorem physical_corrected_sum (sample : PairedComparison.SewnSample source leftSurface rightSurface) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map (fun term =>
      term.data.selectedArea + AnnularEntry.physicalHoleArea term.source.source.source.entry left right)) =
      sample.selectedArea + CellBoundary.sumValues (fun entry => AnnularEntry.physicalHoleArea entry left right)
        excision.entries := by
  rw [sample.selectedArea_eq, ←
    physical_sum sample]
  induction sample.terms with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0; ring1
  | cons term tail ih =>
      change (term.data.selectedArea + _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum _ =
        (term.data.selectedArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum _) + (_ +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum _)
      rw [ih]
      ring1

end SewnSample

/-- The existing sample's annular area plus the physical polygons is small. The per-hole count budget precedes the
Newton grid, and is paid twice. -/
@[expose] def physicalRequest (comparison : PairedComparison prepared first second domains)
    (sewing : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first second) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get second) lifted.mesh)
        (source : PairedComparison.Sample comparison left right)
        (leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
        (sample : PairedComparison.SewnSample source leftSurface rightSurface), threshold ≤ stage →
        Data.Gaussian.Norm.Basic.normSq (sample.selectedArea + CellBoundary.sumValues (fun entry =>
          AnnularEntry.physicalHoleArea entry left right) excision.entries) <
          (82 / 4 : Fraction.Rational) * target} := by
  let acquired := PairedAnnulus.physicalRequests sewing floor comparison.entries
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right source leftSurface rightSurface sample later
  have bounds : ∀ value ∈ sample.terms.map (fun term =>
      term.data.selectedArea + AnnularEntry.physicalHoleArea term.source.source.source.entry left right),
      Data.Gaussian.Norm.Basic.normSq value ≤ (82 / 4 : Fraction.Rational) * request.perHole := by
    intro value member
    obtain ⟨term, present, rfl⟩ := Map.mem_map.mp member
    have retained : term.source.source ∈ comparison.entries := source.terms_eq ▸
      Map.mem_map_of_mem (sample.terms_eq ▸ Map.mem_map_of_mem present)
    have estimate := acquired.property.2 term.source.source retained stage cache left right leftSurface rightSurface
      term.selected later
    have estimate := (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (area +
      AnnularEntry.physicalHoleArea term.source.source.source.entry left right))
      term.data.selectedArea_eq).trans_le estimate
    exact estimate.trans_eq (by simp only [Purelib.Data.Rat.Fraction.Field.div_eq_mul_inv_direct]; ring1)
  have count : (sample.terms.map (fun term =>
      term.data.selectedArea + AnnularEntry.physicalHoleArea term.source.source.source.entry left right)).length ≤
        request.count := by
    rw [List.Map.length_map]
    exact sample.terms_count
  have factorPositive : (0 : Fraction.Rational) < 82 / 4 := Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 82) (by decide)) (by decide)
  have estimate := IncrementArea.sum_bound_of_length
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le request.perHole_positive.le) bounds count
  rw [SewnSample.physical_corrected_sum sample] at estimate
  have paid : (request.count : Fraction.Rational)^2 * request.perHole < target := by
    rw [request.perHole_eq]
    exact (show (request.count : Fraction.Rational)^2 * Aggregate.perTerm target request.count =
      (request.count : Fraction.Rational) * ((request.count : Fraction.Rational) * Aggregate.perTerm target
        request.count) by ring1).trans_lt
      (Aggregate.count_mul_perTerm_lt request.positive request.count)
  exact estimate.trans_lt ((show (request.count : Fraction.Rational)^2 * ((82 / 4 : Fraction.Rational) *
    request.perHole) =
    (82 / 4 : Fraction.Rational) * ((request.count : Fraction.Rational)^2 * request.perHole) by ring1).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive paid))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalAggregate
