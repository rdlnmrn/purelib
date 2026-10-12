module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples
import Batteries.Logic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
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
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! Pay the pre-grid occurrence budget for every cached conjugate annulus
and its actual physical-hole polygons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalRequests
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples (ConjugateSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational}
  {request : Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
    preparation target radius}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid request.single.grid.punctured}
  {excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank
    lifted.frames request.single.grid.faces.regulars}
  {prepared :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {comparison :
    PairedComparison
    prepared first second domains}

/-- The existing sample's annular area plus the physical polygons is small. The per-hole count budget precedes the
Newton grid, and is paid twice. -/
@[expose] def conjugatePhysicalRequest (comparison : PairedComparison prepared first second domains)
    (sewing : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first second) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get second) lifted.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
        (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
        (sample : ConjugateSamples.ConjugateSample left right leftSurface rightSurface pair comparison), threshold ≤
          stage →
        Data.Gaussian.Norm.Basic.normSq (sample.area + sample.holes) <
          (82 / 4 : Fraction.Rational) * target} := by
  let acquired := PairedAnnulus.conjugatePhysicalRequests sewing floor comparison.entries
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right leftSurface rightSurface pair sample later
  have bounds : ∀ value ∈ sample.terms.map (fun term =>
      term.area + term.hole),
      Data.Gaussian.Norm.Basic.normSq value ≤ (82 / 4 : Fraction.Rational) * request.perHole := by
    intro value member
    obtain ⟨term, present, rfl⟩ := Map.mem_map.mp member
    have retained : term.entry ∈ comparison.entries := sample.terms_eq ▸ Map.mem_map_of_mem present
    have estimate := acquired.property.2 term.entry retained stage cache left right leftSurface rightSurface pair
      term.selected later
    have read : term.area + term.hole = Stokes.edgeListArea pair.values
        (term.selected.triangles.flatMap OrientedTriangle.boundary) +
        term.entry.source.entry.conjugatePhysicalHoleArea left right := congrArg₂ (· + ·) term.area_eq term.hole_eq
    have estimate := (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le estimate
    exact estimate.trans_eq (by simp only [Data.Rat.Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]; ring1)
  have count : (sample.terms.map (fun term =>
      term.area + term.hole)).length ≤ request.count := by
    rw [Data.List.Map.length_map]
    exact ConjugateSample.terms_count sample
  have factorPositive : (0 : Fraction.Rational) < 82 / 4 := Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 82) (by decide)) (by decide)
  have estimate := IncrementArea.sum_bound_of_length
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le request.perHole_positive.le) bounds count
  rw [ConjugateSample.residuals_sum sample] at estimate
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

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate
