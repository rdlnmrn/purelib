module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedSources
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedSources.Lifted.OuterPreparation

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! The pre-grid Newton budget controls either lap's retained source polygon.
Membership and occurrence count are kept separate so repeated edges are counted. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SubwordArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation (Comparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original}

namespace NewtonPreparation

namespace AreaRequest

variable {target radius : Rational}

/-- The actual paired source-subword area satisfies the pre-grid Newton target.

Both original differential readings must meet their retained reference stages; source membership and occurrence-count
bounds are supplied separately. -/
theorem paired_subword_area_accurate (request : NewtonPreparation.AreaRequest preparation target radius)
    {index : BranchIsolation.Data.Index branches} {annulus : Faces.AnnularFaces request.grid index}
    {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured} {region : LiftedBoundary.Lifted annulus lifted}
    {prepared : Lifted.OuterPreparation region} {differential : Fin genus}
    {domains : DomainBanks.FaceDomainBank lifted.frames request.grid.faces.regulars}
    (comparison : OuterPreparation.Comparison prepared differential domains request.budget.scale)
    {other : Fin genus} (second : OuterPreparation.Comparison prepared other domains request.budget.scale)
    (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (members : ∀ source ∈ sources, source ∈ prepared.sources)
    (length : sources.length ≤ region.outer.length)
    {stage : Nat} (later : comparison.reference.index ≤ stage) (secondLater : second.reference.index ≤ stage)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    {secondBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential other) stage domains}
    (secondReadings : TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (sources.map (fun source =>
      (⟨source.increment readings.values, source.increment secondReadings.values⟩ : Stokes.PrimitivePoint)))) < target
        := by
  have count := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le sources.length))
    (Fraction.Cast.Order.natCast_le_direct (length.trans (request.outer_count region))) 2
  have increment := request.budget.increment_le
  have nonnegative := comparison.reference.bound_nonnegative
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct count increment nonnegative
    (Fraction.Order.Arithmetic.sq_nonneg_direct (request.count : Fraction.Rational))
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) nonnegative) product 2
  have sourceBound := Comparison.paired_source_bound comparison second later secondLater readings secondReadings
  have areaBound := PairedIncrementArea.area_bound (sources.map (fun source =>
    (⟨source.increment readings.values, source.increment secondReadings.values⟩ : Stokes.PrimitivePoint)))
    nonnegative (by
      intro point member
      obtain ⟨source, present, equal⟩ := Map.mem_map.mp member
      exact sourceBound point (Map.mem_map.mpr ⟨source, members source present, equal⟩))
  rw [Data.List.Map.length_map] at areaBound
  have bounded := areaBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by decide : (0 : Fraction.Rational) ≤ 4))
  exact bounded.trans_lt ((show 4 * ((request.count : Fraction.Rational) ^ 2 * (4 * request.budget.scale)) ^ 2 =
    64 * (request.count : Fraction.Rational) ^ 4 * request.budget.scale ^ 2 by ring1).trans_lt request.budget.area_paid)

end AreaRequest
end NewtonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SubwordArea
