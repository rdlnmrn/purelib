module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Polynomial.Geometry.Grid.WindowSize
public import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

/-!
# Requested small areas on the actual Newton annulus tours

Choose the shared Newton scale using a fixed count cap before constructing
the grid. Its total constructor supplies the cap for every resulting band
window. Every later shared primitive bank then has small complete source
polygons, with no caller mesh-size or successful-refinement assumption.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}

namespace NewtonPreparation

/-- Original line counts and branch count are all fixed before shrinking. -/
@[expose] def outerCount (_preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  : Nat :=
  4 * (original.grid.vertical.length + original.grid.horizontal.length + 4 + 4 * branches.siteCount)

/-- The canonical Newton grid's line count is bounded by the fixed original preparation count. -/
theorem build_lineCount (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  {target radius : Fraction.Rational}
    (positive : 0 < target) (radiusPositive : 0 < radius) :
    4 * ((RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid.build preparation positive
      radiusPositive).shrunk.prepared.grid.vertical.length +
      (RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid.build preparation positive
        radiusPositive).shrunk.prepared.grid.horizontal.length) ≤
        Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation := open
        Purelib.Polynomial in by
  let bands := RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation.Bands.build preparation positive
    radiusPositive
  have lineCount := Polynomial.Geometry.Grid.WindowSize.withFrame_lineCount original.grid
    preparation.shrinking.clearance
    bands.neighborhoods.listed
  have stateCount : bands.neighborhoods.listed.length = branches.siteCount := by
    rw [bands.neighborhoods.listed_eq, Purelib.Data.List.OfFn.Basic.length_ofFn]
  rw [stateCount] at lineCount
  exact Nat.mul_le_mul_left 4 lineCount

set_option genInjectivity false in
/-- The numerical budget precedes the grid. The count certificate accepts
checked alternative grids without equating them to the canonical search. -/
structure AreaRequest (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  (target radius : Fraction.Rational) where
  /-- The count fixed before the grid is constructed. -/ count : Nat
  /-- The retained count equals the original preparation's outer count. -/ count_eq : count =
    Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation
  /-- The original positive path budget for that exact count and target. -/ budget :
    RootContinuation.NewtonPathBudget.PathBudget count target
  /-- The Newton grid built at the original budget's scale and radius. -/ grid :
    RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation budget.scale radius
  /-- The actual retained grid line count. -/ lineCount : Nat
  /-- The line count is exactly the sum of the retained grid dimensions. -/ lineCount_eq : lineCount =
    grid.shrunk.prepared.grid.vertical.length + grid.shrunk.prepared.grid.horizontal.length
  /-- Four times the actual line count is bounded by the original fixed count. -/ lineCount_le : 4 * lineCount ≤ count

constructive_injectivity AreaRequest

namespace AreaRequest

variable {target radius : Fraction.Rational}

/-- Choose the original path budget before building the Newton grid at its retained scale and radius. -/
@[expose] def build (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  (target radius : Fraction.Rational)
    (positive : 0 < target) (radiusPositive : 0 < radius) :
      Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation target radius :=
  let count := Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation
  let budget := RootContinuation.NewtonPathBudget.PathBudget.build count target positive
  let grid := RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid.build preparation budget.scale_positive
    radiusPositive
  ⟨count, rfl, budget, grid, grid.shrunk.prepared.grid.vertical.length + grid.shrunk.prepared.grid.horizontal.length,
    rfl, Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.build_lineCount preparation
      budget.scale_positive radiusPositive⟩

variable {request : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius} {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index} {lifted :
    Meshes.LiftedPuncturedGrid request.grid.punctured}
  {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- The actual two-lap outer boundary length is bounded by the retained request count. -/
theorem outer_count (request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius) {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
    {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index} {lifted :
      Meshes.LiftedPuncturedGrid request.grid.punctured}
    (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) : region.outer.length ≤
      request.count := open Purelib.Polynomial in by
  have count := Polynomial.Geometry.Grid.WindowSize.Window.boundary_edgeCount_le annulus.window
  rw [← request.lineCount_eq] at count
  have cap := request.lineCount_le
  rw [Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted.outer_length region]
  change 2 * annulus.window.boundary.edgeCount ≤ request.count
  omega

/-- The actual hole count is bounded by the square of the original outer count. -/
theorem holes_count (request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius) :
    request.grid.faces.holes.length ≤ Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount
      preparation ^ 2 := open Purelib.Polynomial in by
  have classified := request.grid.faces.length_eq
  have cells := Polynomial.Geometry.Grid.WindowSize.cells_length_le request.grid.shrunk.prepared.grid
  have lines : request.lineCount ≤ request.count := by have cap := request.lineCount_le; omega
  have cap : request.lineCount ^ 2 ≤ request.count ^ 2 := by
    rw [Purelib.Data.Nat.Multiplication.pow_two, Purelib.Data.Nat.Multiplication.pow_two]
    exact Nat.mul_le_mul lines lines
  rw [← request.lineCount_eq] at cells
  rw [request.count_eq] at cap
  exact (Nat.le_add_left _ _).trans (classified.le.trans (cells.trans cap))

/-- Reuse the actual covered outer tour, its root thread and parent bank. -/
@[expose] def compare (request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius)
    {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
      Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index}
    {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured} {region :
      Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
    (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) (differential :
      Fin genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      request.grid.faces.regulars) :
    Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
      domains request.budget.scale :=
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison.build prepared differential
    domains request.budget.scale_positive

/-- The complete original source polygon area is within the target using the actual count cap and retained squared
budget. -/
theorem source_area_accurate (request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius)
    {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
      Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index}
    {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured} {region :
      Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
    {prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region} {differential :
      Fin genus}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      request.grid.faces.regulars}
    (comparison : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared
      differential domains request.budget.scale)
    {stage : Nat} (later : comparison.reference.index ≤ stage)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (prepared.sources.map (fun source =>
      source.increment readings.values))) < target := by
  have count := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le region.outer.length))
    (Fraction.Cast.Order.natCast_le_direct (request.outer_count region)) 2
  have increment := request.budget.increment_le
  have nonnegative := comparison.reference.bound_nonnegative
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct count increment nonnegative
    (Fraction.Order.Arithmetic.sq_nonneg_direct (request.count : Fraction.Rational))
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) nonnegative) product 2
  have bounded :=
    (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison.source_area_bound
    comparison later readings).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by decide : (0 : Fraction.Rational) ≤ 4))
  exact bounded.trans_lt ((show 4 * ((request.count : Fraction.Rational) ^ 2 * (4 * request.budget.scale)) ^ 2 =
    64 * (request.count : Fraction.Rational) ^ 4 * request.budget.scale ^ 2 by ring1).trans_lt request.budget.area_paid)

/-- The same request also pays the physical period correction; this does
not infer small area from a small or vanishing total. -/
theorem source_total_accurate (request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest
  preparation target radius)
    {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
      Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index}
    {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured} {region :
      Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
    {prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region} {differential :
      Fin genus}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      request.grid.faces.regulars}
    (comparison : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared
      differential domains request.budget.scale)
    {stage : Nat} (later : comparison.reference.index ≤ stage)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (prepared.sources.map (fun source => source.increment readings.values))) < target := by
  have bounded : ∀ value ∈ prepared.sources.map (fun source => source.increment readings.values),
      Data.Gaussian.Norm.Basic.normSq value ≤ 4 * request.budget.scale := by
    rw [prepared.sources_eq]
    intro value member
    exact (comparison.reference.source_bound comparison.shared later readings value member).trans
      request.budget.increment_le
  have lengthEq : (prepared.sources.map (fun source => source.increment readings.values)).length = region.outer.length
    := by
    have equal := congrArg List.length
      (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.sources_project prepared)
    rw [Purelib.Data.List.Map.length_map] at equal ⊢
    exact equal
  have total := Path.IncrementArea.sum_bound_of_length
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.budget.scale_positive.le) bounded
    (lengthEq.le.trans (request.outer_count region))
  exact total.trans_lt ((show (request.count : Fraction.Rational) ^ 2 * (4 * request.budget.scale) =
    4 * (request.count : Fraction.Rational) ^ 2 * request.budget.scale by ring1).trans_lt request.budget.total_paid)

end AreaRequest
end NewtonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
