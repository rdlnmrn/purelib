module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartRequests
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! Transfer complete source polygons to the antisymmetric edge valuation.
Every occurrence retains its signed chart request; a fixed magnitude bank
pays the area perturbation before the shared numerical index is chosen. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests

open Purelib.Data
open Purelib.Data.Rat

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib.Integration.Path

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (SignedSourceChartRequest)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Integration.Path.IncrementArea (pathArea)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A paid transfer of an ordered source polygon to its original antisymmetric chart-edge valuation.

Every signed occurrence retains its own source/chart request, while one magnitude reference and common stage pay the
complete area perturbation. -/
structure SourceChartAreaRequest (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) (target : Fraction.Rational) where
  /-- The original requested squared-area target is strictly positive. -/ positive : 0 < target
  /-- The cached complete occurrence-count and magnitude perturbation weight. -/ weight : Fraction.Rational
  /-- The retained weight is exactly the fourth-power source-count scaling with the original magnitude bound. -/
    weight_eq : weight = 16 * (sources.length : Fraction.Rational) ^ 4 * (8 * fixed.bound + 2)
  /-- The retained common signed-occurrence allowance. -/ allowance : Fraction.Rational
  /-- The allowance is the smaller of one and the weighted allowance for the original target. -/ allowance_eq :
    allowance = min 1 (Weighted.allowance target weight)
  /-- All original signed source/chart requests in the actual source occurrence order. -/ requests : SourceChartRequests
    differential domains allowance sources
  /-- The cached common stage paying the original magnitude reference and all occurrence requests. -/ index : Nat
  /-- The retained stage is exactly the maximum of those two original stages. -/ index_eq : index = max fixed.index
    requests.index

constructive_injectivity SourceChartAreaRequest

namespace SourceChartAreaRequest

variable {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential} {sources : List (Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
  mesh.triangles.length)} {target : Purelib.Data.Rat.Fraction.Rational}

/-- The full area perturbation weight is nonnegative for every retained magnitude reference and source list. -/
theorem weight_nonnegative (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (sources : List
  (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) :
    0 ≤ 16 * (sources.length : Fraction.Rational) ^ 4 * (8 * fixed.bound + 2) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative) (by decide))

/-- Prepare the signed request for every nonloop original source and cache their common stage with the retained
magnitude reference. -/
@[expose] def build (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (sources : List
  (SewnPrimitiveContacts.SourceEdge mesh.triangles.length))
    (nonloop : ∀ source ∈ sources, source.first ≠ source.last) (target : Fraction.Rational) (positive : 0 < target) :
    SourceChartAreaRequest fixed sources target :=
  let weight := 16 * (sources.length : Fraction.Rational) ^ 4 * (8 * fixed.bound + 2)
  let allowance := min 1 (Weighted.allowance target weight)
  let requests := SourceChartRequests.build differential domains allowance
    (Fraction.Order.Basic.lt_min (by decide) (Weighted.allowance_positive positive (weight_nonnegative fixed sources)))
      sources nonloop
  ⟨positive, weight, rfl, allowance, rfl, requests, max fixed.index requests.index, rfl⟩

/-- The original single-differential triangle reading parent on the supplied mesh and domains. -/
@[reducible, expose] def Sample :=
  SourceChartComparison.SingleReadings
    (owner := SourceChartComparison.ownerFromMesh mesh)
    domains differential

/-- The actual retained source polygon observation on those same original sample values. -/
@[reducible, expose] def SourceData (sample : Sample (mesh := mesh) (domains := domains) (differential := differential))
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) :=
  SourceChartComparison.SourceObservations sample.values sources

/-- The actual source/chart comparison with the retained original allowance and magnitude bound. -/
@[reducible, expose] def ComparisonData (request : SourceChartAreaRequest fixed sources target)
    (sample : Sample (mesh := mesh) (domains := domains) (differential := differential))
    (source : SourceData sample sources) :=
  SourceChartComparison.Comparison
    sample.values sources source request.allowance (8 * fixed.bound + 2)

set_option genInjectivity false in
/-- A source/chart realization retaining the exact original request, sample and supplied source observation.

Its comparison reuses that source summary and the original chart valuation at a paid common stage. -/
structure Realization (request : SourceChartAreaRequest fixed sources target)
    (sample : Sample (mesh := mesh) (domains := domains) (differential := differential))
    (source : SourceData sample sources) where
  /-- The retained original source/chart area request. -/ selection : SourceChartAreaRequest fixed sources target
  /-- The retained selection is exactly the supplied original request. -/ selection_eq : selection = request
  /-- The retained original triangle sample. -/ readings : Sample (mesh := mesh) (domains := domains) (differential :=
    differential)
  /-- The retained readings are exactly the supplied original sample. -/ readings_eq : readings = sample
  /-- The original request is paid at the actual retained sample stage. -/ later : request.index ≤ sample.stage
  /-- The cached actual source/chart comparison on the supplied source observation. -/ comparison : ComparisonData
    request sample source

constructive_injectivity Realization

/-- The common request stage pays the original magnitude bank's validity floor. -/
theorem magnitude_le (request : SourceChartAreaRequest fixed sources target) : fixed.index ≤ request.index :=
  request.index_eq ▸ Nat.Order.le_max_left _ _

/-- The common request stage pays every retained source/chart occurrence request. -/
theorem chart_le (request : SourceChartAreaRequest fixed sources target) : request.requests.index ≤ request.index :=
  request.index_eq ▸ Nat.Order.le_max_right _ _

/-- Compare the supplied original source observation with the chart polygon using the paid request and the actual
retained sample. -/
@[expose] def realize (request : SourceChartAreaRequest fixed sources target)
    (sample : Sample (mesh := mesh) (domains := domains) (differential := differential))
    (source : SourceData sample sources) (later : request.index ≤ sample.stage) : Realization request sample source :=
  have fixedLater := request.magnitude_le.trans later
  have requestLater := request.chart_le.trans later
  have positive : 0 < request.allowance := by
    rw [request.allowance_eq]
    exact Fraction.Order.Basic.lt_min (by decide) (Weighted.allowance_positive request.positive
      (request.weight_eq ▸ weight_nonnegative fixed sources))
  let magnitude := sample.magnitude fixed fixedLater
  let comparison := SourceChartComparison.realizeSupplied
    source magnitude request.allowance positive.le
    (request.allowance_eq ▸ Fraction.Order.Basic.min_le_left _ _)
    (fun source member => (request.requests.accurate sample.readings requestLater source member).le)
  ⟨request, rfl, sample, rfl, later, comparison⟩

namespace Realization

variable {request : SourceChartAreaRequest fixed sources target}
  {sample : Sample (mesh := mesh) (domains := domains) (differential := differential)}
  {source : SourceData sample sources}

/-- The cached signed discrepancy between the original source and chart polygon areas. -/
@[expose] def residual (result : Realization request sample source) : Gaussian := result.comparison.residual
/-- The cached area of the actual original chart polygon. -/
@[expose] def chartArea (result : Realization request sample source) : Gaussian := result.comparison.chartSummary.area
/-- The cached quantitative bound for the original area discrepancy. -/
@[expose] def areaBound (result : Realization request sample source) : Fraction.Rational := result.comparison.areaBound

/-- The retained residual is the supplied source summary area minus the cached chart area. -/
theorem residual_cached (result : Realization request sample source) :
    result.residual = source.summary.area - result.chartArea := result.comparison.residual_cached

/-- The retained residual is the original source path area minus its projected chart word area. -/
theorem residual_readback (result : Realization request sample source) :
    result.residual = IncrementArea.pathArea (sources.map (fun source => source.increment sample.values)) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation mesh sample.values) (sources.map (fun source =>
        source.project mesh.triangulation.faces)) :=
  result.comparison.residual_readback

/-- The cached chart area reads the original projected word under the antisymmetric edge valuation. -/
theorem chart_readback (result : Realization request sample source) :
    result.chartArea = Purelib.Topology.Mesh.RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation mesh
      sample.values)
      (sources.map (fun source => source.project mesh.triangulation.faces)) := by
  change result.comparison.chartSummary.area = _
  rw [result.comparison.chartSummary.area_eq, result.comparison.chart_eq]
  unfold SourceChartComparison.ChartIncrements RetracingWords.wordArea
  rw [List.Map.map_map]
  rfl

/-- The exact retained signed source/chart request at an original source occurrence. -/
@[expose] def requestAt (result : Realization request sample source) (occurrence : Fin sources.length) :
    SignedSourceChartRequests.SignedSourceChartRequest (sources[occurrence.val]'occurrence.isLt) differential domains
      result.selection.allowance :=
  result.selection.requests.«at» occurrence

/-- The actual retained readings pay every original signed occurrence request. -/
theorem request_stage (result : Realization request sample source) :
    result.selection.requests.index ≤ result.readings.stage := by
  rw [result.selection_eq, result.readings_eq]
  exact (Nat.Order.le_max_right _ _).trans (request.index_eq ▸ result.later)

/-- The original source increment and its chart-edge reading differ within the retained allowance at each occurrence. -/
theorem occurrence_accurate (result : Realization request sample source) (occurrence : Fin sources.length) :
    normSq ((sources[occurrence.val]'occurrence.isLt).increment result.readings.values -
      CanonicalEdgeValues.edgeValuation mesh result.readings.values ((sources[occurrence.val]'occurrence.isLt).project
        mesh.triangulation.faces)) <
      result.selection.allowance :=
  result.selection.requests.at_accurate occurrence result.readings.readings result.request_stage

/-- The actual residual squared norm is bounded by the cached comparison bound. -/
theorem bounded (result : Realization request sample source) : normSq result.residual ≤ result.areaBound :=
  result.comparison.numeric.bounded

/-- The actual cached area bound equals the original request weight times its retained allowance. -/
theorem budget_identity (result : Realization request sample source) :
    result.areaBound = request.weight * request.allowance := by
  rw [areaBound, result.comparison.bound_readback, request.weight_eq]
  rw [Fraction.Field.mul_assoc,
    Fraction.Field.mul_comm request.allowance (8 * fixed.bound + 2),
    ← Fraction.Field.mul_assoc]
  rfl

/-- The original target pays the complete cached area bound. -/
theorem budget (result : Realization request sample source) : result.areaBound ≤ target := by
  rw [result.budget_identity]
  have nonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative fixed sources
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.allowance_eq ▸
    Fraction.Order.Basic.min_le_right _ _) nonnegative).trans
    (Weighted.mul_allowance_le request.positive.le nonnegative)

/-- The original target bounds the squared norm of the retained source/chart residual. -/
theorem pay (result : Realization request sample source) : normSq result.residual ≤ target :=
  result.bounded.trans result.budget

end Realization

/-- At the original paid stage, the complete source path and its projected chart word have squared area discrepancy at
most the requested target. -/
theorem accurate (request : SourceChartAreaRequest fixed sources target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (later : request.index ≤ stage) :
    normSq (IncrementArea.pathArea (sources.map (fun source => source.increment readings.values)) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation mesh readings.values) (sources.map (fun source =>
        source.project mesh.triangulation.faces))) ≤ target := by
  let sample := SingleReadings.ofReadings
    (owner := SourceChartComparison.ownerFromMesh mesh) readings
  let source := SourceObservations.realize sample.values sources
  let result := realize request sample source later
  have paid := result.pay
  rw [result.residual_readback] at paid
  exact paid

end SourceChartAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
