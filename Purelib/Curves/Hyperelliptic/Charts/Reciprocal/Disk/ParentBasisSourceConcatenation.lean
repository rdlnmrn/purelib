module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceBudget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceBudget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors.BasisEndpointPlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining.BasisEndpointPlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! The paid discrepancies are those of the literal concatenated cell paths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceConcatenation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints (BasisEndpointRequests BasisEndpointPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans (Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation (BasisSourceBudgets)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk (ParentBasisSourcePreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest (BasisSourceAllowance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.BasisEndpointPlans (SourcePolygons)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining.BasisEndpointPlans.SourcePolygons
  (basisMaximum basisMaximum_nonnegative)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors.BasisEndpointPlans.SourcePolygons
  (ErrorSum sumErrors)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining.BasisEndpointPlans.SourcePolygons
  (totals JoiningComparison)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors.BasisEndpointPlans.SourcePolygons
  (ErrorSum differences)
variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

variable {target sourceTarget : Coordinate} {floor sourceFloor :
  Nat}

variable {covers : BasisSourceCovers parent}
  {index minimum depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {endpointTarget allowance : Coordinate}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

namespace BasisEndpointPlans.SourcePolygons

variable {numerical :
  BasisSourceLocations.SampleBank covers
  index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The actual retained source-increment paths in original parent-cell order. -/
def sourcePaths : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned endpoints →
      List (List InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      polygons.1.values.values.pairs.map Prod.fst ::
        sourcePaths
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2

/-- The actual retained chart-increment paths in the same parent-cell order. -/
def chartPaths : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned endpoints →
      List (List InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      polygons.1.values.values.pairs.map Prod.snd ::
        chartPaths
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2

/-- Summing each retained source path gives the first coordinates of the cached source/chart total pairs. -/
theorem sourcePaths_totals : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints) →

      (sourcePaths
      plans cells evaluated sources planned endpoints polygons).map Data.Gaussian.Norm.Sum.Basic.gaussianSum =
      (SourcePolygons.totals plans cells evaluated sources planned endpoints polygons).map Prod.fst
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => rfl
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons => by
      change Data.Gaussian.Norm.Sum.Basic.gaussianSum (polygons.1.values.values.pairs.map Prod.fst) ::

          (sourcePaths
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2).map
          Data.Gaussian.Norm.Sum.Basic.gaussianSum =
        polygons.1.values.values.source.total :: (SourcePolygons.totals tail cells evaluated.2 sources.2 planned.2
          endpoints.2 polygons.2).map Prod.fst
      rw [← polygons.1.values.values.source.total_eq,
        sourcePaths_totals
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2]

/-- Summing each retained chart path gives the second coordinates of the cached source/chart total pairs. -/
theorem chartPaths_totals : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints) →

      (chartPaths
      plans cells evaluated sources planned endpoints polygons).map Data.Gaussian.Norm.Sum.Basic.gaussianSum =
      (SourcePolygons.totals plans cells evaluated sources planned endpoints polygons).map Prod.snd
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => rfl
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons => by
      change Data.Gaussian.Norm.Sum.Basic.gaussianSum (polygons.1.values.values.pairs.map Prod.snd) ::

          (chartPaths
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2).map
          Data.Gaussian.Norm.Sum.Basic.gaussianSum =
        polygons.1.chart.total :: (SourcePolygons.totals tail cells evaluated.2 sources.2 planned.2 endpoints.2
          polygons.2).map Prod.snd
      rw [← polygons.1.chart.total_eq,
        chartPaths_totals
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2]

/-- The difference of the actual internal source and chart areas is exactly the sum of the retained cell discrepancies.
-/
theorem internal_difference : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints) →
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((sourcePaths
      plans cells evaluated sources planned endpoints polygons).map IncrementArea.pathArea) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((chartPaths
        plans cells evaluated sources planned endpoints polygons).map IncrementArea.pathArea) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (SourcePolygons.differences plans cells evaluated sources planned
        endpoints polygons)
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => by change (0 : InverseRootPolynomial.Gaussian) - 0 = 0; ring1
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons => by
      change (IncrementArea.pathArea (polygons.1.values.values.pairs.map Prod.fst) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
          ((sourcePaths
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2).map IncrementArea.pathArea)) -
        (IncrementArea.pathArea (polygons.1.values.values.pairs.map Prod.snd) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
          ((chartPaths
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2).map IncrementArea.pathArea)) =
        polygons.1.difference + Data.Gaussian.Norm.Sum.Basic.gaussianSum (SourcePolygons.differences tail cells
          evaluated.2 sources.2 planned.2 endpoints.2 polygons.2)
      rw [← polygons.1.values.values.source.area_eq, ← polygons.1.chart.area_eq, polygons.1.difference_eq,
        ←
          internal_difference
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2]
      ring1

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {sources : BasisEndpointRequests covers
    sourceTarget sourceFloor requests}
  {planned : BasisEndpointPlans polynomials
    plans sources} {endpoints :
    Samples numerical plans
    cells evaluated sources planned}

/-- Exact discrepancy of the literal concatenated paths. The complete coarse polygon is present alongside the internal
cell areas. -/
theorem concatenated_difference
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints)
    (errors : SourcePolygons.ErrorSum polygons) (joining : SourcePolygons.JoiningComparison polygons) :
    IncrementArea.pathArea
      (sourcePaths
      plans cells evaluated sources planned endpoints polygons).flatten -
      IncrementArea.pathArea
        (chartPaths
        plans cells evaluated sources planned endpoints polygons).flatten =
      errors.total + joining.difference := by
  rw [IncrementArea.pathArea_flatten, IncrementArea.pathArea_flatten,

      sourcePaths_totals,
      chartPaths_totals,
      errors.total_eq, errors.errors_eq,
    joining.difference_eq, joining.source.area_eq, joining.chart.area_eq, joining.pairs_eq,
    ←
      internal_difference
      plans cells evaluated sources planned endpoints polygons]
  ring1

end BasisEndpointPlans.SourcePolygons

namespace ParentBasisSourceBudget

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {parentAllowance : Coordinate}

/-- Apply the automatically paid budget to the actual concatenated increment paths. No cancellation of the joining
polygon is needed. -/
theorem concatenated_bound (budget : ParentBasisSourceBudget covers requests endpointTarget
  parentAllowance sourceFloor)
    {numerical : BasisSourceLocations.SampleBank covers index} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {plans : ParentChartRequests.ChartPlans capSample minimum requests} {cells : ParentPaths.ComparedCells source
      capSample depth bank}
    {evaluated : ChartPlans.EvaluationData readingIndex plans cells}
    {sources : ParentBasisEndpoints.BasisEndpointRequests covers budget.prepared.sourceTarget sourceFloor requests}
    {planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources}
    {endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned}
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients budget.cellAllowance plans cells evaluated
      sources planned endpoints)
    (errors : SourcePolygons.ErrorSum polygons)
    (joining : SourcePolygons.JoiningComparison polygons) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea
      (BasisEndpointPlans.SourcePolygons.sourcePaths
      plans cells evaluated sources planned endpoints polygons).flatten -
      IncrementArea.pathArea
        (BasisEndpointPlans.SourcePolygons.chartPaths
        plans cells evaluated sources planned endpoints polygons).flatten) ≤
      (4 * parentAllowance)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw
    [BasisEndpointPlans.SourcePolygons.concatenated_difference
    polygons errors joining]
  exact ParentBasisSourceBudget.combined_bound budget errors joining

end ParentBasisSourceBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceConcatenation
