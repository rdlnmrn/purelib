module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Cached aggregate errors for the original parent cell polygons. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors

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

/-- Read already-computed cell discrepancies in their original order. -/
def differences : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned endpoints →
      List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      polygons.1.difference ::
        differences
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2

/-- The retained discrepancy list has exactly one entry for each original parent edge. -/
theorem differences_count : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
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
    (differences
      plans cells evaluated sources planned endpoints polygons).length = edges.length
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => rfl
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      congrArg Nat.succ
        (differences_count
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2)

/-- Every cached original cell discrepancy satisfies the common source allowance with its homogeneous coefficient
factor. -/
theorem differences_bounded : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
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
    ∀ value ∈
      differences
      plans cells evaluated sources planned endpoints polygons,
      Data.Gaussian.Norm.Basic.normSq value ≤ (4 * allowance)^2 *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, _, _, _, .nil, .nil, _, _, _, _, _, _, member => by cases member
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons, value, member => by
      rcases List.Membership.mem_cons.mp member with equal | later
      · exact equal ▸ polygons.1.bounded
      · exact
          differences_bounded
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2 value later

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

set_option genInjectivity false in
/-- Sum only the certified cell area discrepancies. Joining polygons and trace origins remain separate obligations in
the surface comparison. -/
structure ErrorSum (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated
  sources planned endpoints) where
  /-- The cached actual original cell area discrepancies in their retained order. -/ errors : List
    InverseRootPolynomial.Gaussian
  /-- The retained error list is exactly the original source polygon discrepancy list. -/ errors_eq : errors =
    differences
    plans cells evaluated sources planned endpoints polygons
  /-- The cached sum of the actual retained cell discrepancies. -/ total : InverseRootPolynomial.Gaussian
  /-- The retained total is exactly the Gaussian sum of the cached original errors. -/ total_eq : total =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- The actual error total satisfies the retained count-scaled homogeneous area bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq total ≤ (4 * ((edges.length : InverseRootPolynomial.Coordinate) *
    allowance))^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity ErrorSum

/-- Cache and sum the original certified cell discrepancies, preserving their actual count and homogeneous squared
allowance. -/
def sumErrors (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated
  sources planned endpoints) :
  ErrorSum
  polygons := by
  let errors :=
    differences
    plans cells evaluated sources planned endpoints polygons
  let total := Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le errors
    ((4 * allowance)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2)

      (differences_bounded
      plans cells evaluated sources planned endpoints polygons)
  change Data.Gaussian.Norm.Basic.normSq total ≤ (errors.length : InverseRootPolynomial.Coordinate) *
    ((errors.length : InverseRootPolynomial.Coordinate) * ((4 * allowance)^2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2)) at bound
  have countEq : errors.length = edges.length :=
    differences_count
    plans cells evaluated sources planned endpoints polygons
  rw [countEq] at bound
  exact ⟨errors, rfl, total, rfl, bound.trans_eq (by ring1)⟩

/-- A later parent allowance absorbs the retained count factor. -/
theorem ErrorSum.paid {polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells
  evaluated sources planned endpoints}
    (errors :
      ErrorSum
      polygons) {parentAllowance : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ allowance)
    (paid : (edges.length : InverseRootPolynomial.Coordinate) * allowance ≤ parentAllowance) :
    Data.Gaussian.Norm.Basic.normSq errors.total ≤ (4 * parentAllowance)^2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have nonnegativeCount := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le edges.length)) nonnegative
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4) nonnegativeCount)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)) 2
  exact errors.bounded.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squared
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end BasisEndpointPlans.SourcePolygons
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors
