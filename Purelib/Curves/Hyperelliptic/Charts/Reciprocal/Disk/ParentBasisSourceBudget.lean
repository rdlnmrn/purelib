module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceErrors.BasisEndpointPlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining.BasisEndpointPlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! One automatic budget pays internal and coarse source-polygon errors. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

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

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}

set_option genInjectivity false in
/-- Allocate one parent allowance to internal cell errors and the complete joining polygon before source polynomials and
vertex readings are acquired. -/
structure ParentBasisSourceBudget (covers : SourceLocations.BasisSourceCovers parent) (requests :
  ParentChartRequests.ChartRequests target floor owners)
    (endpointTarget parentAllowance : InverseRootPolynomial.Coordinate) (sourceFloor : Nat) where
  /-- The retained per-cell linear error allowance. -/ cellAllowance : InverseRootPolynomial.Coordinate
  /-- The per-cell allowance is the weighted share of half the parent allowance. -/ cell_eq : cellAllowance =
    Weighted.allowance (parentAllowance / 2) (edges.length : InverseRootPolynomial.Coordinate)
  /-- The per-cell allowance is strictly positive. -/ cell_positive : 0 < cellAllowance
  /-- The complete cell allowance fits half the parent allowance. -/ cell_paid : (edges.length :
    InverseRootPolynomial.Coordinate) * cellAllowance ≤ parentAllowance / 2
  /-- The cached maximum basis magnitude coefficient from the retained chart requests. -/ coefficient :
    InverseRootPolynomial.Coordinate
  /-- The coefficient cache reads the exact retained request bank. -/ coefficient_eq : coefficient =
    SourcePolygons.basisMaximum requests
  /-- The cached joining-polygon error weight. -/ weight : InverseRootPolynomial.Coordinate
  /-- The joining weight uses the fourth-power parent count and retained basis magnitude coefficient. -/ weight_eq :
    weight = 640 * (edges.length : InverseRootPolynomial.Coordinate)^4 * (80 + 32 * coefficient)
  /-- The retained upper bound for all source-reading targets. -/ sourceCeiling : InverseRootPolynomial.Coordinate
  /-- The source ceiling is the minimum of one, the endpoint target and the weighted joining allowance. -/ ceiling_eq :
    sourceCeiling = min 1 (min endpointTarget (Weighted.allowance ((2 * parentAllowance)^2) weight))
  /-- The retained source ceiling is strictly positive. -/ ceiling_positive : 0 < sourceCeiling
  /-- The source ceiling fits the requested endpoint target. -/ endpoint_le : sourceCeiling ≤ endpointTarget
  /-- The actual source preparation using the retained source ceiling and cell allowance. -/ prepared :
    ParentBasisSourcePreparation covers sourceCeiling cellAllowance sourceFloor requests
  /-- The actual prepared source target pays the complete joining-polygon discrepancy. -/ joining_paid : 640 *
    (edges.length : InverseRootPolynomial.Coordinate)^4 * prepared.sourceTarget *
    (80 * prepared.sourceTarget + 32 * SourcePolygons.basisMaximum requests) ≤ (2 * parentAllowance)^2

constructive_injectivity ParentBasisSourceBudget

namespace ParentBasisSourceBudget

/-- Allocate the parent allowance to cell and joining errors, then prepare source requests with a shared positive
ceiling. -/
def build (covers : SourceLocations.BasisSourceCovers parent) (requests : ParentChartRequests.ChartRequests target floor
  owners)
    (endpointTarget parentAllowance : InverseRootPolynomial.Coordinate) (endpointPositive : 0 < endpointTarget)
    (positive : 0 < parentAllowance) (sourceFloor : Nat) :
    ParentBasisSourceBudget covers requests
      endpointTarget parentAllowance sourceFloor := by
  let cellAllowance := Weighted.allowance (parentAllowance / 2) (edges.length : InverseRootPolynomial.Coordinate)
  have halfPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ edges.length := Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _)
  have cellPositive : 0 < cellAllowance := Weighted.allowance_positive halfPositive countNonnegative
  let coefficient := SourcePolygons.basisMaximum requests
  have coefficientNonnegative : 0 ≤ coefficient := SourcePolygons.basisMaximum_nonnegative requests
  let factor := 640 * (edges.length : InverseRootPolynomial.Coordinate)^4
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct countNonnegative 4)
  let weight := factor * (80 + 32 * coefficient)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (add_nonneg (by decide +kernel) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      coefficientNonnegative))
  have squarePositive : 0 < (2 * parentAllowance)^2 := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) 2
  let sourceCeiling := min 1 (min endpointTarget (Weighted.allowance ((2 * parentAllowance)^2) weight))
  have ceilingPositive : 0 < sourceCeiling := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min endpointPositive (Weighted.allowance_positive squarePositive weightNonnegative))
  let prepared := ParentBasisSourcePreparation.build covers sourceCeiling cellAllowance ceilingPositive cellPositive
    sourceFloor requests
  have small : prepared.sourceTarget ≤ 1 := prepared.endpoint_le.trans (Fraction.Order.Basic.min_le_left _ _)
  have factorLe : 80 * prepared.sourceTarget + 32 * coefficient ≤ 80 + 32 * coefficient := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 80)
    rw [Fraction.Field.mul_one_direct] at scaled
    exact Fraction.Order.Arithmetic.add_le_add_direct scaled le_rfl
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorLe
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative prepared.positive.le)
  have budgetLe : prepared.sourceTarget ≤ Weighted.allowance ((2 * parentAllowance)^2) weight :=
    prepared.endpoint_le.trans ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budgetLe weightNonnegative).trans
    (Weighted.mul_allowance_le squarePositive.le weightNonnegative)
  refine ⟨cellAllowance, rfl, cellPositive, Weighted.mul_allowance_le halfPositive.le countNonnegative,
    coefficient, rfl, weight, rfl, sourceCeiling, rfl, ceilingPositive,
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _), prepared, ?_⟩
  exact estimate.trans ((show factor * prepared.sourceTarget * (80 + 32 * coefficient) =
    weight * prepared.sourceTarget by ring1).trans_le paid)

variable {parentAllowance : Coordinate}

/-- Pay both cached errors together. Their identification with the literal concatenated source/chart paths is a separate
exact readback. -/
theorem combined_bound (budget :
  ParentBasisSourceBudget covers requests
  endpointTarget parentAllowance sourceFloor)
    {numerical : BasisSourceLocations.SampleBank covers index} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {plans : ParentChartRequests.ChartPlans capSample minimum requests} {cells : ParentPaths.ComparedCells source
      capSample depth bank}
    {evaluated : ChartPlans.EvaluationData readingIndex plans cells}
    {sources : ParentBasisEndpoints.BasisEndpointRequests covers budget.prepared.sourceTarget sourceFloor requests}
    {planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources}
    {endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned}
    {polygons : BasisEndpointPlans.SourcePolygons numerical coefficients budget.cellAllowance plans cells evaluated
      sources planned endpoints}
    (errors : SourcePolygons.ErrorSum polygons)
    (joining : SourcePolygons.JoiningComparison polygons) :
    Data.Gaussian.Norm.Basic.normSq (errors.total + joining.difference) ≤ (4 * parentAllowance)^2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have internal := errors.paid budget.cell_positive.le budget.cell_paid
  have halfEq : 4 * (parentAllowance / 2) = 2 * parentAllowance := by
    calc
      _ = 2 * ((parentAllowance / 2) * 2) := by ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (2 : InverseRootPolynomial.Coordinate) ≠ 0)]
  rw [halfEq] at internal
  have coarse := joining.bounded.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.joining_paid
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two errors.total joining.difference).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct internal
      coarse) (by decide))
  exact bound.trans_eq (by ring1)

end ParentBasisSourceBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
