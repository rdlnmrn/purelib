module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

@[expose] public section

/-! Quantitative homogeneous comparison for the complete retained parent boundary. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample (BasisBoundarySample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets (BasisBoundaryBudgets)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (boundaryEnergy_sub_budget_le)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {energyTarget joinTarget : Coordinate} {energyFloor energyDepth :
    Nat}

set_option genInjectivity false in
/-- The coefficient-independent aggregate boundary budget on the retained parent cells.

It caches the actual cell budgets, their maximum and the squared-count bound used by the complete signed boundary
comparison. -/
structure ParentBasisBoundaryBudget (plans : ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells) where
  /-- The original boundary budgets on every retained parent cell evaluation. -/ entries :
    ParentBasisBudgets.BasisBoundaryBudgets plans cells evaluated
  /-- The cached maximum of the actual retained cell budgets. -/ maximum : InverseRootPolynomial.Coordinate
  /-- The maximum cache reads the exact retained cell budget bank. -/ maximum_eq : maximum = entries.maximum plans cells
    evaluated
  /-- The cached squared-count aggregate cell error bound. -/ bound : InverseRootPolynomial.Coordinate
  /-- The aggregate bound equals the squared original parent count times the retained maximum. -/ bound_eq : bound =
    (edges.length : InverseRootPolynomial.Coordinate) ^ 2 * maximum
  /-- The cached aggregate cell error bound is nonnegative. -/ nonnegative : 0 ≤ bound

constructive_injectivity ParentBasisBoundaryBudget

namespace ParentBasisBoundaryBudget

/-- Construct the retained cell budgets once and cache their nonnegative squared-count aggregate. -/
def build (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
  capSample depth bank)
    (evaluated : ChartPlans.EvaluationData readingIndex plans cells) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells
      evaluated := by
  let entries := BasisBoundaryBudgets.build plans cells evaluated
  let maximum := entries.maximum plans cells evaluated
  let bound := (edges.length : InverseRootPolynomial.Coordinate) ^ 2 * maximum
  exact ⟨entries, maximum, rfl, bound, rfl,
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (entries.maximum_nonnegative plans cells evaluated)⟩

/-- The original chart target already pays the whole basis at every cell. -/
theorem bound_le (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
  (nonnegative : 0 ≤ target) :
    budget.bound ≤ (edges.length : InverseRootPolynomial.Coordinate) ^ 2 * target := by
  rw [budget.bound_eq, budget.maximum_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (budget.entries.maximum_le nonnegative plans cells
    evaluated) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

variable {energies : BasisEnergyData
  (polynomials := polynomials) energyTarget energyFloor energyDepth plans cells evaluated}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The actual sum of the retained cell energy residuals obeys the cached aggregate budget with its homogeneous
coefficient factor. -/
theorem cell_error_bound (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq sample.cellError ≤ budget.bound *
      (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 := by
  rw [sample.cell_error]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le (BasisEnergyData.cellErrors coefficients plans cells
    evaluated energies) _
    (budget.entries.bounded coefficients branch plans cells evaluated energies)
  rw [BasisEnergyData.cellErrors_length] at estimate
  exact estimate.trans_eq (by rw [budget.bound_eq, budget.maximum_eq]; ring1)

/-- The retained signed boundary pays both cell refinement and internal join defects. No endpoint term is dropped from
the reference expression. -/
theorem boundary_bound (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.energy - (-sample.trace + sample.lastRadial - sample.firstRadial))
      ≤
      2 * (budget.bound + (sample.joins.count : InverseRootPolynomial.Coordinate) ^ 2 * joinTarget) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 := by
  rw [sample.discrepancy]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (budget.cell_error_bound sample branch) sample.joins.bounded) (by
      decide)).trans_eq (by ring1))

/-- The complete residual is paid by the original cell target and the homogeneous junction request, independently of the
later polynomial stage. -/
theorem requested_boundary_bound (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonnegative : 0 ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (sample.energy - (-sample.trace + sample.lastRadial - sample.firstRadial))
      ≤
      2 * ((edges.length : InverseRootPolynomial.Coordinate) ^ 2 * target + ((edges.length - 1 : Nat) :
        InverseRootPolynomial.Coordinate) ^ 2 * joinTarget) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 := by
  have bound := budget.boundary_bound sample branch
  rw [sample.joins.count_edges] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (budget.bound_le nonnegative) le_rfl) (by decide))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Transfer the homogeneous fan lower bound to the literal joined trace once the computed scalar discrepancy is paid by
a linear energy allowance. -/
theorem trace_lower (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (allowance : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : 2 * (budget.bound + (sample.joins.count : InverseRootPolynomial.Coordinate) ^ 2 * joinTarget) ≤ (4 *
      allowance) ^ 2) :
    -(((edges.length : InverseRootPolynomial.Coordinate) * energyTarget + allowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (-sample.trace + sample.lastRadial - sample.firstRadial).im / 4 := by
  have coefficientNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have estimate := (budget.boundary_bound sample branch).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le sample.energy _
    (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative)
    (estimate.trans_eq (by ring1))
  have lower := Fraction.Order.Arithmetic.sub_le_sub_right_direct sample.lower (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)
  exact (show -(((edges.length : InverseRootPolynomial.Coordinate) * energyTarget + allowance) *
    PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(PreparedObservationCoercivity.coefficientNormSq coefficients * ((edges.length : InverseRootPolynomial.Coordinate)
      * energyTarget)) - allowance * PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
      (lower.trans comparison)

/-- The original cell and junction targets imply the signed joined-trace energy lower bound once their complete scalar
discrepancy is paid. -/
theorem requested_trace_lower (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (targetNonnegative : 0 ≤ target)
    (allowance : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : 2 * ((edges.length : InverseRootPolynomial.Coordinate) ^ 2 * target + ((edges.length - 1 : Nat) :
      InverseRootPolynomial.Coordinate) ^ 2 * joinTarget) ≤
      (4 * allowance) ^ 2) :
    -(((edges.length : InverseRootPolynomial.Coordinate) * energyTarget + allowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (-sample.trace + sample.lastRadial - sample.firstRadial).im / 4 := by
  apply budget.trace_lower sample branch allowance nonnegative
  rw [sample.joins.count_edges]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    (budget.bound_le targetNonnegative) le_rfl) (by decide)).trans paid

end ParentBasisBoundaryBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound
