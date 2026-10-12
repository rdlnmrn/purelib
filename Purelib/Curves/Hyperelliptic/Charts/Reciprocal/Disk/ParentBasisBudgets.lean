module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Coefficient-independent boundary budgets on the retained parent cell bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets

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

/-- The original coefficient-independent boundary budget for every retained parent cell, indexed by its actual plans and
evaluation. -/
def BasisBoundaryBudgets : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) → Type
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      Evaluation.BasisBoundaryBudget evaluated.1 ×
        BasisBoundaryBudgets tail cells
        evaluated.2

namespace BasisBoundaryBudgets

/-- Construct the original boundary budget on each retained parent cell evaluation. -/
def build : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets.BasisBoundaryBudgets
      plans cells evaluated
  | _, _, _, _, .nil, .nil, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      ⟨BasisBoundaryBudget.build evaluated.1,
        build tail cells
        evaluated.2⟩

/-- The largest retained original cell boundary bound, with zero for an empty parent bank. -/
def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets.BasisBoundaryBudgets
      plans cells evaluated → InverseRootPolynomial.Coordinate
  | _, _, _, _, .nil, .nil, _, _ => 0
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, budgets => max budgets.1.bound
    (maximum tail cells
    evaluated.2 budgets.2)

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- The maximum of the original retained boundary budgets is nonnegative. -/
theorem maximum_nonnegative (plans : ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells)
    (budgets : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets.BasisBoundaryBudgets plans cells
      evaluated) : 0 ≤ budgets.maximum plans cells evaluated := by
  induction plans with
  | nil => cases cells; exact le_refl _
  | cons head tail ih =>
      cases cells with
      | cons cell cells => exact (ih cells evaluated.2 budgets.2).trans (Fraction.Order.Basic.le_max_right _ _)

/-- The original nonnegative target bounds the maximum of all retained cell budgets. -/
theorem maximum_le (nonnegative : 0 ≤ target) (plans : ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells)
    (budgets : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets.BasisBoundaryBudgets plans cells
      evaluated) : budgets.maximum plans cells evaluated ≤ target := by
  induction plans with
  | nil => cases cells; exact nonnegative
  | cons head tail ih =>
      cases cells with
      | cons cell cells => exact Fraction.Order.Basic.max_le budgets.1.paid.le (ih cells evaluated.2 budgets.2)

open Purelib.Data in
/-- Every actual original cell energy residual satisfies the maximum retained budget with its homogeneous coefficient
factor. -/
theorem bounded (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (branch :
  HyperellipticReciprocal.originOrder curve = 1)
    (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
      capSample depth bank)
    (evaluated : ChartPlans.EvaluationData readingIndex plans cells) (budgets :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets.BasisBoundaryBudgets plans cells evaluated)
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated) :
    ∀ error ∈ BasisEnergyData.cellErrors coefficients plans cells evaluated energies,
      Data.Gaussian.Norm.Basic.normSq error ≤ budgets.maximum plans cells evaluated *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  induction plans with
  | nil => cases cells; intro error member; cases member
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          intro error member
          rcases List.Membership.mem_cons.mp member with equal | member
          · subst error
            have bound := budgets.1.accurate energies.1.val coefficients branch
            rw [energies.1.property] at bound
            exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (Fraction.Order.Basic.le_max_left _ _) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
          · exact (ih cells evaluated.2 budgets.2 energies.2 error member).trans
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right _ _)
                (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end BasisBoundaryBudgets

namespace BasisEnergyData

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- The retained cell-error list has exactly one entry per original parent edge. -/
theorem cellErrors_length (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated) →
    (BasisEnergyData.cellErrors coefficients plans cells evaluated energies).length = edges.length
  | _, _, _, _, .nil, .nil, _, _ => rfl
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, energies =>
      congrArg Nat.succ
        (cellErrors_length
        coefficients tail cells evaluated.2 energies.2)

end BasisEnergyData
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets
