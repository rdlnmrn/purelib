module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Automatic scalar allocation for the homogeneous parent boundary comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound (ParentBasisBoundaryBudget)
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

set_option genInjectivity false in
/-- Select cell and junction targets from the original cell count and a positive linear energy allowance, before any
chart or fan is sampled. -/
structure ParentBasisAllowance (count : Nat) (allowance : InverseRootPolynomial.Coordinate) where
  /-- The requested linear energy allowance is strictly positive. -/ positive : 0 < allowance
  /-- The cached aggregate cell and internal-junction weight. -/ weight : InverseRootPolynomial.Coordinate
  /-- The weight is twice the sum of the squared cell and junction counts. -/ weight_eq : weight = 2 * ((count :
    InverseRootPolynomial.Coordinate)^2 + ((count - 1 : Nat) : InverseRootPolynomial.Coordinate)^2)
  /-- The common cell and junction squared-error target. -/ target : InverseRootPolynomial.Coordinate
  /-- The target is the weighted share of sixteen times the squared linear allowance. -/ target_eq : target =
    Weighted.allowance ((4 * allowance)^2) weight
  /-- The retained common target is strictly positive. -/ target_positive : 0 < target
  /-- The complete weighted cell and junction discrepancy fits the squared energy allowance. -/ paid : 2 * ((count :
    InverseRootPolynomial.Coordinate)^2 * target + ((count - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * target) ≤
    (4 * allowance)^2

constructive_injectivity ParentBasisAllowance

namespace ParentBasisAllowance

/-- Choose a positive common cell and junction target paying the requested linear energy allowance. -/
def build (count : Nat) (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) :
  ParentBasisAllowance count allowance := by
  let weight := 2 * ((count : InverseRootPolynomial.Coordinate)^2 + ((count - 1 : Nat) :
    InverseRootPolynomial.Coordinate)^2)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have targetPositive : 0 < (4 * allowance)^2 := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) 2
  let target := Weighted.allowance ((4 * allowance)^2) weight
  have paid := Weighted.mul_allowance_le targetPositive.le weightNonnegative
  exact ⟨positive, weight, rfl, target, rfl, Weighted.allowance_positive targetPositive weightNonnegative,
    (show 2 * ((count : InverseRootPolynomial.Coordinate)^2 * target + ((count - 1 : Nat) :
      InverseRootPolynomial.Coordinate)^2 * target) = weight * target by ring1).trans_le paid⟩

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {allowance energyTarget : Coordinate} {energyFloor energyDepth :
    Nat}

/-- The preselected targets discharge the complete parent discrepancy; there is no caller residual estimate or
coefficient-dependent schedule. -/
theorem trace_lower (allocation : ParentBasisAllowance
  edges.length allowance)
    {requests : ParentChartRequests.ChartRequests allocation.target floor owners} {plans :
      ParentChartRequests.ChartPlans capSample minimum requests}
    {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated : ChartPlans.EvaluationData readingIndex
      plans cells}
    {energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (budget : ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients allocation.target)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    -(((edges.length : InverseRootPolynomial.Coordinate) * energyTarget + allowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (-sample.trace + sample.lastRadial - sample.firstRadial).im / 4 :=
  budget.requested_trace_lower sample branch allocation.target_positive.le allowance allocation.positive.le
    allocation.paid

end ParentBasisAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
