module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaReplacement
public import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound
import Purelib.Integration.Path.HomogeneousIncrementRestoration
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

@[expose] public section

/-! Restore the actual homogeneous parent trace through source endpoints.
Cached summaries retain every detour and both endpoint potentials. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound (ParentBasisBoundaryBudget)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar} {parent :
    Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}
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

namespace BasisBoundarySample

open Purelib.Integration.Path.IncrementArea (Summary traceArea)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.IncrementRestoration (potential detour)

variable {energies : BasisEnergyData
  (polynomials := polynomials) energyTarget energyFloor energyDepth plans cells evaluated}
  {coefficients : GaussianVector genus}
  {sample : BasisBoundarySample energies
    coefficients joinTarget}
  {endpointTarget joining : Coordinate}

set_option genInjectivity false in
/-- The endpoint-restored parent trace and its retained source comparisons.

The cached core summary reuses the actual chart path, while both radial potentials and all endpoint detours remain
explicit. -/
structure EndpointRestoration (sample : BasisBoundarySample energies coefficients joinTarget)
    (endpointTarget joining : Coordinate) where
  /-- The retained first source endpoint value. -/ firstSource : Gaussian
  /-- The retained last source endpoint value. -/ lastSource : Gaussian
  /-- The retained first endpoint value after source restoration. -/ firstValue : Gaussian
  /-- The retained last endpoint value after source restoration. -/ lastValue : Gaussian
  /-- The first source-to-restored-value discrepancy fits the homogeneous joining budget. -/ first_source :
    Basic.normSq (firstSource - firstValue) ≤ joining *
    coefficientNormSq coefficients
  /-- The last restored-value-to-source discrepancy fits the homogeneous joining budget. -/ last_source :
    Basic.normSq (lastValue - lastSource) ≤ joining *
    coefficientNormSq coefficients
  /-- The first chart-to-source discrepancy fits the homogeneous endpoint budget. -/ first_chart :
    Basic.normSq (sample.firstValue - firstSource) ≤ 4 * endpointTarget *
    coefficientNormSq coefficients
  /-- The last source-to-chart discrepancy fits the homogeneous endpoint budget. -/ last_chart :
    Basic.normSq (lastSource - sample.lastValue) ≤ 4 * endpointTarget *
    coefficientNormSq coefficients
  /-- The cached restored first endpoint potential. -/ firstPotential : Gaussian
  /-- The cached restored last endpoint potential. -/ lastPotential : Gaussian
  /-- The first potential retains the actual radial value and endpoint transport. -/ first_potential : firstPotential =
    potential sample.firstRadial sample.firstValue firstValue
  /-- The last potential retains the actual radial value and endpoint transport. -/ last_potential : lastPotential =
    potential sample.lastRadial sample.lastValue lastValue
  /-- The cached summary of the actual chart path bracketed by both source-endpoint increments. -/ core :
    Summary ((sample.firstValue - firstSource) :: (sample.path ++ [lastSource - sample.lastValue]))

constructive_injectivity EndpointRestoration

namespace EndpointRestoration

/-- Endpoint values and their source comparisons come from the retained basis readings; the chart path and its summary
are reused without resampling. -/
def build (sample : BasisBoundarySample energies coefficients joinTarget)
    (firstSource lastSource firstValue lastValue : Gaussian)
    (firstSourceBound : Basic.normSq (firstSource - firstValue) ≤ joining *
      coefficientNormSq coefficients)
    (lastSourceBound : Basic.normSq (lastValue - lastSource) ≤ joining *
      coefficientNormSq coefficients)
    (firstChartBound : Basic.normSq (sample.firstValue - firstSource) ≤ 4 * endpointTarget *
      coefficientNormSq coefficients)
    (lastChartBound : Basic.normSq (lastSource - sample.lastValue) ≤ 4 * endpointTarget *
      coefficientNormSq coefficients) :
    EndpointRestoration sample
      endpointTarget joining :=
  ⟨firstSource, lastSource, firstValue, lastValue, firstSourceBound, lastSourceBound, firstChartBound, lastChartBound,
    potential sample.firstRadial sample.firstValue firstValue, potential
      sample.lastRadial sample.lastValue lastValue,
    rfl, rfl, IncrementAreaReplacement.bracket sample.summary (sample.firstValue - firstSource) (lastSource -
      sample.lastValue)⟩

/-- The complete restored increment path, including the incoming edge and both endpoint detours. -/
def path (restored :
  EndpointRestoration sample
  endpointTarget joining) (previous : Gaussian) : List Gaussian :=
  (restored.firstSource - previous) :: (((sample.firstValue - restored.firstSource) ::
    (sample.path ++ [restored.lastSource - sample.lastValue])) ++ [restored.lastValue - restored.lastSource])

/-- The cached core summary extended by the actual incoming and final restoration increments. -/
def summary (restored :
  EndpointRestoration sample
  endpointTarget joining) (previous : Gaussian) : Summary (restored.path previous)
  :=
  IncrementAreaReplacement.bracket restored.core (restored.firstSource - previous) (restored.lastValue -
    restored.lastSource)

/-- The restored path total is the retained last endpoint value minus the supplied preceding endpoint. -/
theorem total (restored :
  EndpointRestoration sample
  endpointTarget joining) (previous : Gaussian) :
    (restored.summary previous).total = restored.lastValue - previous := by
  have coreTotal : restored.core.total = restored.lastSource - restored.firstSource := by
    rw [restored.core.total_eq]
    change sample.firstValue - restored.firstSource + gaussianSum (sample.path ++
      [restored.lastSource - sample.lastValue]) = _
    rw [IncrementArea.sum_append, ← sample.summary.total_eq, sample.total_eq]
    change _ + (_ + (_ + 0)) = _
    ring1
  rw
    [summary,
    IncrementAreaReplacement.bracket_total, coreTotal]
  ring1

/-- The signed incoming potential discrepancy relative to the preceding endpoint and potential. -/
def joinError (restored :
  EndpointRestoration sample
  endpointTarget joining) (previous previousPotential : Gaussian) : Gaussian :=
  restored.firstPotential - previousPotential - area previous restored.firstValue

/-- Exact signed transport to the literal endpoint-restored path, including its merged incoming edge. Neither radial
potential is silently discarded. -/
theorem discrepancy (restored :
  EndpointRestoration sample
  endpointTarget joining) (previous previousPotential : Gaussian) :
    sample.energy - (-traceArea previous (restored.path previous) + restored.lastPotential -
      previousPotential) =
      (sample.cellError - sample.joins.total) +
        detour sample.firstValue sample.lastValue restored.firstSource restored.lastSource
          restored.firstValue restored.lastValue previous -
        restored.joinError previous previousPotential := by
  have traceEq : sample.trace = sample.summary.area + area sample.firstValue sample.lastValue := by
    rw [sample.trace_eq, IncrementArea.traceArea_eq, ← sample.summary.area_eq,
      ← sample.summary.total_eq, sample.total_eq, BoundaryRibbon.area_sub_self_right]
  rw [path,
    restored.last_potential, IncrementRestoration.restored_discrepancy sample.summary
    sample.firstValue sample.lastValue restored.firstSource restored.lastSource restored.firstValue restored.lastValue
      previous
    sample.firstRadial sample.lastRadial previousPotential sample.energy sample.total_eq,

      joinError,
      restored.first_potential, ← sample.discrepancy, traceEq]
  ring1

/-- Cell and internal-join errors use the existing parent budget. Only the endpoint detours and the incoming potential
comparison add new losses. -/
theorem boundary_bound (restored :
  EndpointRestoration sample
  endpointTarget joining)
    (budget : ParentBasisBoundaryBudget plans cells evaluated)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (previous previousPotential :
      Gaussian)
    (targetNonnegative : 0 ≤ endpointTarget) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    (gap : Basic.normSq (restored.firstValue - previous) ≤ joining *
      coefficientNormSq coefficients)
    (joined : Basic.normSq (restored.joinError previous previousPotential) ≤
      (80 * endpointTarget + 2 * joining) * (coefficientNormSq coefficients) ^ 2) :
    Basic.normSq (sample.energy - (-traceArea previous (restored.path
      previous) + restored.lastPotential - previousPotential)) ≤
      (8 * (budget.bound + (sample.joins.count : Coordinate) ^ 2 * joinTarget) + 672 *
        endpointTarget + 36 * joining) *
        (coefficientNormSq coefficients) ^ 2 := by
  have raw := ParentBasisBoundaryBudget.boundary_bound budget sample branch
  rw [sample.discrepancy] at raw
  have detourBound := HomogeneousIncrementRestoration.detour_bound_homogeneous targetNonnegative joinNonnegative
    joinSmall
    restored.first_source restored.last_source restored.first_chart restored.last_chart gap
  rw [restored.discrepancy]
  have pair := (Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct raw
      detourBound) (by decide))
  exact (Bounds.normSq_sub_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct pair
      joined) (by decide)).trans_eq (by ring1))

/-- Pay the complete restored discrepancy before transporting the actual fan-energy lower bound; the endpoint potentials
remain in the conclusion. -/
theorem trace_lower (restored :
  EndpointRestoration sample
  endpointTarget joining)
    (budget : ParentBasisBoundaryBudget plans cells evaluated)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (previous previousPotential :
      Gaussian)
    (targetNonnegative : 0 ≤ endpointTarget) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    (gap : Basic.normSq (restored.firstValue - previous) ≤ joining *
      coefficientNormSq coefficients)
    (joined : Basic.normSq (restored.joinError previous previousPotential) ≤
      (80 * endpointTarget + 2 * joining) * (coefficientNormSq coefficients) ^ 2)
    (allowance : Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : 8 * (budget.bound + (sample.joins.count : Coordinate) ^ 2 * joinTarget) +
      672 * endpointTarget + 36 * joining ≤ (4 * allowance) ^ 2) :
    -(((edges.length : Coordinate) * energyTarget + allowance) *
      coefficientNormSq coefficients) ≤
      (-traceArea previous (restored.path previous) + restored.lastPotential - previousPotential).im / 4
        := by
  have coefficientNonnegative : 0 ≤ coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : Coordinate)) _ (fun row =>
        normSq_nonneg (coefficients row)))
  have estimate := (restored.boundary_bound budget branch previous previousPotential targetNonnegative
    joinNonnegative joinSmall gap joined).trans (Arithmetic.mul_le_mul_of_nonneg_right_direct paid
      (Arithmetic.sq_nonneg_direct _))
  have comparison := boundaryEnergy_sub_budget_le sample.energy _
    (allowance * coefficientNormSq coefficients)
      (Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative)
    (estimate.trans_eq (by ring1))
  have lower := Arithmetic.sub_le_sub_right_direct sample.lower (allowance *
    coefficientNormSq coefficients)
  exact (show -(((edges.length : Coordinate) * energyTarget + allowance) *
    coefficientNormSq coefficients) =
    -(coefficientNormSq coefficients * ((edges.length : Coordinate)
      * energyTarget)) - allowance * coefficientNormSq coefficients by ring1).trans_le
      (lower.trans comparison)

end EndpointRestoration
end BasisBoundarySample
set_option genInjectivity false in
/-- One scalar target pays internal cell and junction errors, endpoint restoration, and incoming joins, before any
polynomial or coefficient choice. -/
structure ParentBasisRestorationAllowance (count : Nat) (allowance : Coordinate) where
  /-- The requested linear energy allowance is strictly positive. -/ positive : 0 < allowance
  /-- The retained family cell capacity used to choose the common target. -/ capacity : Nat
  /-- The actual parent cell count is at most the retained capacity. -/ count_le : count ≤ capacity
  /-- The cached complete restoration error weight. -/ weight : Coordinate
  /-- The weight retains the capacity's cell and junction terms together with both endpoint losses. -/ weight_eq :
    weight = 8 * ((capacity : Coordinate) ^ 2 + ((capacity - 1 : Nat) :
    Coordinate) ^ 2) + 708
  /-- The retained common target for cells, junctions and endpoint restoration. -/ target :
    Coordinate
  /-- The target is the unit-capped weighted share of the squared linear energy allowance. -/ target_eq : target = min 1
    (Weighted.allowance ((4 * allowance) ^ 2) weight)
  /-- The retained common restoration target is strictly positive. -/ target_positive : 0 < target
  /-- The retained common target is at most one. -/ small : target ≤ 1
  /-- The complete cell, junction and endpoint error coefficient fits the squared energy allowance. -/ paid : 8 *
    ((count : Coordinate) ^ 2 * target + ((count - 1 : Nat) : Coordinate) ^
    2 * target) +
    672 * target + 36 * target ≤ (4 * allowance) ^ 2

constructive_injectivity ParentBasisRestorationAllowance

namespace ParentBasisRestorationAllowance

/-- Choose one positive target paying all cell, junction and endpoint restoration losses at the supplied capacity. -/
def build (count : Nat) (allowance : Coordinate) (positive : 0 < allowance) :
  ParentBasisRestorationAllowance count allowance :=
  by
  let weight := 8 * ((count : Coordinate) ^ 2 + ((count - 1 : Nat) :
    Coordinate) ^ 2) + 708
  have nonnegative : 0 ≤ weight := add_nonneg
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Arithmetic.sq_nonneg_direct _)
      (Arithmetic.sq_nonneg_direct _))) (by decide +kernel)
  have squarePositive : 0 < (4 * allowance) ^ 2 := Arithmetic.pow_pos_direct
    (Arithmetic.mul_pos_direct (by decide) positive) 2
  let target := min 1 (Weighted.allowance ((4 * allowance) ^ 2) weight)
  have bounded := (Arithmetic.mul_le_mul_of_nonneg_left_direct (Basic.min_le_right 1 _)
    nonnegative).trans
    (Weighted.mul_allowance_le squarePositive.le nonnegative)
  exact ⟨positive, count, le_rfl, weight, rfl, target, rfl,
    Basic.lt_min (by decide) (Weighted.allowance_positive squarePositive nonnegative),
      Basic.min_le_left _ _,
    (show 8 * ((count : Coordinate) ^ 2 * target + ((count - 1 : Nat) :
      Coordinate) ^ 2 * target) +
      672 * target + 36 * target = weight * target by ring1).trans_le bounded⟩

/-- Use one family's cached target for a smaller parent. This preserves the exact source and join tolerances shared by
adjacent parents. -/
def forCount {count smaller : Nat} {allowance : Coordinate}
    (allocation : ParentBasisRestorationAllowance
      count allowance) (counted : smaller ≤ count) :
    ParentBasisRestorationAllowance smaller allowance
      := by
  have cells := Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    smaller)) (Fraction.Cast.Order.natCast_le_direct counted) 2
  have joins := Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (smaller
    - 1)))
    (Fraction.Cast.Order.natCast_le_direct (Nat.sub_le_sub_right counted 1)) 2
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Arithmetic.mul_le_mul_of_nonneg_right_direct cells
      allocation.target_positive.le)
      (Arithmetic.mul_le_mul_of_nonneg_right_direct joins allocation.target_positive.le)) (by
          decide : (0 : Coordinate) ≤ 8)
  exact ⟨allocation.positive, allocation.capacity, counted.trans allocation.count_le,
    allocation.weight, allocation.weight_eq, allocation.target, allocation.target_eq,
    allocation.target_positive, allocation.small,
    (Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct paid le_rfl) le_rfl).trans
      allocation.paid⟩

variable {allowance : Coordinate}

/-- The preselected common restoration target transports the parent fan-energy lower bound to its actual restored trace,
retaining both endpoint potentials. -/
theorem trace_lower (allocation :
  ParentBasisRestorationAllowance edges.length
  allowance)
    {requests : ChartRequests allocation.target floor owners} {plans :
      ChartPlans capSample minimum requests}
    {cells : ComparedCells source capSample depth bank} {evaluated : EvaluationData readingIndex
      plans cells}
    {energies : BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : GaussianVector genus}
    {sample : BasisBoundarySample energies coefficients allocation.target}
    (restored :
      BasisBoundarySample.EndpointRestoration sample
      allocation.target allocation.target)
    (budget : ParentBasisBoundaryBudget plans cells evaluated)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (previous previousPotential :
      Gaussian)
    (gap : Basic.normSq (restored.firstValue - previous) ≤ allocation.target *
      coefficientNormSq coefficients)
    (joined : Basic.normSq (restored.joinError previous previousPotential) ≤
      (80 * allocation.target + 2 * allocation.target) * (coefficientNormSq coefficients)
        ^ 2) :
    -(((edges.length : Coordinate) * energyTarget + allowance) *
      coefficientNormSq coefficients) ≤
      (-IncrementArea.traceArea previous (restored.path previous) + restored.lastPotential - previousPotential).im / 4
        := by
  apply restored.trace_lower budget branch previous previousPotential allocation.target_positive.le
    allocation.target_positive.le allocation.small gap joined allowance allocation.positive.le
  rw [sample.joins.count_edges]
  have bound : 8 * (budget.bound + ((edges.length - 1 : Nat) : Coordinate) ^ 2 *
    allocation.target) ≤
      8 * ((edges.length : Coordinate) ^ 2 * allocation.target + ((edges.length - 1 : Nat) :
        Coordinate) ^ 2 * allocation.target) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (budget.bound_le allocation.target_positive.le) le_rfl) (by
        decide : (0 : Coordinate) ≤ 8)
  exact (Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct bound le_rfl)
    le_rfl).trans allocation.paid

end ParentBasisRestorationAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration.BasisBoundarySample
namespace EndpointRestoration

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration.BasisBoundarySample.EndpointRestoration
