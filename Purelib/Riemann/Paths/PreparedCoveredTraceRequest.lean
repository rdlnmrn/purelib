module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Readings.PreparedDescendantSampleBounds
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Paths.PathArea

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Periods.PreparedCoveredPeriodTrace
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Requested trace accuracy from a retained period cover

The patch-only sample ceiling is computed before choosing a polynomial
tolerance. Its readback through canonical acquisition proves that the paid
tolerance controls every later original period trace. No later sample is
evaluated to select the tolerance or the stage.
-/

namespace Purelib.Riemann.Paths.PreparedCoveredTraceRequest

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover (CoveredPeriodStage)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
  (ControlledLocalRequest ControlledParents ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedDescendantSampleBounds.PreparedPrimitiveChargeBounds
  (sampleDensityMaximum)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds
  (CoveredPeriodRequest)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)

open Purelib.Data.Rat in
/-- Rational coordinate type for covered trace estimates. -/
private abbrev Coordinate := Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
/-- Density bound of a prepared patch at a retained subdivision count.

Combines the differential numerator bound, inverse derivative bound and inverse approximation error on the patch
neighborhood. -/
def patchDensity {parent : CenteredEdge curve differential} (patch : PreparedPatch parent) (count : Nat) :
  Fraction.Rational :=
  let neighborhood := patch.neighborhood count
  let numerator := Bounds.Box.denseEvalNormBound (differentialNumerator differential) neighborhood.box
  2 * (numerator * (SeededPrimitiveBounds.derivativeBounds neighborhood.base).inverseUpper +
    2 * numerator * neighborhood.inverseErrorScale)

section
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Data.Rat
/-- Maximum patch density over the covered parent list.

Recurses through the exact covered-parent witnesses with zero for the empty cover. -/
def coverDensity : {parents : List (CenteredEdge curve differential)} → Observation.UniformPreparedMesh.CoveredParents
  count parents → Fraction.Rational
  | _, .nil => 0
  | _, .cons patch _ tail => max (patchDensity patch count) (coverDensity tail)

/-- The maximum covered-parent density is nonnegative.

The empty value is zero and each recursive maximum retains the nonnegative tail bound. -/
private theorem coverDensity_nonnegative : ∀ {parents : List (CenteredEdge curve differential)}
    (covered : Observation.UniformPreparedMesh.CoveredParents count parents), 0 ≤ coverDensity covered
  | _, .nil => le_rfl
  | _, .cons _ _ tail => (coverDensity_nonnegative tail).trans (Fraction.Order.Basic.le_max_right _ _)

end

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Acquiring controlled parents preserves the cover density.

The sample-density maximum is independent of the requested numerical targets and minimum index because acquisition
retains the original patch neighborhoods. -/
private theorem acquired_density {parents : List (CenteredEdge curve differential)} (covered :
  Observation.UniformPreparedMesh.CoveredParents count parents)
    (target coefficientTarget : Fraction.Rational) (positive : 0 < target) (coefficientPositive : 0 < coefficientTarget)
    (proper : AllParentsProper parents) (minimum : Nat) :
    sampleDensityMaximum (ControlledParents.acquire covered target coefficientTarget positive coefficientPositive proper
      minimum).requests =
      coverDensity covered := by
  induction covered with
  | nil => rfl
  | cons patch finishInside tail ih =>
      change max
        (PreparedDescendantSampleBounds.LocalRequest.sampleDensity ((ControlledLocalRequest.acquire patch count target
          coefficientTarget positive coefficientPositive finishInside proper.1 minimum).localRequest))
        (sampleDensityMaximum (ControlledParents.acquire tail target coefficientTarget positive coefficientPositive
          proper.2 minimum).requests) = _
      have head : PreparedDescendantSampleBounds.LocalRequest.sampleDensity ((ControlledLocalRequest.acquire patch count
        target coefficientTarget positive coefficientPositive finishInside proper.1 minimum).localRequest) =
          patchDensity patch count := rfl
      exact congrArg₂ max head (ih proper.2)

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- The acquired controlled sum has the original cover density.

Specializes the controlled-parent density identity to the sum request and its retained properness witnesses. -/
private theorem acquired_sum_density {parents : List (CenteredEdge curve differential)} (covered :
  Observation.UniformPreparedMesh.CoveredParents count parents)
    (proper : AllParentsProper parents) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    sampleDensityMaximum (ControlledSumRequest.acquire covered proper target positive minimum).requests = coverDensity
      covered :=
  acquired_density covered _ _ _ _ proper minimum

variable {source : Differential genus} {root :
  Purelib.Riemann.Topology.PreparedRefinementRootChains.Named}
  {initial : RootClosedState curve source root} {targets : List
    (Differential genus)} {minimum : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Uniform sample bound for a covered period stage and differential.

Combines the recast cover density and parent movement mass with five halves of the initial schedule base. -/
def coverSampleBound (cover : CoveredPeriodStage initial targets count minimum) (differential :
  Differentials.Basic.Differential genus) : Fraction.Rational :=
  coverDensity (cover.recast differential) * movementMass (cover.retained.current.state.parents.map
    (PreparedEdgeRecasting.recastCenteredEdge differential)) +
    (5 / 2) * initial.state.scheduleBase targets

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The covered period sample bound is nonnegative.

Uses the nonnegative cover density and movement mass together with positivity of the initial schedule base. -/
theorem coverSampleBound_nonnegative (cover : CoveredPeriodStage initial targets count minimum) (differential :
  Differentials.Basic.Differential genus) :
    0 ≤ coverSampleBound cover differential :=
  add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (coverDensity_nonnegative _) (movementMass_nonnegative _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 5 / 2)
      (initial.state.scheduleBase_positive targets).le)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- Acquiring a period comparison preserves the cover sample bound.

The acquired request keeps the cover, recast parents and density data, so its sample bound is exactly the bound computed
before acquisition. -/
theorem acquired_sampleBound (cover : CoveredPeriodStage initial targets count minimum) (differential :
  Differentials.Basic.Differential genus)
    (target : Fraction.Rational) (positive : 0 < target) (minimumIndex : Nat) :
    PreparedCoveredPeriodTrace.CoveredPeriodRequest.sampleBound (CoveredPeriodRequest.ofCover cover differential target
      positive minimumIndex) = coverSampleBound cover differential := by
  change sampleDensityMaximum (ControlledSumRequest.acquire (cover.recast differential) _ target positive
    minimumIndex).requests *
    movementMass (cover.retained.current.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential)) + _
      = _
  rw [acquired_sum_density]
  rfl

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- Covered period comparison with a paid trace-area tolerance.

Retains a positive comparison tolerance and its exact sample bound, with the quadratic and start-dependent terms paid by
the requested target. -/
structure CoveredTraceRequest (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (count minimum : Nat) (start : Gaussian) (target :
      Fraction.Rational) where
  /-- Positive local tolerance allocated to the period comparison. -/ tolerance : Fraction.Rational
  /-- Strict positivity of the retained tolerance. -/ tolerance_positive : 0 < tolerance
  /-- Actual covered period comparison at that tolerance. -/ comparison : CoveredPeriodRequest initial targets
    differential count minimum tolerance
  /-- Cached sample bound used to allocate the trace tolerance. -/ sampleBound : Fraction.Rational
  /-- The cached bound is exactly the comparison sample bound. -/ sampleBound_eq : sampleBound =
    PreparedCoveredPeriodTrace.CoveredPeriodRequest.sampleBound comparison
  /-- The trace perturbation and starting-point terms fit the target. -/ paid : 64 * tolerance * (sampleBound +
    tolerance) + 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance ≤ target

constructive_injectivity CoveredTraceRequest

namespace CoveredTraceRequest

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Acquire a covered trace comparison within a positive target.

Caps the weighted allowance at one, uses the cover sample bound to allocate the comparison tolerance, and retains the
exact sample-bound identity and payment. -/
def ofCover (cover : CoveredPeriodStage initial targets count minimum) (differential : Differentials.Basic.Differential
  genus)
    (start : Gaussian) (target : Fraction.Rational) (positive : 0 < target) (minimumIndex : Nat := 0) :
    CoveredTraceRequest initial targets differential count minimum start target := by
  let bound := coverSampleBound cover differential
  have boundNonnegative : 0 ≤ bound := coverSampleBound_nonnegative cover differential
  let weight := 64 * (bound + 1) + 8 * Data.Gaussian.Norm.Basic.normSq start
  have weightNonnegative : 0 ≤ weight := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 64) (add_nonneg
      boundNonnegative (by decide)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 8) (Norm.Basic.normSq_nonneg
      start))
  let tolerance := min 1 (Budget.Weighted.allowance target weight)
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  let comparison := CoveredPeriodRequest.ofCover cover differential tolerance tolerancePositive minimumIndex
  have paid : 64 * tolerance * (bound + tolerance) + 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance ≤ target :=
    by
    have linear : 64 * tolerance * (bound + tolerance) + 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance ≤
        64 * tolerance * (bound + 1) + 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance :=
          Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Fraction.Order.Basic.min_le_left 1 _))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 64)
          tolerancePositive.le))
      (le_rfl : 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance ≤ 8 * Data.Gaussian.Norm.Basic.normSq start *
        tolerance)
    have budget := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right 1 _)
      weightNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)
    exact (linear.trans_eq (show 64 * tolerance * (bound + 1) + 8 * Data.Gaussian.Norm.Basic.normSq start * tolerance =
      weight * tolerance by
      dsimp only [weight]; ring1)).trans budget
  exact ⟨tolerance, tolerancePositive, comparison, bound, (acquired_sampleBound cover differential tolerance
    tolerancePositive minimumIndex).symm, paid⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Acquire a covered trace request from an initial root-closed state.

Builds the covered period stage at the requested count and floor, then allocates a positive trace tolerance for the
supplied differential and start point. -/
def acquire (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (count minimum : Nat) (start : Gaussian) (target :
      Fraction.Rational)
    (positive : 0 < target) (minimumIndex : Nat := 0) :
    CoveredTraceRequest initial targets differential count minimum start target :=
  ofCover (CoveredPeriodStage.acquire initial targets count minimum) differential start target positive minimumIndex

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Periods in
/-- The retained primitive trace area meets the requested target.

For a differential in the target list and a stage after the comparison threshold, composes the trace estimate with the
retained tolerance payment. -/
theorem accurate {start : Gaussian} {target : Fraction.Rational}
    (request : CoveredTraceRequest initial targets differential count minimum start target)
    (member : differential ∈ targets) (stage : Nat) (later : request.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.traceArea start
      (PreparedCoveredPeriodTrace.CoveredPeriodRequest.primitiveTracePath request.comparison stage
        (request.comparison.stage_after.trans later)) -
      IncrementArea.traceArea start (PathArea.increments ((initial.states targets stage).state.model differential))) ≤
        target := by
  have comparison := PreparedCoveredPeriodTrace.CoveredPeriodRequest.trace_accurate request.comparison
    request.tolerance_positive member stage later start
  rw [← request.sampleBound_eq] at comparison
  exact comparison.trans request.paid

end CoveredTraceRequest
end Purelib.Riemann.Paths.PreparedCoveredTraceRequest
