module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Primitive requests with an automatically paid polynomial floor

The inverse-root polynomial index must pay both the local primitive request
and the coefficient floor of the actual period comparison.  Its finite index
is selected before the polynomial and spatial meshes are constructed.  The
semantic request interfaces still accept independently generated models.
An optional mesh-wide minimum index is paid before polynomial construction,
and its readback is retained throughout the actual request spine.
-/

namespace Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Readings.UniformPreparedRequests
  (LocalRequest RequestedParents PrimitiveSumRequest)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
  (localCoefficient coefficientMaximum)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay (DecayBudget)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_antitone)

set_option genInjectivity false in
open Purelib.Approximation.Rational in
/-- One refinement index meeting two original accuracy requests and a retained lower bound.

Both quarter-radius inequalities retain their own scales and positive targets, while the selected index is explicitly
above the original minimum. -/
structure DualIndex (firstScale secondScale firstTarget secondTarget : Coordinate) (minimum : Nat := 0) where
  /-- The retained common refinement index. -/ index : Nat
  /-- The retained index is above the original requested minimum. -/ index_ge : minimum ≤ index
  /-- The first original scale's quarter-radius is strictly below its target. -/ first_accurate :
    Geometric.Basic.quarterRadius firstScale index < firstTarget
  /-- The second original scale's quarter-radius is strictly below its target. -/ second_accurate :
    Geometric.Basic.quarterRadius secondScale index < secondTarget

constructive_injectivity DualIndex

open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Select one index above the original minimum satisfying both retained quarter-radius requests.

The second scale is bounded by its maximum with zero; the two finite searches and supplied minimum are combined by
maxima without changing either target. -/
@[expose] def DualIndex.acquire (firstScale secondScale firstTarget secondTarget : Coordinate)
    (firstNonnegative : 0 ≤ firstScale) (firstPositive : 0 < firstTarget) (secondPositive : 0 < secondTarget)
    (minimum : Nat := 0) : DualIndex firstScale secondScale firstTarget secondTarget minimum :=
  let second := max secondScale 0
  have secondNonnegative : 0 ≤ second := Fraction.Order.Basic.le_max_right _ _
  let firstIndex := Geometric.Search.firstQuarterBelow firstScale 0 firstTarget
  let secondIndex := Geometric.Search.firstQuarterBelow second 0 secondTarget
  let index := max minimum (max firstIndex secondIndex)
  have aboveMinimum : minimum ≤ index := by
    change minimum ≤ max minimum (max firstIndex secondIndex)
    rw [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_left _ _
  have aboveFirst : firstIndex ≤ index := by
    change firstIndex ≤ max minimum (max firstIndex secondIndex)
    rw [Nat.Order.max_eq_natMax, Nat.Order.max_eq_natMax]
    exact (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)
  have aboveSecond : secondIndex ≤ index := by
    change secondIndex ≤ max minimum (max firstIndex secondIndex)
    rw [Nat.Order.max_eq_natMax, Nat.Order.max_eq_natMax]
    exact (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)
  have secondScaleBound : Geometric.Basic.quarterRadius secondScale index ≤
      Geometric.Basic.quarterRadius second index := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Basic.le_max_left _ _)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index)
  { index := index
    index_ge := aboveMinimum
    first_accurate := (quarterRadius_antitone firstNonnegative
      aboveFirst).trans_lt
      (Geometric.Search.firstQuarterBelow_accurate firstScale firstNonnegative 0 firstTarget firstPositive)
    second_accurate := (secondScaleBound.trans
      (quarterRadius_antitone secondNonnegative
        aboveSecond)).trans_lt
        (Geometric.Search.firstQuarterBelow_accurate second secondNonnegative 0 secondTarget secondPositive) }

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- An original local primitive request with a strict coefficient target and index floor.

The request retains its original parent and count; its coefficient accuracy concerns that exact request's local
inverse-error coefficient. -/
structure ControlledLocalRequest (parent : CenteredEdge curve differential) (count : Nat)
    (target coefficientTarget : Coordinate) (minimum : Nat := 0) where
  /-- The original local primitive request with its exact parent and neighborhood. -/ localRequest : LocalRequest parent
    count target
  /-- The original request coefficient is strictly below the retained coefficient target. -/ coefficient_accurate :
    localCoefficient localRequest < coefficientTarget
  /-- The retained index is above the original requested minimum. -/ index_ge : minimum ≤ localRequest.request.index

constructive_injectivity ControlledLocalRequest

namespace ControlledLocalRequest

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Normalization in
/-- Acquire one original primitive model paying both approximation error and local coefficient targets.

The same neighborhood, numerator bound and selected dual index construct the retained model and block; endpoint
containment and the proper parent edge are preserved. -/
@[expose] def acquire {parent : CenteredEdge curve differential} (patch : PreparedPatch parent) (count : Nat)
    (target coefficientTarget : Coordinate) (positive : 0 < target) (coefficientPositive : 0 < coefficientTarget)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat := 0) :
    ControlledLocalRequest parent count target coefficientTarget minimum := by
  let neighborhood := patch.neighborhood count
  let numerator := differentialNumerator differential
  let numeratorBound := Bounds.Box.denseEvalNormBound numerator neighborhood.box
  have numeratorNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg numerator neighborhood.box).1
  have numeratorLe : ∀ point, neighborhood.box.Contains point → normSq (numerator.eval point) ≤ numeratorBound :=
    fun _ inside => by
      have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar
  let localScale := PreparedPrimitiveRequests.rootScale neighborhood numeratorBound (PreparedPrimitiveRequests.movement
    parent)
  let coefficientScale := 4 * numeratorBound * neighborhood.inverseErrorScale
  have localPositive : 0 < target / 8 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let selected := DualIndex.acquire localScale coefficientScale ((target / 8) / 3) coefficientTarget
    (PreparedPrimitiveRequests.rootScale_nonnegative neighborhood numeratorNonnegative
      (PreparedPrimitiveRequests.movement_nonnegative parent))
    (Fraction.Order.Field.div_pos_direct localPositive (by decide)) coefficientPositive minimum
  let model := InverseRootPrimitive.PrimitiveModel.ofIndex
    neighborhood selected.index numerator
  let approximation := PreparedPrimitiveRequests.Request.ofModel parent neighborhood (target / 8) localPositive proper
    numeratorBound numeratorNonnegative numeratorLe selected.index model selected.first_accurate
  let localRequest : LocalRequest parent count target := ⟨patch, neighborhood, rfl, approximation, finishInside⟩
  refine ⟨localRequest, ?_, selected.index_ge⟩
  have coefficientEq : localCoefficient localRequest = Geometric.Basic.quarterRadius coefficientScale selected.index :=
    by
    change 4 * numeratorBound * Geometric.Basic.quarterRadius neighborhood.inverseErrorScale selected.index =
      Geometric.Basic.quarterRadius (4 * numeratorBound * neighborhood.inverseErrorScale) selected.index
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact coefficientEq.trans_lt selected.second_accurate

end ControlledLocalRequest

/-- Every request in the original parent family retains an index above the supplied minimum.

The proposition follows the retained request spine. Each original parent
contributes its stored request index and the remaining family's lower-bound certificate. -/
@[expose] def IndicesAbove (minimum : Nat) : {parents : List (CenteredEdge curve differential)} →
    {target : Coordinate} → RequestedParents count target parents → Prop
  | _, _, .nil => True
  | _, _, .cons request tail => minimum ≤ request.request.index ∧ IndicesAbove minimum tail

set_option genInjectivity false in
/-- An original request family with a controlled coefficient maximum and retained index floors.

The exact parent list and per-parent target remain unchanged, and every retained request contributes to the same strict
maximum bound. -/
structure ControlledParents (parents : List (CenteredEdge curve differential)) (count : Nat)
    (target coefficientTarget : Coordinate) (minimum : Nat := 0) where
  /-- The original indexed family of retained local parent requests. -/ requests : RequestedParents count target parents
  /-- The original request family coefficient maximum is strictly below its retained target. -/ coefficient_accurate :
    coefficientMaximum requests < coefficientTarget
  /-- Every retained original request meets the stored minimum index. -/ indices_ge : IndicesAbove minimum requests

constructive_injectivity ControlledParents

open Purelib.Curves.Hyperelliptic.Integration in
/-- Acquire controlled original requests recursively along the retained covered parent list.

Each parent keeps its own patch and finish-containment witness, with one shared coefficient target and minimum index;
the resulting maximum bound retains that exact list. -/
@[expose] def ControlledParents.acquire {parents : List (CenteredEdge curve differential)} (covered :
  Observation.UniformPreparedMesh.CoveredParents count parents)
    (target coefficientTarget : Coordinate) (positive : 0 < target) (coefficientPositive : 0 < coefficientTarget)
    (proper : AllParentsProper parents) (minimum : Nat := 0) :
    ControlledParents parents count target coefficientTarget minimum :=
  match covered with
  | .nil => ⟨.nil, coefficientPositive, True.intro⟩
  | .cons patch finishInside tail =>
      let head := ControlledLocalRequest.acquire patch count target coefficientTarget positive coefficientPositive
        finishInside proper.1 minimum
      let remaining := ControlledParents.acquire tail target coefficientTarget positive coefficientPositive proper.2
        minimum
      ⟨.cons head.localRequest remaining.requests, (by
        change (if localCoefficient head.localRequest ≤ coefficientMaximum remaining.requests then
          coefficientMaximum remaining.requests else localCoefficient head.localRequest) < coefficientTarget
        by_cases ordered : localCoefficient head.localRequest ≤ coefficientMaximum remaining.requests
        · rw [if_pos ordered]
          exact remaining.coefficient_accurate
        · rw [if_neg ordered]
          exact head.coefficient_accurate),
        head.index_ge, remaining.indices_ge⟩
termination_by structural covered

set_option genInjectivity false in
/-- An original primitive-sum request with cached movement mass and a controlled polynomial-error floor.

The coefficient target is exactly half the original target divided by mass plus one; all retained parent requests also
satisfy the stored minimum index. -/
structure ControlledSumRequest (parents : List (CenteredEdge curve differential)) (count : Nat) (target : Coordinate)
  extends
    PrimitiveSumRequest parents count target where
  /-- The cached movement mass of the original parents. -/ mass : Coordinate
  /-- Exact equality between the cache and original parent movement mass. -/ mass_eq : mass = movementMass parents
  /-- The retained coefficient accuracy target. -/ coefficientTarget : Coordinate
  /-- The coefficient target is half the original target divided by mass plus one. -/ coefficientTarget_eq :
    coefficientTarget = (target / 2) / (mass + 1)
  /-- The retained sum request coefficient maximum is strictly below its original mass-based target. -/
    coefficient_accurate : coefficientMaximum requests < coefficientTarget
  /-- The original requested lower bound on all retained primitive indices. -/ minimumIndex : Nat
  /-- Every retained original request meets the stored minimum index. -/ indices_ge : IndicesAbove minimumIndex requests

constructive_injectivity ControlledSumRequest

namespace ControlledSumRequest

variable {parents : List (CenteredEdge curve differential)} {target : Coordinate}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
/-- Acquire an original primitive-sum request with a polynomial floor paid below half the target.

The original movement mass and mass-plus-one denominator set the coefficient target; per-term budgets and minimum
indices are retained in the exact acquired request family. -/
@[expose] def acquire (covered : Observation.UniformPreparedMesh.CoveredParents count parents) (proper :
  AllParentsProper parents)
    (target : Coordinate) (positive : 0 < target) (minimumIndex : Nat := 0) : ControlledSumRequest parents count target
      := by
  let mass := movementMass parents
  let coefficientTarget := (target / 2) / (mass + 1)
  have coefficientPositive : 0 < coefficientTarget := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide))
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (movementMass_nonnegative parents) (by decide))
  let localTarget := Budget.Aggregate.perTerm target parents.length
  let controlled := ControlledParents.acquire covered localTarget coefficientTarget
    (Budget.Aggregate.perTerm_positive positive parents.length) coefficientPositive proper minimumIndex
  let result := PrimitiveSumRequest.ofRequests parents target positive controlled.requests
  exact { toPrimitiveSumRequest := result
          mass := mass
          mass_eq := rfl
          coefficientTarget := coefficientTarget
          coefficientTarget_eq := rfl
          coefficient_accurate := controlled.coefficient_accurate
          minimumIndex := minimumIndex
          indices_ge := controlled.indices_ge }

open Purelib.Curves.Hyperelliptic.Integration in
/-- The acquired controlled sum request retains the exact requested minimum index. -/
theorem acquire_minimumIndex (covered : Observation.UniformPreparedMesh.CoveredParents count parents)
    (proper : AllParentsProper parents) (target : Coordinate) (positive : 0 < target) (minimumIndex : Nat) :
    (acquire covered proper target positive minimumIndex).minimumIndex = minimumIndex := rfl

open Purelib.Data.Rat in
/-- The controlled original request's polynomial floor is below half its target.

The proof uses the retained coefficient maximum, exact movement-mass identity and positive mass-plus-one denominator of
the same request family. -/
theorem polynomialFloor_lt (request : ControlledSumRequest parents count target) {base : Coordinate}
    (budget : DecayBudget request.requests base) : budget.polynomialFloor < target / 2 := by
  have factorPositive : 0 < budget.mass + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    budget.mass_nonnegative (by decide)
  have coefficientBound : budget.coefficient < (target / 2) / (budget.mass + 1) := by
    calc
      budget.coefficient = coefficientMaximum request.requests := budget.coefficient_eq
      _ < request.coefficientTarget := request.coefficient_accurate
      _ = (target / 2) / (budget.mass + 1) := by rw [request.coefficientTarget_eq, request.mass_eq, budget.mass_eq]
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct factorPositive coefficientBound
  have paid : (budget.mass + 1) * ((target / 2) / (budget.mass + 1)) = target / 2 := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ factorPositive.ne'
  have enlarged : budget.mass ≤ budget.mass + 1 := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      (by decide : (0 : Coordinate) ≤ 1) budget.mass
    calc
      budget.mass = 0 + budget.mass := by ring1
      _ ≤ 1 + budget.mass := shifted
      _ = budget.mass + 1 := by ring1
  calc
    budget.polynomialFloor = budget.mass * budget.coefficient := by rw [budget.polynomialFloor_eq]; ring1
    _ ≤ (budget.mass + 1) * budget.coefficient :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged budget.coefficient_nonnegative
    _ < target / 2 := scaled.trans_eq paid

end ControlledSumRequest

end Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
