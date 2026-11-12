module

public import Purelib.Integration.Exponential.Integrand
public import Purelib.Integration.Exponential.Equivalence.Policy
public import Purelib.Integration.Program.Gaussian.Cached.Scale
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Exponential.Program
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.CCL.Program
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained finite comparisons of normalized exponential integrals

The supported integrands are finite Gaussian linear combinations of `exp(x)`
on the original oriented segment from zero to one. Scaling transforms the
actual original polynomial cells and observations, retaining every cached
source model and the Horner boundary subtraction by one. The shared source
bound is computed from the normalized coefficient rather than assumed.
-/

public section
namespace Purelib.Integration.Exponential.Comparison

open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat
open Purelib.Integration.Program.Gaussian.Cached.Basic (CachedProgram)
open Purelib.Integration.Exponential.Geometry (Policy)

set_option genInjectivity false in
/-- One original integration program and its normalized integrand-scaled cache.

The original program is computed once from its policy and schedule. The scaled
program consumes that exact cache and preserves every original oriented cell.
-/
structure Realization (integrand : Integrand) (policy : Policy)
    (schedule : Schedule.PositiveStride) (extraDepth : Nat) where
  /-- The retained original exponential integration program. -/
  original : CachedProgram
  /-- The original cache comes from this exact policy and schedule. -/
  original_eq : original = Program.program policy schedule extraDepth
  /-- The actual scaled cell/cache program for the computed coefficient. -/
  integral : CachedProgram
  /-- Scaling consumed the retained original program. -/
  integral_eq : integral = original.scale integrand.coefficient

constructive_injectivity Realization

namespace Realization

/-- Compute the original policy-controlled integration caches once and scale those same caches. -/
@[expose] def ofPolicy (integrand : Integrand) (policy : Policy)
    (schedule : Schedule.PositiveStride) (extraDepth : Nat) : Realization integrand policy schedule extraDepth :=
  let original := Program.program policy schedule extraDepth
  ⟨original, rfl, original.scale integrand.coefficient, rfl⟩

/-- Read the coherent output of the retained scaled integration program. -/
@[expose] def output {integrand : Integrand} {policy : Policy}
    {schedule : Schedule.PositiveStride} {extraDepth : Nat}
    (realization : Realization integrand policy schedule extraDepth) : CoherentNamed := realization.integral.output

/-- The scaled cached sample is the normalized coefficient times the original selected Horner integral. -/
theorem sample {integrand : Integrand} {policy : Policy}
    {schedule : Schedule.PositiveStride} {extraDepth : Nat}
    (realization : Realization integrand policy schedule extraDepth) (index : Nat) :
    (realization.integral.stage index).sample =
      integrand.coefficient * (Horner.Sample.sample 1 ((Selection.selection policy schedule index).depth + 1) - 1) := by
  rewrite [realization.integral_eq]
  rw [CachedProgram.scale_sample, realization.original_eq]
  exact congrArg (integrand.coefficient * ·) (Program.program_sample policy schedule extraDepth index)

/-- The comparison error scale pays both original Horner tails and the exact integrand coefficient. -/
@[expose] def comparisonScale (coefficient : Basic.Canonical) : Fraction.Rational :=
  (2 * (10 + 10)) * Norm.Basic.normSq coefficient

/-- The computed comparison budget is nonnegative, including exact cancellation to coefficient zero. -/
theorem comparisonScale_nonnegative (coefficient : Basic.Canonical) : 0 ≤ comparisonScale coefficient :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide : (0 : Fraction.Rational) ≤ 10) (by decide)))
    (Norm.Basic.normSq_nonneg coefficient)

/-- Every pair of later original program samples meets the computed common-source budget.

The canonical selection floors derive both Horner comparisons. The coefficient
identity is an exact supported integrand identity, not a sample-bound premise.
-/
theorem samples_bound {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra)
    (same : leftIntegrand.coefficient = rightIntegrand.coefficient)
    (common leftStage rightStage : Nat) (leftOrder : common ≤ leftStage) (rightOrder : common ≤ rightStage) :
    Norm.Basic.normSq ((left.integral.stage leftStage).sample - (right.integral.stage rightStage).sample) ≤
      Geometric.Basic.quarterRadius (comparisonScale leftIntegrand.coefficient) common := by
  rw [left.sample, right.sample, ← same]
  let leftSource := (Selection.selection leftPolicy leftSchedule leftStage).depth + 1
  let rightSource := (Selection.selection rightPolicy rightSchedule rightStage).depth + 1
  have leftFloor : common ≤ leftSource :=
    leftOrder.trans ((Selection.selection leftPolicy leftSchedule leftStage).stage_le_depth.trans (Nat.le_succ _))
  have rightFloor : common ≤ rightSource :=
    rightOrder.trans ((Selection.selection rightPolicy rightSchedule rightStage).stage_le_depth.trans (Nat.le_succ _))
  have leftClose := Horner.Sample.sample_later_close 1 (by decide) leftFloor
  have rightClose := Horner.Sample.sample_later_close 1 (by decide) rightFloor
  have rightReverse : Norm.Basic.normSq (Horner.Sample.sample 1 common - Horner.Sample.sample 1 rightSource) ≤
      Geometric.Basic.quarterRadius 10 common := by
    rw [Norm.Bounds.normSq_sub_symm]
    exact rightClose
  have difference : leftIntegrand.coefficient * (Horner.Sample.sample 1 leftSource - 1) -
      leftIntegrand.coefficient * (Horner.Sample.sample 1 rightSource - 1) =
      leftIntegrand.coefficient * (Horner.Sample.sample 1 leftSource - Horner.Sample.sample 1 rightSource) := by ring1
  change Norm.Basic.normSq
    (leftIntegrand.coefficient * (Horner.Sample.sample 1 leftSource - 1) -
      leftIntegrand.coefficient * (Horner.Sample.sample 1 rightSource - 1)) ≤ _
  rw [difference, Norm.Basic.normSq_mul]
  have tails := (Norm.Bounds.normSq_sub_le_via
    (Horner.Sample.sample 1 leftSource) (Horner.Sample.sample 1 common) (Horner.Sample.sample 1 rightSource)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct leftClose rightReverse) (by decide))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tails
    (Norm.Basic.normSq_nonneg leftIntegrand.coefficient)).trans_eq (by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      unfold comparisonScale
      ring1)

/-- Compute sufficient original program stages from both starts and the actual coefficient budget. -/
@[expose] def equivalent {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra)
    (same : leftIntegrand.coefficient = rightIntegrand.coefficient) :
    Equivalent left.integral.approximation right.integral.approximation where
  compare leftStart rightStart target positive :=
    let common := Geometric.Search.firstQuarterBelow (comparisonScale leftIntegrand.coefficient)
      (max leftStart rightStart) target
    let startFloor := Geometric.Search.firstQuarterBelow_ge (comparisonScale leftIntegrand.coefficient)
      (max leftStart rightStart) target
    { leftIndex := common
      rightIndex := common
      left_ge := (Order.le_max_left leftStart rightStart).trans startFloor
      right_ge := (Order.le_max_right leftStart rightStart).trans startFloor
      close := fun leftOrder rightOrder =>
        (left.samples_bound right same common _ _ leftOrder rightOrder).trans_lt
          (Geometric.Search.firstQuarterBelow_accurate (comparisonScale leftIntegrand.coefficient)
            (comparisonScale_nonnegative _) (max leftStart rightStart) target positive) }

/-- Lift the internally computed integrand/schedule comparison to both original output programs. -/
@[expose] def outputsEquivalent {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra)
    (same : leftIntegrand.coefficient = rightIntegrand.coefficient) :
    NamedEquivalent left.output.name right.output.name :=
  (left.equivalent right same).toNamed

set_option genInjectivity false in
/-- A finite comparison retaining both actual selected integration caches and its original request. -/
structure Observation {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra)
    (leftStart rightStart : Nat) (target : Fraction.Rational) where
  /-- The exact computed all-later comparison of the two original programs. -/
  comparison : Purelib.Approximation.Gaussian.Equivalence.Comparison
    left.integral.approximation right.integral.approximation leftStart rightStart target
  /-- The retained original left cache at its own computed stage. -/
  leftCache : Purelib.Integration.Program.Gaussian.Cached.Basic.CachedModel
  /-- The retained original right cache at its own computed stage. -/
  rightCache : Purelib.Integration.Program.Gaussian.Cached.Basic.CachedModel
  /-- The left cache comes from the original left program and computed index. -/
  leftCache_eq : leftCache = left.integral.stage comparison.leftIndex
  /-- The right cache comes from the original right program and computed index. -/
  rightCache_eq : rightCache = right.integral.stage comparison.rightIndex
  /-- The actual retained sample readings meet the original requested tolerance. -/
  close : Norm.Basic.normSq (leftCache.sample - rightCache.sample) < target

constructive_injectivity Observation

/-- Compute a finite request and retain the same actual original program caches used by its payment. -/
@[expose] def observe {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra)
    (same : leftIntegrand.coefficient = rightIntegrand.coefficient)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Observation left right leftStart rightStart target :=
  let comparison := (left.equivalent right same).compare leftStart rightStart target positive
  let leftCache := left.integral.stage comparison.leftIndex
  let rightCache := right.integral.stage comparison.rightIndex
  ⟨comparison, leftCache, rightCache, rfl, rfl, comparison.close (Nat.le_refl _) (Nat.le_refl _)⟩

set_option genInjectivity false in
/-- Distinct normalized coefficients retain the exact unresolved supported-integrand comparison. -/
structure CoefficientMismatch (left right : Integrand) where
  /-- The actual left normalized coefficient. -/
  first : Basic.Canonical
  /-- The actual right normalized coefficient. -/
  second : Basic.Canonical
  /-- The first coefficient reads the original left construction. -/
  first_eq : first = left.coefficient
  /-- The second coefficient reads the original right construction. -/
  second_eq : second = right.coefficient
  /-- The two exact formal coefficients differ. This supplies no integral inequality. -/
  different : first ≠ second

constructive_injectivity CoefficientMismatch

/-- Check the supported integrand identity and return its original-program comparison or exact formal mismatch. -/
@[expose] def compare {leftIntegrand rightIntegrand : Integrand} {leftPolicy rightPolicy : Policy}
    {leftSchedule rightSchedule : Schedule.PositiveStride} {leftExtra rightExtra : Nat}
    (left : Realization leftIntegrand leftPolicy leftSchedule leftExtra)
    (right : Realization rightIntegrand rightPolicy rightSchedule rightExtra) :
    Except (CoefficientMismatch leftIntegrand rightIntegrand) (NamedEquivalent left.output.name right.output.name) :=
  if same : leftIntegrand.coefficient = rightIntegrand.coefficient then .ok (left.outputsEquivalent right same)
  else .error ⟨leftIntegrand.coefficient, rightIntegrand.coefficient, rfl, rfl, same⟩

end Realization
end Purelib.Integration.Exponential.Comparison
end
