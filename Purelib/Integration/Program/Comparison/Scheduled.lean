module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Schedule.Common
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.CCL.Program
public import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Integration.Program.Gaussian.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone quarterRadius_weighted_sum)

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Integration.Program.Comparison.Scheduled

open Purelib.Data in
open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Program in
open Purelib.Riemann.Periods in
/-- Compare two original integration outputs through retained common-schedule sample bounds.

The certificate selects sufficiently late original schedule indices and combines both programs' own decay bounds with
the separate bridge scale to meet each positive target. -/
def scheduledProgram_output_equivalent
    (left right : Gaussian.Basic.RefinementProgram) (schedule : Approximation.Schedule.Common.CommonSchedule)
    (bridgeScale : Fraction.Rational) (bridgeScale_nonnegative : 0 ≤ bridgeScale)
    (samples : forall request,
      Norm.Basic.normSq
          (((left.model (schedule.targetIndex request)).integralSample) -
            ((right.model (schedule.comparisonIndex request)).integralSample)) ≤
        Geometric.Basic.quarterRadius bridgeScale request) :
    Equivalence.NamedEquivalent left.output.name right.output.name := by
  let totalScale : Fraction.Rational :=
    2 * (left.errorScale + 2 * (bridgeScale + right.errorScale))
  have totalScale_nonnegative : 0 ≤ totalScale :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg bridgeScale_nonnegative right.errorScale_nonneg)))
  have equivalent : Equivalence.Equivalent
      left.approximation right.approximation := by
    refine { compare := ?_ }
    intro leftStart rightStart target positive
    let common := Geometric.Search.firstQuarterBelow totalScale
      (max leftStart rightStart) target
    have common_ge_left : leftStart ≤ common :=
      (Nat.Order.le_max_left leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have common_ge_right : rightStart ≤ common :=
      (Nat.Order.le_max_right leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have totalSmall : Geometric.Basic.quarterRadius totalScale common <
        target :=
      Geometric.Search.firstQuarterBelow_accurate totalScale
        totalScale_nonnegative (max leftStart rightStart) target positive
    exact
      { leftIndex := schedule.targetIndex common
        rightIndex := schedule.comparisonIndex common
        left_ge := common_ge_left.trans (schedule.target_ge common)
        right_ge := common_ge_right.trans (schedule.comparison_ge common)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftEarlier := schedule.targetIndex common
          let rightEarlier := schedule.comparisonIndex common
          have leftClose : Norm.Basic.normSq
              ((left.model leftLater).integralSample -
                (left.model leftEarlier).integralSample) ≤
              Geometric.Basic.quarterRadius left.errorScale common :=
            by
              have scalar := left.later_close leftOrder
              rw [← Norm.Basic.normSq_eq_canonical] at scalar
              exact scalar.trans
                (quarterRadius_antitone left.errorScale_nonneg
                  (schedule.target_ge common))
          have middleClose := samples common
          have rightForward := right.later_close rightOrder
          rw [← Norm.Basic.normSq_eq_canonical] at rightForward
          have rightClose : Norm.Basic.normSq
              ((right.model rightEarlier).integralSample -
                (right.model rightLater).integralSample) ≤
              Geometric.Basic.quarterRadius right.errorScale common := by
            rw [Norm.Bounds.normSq_sub_symm]
            exact rightForward.trans
              (quarterRadius_antitone right.errorScale_nonneg
                (schedule.comparison_ge common))
          change Norm.Basic.normSq
              ((left.model leftLater).integralSample -
                (right.model rightLater).integralSample) < target
          apply (Norm.Bounds.normSq_sub_le_weighted_sum
            (left.model leftLater).integralSample
            (left.model leftEarlier).integralSample
            (right.model rightEarlier).integralSample
            (right.model rightLater).integralSample
            (Geometric.Basic.quarterRadius left.errorScale common)
            (Geometric.Basic.quarterRadius bridgeScale common)
            (Geometric.Basic.quarterRadius right.errorScale common)
            leftClose middleClose rightClose).trans_lt
          rw [quarterRadius_weighted_sum]
          exact totalSmall }
  simpa only [RefinementProgram.output,
    CertifiedProgram.Program.output,
    RefinementProgram.approximation,
    Name.Coherent.CoherentNamed.ofApproximation] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed equivalent

end Purelib.Integration.Program.Comparison.Scheduled

end

public section

namespace Purelib.Integration.Program.Comparison.Scheduled

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

/-- The actual original-name comparison retained at one finite schedule request. -/
@[expose] def TailObservation (left right : CoherentNamed) (leftStart rightStart : Nat)
    (scale : Rational) (request : Nat) :=
  Equivalence.Comparison (Name.Sampling.approximation left.name) (Name.Sampling.approximation right.name)
    leftStart rightStart (Basic.quarterRadius scale request)

set_option genInjectivity false in
/-- One cached finite comparison and the floors from which it was computed. -/
structure Selection (left right : CoherentNamed) (scale : Rational) (request : Nat) where
  /-- The original first-name starting index requested from the comparison. -/
  leftStart : Nat
  /-- The original second-name starting index requested from the comparison. -/
  rightStart : Nat
  /-- The first starting index meets the original request. -/
  left_floor : request ≤ leftStart
  /-- The second starting index meets the original request. -/
  right_floor : request ≤ rightStart
  /-- The actual comparison payload, computed once at those same starts and tolerance. -/
  observation : TailObservation left right leftStart rightStart scale request

constructive_injectivity Selection

/-- Build one retained selection using the original comparison procedure. -/
private def select (left right : CoherentNamed) (equivalent : Equivalence.NamedEquivalent left.name right.name)
    (scale : Rational) (positive : 0 < scale) (request leftStart rightStart : Nat)
    (leftFloor : request ≤ leftStart) (rightFloor : request ≤ rightStart) : Selection left right scale request :=
  ⟨leftStart, rightStart, leftFloor, rightFloor,
    equivalent.compare leftStart rightStart (Basic.quarterRadius scale request) (Basic.quarterRadius_pos positive _)⟩

/-- Construct a requested finite comparison after the retained previous comparison's indices.

Each successor consumes the preceding comparison once, then includes both
its selected indices and the new requested floor in the original call. -/
def selections (left right : CoherentNamed) (equivalent : Equivalence.NamedEquivalent left.name right.name)
    (scale : Rational) (positive : 0 < scale) : (request : Nat) → Selection left right scale request
  | 0 => select left right equivalent scale positive 0 0 0 (Nat.le_refl _) (Nat.le_refl _)
  | request + 1 =>
      let previous := selections left right equivalent scale positive request
      select left right equivalent scale positive (request + 1)
        (max (request + 1) previous.observation.leftIndex) (max (request + 1) previous.observation.rightIndex)
        (Purelib.Data.Nat.Order.le_max_left _ _) (Purelib.Data.Nat.Order.le_max_left _ _)

private theorem selections_left_step (left right : CoherentNamed)
    (equivalent : Equivalence.NamedEquivalent left.name right.name) (scale : Rational) (positive : 0 < scale)
    (request : Nat) :
    (selections left right equivalent scale positive request).observation.leftIndex ≤
      (selections left right equivalent scale positive (request + 1)).observation.leftIndex := by
  let previous := selections left right equivalent scale positive request
  exact (Purelib.Data.Nat.Order.le_max_right (request + 1) previous.observation.leftIndex).trans
    (selections left right equivalent scale positive (request + 1)).observation.left_ge

private theorem selections_right_step (left right : CoherentNamed)
    (equivalent : Equivalence.NamedEquivalent left.name right.name) (scale : Rational) (positive : 0 < scale)
    (request : Nat) :
    (selections left right equivalent scale positive request).observation.rightIndex ≤
      (selections left right equivalent scale positive (request + 1)).observation.rightIndex := by
  let previous := selections left right equivalent scale positive request
  exact (Purelib.Data.Nat.Order.le_max_right (request + 1) previous.observation.rightIndex).trans
    (selections left right equivalent scale positive (request + 1)).observation.right_ge

set_option genInjectivity false in
/-- Cached canonical carriers and a common schedule with its actual sample certificates. -/
structure ScheduledComparison (left right : CoherentNamed) (scale : Rational) where
  /-- The cached canonical carrier of the original first name. -/
  leftCarrier : RefinementProgram
  /-- The first carrier belongs to the original first name. -/
  leftCarrier_eq : leftCarrier = RefinementProgram.ofCoherentNamed left
  /-- The cached canonical carrier of the original second name. -/
  rightCarrier : RefinementProgram
  /-- The second carrier belongs to the original second name. -/
  rightCarrier_eq : rightCarrier = RefinementProgram.ofCoherentNamed right
  /-- The original finite comparison payload available at each requested stage. -/
  attempts : (request : Nat) → Selection left right scale request
  /-- The deterministic common schedule constructed from the same retained attempts. -/
  schedule : Purelib.Approximation.Schedule.Common.CommonSchedule
  /-- The selected first index reads its original cached comparison. -/
  target_eq : ∀ request, schedule.targetIndex request = (attempts request).observation.leftIndex
  /-- The selected second index reads its original cached comparison. -/
  comparison_eq : ∀ request, schedule.comparisonIndex request = (attempts request).observation.rightIndex

constructive_injectivity ScheduledComparison

/-- Derive a monotone common schedule from a retained operational equivalence.

Production callers derive that equivalence from their original source data;
this constructor computes the schedule and all later sample comparisons. -/
def fromEquivalent (left right : CoherentNamed) (equivalent : Equivalence.NamedEquivalent left.name right.name)
    (scale : Rational) (positive : 0 < scale) : ScheduledComparison left right scale := by
  let attempts := selections left right equivalent scale positive
  have leftMono : ∀ {first second}, first ≤ second →
      (attempts first).observation.leftIndex ≤ (attempts second).observation.leftIndex := by
    intro first second order
    induction order with
    | refl => exact Nat.le_refl _
    | @step second order previous => exact previous.trans (selections_left_step left right equivalent scale positive _)
  have rightMono : ∀ {first second}, first ≤ second →
      (attempts first).observation.rightIndex ≤ (attempts second).observation.rightIndex := by
    intro first second order
    induction order with
    | refl => exact Nat.le_refl _
    | @step second order previous => exact previous.trans (selections_right_step left right equivalent scale positive _)
  let schedule : Purelib.Approximation.Schedule.Common.CommonSchedule :=
    { sourceIndex := id
      targetIndex := fun request => (attempts request).observation.leftIndex
      comparisonIndex := fun request => (attempts request).observation.rightIndex
      source_ge := fun request => Nat.le_refl request
      target_ge := fun request => (attempts request).left_floor.trans (attempts request).observation.left_ge
      comparison_ge := fun request => (attempts request).right_floor.trans (attempts request).observation.right_ge
      source_mono := fun order => order
      target_mono := leftMono
      comparison_mono := rightMono }
  exact ⟨RefinementProgram.ofCoherentNamed left, rfl, RefinementProgram.ofCoherentNamed right, rfl,
    attempts, schedule, fun _ => rfl, fun _ => rfl⟩

/-- Later original carrier samples meet the cached comparison's same geometric tolerance.

The retained tail observation already certifies every later pair of indices;
advancing a shared schedule therefore reuses that observation without
running the original comparison procedure again. -/
theorem ScheduledComparison.samples_close_later {left right : CoherentNamed} {scale : Rational}
    (prepared : ScheduledComparison left right scale) (request leftIndex rightIndex : Nat)
    (leftLater : prepared.schedule.targetIndex request ≤ leftIndex)
    (rightLater : prepared.schedule.comparisonIndex request ≤ rightIndex) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (((RefinementProgram.ofCoherentNamed left).model leftIndex).integralSample -
        ((RefinementProgram.ofCoherentNamed right).model rightIndex).integralSample) ≤
      Basic.quarterRadius scale request := by
  rw [RefinementProgram.ofCoherentNamed_integralSample, RefinementProgram.ofCoherentNamed_integralSample]
  rw [prepared.target_eq request] at leftLater
  rw [prepared.comparison_eq request] at rightLater
  exact ((prepared.attempts request).observation.close leftLater rightLater).le

/-- The original canonical carrier samples meet the same retained comparison's geometric tolerance. -/
theorem ScheduledComparison.samples_close {left right : CoherentNamed} {scale : Rational}
    (prepared : ScheduledComparison left right scale) (request : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (((RefinementProgram.ofCoherentNamed left).model (prepared.schedule.targetIndex request)).integralSample -
        ((RefinementProgram.ofCoherentNamed right).model (prepared.schedule.comparisonIndex request)).integralSample) ≤
      Basic.quarterRadius scale request :=
  prepared.samples_close_later request _ _ (Nat.le_refl _) (Nat.le_refl _)

namespace ScheduledComparison

set_option genInjectivity false in
/-- Two actual original comparison attempts with one computed pair of shared indices.

Both original prepared owners and their returned selections remain retained.
The shared indices advance each stored tail observation. A consumer can
evaluate the request once and read both rows from this same bundle.
-/
structure JoinedSelection {leftZero rightZero leftOne rightOne : CoherentNamed} {scale : Rational}
    (first : ScheduledComparison leftZero rightZero scale)
    (second : ScheduledComparison leftOne rightOne scale) (request : Nat) where
  /-- The original first prepared comparison owner. -/
  firstOwner : ScheduledComparison leftZero rightZero scale
  /-- The retained first owner is the original input. -/
  firstOwner_eq : firstOwner = first
  /-- The original second prepared comparison owner. -/
  secondOwner : ScheduledComparison leftOne rightOne scale
  /-- The retained second owner is the original input. -/
  secondOwner_eq : secondOwner = second
  /-- The actual first comparison selection computed for this request. -/
  firstAttempt : Selection leftZero rightZero scale request
  /-- The first attempt belongs to the original prepared procedure and request. -/
  firstAttempt_eq : firstAttempt = first.attempts request
  /-- The actual second comparison selection computed for the same request. -/
  secondAttempt : Selection leftOne rightOne scale request
  /-- The second attempt belongs to the original prepared procedure and request. -/
  secondAttempt_eq : secondAttempt = second.attempts request
  /-- The cached maximum of the two actual original first-side indices. -/
  targetIndex : Nat
  /-- The shared first-side index consumes both retained actual attempts. -/
  targetIndex_eq : targetIndex = max firstAttempt.observation.leftIndex secondAttempt.observation.leftIndex
  /-- The cached maximum of the two actual original second-side indices. -/
  comparisonIndex : Nat
  /-- The shared second-side index consumes those same original attempts. -/
  comparisonIndex_eq : comparisonIndex = max firstAttempt.observation.rightIndex secondAttempt.observation.rightIndex

constructive_injectivity JoinedSelection

namespace JoinedSelection

variable {leftZero rightZero leftOne rightOne : CoherentNamed} {scale : Rational}
    {first : ScheduledComparison leftZero rightZero scale} {second : ScheduledComparison leftOne rightOne scale}
    {request : Nat}

/-- Compute each original comparison attempt once and retain both shared index maxima.

Independent calls to this constructor are independent queries. Reading the
two selections from one returned bundle reuses its actual retained attempts.
-/
@[expose] def build (first : ScheduledComparison leftZero rightZero scale)
    (second : ScheduledComparison leftOne rightOne scale) (request : Nat) : JoinedSelection first second request :=
  let firstAttempt := first.attempts request
  let secondAttempt := second.attempts request
  let targetIndex := max firstAttempt.observation.leftIndex secondAttempt.observation.leftIndex
  let comparisonIndex := max firstAttempt.observation.rightIndex secondAttempt.observation.rightIndex
  ⟨first, rfl, second, rfl, firstAttempt, rfl, secondAttempt, rfl, targetIndex, rfl, comparisonIndex, rfl⟩

/-- The shared target advances the first retained original attempt. -/
theorem first_target_le (joined : JoinedSelection first second request) :
    joined.firstAttempt.observation.leftIndex ≤ joined.targetIndex := by
  rewrite [joined.targetIndex_eq]
  exact Purelib.Data.Nat.Order.le_max_left _ _

/-- The shared target advances the second retained original attempt. -/
theorem second_target_le (joined : JoinedSelection first second request) :
    joined.secondAttempt.observation.leftIndex ≤ joined.targetIndex := by
  rewrite [joined.targetIndex_eq]
  exact Purelib.Data.Nat.Order.le_max_right _ _

/-- The shared comparison index advances the first retained original attempt. -/
theorem first_comparison_le (joined : JoinedSelection first second request) :
    joined.firstAttempt.observation.rightIndex ≤ joined.comparisonIndex := by
  rewrite [joined.comparisonIndex_eq]
  exact Purelib.Data.Nat.Order.le_max_left _ _

/-- The shared comparison index advances the second retained original attempt. -/
theorem second_comparison_le (joined : JoinedSelection first second request) :
    joined.secondAttempt.observation.rightIndex ≤ joined.comparisonIndex := by
  rewrite [joined.comparisonIndex_eq]
  exact Purelib.Data.Nat.Order.le_max_right _ _

/-- Advance the first original tail observation to the cached shared indices.

The original request starts and floors are unchanged. Its stored tail
certificate proves every later reading at the returned shared indices;
the original comparison procedure is not executed by this operation.
-/
@[expose] def firstSelection (joined : JoinedSelection first second request) :
    Selection leftZero rightZero scale request where
  leftStart := joined.firstAttempt.leftStart
  rightStart := joined.firstAttempt.rightStart
  left_floor := joined.firstAttempt.left_floor
  right_floor := joined.firstAttempt.right_floor
  observation :=
    { leftIndex := joined.targetIndex
      rightIndex := joined.comparisonIndex
      left_ge := joined.firstAttempt.observation.left_ge.trans joined.first_target_le
      right_ge := joined.firstAttempt.observation.right_ge.trans joined.first_comparison_le
      close := fun leftLater rightLater => joined.firstAttempt.observation.close
        (joined.first_target_le.trans leftLater) (joined.first_comparison_le.trans rightLater) }

/-- Advance the second original tail observation to those same cached shared indices.

The actual original second attempt and its starts remain retained. This
view consumes its original tail certificate, reusing the same computed
joint indices without another comparison query.
-/
@[expose] def secondSelection (joined : JoinedSelection first second request) :
    Selection leftOne rightOne scale request where
  leftStart := joined.secondAttempt.leftStart
  rightStart := joined.secondAttempt.rightStart
  left_floor := joined.secondAttempt.left_floor
  right_floor := joined.secondAttempt.right_floor
  observation :=
    { leftIndex := joined.targetIndex
      rightIndex := joined.comparisonIndex
      left_ge := joined.secondAttempt.observation.left_ge.trans joined.second_target_le
      right_ge := joined.secondAttempt.observation.right_ge.trans joined.second_comparison_le
      close := fun leftLater rightLater => joined.secondAttempt.observation.close
        (joined.second_target_le.trans leftLater) (joined.second_comparison_le.trans rightLater) }

/-- The retained shared target is the target of the original joined schedule. -/
theorem target_readback (joined : JoinedSelection first second request) :
    joined.targetIndex = (first.schedule.join second.schedule).targetIndex request := by
  have firstReadback := congrArg (fun retained => retained.observation.leftIndex) joined.firstAttempt_eq
  have secondReadback := congrArg (fun retained => retained.observation.leftIndex) joined.secondAttempt_eq
  rewrite [joined.targetIndex_eq, firstReadback, secondReadback, ← first.target_eq request, ← second.target_eq request]
  rfl

/-- The retained shared comparison index is the comparison index of the original joined schedule. -/
theorem comparison_readback (joined : JoinedSelection first second request) :
    joined.comparisonIndex = (first.schedule.join second.schedule).comparisonIndex request := by
  have firstReadback := congrArg (fun retained => retained.observation.rightIndex) joined.firstAttempt_eq
  have secondReadback := congrArg (fun retained => retained.observation.rightIndex) joined.secondAttempt_eq
  rewrite [joined.comparisonIndex_eq, firstReadback, secondReadback,
    ← first.comparison_eq request, ← second.comparison_eq request]
  rfl

end JoinedSelection

end ScheduledComparison

/-- Compare two original names by consuming one retained finite selection per requested tolerance.

The positive geometric scale selects a request above both original starts.
One let-bound returned selection supplies both comparison indices and its
actual tail certificate. Factories can return shared-index views of a
retained joint bundle; this constructor never reads two schedule projections.
-/
@[expose] def namedEquivalent_of_selections (left right : CoherentNamed) (scale : Rational) (positive : 0 < scale)
    (select : (request : Nat) → Selection left right scale request) :
    Equivalence.NamedEquivalent left.name right.name where
  compare := fun leftStart rightStart target targetPositive =>
    let request := Search.firstQuarterBelow scale (max leftStart rightStart) target
    let retained := select request
    have requestFloor := Search.firstQuarterBelow_ge scale (max leftStart rightStart) target
    have targetSmall := Search.firstQuarterBelow_accurate scale positive.le
      (max leftStart rightStart) target targetPositive
    { leftIndex := retained.observation.leftIndex
      rightIndex := retained.observation.rightIndex
      left_ge := (Purelib.Data.Nat.Order.le_max_left leftStart rightStart).trans
        (requestFloor.trans (retained.left_floor.trans retained.observation.left_ge))
      right_ge := (Purelib.Data.Nat.Order.le_max_right leftStart rightStart).trans
        (requestFloor.trans (retained.right_floor.trans retained.observation.right_ge))
      close := fun leftLater rightLater => (retained.observation.close leftLater rightLater).trans targetSmall }

end Purelib.Integration.Program.Comparison.Scheduled

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Integration.Program.Comparison.Scheduled

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Program.Comparison in
/-- Lift retained common-schedule carrier sample bounds to equivalence of the two original coherent names.

Each original name remains linked to its own exact carrier output, and the bridge scale is applied at the same retained
requests. -/
def namedEquivalent_of_scheduled_samples
    (left right : Name.Coherent.CoherentNamed) (schedule : Approximation.Schedule.Common.CommonSchedule)
    (bridgeScale : Fraction.Rational) (bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall request,
      Norm.Basic.normSq
          (((RefinementProgram.ofCoherentNamed left).model
              (schedule.targetIndex request)).integralSample -
            ((RefinementProgram.ofCoherentNamed right).model
              (schedule.comparisonIndex request)).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale request) :
    Equivalence.NamedEquivalent left.name right.name := by
  have leftCarrier : Equivalence.NamedEquivalent left.name
      (RefinementProgram.ofCoherentNamed left).output.name :=
    ofCoherentNamed_output_equivalent left
  have carriers : Equivalence.NamedEquivalent (RefinementProgram.ofCoherentNamed
    left).output.name
      (RefinementProgram.ofCoherentNamed right).output.name :=
    scheduledProgram_output_equivalent
      (RefinementProgram.ofCoherentNamed
        left) (RefinementProgram.ofCoherentNamed right) schedule bridgeScale
      bridgeScale_nonnegative samples
  have rightCarrier : Equivalence.NamedEquivalent right.name
      (RefinementProgram.ofCoherentNamed right).output.name :=
    ofCoherentNamed_output_equivalent right
  exact Equivalence.NamedEquivalent.trans leftCarrier
    (Equivalence.NamedEquivalent.trans carriers
      (Equivalence.NamedEquivalent.symm rightCarrier))

end Purelib.Integration.Program.Comparison.Scheduled

end
