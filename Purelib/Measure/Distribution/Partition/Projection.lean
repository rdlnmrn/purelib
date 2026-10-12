module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Moments.Basic
public import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Partition.Expectation

section
/-!
# Conditional expectation as a finite L2 projection

A cellwise observable carries explicit rational values for the cells of a
positive finite event partition.  The conditional-expectation residual has
zero integral on each cell, hence is orthogonal to every such observable.
Expanding one rational square yields the exact Pythagorean identity and the
best powered-L2 approximation theorem.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- The original observable minus its partition conditional expectation integrates to zero on every retained partition
cell. -/
private theorem eventIntegral_residual_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event (fun item =>
      value item - partition.conditionalExpectation value item) = 0 := by
  have preserved :=
    partition.eventIntegral_conditionalExpectation value event eventMember
  unfold Distribution.eventIntegral at preserved
  unfold Distribution.eventIntegral
  calc
    distribution.expectation (fun item => Distribution.indicator event item *
          (value item - partition.conditionalExpectation value item)) =
        distribution.expectation (fun item =>
          Distribution.indicator event item * value item -
            Distribution.indicator event item *
              partition.conditionalExpectation value item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          Distribution.indicator event item * value item) -
        distribution.expectation (fun item =>
          Distribution.indicator event item *
            partition.conditionalExpectation value item) :=
      distribution.expectation_sub _ _
    _ = 0 := by
      rw [preserved]
      ring1

/-- Multiplying the projection residual by a retained cellwise observable still gives zero integral on every partition
cell. -/
private theorem eventIntegral_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Fraction.Rational)
    (represented : CellwiseObservable partition cellwise)
    (event : α → Bool) (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item) = 0 := by
  unfold Distribution.eventIntegral
  calc
    distribution.expectation (fun item =>
          Distribution.indicator event item *
            ((value item - partition.conditionalExpectation value item) *
              cellwise item)) =
        distribution.expectation (fun item =>
          represented.cellValue event *
            (Distribution.indicator event item *
              (value item - partition.conditionalExpectation value item))) := by
      apply distribution.expectation_congr_off_zero
      intro atom atomMember
      apply Or.inr
      change Distribution.indicator event atom.item *
          ((value atom.item -
              partition.conditionalExpectation value atom.item) *
            cellwise atom.item) =
        represented.cellValue event *
          (Distribution.indicator event atom.item *
            (value atom.item -
              partition.conditionalExpectation value atom.item))
      cases selected : event atom.item
      · simp only [Distribution.indicator, selected, zero_mul]
        ring1
      · rw [represented.agrees event eventMember atom atomMember selected]
        simp only [Distribution.indicator, selected, one_mul]
        ring1
    _ = represented.cellValue event *
        distribution.expectation (fun item =>
          Distribution.indicator event item *
            (value item - partition.conditionalExpectation value item)) :=
      distribution.expectation_scale _ _
    _ = represented.cellValue event *
        distribution.eventIntegral event (fun item =>
          value item - partition.conditionalExpectation value item) := rfl
    _ = 0 := by
      rw [partition.eventIntegral_residual_eq_zero value event eventMember,
        mul_zero]

/-- The finite sum of residual-times-cellwise integrals vanishes on any retained sublist of partition cells. -/
private theorem sum_eventIntegral_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Fraction.Rational)
    (represented : CellwiseObservable partition cellwise) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => distribution.eventIntegral event (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item)).sum = 0
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [partition.eventIntegral_residual_mul_cellwise_eq_zero
          value cellwise represented event
          (subset event List.mem_cons_self),
        partition.sum_eventIntegral_residual_mul_cellwise_eq_zero
          value cellwise represented remaining
          (fun candidate member =>
            subset candidate (List.mem_cons_of_mem event member)),
        zero_add]

/-- The partition projection residual is orthogonal in expectation to every retained cellwise observable. -/
theorem expectation_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Fraction.Rational)
    (represented : CellwiseObservable partition cellwise) :
    distribution.expectation (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item) = 0 := by
  calc
    distribution.expectation (fun item =>
          (value item - partition.conditionalExpectation value item) *
            cellwise item) =
        (partition.events.map fun event =>
          distribution.eventIntegral event (fun item =>
            (value item - partition.conditionalExpectation value item) *
              cellwise item)).sum :=
      (partition.toEventPartition.total_expectation _).symm
    _ = 0 :=
      partition.sum_eventIntegral_residual_mul_cellwise_eq_zero
        value cellwise represented partition.events
        (fun event member => member)

/-- Squared error to a retained cellwise competitor splits into squared projection residual plus squared projected
error. -/
theorem expectation_sq_sub_pythagorean
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Fraction.Rational)
    (represented : CellwiseObservable partition competitor) :
    distribution.expectation (fun item =>
        (value item - competitor item) ^ 2) =
      distribution.expectation (fun item =>
        (value item - partition.conditionalExpectation value item) ^ 2) +
      distribution.expectation (fun item =>
        (partition.conditionalExpectation value item - competitor item) ^ 2) := by
  let projected := partition.conditionalExpectation value
  let projectedCellwise := partition.conditionalExpectation_cellwise value
  let differenceCellwise := projectedCellwise.sub represented
  have orthogonal : distribution.expectation (fun item =>
      (value item - projected item) *
        (projected item - competitor item)) = 0 :=
    partition.expectation_residual_mul_cellwise_eq_zero value
      (fun item => projected item - competitor item) differenceCellwise
  calc
    distribution.expectation (fun item =>
          (value item - competitor item) ^ 2) =
        distribution.expectation (fun item =>
          (value item - projected item) ^ 2 +
            (projected item - competitor item) ^ 2 +
            2 * ((value item - projected item) *
              (projected item - competitor item))) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          (value item - projected item) ^ 2) +
        distribution.expectation (fun item =>
          (projected item - competitor item) ^ 2) := by
      rw [distribution.expectation_add, distribution.expectation_add,
        distribution.expectation_scale, orthogonal, mul_zero, add_zero]

/-- Squared integrated distance to a retained cellwise competitor splits through the partition conditional expectation.
-/
theorem poweredL2Distance_pythagorean
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Fraction.Rational)
    (represented : CellwiseObservable partition competitor) :
    distribution.poweredL2Distance value competitor =
      distribution.poweredL2Distance value
          (partition.conditionalExpectation value) +
        distribution.poweredL2Distance
          (partition.conditionalExpectation value) competitor := by
  unfold Distribution.poweredL2Distance Content.poweredL2Distance
    Content.poweredL2 Content.integral
  exact partition.expectation_sq_sub_pythagorean value competitor represented

/-- Partition conditional expectation minimizes squared integrated distance among retained cellwise competitors. -/
theorem poweredL2Distance_conditionalExpectation_le
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Fraction.Rational)
    (represented : CellwiseObservable partition competitor) :
    distribution.poweredL2Distance value
        (partition.conditionalExpectation value) ≤
      distribution.poweredL2Distance value competitor := by
  rw [partition.poweredL2Distance_pythagorean value competitor represented]
  exact le_add_of_nonneg_right
    (distribution.toContent.poweredL2Distance_nonnegative
      (partition.conditionalExpectation value) competitor)

end PositiveEventPartition

end Purelib.Measure

end

section
public section

/-!
# Finite martingale differences

Every step of a displayed finite martingale has a rational difference whose
conditional expectation on the preceding partition is zero.  Consequently
the difference is orthogonal to every explicitly cellwise observable.  A
finite induction then gives exact second-moment and variance growth formulas.

There is no unbounded time index, limiting process, or stopping theorem here:
the expected quadratic variation below is a finite rational sum carried by
the inductive martingale itself.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- A fine-to-coarse conditional expectation identity makes its step difference orthogonal to every retained
coarse-cellwise observable. -/
theorem expectation_stepDifference_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue cellwise : α → Fraction.Rational)
    (step : ∀ item,
      coarse.conditionalExpectation fineValue item = coarseValue item)
    (represented : CellwiseObservable coarse cellwise) :
    distribution.expectation (fun item =>
        (fineValue item - coarseValue item) * cellwise item) = 0 := by
  calc
    distribution.expectation (fun item =>
          (fineValue item - coarseValue item) * cellwise item) =
        distribution.expectation (fun item =>
          (fineValue item - coarse.conditionalExpectation fineValue item) *
            cellwise item) :=
      distribution.expectation_congr _ _ (fun item => by
        rw [step item])
    _ = 0 := coarse.expectation_residual_mul_cellwise_eq_zero
      fineValue cellwise represented

/-- A retained fine-to-coarse conditional expectation step splits fine squared expectation into coarse squared
expectation and squared step distance. -/
theorem poweredL2_step_eq
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue : α → Fraction.Rational)
    (step : ∀ item,
      coarse.conditionalExpectation fineValue item = coarseValue item) :
    distribution.poweredL2 fineValue =
      distribution.poweredL2 coarseValue +
        distribution.poweredL2Distance fineValue coarseValue := by
  have pythagorean := coarse.poweredL2Distance_pythagorean fineValue
    (fun _ => 0) coarse.zeroCellwise
  have projectedL2 :
      distribution.poweredL2 (coarse.conditionalExpectation fineValue) =
        distribution.poweredL2 coarseValue := by
    change distribution.toContent.poweredL2
        (coarse.conditionalExpectation fineValue) =
      distribution.toContent.poweredL2 coarseValue
    exact distribution.toContent.poweredL2_congr _ _ step
  have stepDistance :
      distribution.poweredL2Distance fineValue
          (coarse.conditionalExpectation fineValue) =
        distribution.poweredL2Distance fineValue coarseValue := by
    unfold Distribution.poweredL2Distance
      Content.poweredL2Distance
    exact distribution.toContent.poweredL2_congr _ _ (fun item => by
      rw [step item])
  rw [distribution.poweredL2Distance_zero,
    distribution.poweredL2Distance_zero] at pythagorean
  rw [projectedL2, stepDistance] at pythagorean
  rw [pythagorean]
  ring1

/-- A retained fine-to-coarse conditional expectation step splits fine variance into coarse variance and squared step
distance. -/
theorem variance_step_eq
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue : α → Fraction.Rational)
    (step : ∀ item,
      coarse.conditionalExpectation fineValue item = coarseValue item) :
    distribution.variance fineValue =
      distribution.variance coarseValue +
        distribution.poweredL2Distance fineValue coarseValue := by
  have meanPreserved := coarse.expectation_conditionalExpectation fineValue
  have projectedMean := distribution.expectation_congr
    (coarse.conditionalExpectation fineValue) coarseValue step
  have meanEqual : distribution.expectation fineValue =
      distribution.expectation coarseValue :=
    meanPreserved.symm.trans projectedMean
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    ← distribution.poweredL2_eq_expectation_sq,
    ← distribution.poweredL2_eq_expectation_sq,
    coarse.poweredL2_step_eq fineValue coarseValue step,
    meanEqual]
  ring1

end PositiveEventPartition

end Purelib.Measure

end

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat
namespace Distribution

/-- Partition conditional expectation preserves integration over any event with a retained cellwise indicator. -/
theorem eventIntegral_conditionalExpectation_of_indicator_cellwise
    {α : Type} (distribution : Distribution α)
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (event : α → Bool)
    (represented : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator event)) :
    distribution.eventIntegral event
        (partition.conditionalExpectation value) =
      distribution.eventIntegral event value := by
  have orthogonal := partition.expectation_residual_mul_cellwise_eq_zero
    value (Distribution.indicator event) represented
  have rearranged : distribution.expectation (fun item =>
      (value item - partition.conditionalExpectation value item) *
        Distribution.indicator event item) =
      distribution.expectation (fun item =>
        Distribution.indicator event item * value item -
          Distribution.indicator event item *
            partition.conditionalExpectation value item) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [rearranged, distribution.expectation_sub] at orthogonal
  have equality : distribution.expectation
      (fun item => Distribution.indicator event item * value item) =
      distribution.expectation (fun item => Distribution.indicator event item *
        partition.conditionalExpectation value item) := by
    calc
      _ = (distribution.expectation
          (fun item => Distribution.indicator event item * value item) -
          distribution.expectation (fun item => Distribution.indicator event item *
            partition.conditionalExpectation value item)) +
          distribution.expectation (fun item => Distribution.indicator event item *
            partition.conditionalExpectation value item) := by ring1
      _ = _ := by rw [orthogonal]; ring1
  exact equality.symm

end Distribution

namespace PositiveEventPartition

/-- Partition conditional expectation preserves the integral over its own threshold event. -/
theorem eventIntegral_conditionalExpectation_atLeast {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational) :
    distribution.eventIntegral
        (Measure.atLeastEvent threshold
          (partition.conditionalExpectation value))
        (partition.conditionalExpectation value) =
      distribution.eventIntegral
        (Measure.atLeastEvent threshold
          (partition.conditionalExpectation value)) value := by
  apply distribution.eventIntegral_conditionalExpectation_of_indicator_cellwise
  exact (partition.conditionalExpectation_cellwise value).indicatorAtLeast
    threshold

end PositiveEventPartition

end Purelib.Measure

end
