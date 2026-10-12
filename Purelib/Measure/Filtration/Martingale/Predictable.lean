module
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Distribution.Partition.PredictableStake
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Distribution.Partition.Projection
import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.Filtration.Martingale.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Data.Rat.Fraction.Arithmetic

section
public section

/-!
# Predictable transforms and finite optional sampling

A predictable strategy attaches one rational stake to each displayed
martingale step.  The stake is explicitly cellwise on the preceding positive
partition.  Its gain is therefore a finite sum of martingale differences
multiplied by preceding-stage observables, so exact orthogonality makes the
expected total gain zero.

Zero-or-one stakes which decrease pointwise form an explicit finite stopping
strategy.  Its stopped value is the initial value plus the active increments,
and the same finite calculation gives optional sampling.  There is no
unbounded stopping time, convergence theorem, or integrability side condition.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace Filtration.Martingale

/-- Retain one coarse-partition predictable stake for each step of the exact finite martingale.

The recursive product follows the original chain; its initial stage has no stake and each extension retains the earlier
strategy and the next stake. -/
@[expose]
def PredictableStrategy {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → Type
  | _, _, _, .base partition value => Unit
  | _, _, _, .extend past fine refinement fineValue _step =>
      PredictableStrategy past × PositiveEventPartition.PredictableStake past.currentPartition

/-- Assign zero stake to every retained martingale step. -/
@[expose]
def stopImmediatelyStrategy {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy
  | _, _, _, .base partition value => ()
  | _, _, _, .extend past fine refinement fineValue _step =>
      (past.stopImmediatelyStrategy,
        PositiveEventPartition.PredictableStake.constant past.currentPartition 0)

/-- Assign unit stake to every retained martingale step. -/
@[expose]
def continueStrategy {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy
  | _, _, _, .base partition value => ()
  | _, _, _, .extend past fine refinement fineValue _step =>
      (past.continueStrategy,
        PositiveEventPartition.PredictableStake.constant past.currentPartition 1)

/-- Sum the retained step increments multiplied by their exact predictable stakes.

The recursive gain uses the original fine and coarse observables and the corresponding stake from the same retained
strategy. -/
@[expose]
def terminalGain {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → α → Fraction.Rational
  | _, _, _, .base partition value, _strategy => fun _ => 0
  | _, _, _, .extend past fine refinement fineValue _step, strategy =>
      fun item =>
        past.terminalGain strategy.1 item +
          (fineValue item - past.lastValue item) * strategy.2.value item

/-- Every retained predictable strategy has terminal gain expectation zero. -/
theorem expectation_terminalGain_eq_zero {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    ∀ strategy : martingale.PredictableStrategy,
      distribution.expectation (martingale.terminalGain strategy) = 0 := by
  induction martingale with
  | base partition value =>
      intro strategy
      simpa only [-eq_self, -iff_self, terminalGain] using distribution.expectation_constant 0
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      intro strategy
      rcases strategy with ⟨pastStrategy, stake⟩
      rw [terminalGain, distribution.expectation_add,
        inductionHypothesis pastStrategy]
      change 0 + distribution.expectation (fun item =>
        (fineValue item - coarseValue item) * stake.value item) = 0
      rw [coarse.expectation_stepDifference_mul_cellwise_eq_zero
        fineValue coarseValue stake.value step stake.cellwise, zero_add]

/-- Add the retained predictable terminal gain to the exact original initial observable. -/
@[expose]
def terminalWealth {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (strategy : martingale.PredictableStrategy) :
    α → Fraction.Rational :=
  fun item => martingale.initialValue item +
    martingale.terminalGain strategy item

/-- Predictable terminal wealth has expectation equal to the original initial observable's expectation. -/
theorem expectation_terminalWealth_eq_initial {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (strategy : martingale.PredictableStrategy) :
    distribution.expectation (martingale.terminalWealth strategy) =
      distribution.expectation martingale.initialValue := by
  unfold terminalWealth
  rw [distribution.expectation_add,
    martingale.expectation_terminalGain_eq_zero strategy, add_zero]

/-- Read the final retained stake, returning one at a chain with no steps. -/
@[expose]
def lastActiveStake {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → α → Fraction.Rational
  | _, _, _, .base partition value, _strategy => fun _ => 1
  | _, _, _, .extend _past fine refinement fineValue _step, strategy =>
      strategy.2.value

/-- The stop-immediately strategy's final active stake is nonnegative, including the initial-stage convention. -/
theorem lastActiveStake_stopImmediatelyStrategy_nonnegative
    {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    0 ≤ martingale.lastActiveStake martingale.stopImmediatelyStrategy item := by
  cases martingale <;>
    simp only [-eq_self, -iff_self, lastActiveStake, stopImmediatelyStrategy,
      PositiveEventPartition.PredictableStake.constant] <;> decide

/-- The continue strategy's final active stake is one at every retained chain length. -/
theorem lastActiveStake_continueStrategy_eq_one
    {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.lastActiveStake martingale.continueStrategy item = 1 := by
  cases martingale <;> rfl

end Filtration.Martingale

end Purelib.Measure

end
