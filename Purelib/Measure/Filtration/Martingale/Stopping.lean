module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Partition.PredictableStake
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
public import Purelib.Measure.Filtration.Martingale.Predictable
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Filtration.Martingale.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

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

/-- Require each retained predictable stake to be zero or one and no larger than the preceding active stake on every
original atom.

The recursive condition follows the exact martingale chain and certifies that a stopped strategy cannot resume at a
later step. -/
@[expose]
def IsStoppingStrategy {α : Type} {distribution : Measure.Distribution α} :
    {finest : Measure.PositiveEventPartition distribution} →
    {filtration : Measure.Filtration distribution finest} →
    {terminalValue : α → Fraction.Rational} →
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → Prop
  | _, _, _, .base partition value, _strategy => True
  | _, _, _, .extend past fine refinement fineValue _step, strategy =>
      past.IsStoppingStrategy strategy.1 ∧
        ∀ atom, atom ∈ distribution.atoms →
          (strategy.2.value atom.item = 0 ∨
            strategy.2.value atom.item = 1) ∧
          strategy.2.value atom.item ≤
            past.lastActiveStake strategy.1 atom.item

/-- The strategy assigning zero to every retained step is a stopping strategy. -/
theorem isStoppingStrategy_stopImmediatelyStrategy
    {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    martingale.IsStoppingStrategy martingale.stopImmediatelyStrategy := by
  induction martingale with
  | base partition value => trivial
  | extend past fine refinement fineValue step inductionHypothesis =>
      refine ⟨inductionHypothesis, ?_⟩
      intro atom atomMember
      constructor
      · exact Or.inl rfl
      · exact past.lastActiveStake_stopImmediatelyStrategy_nonnegative atom.item

/-- The strategy assigning one to every retained step is a stopping strategy. -/
theorem isStoppingStrategy_continueStrategy
    {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    martingale.IsStoppingStrategy martingale.continueStrategy := by
  induction martingale with
  | base partition value => trivial
  | extend past fine refinement fineValue step inductionHypothesis =>
      refine ⟨inductionHypothesis, ?_⟩
      intro atom atomMember
      constructor
      · exact Or.inr rfl
      · change (1 : Fraction.Rational) ≤
          past.lastActiveStake past.continueStrategy atom.item
        rw [past.lastActiveStake_continueStrategy_eq_one]

set_option genInjectivity false in
/-- Retain an exact predictable strategy with its occurrence-wise stopping certificate.

The certificate refers to the same finite martingale and the exact retained stakes used to compute terminal wealth. -/
structure StoppingStrategy {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) where
  /-- The exact predictable stakes retained along the original martingale chain. -/ strategy :
    martingale.PredictableStrategy
  /-- Those exact retained stakes satisfy the stopping condition on every original atom. -/ valid :
    martingale.IsStoppingStrategy strategy

constructive_injectivity StoppingStrategy

/-- Construct the stopping strategy with zero stake at every retained step. -/
@[expose]
def stopImmediately {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) : StoppingStrategy martingale where
  strategy := martingale.stopImmediatelyStrategy
  valid := martingale.isStoppingStrategy_stopImmediatelyStrategy

/-- Construct the stopping strategy with unit stake at every retained step. -/
@[expose]
def continueToEnd {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) : StoppingStrategy martingale where
  strategy := martingale.continueStrategy
  valid := martingale.isStoppingStrategy_continueStrategy

namespace StoppingStrategy

/-- Read terminal wealth from the exact predictable strategy retained by the stopping certificate. -/
@[expose]
def stoppedValue {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    {martingale : Filtration.Martingale distribution filtration
      terminalValue} (stopping : StoppingStrategy martingale) :
    α → Fraction.Rational :=
  martingale.terminalWealth stopping.strategy

/-- The strategy stopping immediately has zero terminal gain at every item. -/
private theorem terminalGain_stopImmediatelyStrategy_eq_zero {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.terminalGain martingale.stopImmediatelyStrategy item = 0 := by
  induction martingale with
  | base partition value =>
    rfl
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      simp only [terminalGain, stopImmediatelyStrategy,
        PositiveEventPartition.PredictableStake.constant, mul_zero, add_zero]
      exact inductionHypothesis

/-- Stopping immediately returns the exact original initial observable pointwise. -/
theorem stoppedValue_stopImmediately {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    (martingale.stopImmediately).stoppedValue item =
      martingale.initialValue item := by
  unfold Filtration.Martingale.StoppingStrategy.stoppedValue terminalWealth stopImmediately
  rw [terminalGain_stopImmediatelyStrategy_eq_zero martingale item]
  ring1

/-- Continuing through every retained step gives terminal gain equal to terminal value minus initial value. -/
private theorem terminalGain_continueStrategy_eq_sub_initial
    {α : Type} {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.terminalGain martingale.continueStrategy item =
      terminalValue item - martingale.initialValue item := by
  induction martingale with
  | base partition value =>
      simp only [terminalGain, initialValue]
      ring1
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      simp only [terminalGain, continueStrategy, PositiveEventPartition.PredictableStake.constant,
        mul_one, lastValue, initialValue]
      rw [inductionHypothesis]
      ring1

/-- Continuing to the end returns the exact terminal observable pointwise. -/
theorem stoppedValue_continueToEnd {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) (item : α) :
    (martingale.continueToEnd).stoppedValue item = terminalValue item := by
  unfold Filtration.Martingale.StoppingStrategy.stoppedValue terminalWealth continueToEnd
  rw [terminalGain_continueStrategy_eq_sub_initial martingale item]
  ring1

/-- The retained stopped observable has expectation equal to the original initial observable's expectation. -/
theorem expectation_stoppedValue_eq_initial {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    {filtration : Measure.Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    {martingale : Filtration.Martingale distribution filtration
      terminalValue} (stopping : StoppingStrategy martingale) :
    distribution.expectation stopping.stoppedValue =
      distribution.expectation martingale.initialValue :=
  martingale.expectation_terminalWealth_eq_initial stopping.strategy

end StoppingStrategy

end Filtration.Martingale

end Purelib.Measure

end
