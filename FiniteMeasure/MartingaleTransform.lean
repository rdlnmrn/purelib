import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.MartingaleDifferences

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

namespace FiniteMeasure

namespace FiniteFiltration.Martingale

/-- The finest partition indexing a displayed martingale. -/
def currentPartition {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (_martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) : PositiveEventPartition distribution :=
  finest

/-- One rational stake explicitly measurable at a displayed partition. -/
structure PredictableStake {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) where
  value : α → Coordinate
  cellwise : PositiveEventPartition.CellwiseObservable partition value

namespace PredictableStake

/-- A constant rational stake is predictable at every displayed partition. -/
def constant {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (constant : Coordinate) : PredictableStake partition where
  value := fun _ => constant
  cellwise :=
    { cellValue := fun _ => constant
      agrees := by
        intro event eventMember atom atomMember selected
        rfl }

end PredictableStake

/-- All stakes for a displayed finite martingale.  At an extension the new
stake is measurable at the preceding stage. -/
def PredictableStrategy {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → Type
  | _, _, _, .base partition value => Unit
  | _, _, _, .extend past fine refinement fineValue _step =>
      PredictableStrategy past × PredictableStake past.currentPartition

/-- Strategy which takes no displayed increment. -/
def stopImmediatelyStrategy {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy
  | _, _, _, .base partition value => ()
  | _, _, _, .extend past fine refinement fineValue _step =>
      (past.stopImmediatelyStrategy,
        PredictableStake.constant past.currentPartition 0)

/-- Strategy which takes every displayed increment through the final stage. -/
def continueStrategy {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy
  | _, _, _, .base partition value => ()
  | _, _, _, .extend past fine refinement fineValue _step =>
      (past.continueStrategy,
        PredictableStake.constant past.currentPartition 1)

/-- Pointwise terminal gain of a predictable strategy. -/
def terminalGain {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → α → Coordinate
  | _, _, _, .base partition value, _strategy => fun _ => 0
  | _, _, _, .extend past fine refinement fineValue _step, strategy =>
      fun item =>
        past.terminalGain strategy.1 item +
          (fineValue item - past.lastValue item) * strategy.2.value item

/-- Every predictable transform of a displayed finite martingale has exact
zero expected gain. -/
theorem expectation_terminalGain_eq_zero {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) :
    ∀ strategy : martingale.PredictableStrategy,
      distribution.expectation (martingale.terminalGain strategy) = 0 := by
  induction martingale with
  | base partition value =>
      intro strategy
      simpa only [terminalGain] using distribution.expectation_constant 0
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

/-- Terminal wealth is initial value plus the finite predictable gain. -/
def terminalWealth {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (strategy : martingale.PredictableStrategy) :
    α → Coordinate :=
  fun item => martingale.initialValue item +
    martingale.terminalGain strategy item

/-- Fair-game identity for every displayed finite predictable strategy. -/
theorem expectation_terminalWealth_eq_initial {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (strategy : martingale.PredictableStrategy) :
    distribution.expectation (martingale.terminalWealth strategy) =
      distribution.expectation martingale.initialValue := by
  unfold terminalWealth
  rw [distribution.expectation_add,
    martingale.expectation_terminalGain_eq_zero strategy, add_zero]

/-- Most recent active stake, with activity initially equal to one before any
increment is offered. -/
def lastActiveStake {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → α → Coordinate
  | _, _, _, .base partition value, _strategy => fun _ => 1
  | _, _, _, .extend _past fine refinement fineValue _step, strategy =>
      strategy.2.value

theorem lastActiveStake_stopImmediatelyStrategy_nonnegative
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    0 ≤ martingale.lastActiveStake martingale.stopImmediatelyStrategy item := by
  cases martingale <;>
    simp only [lastActiveStake, stopImmediatelyStrategy,
      PredictableStake.constant] <;> decide

theorem lastActiveStake_continueStrategy_eq_one
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.lastActiveStake martingale.continueStrategy item = 1 := by
  cases martingale <;>
    simp only [lastActiveStake, continueStrategy,
      PredictableStake.constant]

/-- Zero-or-one predictable stakes which can only decrease along each
displayed atom encode a finite stopping rule. -/
def IsStoppingStrategy {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
    {filtration : FiniteFiltration distribution finest} →
    {terminalValue : α → Coordinate} →
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) → martingale.PredictableStrategy → Prop
  | _, _, _, .base partition value, _strategy => True
  | _, _, _, .extend past fine refinement fineValue _step, strategy =>
      past.IsStoppingStrategy strategy.1 ∧
        ∀ atom, atom ∈ distribution.atoms →
          (strategy.2.value atom.item = 0 ∨
            strategy.2.value atom.item = 1) ∧
          strategy.2.value atom.item ≤
            past.lastActiveStake strategy.1 atom.item

theorem isStoppingStrategy_stopImmediatelyStrategy
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
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

theorem isStoppingStrategy_continueStrategy
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) :
    martingale.IsStoppingStrategy martingale.continueStrategy := by
  induction martingale with
  | base partition value => trivial
  | extend past fine refinement fineValue step inductionHypothesis =>
      refine ⟨inductionHypothesis, ?_⟩
      intro atom atomMember
      constructor
      · exact Or.inr rfl
      · change (1 : Coordinate) ≤
          past.lastActiveStake past.continueStrategy atom.item
        rw [past.lastActiveStake_continueStrategy_eq_one]

/-- An explicit finite stopping strategy. -/
structure StoppingStrategy {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) where
  strategy : martingale.PredictableStrategy
  valid : martingale.IsStoppingStrategy strategy

/-- Stop before taking any displayed increment. -/
def stopImmediately {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) : StoppingStrategy martingale where
  strategy := martingale.stopImmediatelyStrategy
  valid := martingale.isStoppingStrategy_stopImmediatelyStrategy

/-- Continue through every displayed increment. -/
def continueToEnd {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) : StoppingStrategy martingale where
  strategy := martingale.continueStrategy
  valid := martingale.isStoppingStrategy_continueStrategy

namespace StoppingStrategy

/-- Observable obtained by retaining precisely the increments for which the
stopping strategy remains active. -/
def stoppedValue {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    {martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue} (stopping : StoppingStrategy martingale) :
    α → Coordinate :=
  martingale.terminalWealth stopping.strategy

private theorem terminalGain_stopImmediatelyStrategy_eq_zero {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.terminalGain martingale.stopImmediatelyStrategy item = 0 := by
  induction martingale with
  | base partition value =>
    rfl
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      simp only [terminalGain, stopImmediatelyStrategy,
        PredictableStake.constant, mul_zero, add_zero]
      exact inductionHypothesis

theorem stoppedValue_stopImmediately {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    (martingale.stopImmediately).stoppedValue item =
      martingale.initialValue item := by
  unfold stoppedValue terminalWealth stopImmediately
  rw [terminalGain_stopImmediatelyStrategy_eq_zero martingale item]
  ring1

private theorem terminalGain_continueStrategy_eq_sub_initial
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    martingale.terminalGain martingale.continueStrategy item =
      terminalValue item - martingale.initialValue item := by
  induction martingale with
  | base partition value =>
      simp only [terminalGain, initialValue]
      ring1
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      simp only [terminalGain, continueStrategy, PredictableStake.constant,
        mul_one, lastValue, initialValue]
      rw [inductionHypothesis]
      ring1

theorem stoppedValue_continueToEnd {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) (item : α) :
    (martingale.continueToEnd).stoppedValue item = terminalValue item := by
  unfold stoppedValue terminalWealth continueToEnd
  rw [terminalGain_continueStrategy_eq_sub_initial martingale item]
  ring1

/-- Finite optional-sampling identity. -/
theorem expectation_stoppedValue_eq_initial {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    {martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue} (stopping : StoppingStrategy martingale) :
    distribution.expectation stopping.stoppedValue =
      distribution.expectation martingale.initialValue :=
  martingale.expectation_terminalWealth_eq_initial stopping.strategy

end StoppingStrategy

end FiniteFiltration.Martingale

end FiniteMeasure
