module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Partition.Projection
import Purelib.Measure.Filtration.Basic
public import Purelib.Measure.Filtration.Martingale.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Filtration.Martingale

/-- Sum the expectations of squared increments along the exact retained martingale chain.

The initial chain contributes zero; each extension adds the powered-L2 distance between its original fine and coarse
observables. -/
@[expose]
def expectedQuadraticVariation {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational} :
    Filtration.Martingale distribution filtration terminalValue →
      Fraction.Rational
  | .base partition value => 0
  | .extend past fine refinement fineValue step =>
      past.expectedQuadraticVariation +
        distribution.poweredL2Distance fineValue
          past.lastValue

/-- The expected sum of squared retained martingale increments is nonnegative. -/
theorem expectedQuadraticVariation_nonnegative {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    0 ≤ martingale.expectedQuadraticVariation := by
  induction martingale with
  | base partition value => exact le_rfl
  | extend past fine refinement fineValue step inductionHypothesis =>
      exact add_nonneg inductionHypothesis
        (distribution.toContent.poweredL2Distance_nonnegative
          fineValue past.lastValue)

/-- The terminal second moment equals the initial second moment plus the retained expected quadratic variation. -/
theorem poweredL2_terminal_eq_initial_add_expectedQuadraticVariation
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    distribution.poweredL2 terminalValue =
      distribution.poweredL2 martingale.initialValue +
        martingale.expectedQuadraticVariation := by
  induction martingale with
  | base partition value =>
      simp only [-eq_self, -iff_self, initialValue, expectedQuadraticVariation, add_zero]; try rfl
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      rw [coarse.poweredL2_step_eq fineValue coarseValue step,
        inductionHypothesis]
      simp only [-eq_self, -iff_self, initialValue, expectedQuadraticVariation, lastValue]; try rfl
      ring1

/-- The terminal variance equals the initial variance plus the retained expected quadratic variation. -/
theorem variance_terminal_eq_initial_add_expectedQuadraticVariation
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    distribution.variance terminalValue =
      distribution.variance martingale.initialValue +
        martingale.expectedQuadraticVariation := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    ← distribution.poweredL2_eq_expectation_sq,
    ← distribution.poweredL2_eq_expectation_sq,
    martingale.poweredL2_terminal_eq_initial_add_expectedQuadraticVariation,
    martingale.expectation_terminal_eq_initial]
  ring1

/-- The initial observable's variance is at most the terminal observable's variance along the retained finite
martingale. -/
theorem variance_initial_le_terminal {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Filtration.Martingale distribution filtration
      terminalValue) :
    distribution.variance martingale.initialValue ≤
      distribution.variance terminalValue := by
  rw [martingale.variance_terminal_eq_initial_add_expectedQuadraticVariation]
  exact le_add_of_nonneg_right
    martingale.expectedQuadraticVariation_nonnegative

end Filtration.Martingale

end Purelib.Measure

end
