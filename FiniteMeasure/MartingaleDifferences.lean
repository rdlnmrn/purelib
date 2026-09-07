import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Filtration
import FiniteMeasure.ConditionalProjection
import FiniteMeasure.Moments

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

namespace FiniteMeasure

namespace Distribution

/-- Powered L2 distance from zero is the exact rational second moment. -/
theorem poweredL2Distance_zero {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.poweredL2Distance value (fun _ => 0) =
      distribution.poweredL2 value := by
  unfold poweredL2Distance poweredL2 FiniteContent.poweredL2Distance
    FiniteContent.poweredL2
  exact distribution.toFiniteContent.integral_congr _ _
    (fun item => by ring1)

/-- The powered L2 quantity is the ordinary finite rational second moment. -/
theorem poweredL2_eq_expectation_sq {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL2 value =
      distribution.expectation (fun item => value item ^ 2) := rfl

end Distribution

namespace PositiveEventPartition

/-- The zero observable is cellwise on every displayed partition. -/
def zeroCellwise {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    CellwiseObservable partition (fun _ : α => (0 : Coordinate)) where
  cellValue := fun _ => 0
  agrees := by
    intro event eventMember atom atomMember selected
    rfl

/-- A martingale step difference is orthogonal to every observable displayed
cellwise on the preceding partition. -/
theorem expectation_stepDifference_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue cellwise : α → Coordinate)
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

/-- One martingale step splits its exact second moment into the preceding
second moment and the powered-L2 size of its difference. -/
theorem poweredL2_step_eq
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue : α → Coordinate)
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
    change distribution.toFiniteContent.poweredL2
        (coarse.conditionalExpectation fineValue) =
      distribution.toFiniteContent.poweredL2 coarseValue
    exact distribution.toFiniteContent.poweredL2_congr _ _ step
  have stepDistance :
      distribution.poweredL2Distance fineValue
          (coarse.conditionalExpectation fineValue) =
        distribution.poweredL2Distance fineValue coarseValue := by
    unfold Distribution.poweredL2Distance
      FiniteContent.poweredL2Distance
    exact distribution.toFiniteContent.poweredL2_congr _ _ (fun item => by
      rw [step item])
  rw [distribution.poweredL2Distance_zero,
    distribution.poweredL2Distance_zero] at pythagorean
  rw [projectedL2, stepDistance] at pythagorean
  rw [pythagorean]
  ring1

/-- Exact variance growth across one displayed martingale step. -/
theorem variance_step_eq
    {α : Type} {distribution : Distribution α}
    (coarse : PositiveEventPartition distribution)
    (fineValue coarseValue : α → Coordinate)
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

namespace FiniteFiltration.Martingale

/-- Last value of a displayed martingale, exposed as data for recursive
constructions over its preceding stages. -/
def lastValue {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (_martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) : α → Coordinate :=
  terminalValue

/-- The finite rational sum of the powered-L2 sizes of all displayed
martingale differences. -/
def expectedQuadraticVariation {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate} :
    FiniteFiltration.Martingale distribution filtration terminalValue →
      Coordinate
  | .base partition value => 0
  | .extend past fine refinement fineValue step =>
      past.expectedQuadraticVariation +
        distribution.poweredL2Distance fineValue
          past.lastValue

/-- Expected quadratic variation is nonnegative, proved by finite induction
over the displayed martingale steps. -/
theorem expectedQuadraticVariation_nonnegative {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) :
    0 ≤ martingale.expectedQuadraticVariation := by
  induction martingale with
  | base partition value => exact le_rfl
  | extend past fine refinement fineValue step inductionHypothesis =>
      exact add_nonneg inductionHypothesis
        (distribution.toFiniteContent.poweredL2Distance_nonnegative
          fineValue past.lastValue)

/-- Exact finite martingale second-moment identity: terminal second moment is
initial second moment plus the finite sum of squared differences. -/
theorem poweredL2_terminal_eq_initial_add_expectedQuadraticVariation
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) :
    distribution.poweredL2 terminalValue =
      distribution.poweredL2 martingale.initialValue +
        martingale.expectedQuadraticVariation := by
  induction martingale with
  | base partition value =>
      simp only [initialValue, expectedQuadraticVariation, add_zero]
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      rw [coarse.poweredL2_step_eq fineValue coarseValue step,
        inductionHypothesis]
      simp only [initialValue, expectedQuadraticVariation, lastValue]
      ring1

/-- Exact finite martingale variance identity.  Equal means cancel, leaving
precisely the expected quadratic variation. -/
theorem variance_terminal_eq_initial_add_expectedQuadraticVariation
    {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
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

/-- Variance cannot decrease along a displayed finite martingale. -/
theorem variance_initial_le_terminal {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : FiniteFiltration.Martingale distribution filtration
      terminalValue) :
    distribution.variance martingale.initialValue ≤
      distribution.variance terminalValue := by
  rw [martingale.variance_terminal_eq_initial_add_expectedQuadraticVariation]
  exact le_add_of_nonneg_right
    martingale.expectedQuadraticVariation_nonnegative

end FiniteFiltration.Martingale

end FiniteMeasure
