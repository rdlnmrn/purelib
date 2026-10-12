module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Measure.Event.RationalDistance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Finite convergence-mode certificates

Instead of asserting convergence of a sequence, this module records one
finite accuracy claim: at a positive rational tolerance, the probability of
a larger error is bounded by an explicit rational failure budget.  L1 error,
almost-everywhere equality, and exceptional-event control all produce such
certificates.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a positive separation threshold and nonnegative bound for its exact exceedance probability.

The threshold event compares the same two observables under the original finite distribution; the certificate binds that
reading to the retained failure allowance. -/
structure InMeasureBudget {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) where
  /-- The exact rational separation threshold defining the exceedance event. -/ threshold : Fraction.Rational
  /-- The retained threshold is strictly positive. -/ threshold_positive : 0 < threshold
  /-- The retained rational allowance for exceedance probability. -/ failure : Fraction.Rational
  /-- The retained probability allowance is nonnegative. -/ failure_nonnegative : 0 ≤ failure
  /-- The original distribution's exact threshold-event probability is bounded by the retained allowance. -/
    probability_le :
    distribution.probability (separationAtLeast threshold left right) ≤
      failure

constructive_injectivity InMeasureBudget

namespace InMeasureBudget

open Purelib.Data.Rat
/-- Build an exceedance budget from expected separation divided by the supplied positive threshold. -/
def ofL1 {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold) : InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := distribution.l1Distance left right / threshold
  failure_nonnegative := Fraction.Order.Field.div_nonneg_direct
    (distribution.l1Distance_nonneg left right) positive.le
  probability_le :=
    distribution.probability_separationAtLeast_le_l1
      threshold positive left right

/-- Reverse the two observables while preserving the exact threshold and failure allowance. -/
def symm {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : InMeasureBudget distribution left right) :
    InMeasureBudget distribution right left where
  threshold := budget.threshold
  threshold_positive := budget.threshold_positive
  failure := budget.failure
  failure_nonnegative := budget.failure_nonnegative
  probability_le := by
    calc
      distribution.probability
            (separationAtLeast budget.threshold right left) =
          distribution.probability
            (separationAtLeast budget.threshold left right) :=
        distribution.probability_congr _ _ (fun item => by
          unfold separationAtLeast
          rw [Distance.rationalSeparation_symm])
      _ ≤ budget.failure := budget.probability_le

/-- A retained failure allowance below a tolerance makes the corresponding exceedance probability strictly smaller than
that tolerance. -/
theorem accurate {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : InMeasureBudget distribution left right)
    (epsilon : Fraction.Rational) (small : budget.failure < epsilon) :
    distribution.probability
        (separationAtLeast budget.threshold left right) < epsilon :=
  budget.probability_le.trans_lt small

end InMeasureBudget

open Purelib.Data.Rat in
/-- Observables equal at nonzero-weight occurrences have zero probability of separation above any positive threshold. -/
theorem probability_separationAtLeast_eq_zero_of_equalAlmostEverywhere
    {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational)
    (equal : distribution.EqualAlmostEverywhere left right)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
    distribution.probability (separationAtLeast threshold left right) = 0 := by
  calc
    distribution.probability (separationAtLeast threshold left right) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      rcases equal atom member with zero | same
      · exact Or.inl zero
      · apply Or.inr
        change decide (threshold ≤
          Distance.rationalSeparation (left atom.item) (right atom.item)) = false
        apply decide_eq_false_iff_not.mpr
        intro thresholdLe
        have separationZero :
            Distance.rationalSeparation (left atom.item) (right atom.item) = 0 :=
          (Distance.rationalSeparation_eq_zero_iff _ _).mpr same
        rw [separationZero] at thresholdLe
        exact (not_le_of_gt positive) thresholdLe
    _ = 0 := distribution.probability_false

open Purelib.Data.Rat
/-- Build a zero-failure budget at any positive threshold from equality at all nonzero-weight occurrences. -/
def InMeasureBudget.ofEqualAlmostEverywhere {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (equal : distribution.EqualAlmostEverywhere left right)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
    InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := 0
  failure_nonnegative := le_rfl
  probability_le := by
    rw [distribution.probability_separationAtLeast_eq_zero_of_equalAlmostEverywhere
      left right equal threshold positive]

/-- Use the exact exceptional-event probability as failure allowance when all retained occurrences outside it have
separation below the supplied threshold. -/
def InMeasureBudget.ofExceptionalEvent {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (exceptional : α → Bool)
    (outside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = false →
        Distance.rationalSeparation (left atom.item) (right atom.item) < threshold) :
    InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := distribution.probability exceptional
  failure_nonnegative := distribution.probability_nonneg exceptional
  probability_le := by
    apply eventWeight_mono
    intro atom member selected
    cases exceptionalSelected : exceptional atom.item
    · have thresholdLe : threshold ≤
          Distance.rationalSeparation (left atom.item) (right atom.item) :=
        of_decide_eq_true selected
      exact ((outside atom member exceptionalSelected).2 thresholdLe).elim
    · rfl

end Distribution

end Purelib.Measure
