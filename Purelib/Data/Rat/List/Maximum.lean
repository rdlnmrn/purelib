module

public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Nonnegative maximum of a displayed rational list

A right fold of the owned rational maximum starts at zero. The resulting
nonnegative payment bounds every original entry, including the empty list.
-/

public section

namespace Purelib.Data.Rat.List.Maximum

open Purelib.Data.Rat

/-- Compute the maximum of the displayed rational entries with an initial floor of zero. -/
@[expose] def nonnegativeMaximum (values : List Fraction.Rational) : Fraction.Rational :=
  values.foldr max 0

/-- The displayed maximum retains a nonnegative floor even when the list is empty. -/
theorem nonnegativeMaximum_nonneg (values : List Fraction.Rational) :
    0 ≤ nonnegativeMaximum values := by
  induction values with
  | nil => exact Fraction.Order.Basic.le_refl _
  | cons head tail inductionHypothesis =>
      exact Fraction.Order.Basic.le_trans _ _ _ inductionHypothesis
        (Fraction.Order.Basic.le_max_right _ _)

/-- Every original list occurrence is bounded by the retained nonnegative maximum. -/
theorem le_nonnegativeMaximum_of_mem {values : List Fraction.Rational} {value : Fraction.Rational}
    (member : value ∈ values) : value ≤ nonnegativeMaximum values := by
  induction values with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      cases member with
      | head => exact Fraction.Order.Basic.le_max_left _ _
      | tail _ tailMember =>
          exact Fraction.Order.Basic.le_trans _ _ _ (inductionHypothesis tailMember)
            (Fraction.Order.Basic.le_max_right _ _)

/-- A nonnegative common upper bound for all displayed entries bounds their retained maximum. -/
theorem nonnegativeMaximum_le {upper : Fraction.Rational} (values : List Fraction.Rational)
    (nonnegative : 0 ≤ upper) (bounded : ∀ value ∈ values, value ≤ upper) :
    nonnegativeMaximum values ≤ upper := by
  induction values with
  | nil => exact nonnegative
  | cons head tail inductionHypothesis =>
      exact Fraction.Order.Basic.max_le (bounded head (List.Mem.head _))
        (inductionHypothesis fun value member => bounded value (List.Mem.tail _ member))

end Purelib.Data.Rat.List.Maximum
