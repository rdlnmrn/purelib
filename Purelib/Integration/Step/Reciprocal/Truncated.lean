module
public import Purelib.Integration.Step.Reciprocal.Regular
public import Purelib.Approximation.Rational.Exceptional.Modulus
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Finite truncation of the rational reciprocal step

The source is unchanged above a retained positive reciprocal tail and is zero
on that tail. Its only exceptional locations are the tail endpoint and the
finite prefix of the original reciprocal cuts above it.
-/

public section

namespace Purelib.Integration.Step.Reciprocal

open Purelib.Data.Rat
open Purelib.Approximation

/-- Replace the reciprocal step on the initial tail by zero, retaining the original rule above it. -/
@[expose] def truncated (count : Nat) (point : Fraction.Rational) : Fraction.Rational :=
  if point ≤ 1 / (count : Fraction.Rational) then 0 else value point

/-- The truncated source is the original rule at every rational point above the retained tail. -/
theorem truncated_eq_of_above (count : Nat) (point : Fraction.Rational)
    (above : 1 / (count : Fraction.Rational) < point) : truncated count point = value point := by
  unfold truncated
  rw [if_neg above.2]

/-- A constant rational reading is enclosed by any positive variation budget. -/
private theorem constant_variation (reading variation : Fraction.Rational) (positive : 0 < variation) :
    reading - variation ≤ reading ∧ reading ≤ reading + variation := by
  have negative := Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
  rw [neg_zero] at negative
  have lower := Fraction.Order.Arithmetic.add_le_add_right_direct negative reading
  have upper := Fraction.Order.Arithmetic.add_le_add_right_direct positive.le reading
  have lowerEq : -variation + reading = reading - variation := by ring1
  have upperEq : variation + reading = reading + variation := by ring1
  rw [lowerEq, Fraction.Field.zero_add] at lower
  rw [Fraction.Field.zero_add, upperEq] at upper
  exact ⟨lower, upper⟩

/-- The finite truncation has a bounded effective modulus away from its retained cuts.

The original cutoff and all reciprocal cuts above it are kept as closed
exceptions. Away from them the source is exactly constant, so any positive
mesh radius supplies the requested local variation. -/
@[expose] def truncatedModulus (count : Nat) (countBound : 2 ≤ count) :
    Rational.Exceptional.Modulus (truncated count) where
  points := 1 / (count : Fraction.Rational) :: cuts (count - 2)
  magnitude := 1
  magnitude_nonnegative := by decide
  bounded := by
    intro point _ _
    unfold truncated
    split
    · constructor <;> decide
    · have bound := value_range point
      exact ⟨(by decide : (-1 : Fraction.Rational) ≤ 0).trans bound.1, bound.2⟩
  radius := fun _ => 1
  radius_pos := fun _ _ => by decide
  variation := by
    intro variation positive first second _ ordered upper noExceptions _
    have noTail := noExceptions (1 / (count : Fraction.Rational)) List.mem_cons_self
    have noCuts : ∀ point ∈ cuts (count - 2), ¬ (first ≤ point ∧ point ≤ second) := by
      intro point member
      exact noExceptions point (List.mem_cons_of_mem _ member)
    have same : truncated count first = truncated count second := by
      by_cases firstBelow : first ≤ 1 / (count : Fraction.Rational)
      · by_cases secondBelow : second ≤ 1 / (count : Fraction.Rational)
        · unfold truncated
          rw [if_pos firstBelow, if_pos secondBelow]
        · have tailBefore := Fraction.Order.Arithmetic.lt_of_not_ge_direct secondBelow
          exact (noTail ⟨firstBelow, tailBefore.le⟩).elim
      · have firstAbove := Fraction.Order.Arithmetic.lt_of_not_ge_direct firstBelow
        have secondAbove := firstAbove.trans_le ordered
        rw [truncated_eq_of_above count first firstAbove, truncated_eq_of_above count second secondAbove]
        exact value_eq_of_no_cuts count countBound first second firstAbove ordered upper noCuts
    rw [same]
    exact constant_variation (truncated count second) variation positive

end Purelib.Integration.Step.Reciprocal

end
