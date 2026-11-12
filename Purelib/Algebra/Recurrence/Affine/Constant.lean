module

public import Purelib.Algebra.Recurrence.Affine
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Constant forcing in the original finite affine recurrence

The same original iterate supplies its scalar response. No second loop or
closed-form power implementation defines a replacement recurrence.
-/

public section

namespace Purelib.Algebra.Recurrence.Affine

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Nonnegative original initial data, coefficients and forcing keep every bounded affine iterate nonnegative. -/
theorem iterate_nonnegative (coefficient forcing : Nat → Rational) (initial : Rational) (count : Nat)
    (start : 0 ≤ initial) (coefficientNonnegative : ∀ index, index < count → 0 ≤ coefficient index)
    (forcingNonnegative : ∀ index, index < count → 0 ≤ forcing index) :
    0 ≤ iterate coefficient forcing initial count := by
  induction count with
  | zero => exact start
  | succ count prior =>
      exact (show (0 : Rational) = 0 + 0 by ring1).trans_le
        (Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.mul_nonneg_direct (coefficientNonnegative count (Nat.lt_succ_self count))
            (prior (fun index before => coefficientNonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
              (fun index before => forcingNonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))))
          (forcingNonnegative count (Nat.lt_succ_self count)))

/-- Constant forcing factors out of the same original zero-initial affine iterate. -/
theorem iterate_constant_forcing (coefficient forcing : Rational) (count : Nat) :
    iterate (fun _ => coefficient) (fun _ => forcing) 0 count =
      forcing * iterate (fun _ => coefficient) (fun _ => 1) 0 count := by
  induction count with
  | zero => change (0 : Rational) = forcing * 0; ring1
  | succ count prior =>
      exact (congrArg (fun value : Rational => coefficient * value + forcing) prior).trans (by
        change coefficient * (forcing * iterate (fun _ => coefficient) (fun _ => 1) 0 count) + forcing =
          forcing * (coefficient * iterate (fun _ => coefficient) (fun _ => 1) 0 count + 1)
        ring1)

/-- The original affine iterate splits into its unit-initial response and SAME zero-initial forced iterate.

The coefficient and forcing remain their original indexed functions.
Structural recurrence and scalar distributivity prove exact dependence on
the supplied initial value; no second amplification algorithm is defined.
-/
theorem iterate_initial (coefficient forcing : Nat → Rational) (initial : Rational) (count : Nat) :
    iterate coefficient forcing initial count =
      iterate coefficient (fun _ => 0) 1 count * initial + iterate coefficient forcing 0 count := by
  induction count with
  | zero => change initial = (1 : Rational) * initial + 0; ring1
  | succ count prior =>
      exact (congrArg (fun value : Rational => coefficient count * value + forcing count) prior).trans (by
        change coefficient count *
            (iterate coefficient (fun _ => 0) 1 count * initial + iterate coefficient forcing 0 count) +
              forcing count =
          (coefficient count * iterate coefficient (fun _ => 0) 1 count + 0) * initial +
            (coefficient count * iterate coefficient forcing 0 count + forcing count)
        ring1)

end Purelib.Algebra.Recurrence.Affine

end
