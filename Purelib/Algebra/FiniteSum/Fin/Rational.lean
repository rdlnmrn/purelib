module
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Rational.Order
-- Public entry bounds retain the original rational comparison operations.
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

open Purelib.Data.Rat

open Purelib.Algebra

public section

namespace Purelib.Algebra.FiniteSum.Fin.Rational

open scoped Purelib.Data.Nat

/-- Each nonnegative rational entry is at most the complete finite sum.

The original bounded coordinate is split into its first or successor position.
All remaining entries contribute a nonnegative retained tail sum. -/
theorem entry_le_sum {count : Nat} (values : Fin count → Fraction.Rational) (positive : ∀ i, 0 ≤ values i)
    (index : Fin count) : values index ≤ FiniteSum.Fin.sumFin values := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      refine Purelib.Data.Fin.cases_induction ?_ (fun i => ?_) index
      · exact le_add_of_nonneg_right (FiniteSum.Rational.Order.weight_sum_nonnegative (fun i => values i.succ) (fun i =>
          positive i.succ))
      · exact (ih (fun i => values i.succ) (fun i => positive i.succ) i).trans (le_add_of_nonneg_left (positive ⟨0,
          Nat.zero_lt_succ count⟩))

/-- A constant rational sum equals its finite index count times that constant.

The original successor-index sum separates its first entry from the remaining entries; the natural cast and scalar
addition preserve that same count. -/
theorem sum_constant (count : Nat) (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin count => value) = (count : Fraction.Rational) * value := by
  induction count with
  | zero => change (0 : Fraction.Rational) = 0 * value; ring1
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ, ih, NatCast.add, Nat.cast_one]
      ring1

/-- A constant rational sum over eight entries equals eight times its value.

The finite index set and the right-associated sum are reduced explicitly. -/
theorem sumFin_eight_constant (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin 8 => value) =
      8 * value := by
  rw [FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ]
  rw [show FiniteSum.Fin.sumFin
      (fun _ : Fin 0 => value) = 0 by rfl]
  ring1

/-- A constant rational sum over two entries equals twice its value.

The finite index set and the right-associated sum are reduced explicitly. -/
theorem sumFin_two_constant (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin 2 => value) =
      2 * value := by
  rw [FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ]
  rw [show FiniteSum.Fin.sumFin
      (fun _ : Fin 0 => value) = 0 by rfl]
  ring1

/-- A constant rational sum over four entries equals four times its value.

The finite index set and the right-associated sum are reduced explicitly. -/
theorem sumFin_four_constant (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin 4 => value) =
      4 * value := by
  rw [FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ]
  rw [show FiniteSum.Fin.sumFin
      (fun _ : Fin 0 => value) = 0 by rfl]
  ring1

/-- Read the zero-inclusive maximum of the original finite rational family.

The empty family has maximum zero; a successor family compares its first entry with the recursively retained
successor-index tail. -/
@[expose] def maximum {n : Nat} (values : Fin n → Fraction.Rational) : Fraction.Rational :=
  match n, values with
  | 0, _ => 0
  | _ + 1, values => max (values 0) (Purelib.Algebra.FiniteSum.Fin.Rational.maximum (fun i => values i.succ))

/-- The zero-inclusive maximum is nonnegative.

Zero is retained as the empty-family base value even when every supplied entry is negative. -/
theorem maximum_nonnegative {n : Nat} (values : Fin n → Fraction.Rational) : 0 ≤ maximum values := by
  induction n with
  | zero => exact Fraction.Order.Basic.le_refl _
  | succ n ih => exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _ (ih _) (Fraction.Order.Basic.le_max_right _ _)

/-- Every original finite-family entry is bounded by the zero-inclusive maximum.

The supplied retained index selects either the head or its exact successor-index tail entry. -/
theorem le_maximum {n : Nat} (values : Fin n → Fraction.Rational) (i : Fin n) : values i ≤ maximum values := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Purelib.Data.Fin.cases_induction ?_ (fun i => ?_) i
    · exact Fraction.Order.Basic.le_max_left _ _
    · exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (ih (fun i => values i.succ) i) (Fraction.Order.Basic.le_max_right _ _)

/-- A nonnegative ceiling on each entry bounds the complete zero-inclusive maximum.

The ceiling also bounds the retained zero base case, so the empty family is included. -/
theorem maximum_le {n : Nat} (values : Fin n → Fraction.Rational) {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : ∀ i, values i ≤ bound) : maximum values ≤ bound := by
  induction n with
  | zero => exact nonnegative
  | succ n ih => exact Fraction.Order.Basic.max_le (bounded 0) (ih _ (fun i => bounded i.succ))

end Purelib.Algebra.FiniteSum.Fin.Rational
