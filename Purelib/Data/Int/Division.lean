module
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Lattice

public import Init.Data.Int.DivMod.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Subtraction

/-!
# Euclidean division of displayed integers

The quotient and remainder are the ordinary executable integer operations.
Positive natural divisors admit a natural remainder readback, and displayed
multiples admit exact quotient cancellation for every integer sign.
-/

namespace Purelib.Data.Int.Division

open Purelib.Data.Int
open Purelib.Data
open Purelib.Data.Nat

/-- Convert the Euclidean remainder of an integer by a natural divisor to Nat.

The divisor is cast to Int before taking the remainder, and toNat gives a total
result even when the supplied divisor is zero. -/
@[expose] public def remNat (numerator : Int) (denominator : Nat) : Nat :=
  (numerator % (denominator : Int)).toNat

/-- The natural remainder reconstructs the integer remainder for a positive divisor.

For a negative numerator, the retained natural remainder bound places the
signed difference in its nonnegative branch. -/
public theorem remNat_cast (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    numerator % (denominator : Int) = Int.ofNat (remNat numerator denominator) := by
  cases denominator with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ denominator =>
      cases numerator with
      | ofNat numerator => rfl
      | negSucc numerator =>
          have bound : numerator % (denominator + 1) ≤ denominator :=
            Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ denominator))
          change Int.subNatNat (denominator + 1) (numerator % (denominator + 1) + 1) =
            Int.ofNat ((Int.subNatNat (denominator + 1)
              (numerator % (denominator + 1) + 1)).toNat)
          rw [Arithmetic.subNatNat_succ_succ, Arithmetic.subNatNat_of_le bound]
          rfl

/-- The natural Euclidean remainder is smaller than its positive divisor.

Both numerator signs reduce to the retained bound on ordinary natural
remainders, with a bounded natural difference for the negative branch. -/
public theorem remNat_lt (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) : remNat numerator denominator < denominator := by
  cases denominator with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ denominator =>
      cases numerator with
      | ofNat numerator => exact Nat.mod_lt _ (Nat.zero_lt_succ denominator)
      | negSucc numerator =>
          have bound : numerator % (denominator + 1) ≤ denominator :=
            Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ denominator))
          change (Int.subNatNat (denominator + 1)
            (numerator % (denominator + 1) + 1)).toNat < denominator + 1
          rw [Arithmetic.subNatNat_succ_succ, Arithmetic.subNatNat_of_le bound]
          exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self denominator)

/-- A positive natural divisor's original quotient and remainder reconstruct an integer.

Both signs follow the original Euclidean operations. The negative branch retains
its quotient shifted by one and its bounded natural remainder complement,
using the same original natural quotient/remainder reconstruction equation. -/
public theorem ediv_add_remNat (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    (denominator : Int) * (numerator / (denominator : Int)) +
      (remNat numerator denominator : Int) = numerator := by
  cases denominator with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ denominator =>
      cases numerator with
      | ofNat numerator =>
          change ((denominator + 1 : Nat) : Int) *
              ((numerator / (denominator + 1) : Nat) : Int) +
              ((numerator % (denominator + 1) : Nat) : Int) = (numerator : Int)
          rw [← Int.natCast_mul, ← Int.natCast_add]
          exact congrArg Int.ofNat
            ((Nat.add_comm _ _).trans (Nat.Division.mod_add_div numerator (denominator + 1)))
      | negSucc numerator =>
          let quotient := numerator / (denominator + 1)
          let remainder := numerator % (denominator + 1)
          have remainderBound : remainder + 1 ≤ denominator + 1 :=
            Nat.succ_le_of_lt (Nat.mod_lt numerator (Nat.zero_lt_succ denominator))
          have complement := Subtraction.add_sub_of_le remainderBound
          have reconstruction := Nat.Division.mod_add_div numerator (denominator + 1)
          have natural : (denominator + 1) * (quotient + 1) =
              (numerator + 1) + ((denominator + 1) - (remainder + 1)) := by
            calc
              (denominator + 1) * (quotient + 1) =
                  (denominator + 1) * quotient + (denominator + 1) := Nat.mul_succ _ _
              _ = (denominator + 1) * quotient +
                  ((remainder + 1) + ((denominator + 1) - (remainder + 1))) :=
                congrArg (fun tail => (denominator + 1) * quotient + tail) complement.symm
              _ = ((denominator + 1) * quotient + remainder) + 1 +
                  ((denominator + 1) - (remainder + 1)) :=
                (Nat.add_assoc ((denominator + 1) * quotient) (remainder + 1)
                  ((denominator + 1) - (remainder + 1))).symm.trans
                  (congrArg (fun initial => initial + ((denominator + 1) - (remainder + 1)))
                    (Nat.add_assoc ((denominator + 1) * quotient) remainder 1).symm)
              _ = (numerator + 1) + ((denominator + 1) - (remainder + 1)) := by
                rw [Nat.add_comm ((denominator + 1) * quotient) remainder, reconstruction]
          change Int.negOfNat ((denominator + 1) * (quotient + 1)) +
              Int.ofNat ((Int.subNatNat (denominator + 1) (remainder + 1)).toNat) =
            Int.negSucc numerator
          rw [Arithmetic.subNatNat_of_le remainderBound]
          change -(((denominator + 1) * (quotient + 1) : Nat) : Int) +
              (((denominator + 1) - (remainder + 1) : Nat) : Int) =
            -((numerator + 1 : Nat) : Int)
          rw [natural, Int.natCast_add, Arithmetic.neg_add, Arithmetic.add_assoc,
            Arithmetic.neg_add_cancel, Int.add_zero]

/-- Multiplying the quotient by its positive natural divisor does not exceed the dividend.

The original natural remainder is the retained nonnegative additive difference.
Its exact reconstruction certifies the bound for either sign of the dividend. -/
public theorem mul_ediv_self_le (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    (denominator : Int) * (numerator / (denominator : Int)) ≤ numerator :=
  Order.le_intro (remNat numerator denominator) (ediv_add_remNat numerator positive)

/-- A dividend lies below the quotient multiple plus its positive natural divisor.

The original natural remainder is strictly below that divisor. Its retained
successor complement provides the additive witness for the strict integer bound. -/
public theorem lt_mul_ediv_self_add (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    numerator < (denominator : Int) * (numerator / (denominator : Int)) +
      (denominator : Int) := by
  let remainder := remNat numerator denominator
  let multiple := (denominator : Int) * (numerator / (denominator : Int))
  have bound : remainder + 1 ≤ denominator := Nat.succ_le_of_lt (remNat_lt numerator positive)
  have final := congrArg (fun value : Nat => multiple + (value : Int))
    (Subtraction.add_sub_of_le bound)
  rw [Int.natCast_add (remainder + 1) (denominator - (remainder + 1)),
    Int.natCast_add remainder 1, Int.natCast_one] at final
  apply Order.le_intro (denominator - (remainder + 1))
  have reconstruction : multiple + (remainder : Int) = numerator :=
    ediv_add_remNat numerator positive
  calc
    numerator + 1 + ((denominator - (remainder + 1) : Nat) : Int) =
        (multiple + (remainder : Int)) + 1 +
          ((denominator - (remainder + 1) : Nat) : Int) :=
      congrArg (fun value : Int => value + 1 +
        ((denominator - (remainder + 1) : Nat) : Int)) reconstruction.symm
    _ = multiple + (denominator : Int) := by
      rw [Arithmetic.add_assoc multiple (remainder : Int) 1,
        Arithmetic.add_assoc multiple ((remainder : Int) + 1)
          ((denominator - (remainder + 1) : Nat) : Int)]
      exact final

/-- The remainder is the original dividend minus its original quotient multiple.

The positive natural divisor permits the same retained reconstruction for
both dividend signs. Cancelling the quotient multiple leaves its exact original
Euclidean remainder rather than a separately selected difference. -/
public theorem emod_def (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    numerator % (denominator : Int) =
      numerator - (denominator : Int) * (numerator / (denominator : Int)) := by
  let multiple := (denominator : Int) * (numerator / (denominator : Int))
  have removed : numerator - multiple = (remNat numerator denominator : Int) := by
    have reconstruction : multiple + (remNat numerator denominator : Int) = numerator :=
      ediv_add_remNat numerator positive
    calc
      numerator - multiple = (multiple + (remNat numerator denominator : Int)) - multiple :=
        congrArg (fun value : Int => value - multiple) reconstruction.symm
      _ = (remNat numerator denominator : Int) := by
        rw [Int.sub_eq_add_neg, Arithmetic.add_comm multiple (remNat numerator denominator : Int),
          Arithmetic.add_assoc, Arithmetic.add_comm multiple (-multiple),
          Arithmetic.neg_add_cancel, Int.add_zero]
  exact (remNat_cast numerator positive).trans removed.symm

/-- A nonzero integer remainder has a positive natural readback.

The divisor is positive, so the readback reconstructs the integer remainder;
a zero readback would contradict the supplied nonzero remainder. -/
public theorem remNat_pos (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator)
    (remainderNonzero : numerator % (denominator : Int) ≠ 0) :
    0 < remNat numerator denominator := by
  apply Nat.pos_of_ne_zero
  intro readbackZero
  apply remainderNonzero
  exact (remNat_cast numerator positive).trans (congrArg Int.ofNat readbackZero)

/-- Dividing an integer multiple by its nonzero left factor recovers the multiplier.

The four displayed integer signs reduce to natural quotient cancellation
or to a quotient shifted by a retained multiple of a positive natural divisor. -/
public theorem mul_ediv_cancel_left (factor : Int) {divisor : Int}
    (nonzero : divisor ≠ 0) : divisor * factor / divisor = factor := by
  cases divisor with
  | ofNat divisor =>
      cases divisor with
      | zero => exact (nonzero rfl).elim
      | succ divisor =>
          cases factor with
          | ofNat factor =>
              exact congrArg Int.ofNat
                (Nat.Division.mul_div_cancel_left factor (Nat.zero_lt_succ divisor))
          | negSucc factor =>
              change Int.negOfNat ((divisor + 1) * (factor + 1)) /
                Int.ofNat (divisor + 1) = Int.negSucc factor
              rw [Nat.mul_succ, Nat.add_succ]
              change Int.negSucc (((divisor + 1) * factor + divisor) / (divisor + 1)) =
                Int.negSucc factor
              rw [Nat.Division.mul_add_div (Nat.zero_lt_succ divisor),
                Nat.Division.div_eq_of_lt (Nat.lt_succ_self divisor), Nat.add_zero]
  | negSucc divisor =>
      cases factor with
      | ofNat factor =>
          cases factor with
          | zero =>
              change -Int.ofNat (0 / (divisor + 1)) = 0
              rw [Nat.Division.zero_div]
              rfl
          | succ factor =>
              change Int.negOfNat ((divisor + 1) * (factor + 1)) /
                Int.negSucc divisor = Int.ofNat (factor + 1)
              rw [Nat.mul_succ, Nat.add_succ]
              change Int.ofNat ((((divisor + 1) * factor + divisor) / (divisor + 1)) + 1) =
                Int.ofNat (factor + 1)
              rw [Nat.Division.mul_add_div (Nat.zero_lt_succ divisor),
                Nat.Division.div_eq_of_lt (Nat.lt_succ_self divisor), Nat.add_zero]
      | negSucc factor =>
          change -Int.ofNat (((divisor + 1) * (factor + 1)) / (divisor + 1)) =
            Int.negSucc factor
          rw [Nat.Division.mul_div_cancel_left (factor + 1) (Nat.zero_lt_succ divisor)]
          rfl

/-- Increasing an integer dividend cannot decrease its quotient by a positive natural divisor.

The original Euclidean division is retained for each integer sign. Its
natural quotients are monotone; negation reverses both the retained negative
magnitudes and their original quotient bounds. -/
public theorem ediv_le_ediv_right {left right : Int} (bound : left ≤ right)
    {divisor : Nat} (positive : 0 < divisor) :
    left / (divisor : Int) ≤ right / (divisor : Int) := by
  cases divisor with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ divisor =>
      cases left with
      | ofNat left =>
          cases right with
          | ofNat right =>
              change ((left / (divisor + 1) : Nat) : Int) ≤
                ((right / (divisor + 1) : Nat) : Int)
              exact Order.natCast_le_iff.mpr
                (Nat.Division.div_le_div_right (Order.natCast_le_iff.mp bound)
                  (divisor + 1))
          | negSucc right =>
              obtain ⟨difference, equation⟩ := Order.le_dest bound
              change Int.ofNat (left + difference) = Int.negSucc right at equation
              cases equation
      | negSucc left =>
          cases right with
          | ofNat right =>
              apply Order.le_intro
                (left / (divisor + 1) + 1 + right / (divisor + 1))
              change -((left / (divisor + 1) + 1 : Nat) : Int) +
                  ((left / (divisor + 1) + 1 + right / (divisor + 1) : Nat) : Int) =
                ((right / (divisor + 1) : Nat) : Int)
              rw [Int.natCast_add (left / (divisor + 1) + 1) (right / (divisor + 1)),
                ← Arithmetic.add_assoc,
                Arithmetic.neg_add_cancel, Arithmetic.zero_add]
          | negSucc right =>
              have reversed := Order.neg_le_neg bound
              change ((right + 1 : Nat) : Int) ≤ ((left + 1 : Nat) : Int) at reversed
              have naturalBound : right ≤ left :=
                Nat.le_of_succ_le_succ (Order.natCast_le_iff.mp reversed)
              have quotientBound :=
                Nat.Division.div_le_div_right naturalBound (divisor + 1)
              have castBound : ((right / (divisor + 1) + 1 : Nat) : Int) ≤
                  ((left / (divisor + 1) + 1 : Nat) : Int) :=
                Order.natCast_le_iff.mpr (Nat.succ_le_succ quotientBound)
              exact Order.neg_le_neg castBound

/-- A divisible integer quotient reconstructs its dividend when multiplied back.

The original divisibility multiplier certifies cancellation. A zero divisor
forces the displayed dividend to be zero and is handled directly. -/
public theorem ediv_mul_cancel {value divisor : Int} (retained : divisor ∣ value) :
    value / divisor * divisor = value := by
  obtain ⟨factor, equation⟩ := retained
  rw [equation]
  by_cases divisorZero : divisor = 0
  · rw [divisorZero, Arithmetic.zero_mul, Int.mul_zero]
  · rw [mul_ediv_cancel_left factor divisorZero, Arithmetic.mul_comm]

end Purelib.Data.Int.Division
