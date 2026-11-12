module

public import Purelib.Data.Vector.Basic
public import Purelib.Data.Nat.Choose
import Purelib.Algebra.NatCast
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Generalized polynomial modes on finite horizons

Binomial coordinates describe repeated-root blocks without inverse roots.
At a zero root the same coordinates are the finitely supported transients.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Nat.Choose
open Purelib.Algebra

variable {K : Type*} [CommRing K]

/-- Read one binomial generalized-mode coordinate.

The conditional omits negative powers, including at the zero root. Each
reading uses only a finite natural power and one Pascal coefficient.
-/
@[expose] def entry (root : K) (order index : Nat) : K :=
  if order ≤ index then (Pascal.choose index order : K) * root ^ (index - order) else 0

/-- Retain the requested finite horizon of one generalized mode. -/
@[expose] def window (root : K) (order count : Nat) : Vec K count :=
  vectorOfFn fun index => entry root order index.val

/-- Every retained mode-window entry is its original finite reading. -/
theorem window_at (root : K) (order count : Nat) (index : Fin count) :
    window root order count index = entry root order index.val := vectorOfFn_apply _ _

/-- The order-zero mode is the original finite power of its root. -/
theorem entry_zero_order (root : K) (index : Nat) : entry root 0 index = root ^ index := by
  rw [entry, if_pos (Nat.zero_le index), Pascal.choose_zero_right, Nat.sub_zero,
    Nat.cast_one, one_mul]

/-- Every generalized mode vanishes before its own startup coordinate. -/
theorem entry_before (root : K) (order index : Nat) (before : index < order) :
    entry root order index = 0 := by
  rw [entry, if_neg (Nat.not_le_of_gt before)]

/-- A generalized mode has value one at its startup coordinate. -/
theorem entry_start (root : K) (order : Nat) : entry root order order = 1 := by
  rw [entry, if_pos (Nat.le_refl order), Pascal.choose_self, Nat.sub_self,
    Nat.cast_one, pow_zero, one_mul]

/-- At a zero root a generalized mode is its one-coordinate transient.

No inverse or nonzero-root premise enters this equality.
-/
theorem entry_zero_root (order index : Nat) :
    entry (0 : K) order index = if index = order then 1 else 0 := by
  by_cases equal : index = order
  · subst index
    rw [entry_start, if_pos rfl]
  · rw [if_neg equal]
    by_cases before : index < order
    · exact entry_before _ _ _ before
    · have le : order ≤ index := Nat.le_of_not_gt before
      have positive : 0 < index - order := by omega0
      rw [entry, if_pos le, zero_pow (Nat.ne_of_gt positive), mul_zero]

/-- The successor reading of an order-zero mode multiplies by its root. -/
theorem entry_succ_zero (root : K) (index : Nat) :
    entry root 0 (index + 1) = root * entry root 0 index := by
  rw [entry_zero_order, entry_zero_order, pow_succ, mul_comm]

/-- Consecutive binomial modes satisfy the original Jordan-block transition.

Pascal's finite recurrence splits the next reading into the same root-scaled
mode and the preceding-order mode, with no negative powers at startup.
-/
theorem entry_succ (root : K) (order index : Nat) :
    entry root (order + 1) (index + 1) =
      root * entry root (order + 1) index + entry root order index := by
  by_cases before : index < order
  · have beforeNext : index + 1 < order + 1 := Nat.succ_lt_succ before
    have beforeHigher : index < order + 1 := Nat.lt_succ_of_lt before
    rw [entry_before _ _ _ beforeNext, entry_before _ _ _ beforeHigher,
      entry_before _ _ _ before, mul_zero, zero_add]
  · by_cases equal : index = order
    · subst index
      rw [entry_start, entry_before _ _ _ (Nat.lt_succ_self order), entry_start,
        mul_zero, zero_add]
    · have lower : order ≤ index := Nat.le_of_not_gt before
      have higher : order + 1 ≤ index := by omega0
      have nextHigher : order + 1 ≤ index + 1 := Nat.succ_le_succ lower
      have exponent : index + 1 - (order + 1) = index - order := by omega0
      have power : index - order = index - (order + 1) + 1 := by omega0
      rw [entry, if_pos nextHigher, entry, if_pos higher, entry, if_pos lower,
        exponent, Pascal.choose_succ_succ, NatCast.add]
      rw [power, pow_succ]
      ring0

/-- A first-order difference of an order-zero mode scales it by the root difference. -/
theorem entry_difference_zero (root center : K) (index : Nat) :
    entry root 0 (index + 1) - center * entry root 0 index =
      (root - center) * entry root 0 index := by
  rw [entry_succ_zero]
  ring0

/-- A first-order difference preserves the original root mode and its preceding order.

The original Pascal transition gives this identity over every commutative
ring. Neither the root nor the difference from the supplied center is inverted.
-/
theorem entry_difference_succ (root center : K) (order index : Nat) :
    entry root (order + 1) (index + 1) - center * entry root (order + 1) index =
      (root - center) * entry root (order + 1) index + entry root order index := by
  rw [entry_succ]
  ring0

/-- Taking the difference at the same root lowers the generalized mode by one order. -/
theorem entry_difference_same (root : K) (order index : Nat) :
    entry root (order + 1) (index + 1) - root * entry root (order + 1) index =
      entry root order index := by
  rw [entry_difference_succ, sub_self, zero_mul, zero_add]

end Purelib.Polynomial.Recurrence.Mode
