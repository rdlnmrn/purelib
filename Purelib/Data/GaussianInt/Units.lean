module
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Nat.Addition
import Purelib.Data.Int.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# The four integral Gaussian coordinate units
-/

namespace Purelib.Data.GaussianInt.Units

open Purelib.Data
open Purelib.Data.GaussianInt

public section

/-- The displayed Gaussian integer with zero real coordinate and imaginary coordinate
one. -/
@[expose] def imaginaryUnit : GaussianInt := ⟨0, 1⟩

/-! ## Uniqueness of the canonical displayed coordinates -/

/-- Every positive natural is at most its square. -/
private theorem nat_le_square_of_pos {value : Nat} (positive : 0 < value) :
    value ≤ value ^ 2 := by
  simpa only [pow_two] using Nat.le_mul_of_pos_right value positive

/-- An integer of natural absolute value one is either one or negative one. -/
private theorem int_eq_one_or_neg_one_of_natAbs_eq_one {value : Int}
    (magnitude : value.natAbs = 1) : value = 1 ∨ value = -1 := by
  cases value with
  | ofNat natural =>
      change natural = 1 at magnitude
      subst natural
      left
      rfl
  | negSucc predecessor =>
      change predecessor + 1 = 1 at magnitude
      have predecessorZero : predecessor = 0 :=
        Purelib.Data.Nat.Addition.add_right_cancel magnitude
      subst predecessor
      right
      rfl

/-- A Gaussian integer of natural quadrance one is one of the four coordinate units.

The two component squares sum to one, so exactly one component has absolute value one
and the other is zero. -/
theorem normNat_eq_one_cases {unit : GaussianInt}
    (unitNorm : GaussianInt.normNat unit = 1) :
    unit = 1 ∨ unit = -1 ∨ unit = Units.imaginaryUnit ∨ unit = -Units.imaginaryUnit := by
  have componentIdentity := GaussianInt.normNat_eq_component_squares unit
  rw [unitNorm] at componentIdentity
  have realSquareLe : unit.re.natAbs ^ 2 ≤ 1 := by
    calc
      unit.re.natAbs ^ 2 ≤
          unit.re.natAbs ^ 2 + unit.im.natAbs ^ 2 := Nat.le_add_right _ _
      _ = 1 := componentIdentity.symm
  have imaginarySquareLe : unit.im.natAbs ^ 2 ≤ 1 := by
    calc
      unit.im.natAbs ^ 2 ≤
          unit.re.natAbs ^ 2 + unit.im.natAbs ^ 2 := Nat.le_add_left _ _
      _ = 1 := componentIdentity.symm
  have realLeOne : unit.re.natAbs ≤ 1 := by
    by_cases realZero : unit.re.natAbs = 0
    · rw [realZero]
      exact Nat.zero_le 1
    · exact (Units.nat_le_square_of_pos (Nat.pos_of_ne_zero realZero)).trans
        realSquareLe
  have imaginaryLeOne : unit.im.natAbs ≤ 1 := by
    by_cases imaginaryZero : unit.im.natAbs = 0
    · rw [imaginaryZero]
      exact Nat.zero_le 1
    · exact (Units.nat_le_square_of_pos
        (Nat.pos_of_ne_zero imaginaryZero)).trans imaginarySquareLe
  have realCases : unit.re.natAbs = 0 ∨ unit.re.natAbs = 1 := by
    rcases Nat.eq_zero_or_pos unit.re.natAbs with realZero | realPositive
    · exact Or.inl realZero
    · exact Or.inr (Nat.le_antisymm realLeOne realPositive)
  have imaginaryCases : unit.im.natAbs = 0 ∨ unit.im.natAbs = 1 := by
    rcases Nat.eq_zero_or_pos unit.im.natAbs with imaginaryZero |
      imaginaryPositive
    · exact Or.inl imaginaryZero
    · exact Or.inr (Nat.le_antisymm imaginaryLeOne imaginaryPositive)
  rcases realCases with realZero | realOne
  · have realCoordinateZero : unit.re = 0 := by
      by_cases zero : unit.re = 0
      · exact zero
      · have positive := Int.Arithmetic.natAbs_pos_of_ne_zero zero
        rw [realZero] at positive
        exact (Nat.lt_irrefl 0 positive).elim
    rcases imaginaryCases with imaginaryZero | imaginaryOne
    · rw [realZero, imaginaryZero] at componentIdentity
      exact False.elim ((by decide : (0 : Nat) ^ 2 + 0 ^ 2 ≠ 1)
        componentIdentity.symm)
    · rcases Units.int_eq_one_or_neg_one_of_natAbs_eq_one imaginaryOne with
        imaginaryPositive | imaginaryNegative
      · right; right; left
        apply GaussianInt.ext
        · exact realCoordinateZero
        · exact imaginaryPositive
      · right; right; right
        apply GaussianInt.ext
        · exact realCoordinateZero
        · simpa only [Units.imaginaryUnit, GaussianInt.neg_im] using imaginaryNegative
  · rcases Units.int_eq_one_or_neg_one_of_natAbs_eq_one realOne with
      realPositive | realNegative
    · rcases imaginaryCases with imaginaryZero | imaginaryOne
      · have imaginaryCoordinateZero : unit.im = 0 :=
          by
            by_cases zero : unit.im = 0
            · exact zero
            · have positive := Int.Arithmetic.natAbs_pos_of_ne_zero zero
              rw [imaginaryZero] at positive
              exact (Nat.lt_irrefl 0 positive).elim
        left
        apply GaussianInt.ext
        · exact realPositive
        · exact imaginaryCoordinateZero
      · rw [realOne, imaginaryOne] at componentIdentity
        exact False.elim ((by decide : (1 : Nat) ^ 2 + 1 ^ 2 ≠ 1)
          componentIdentity.symm)
    · rcases imaginaryCases with imaginaryZero | imaginaryOne
      · have imaginaryCoordinateZero : unit.im = 0 :=
          by
            by_cases zero : unit.im = 0
            · exact zero
            · have positive := Int.Arithmetic.natAbs_pos_of_ne_zero zero
              rw [imaginaryZero] at positive
              exact (Nat.lt_irrefl 0 positive).elim
        right; left
        apply GaussianInt.ext
        · simpa only [GaussianInt.neg_re, GaussianInt.one_re] using realNegative
        · exact imaginaryCoordinateZero
      · rw [realOne, imaginaryOne] at componentIdentity
        exact False.elim ((by decide : (1 : Nat) ^ 2 + 1 ^ 2 ≠ 1)
          componentIdentity.symm)

end

end Purelib.Data.GaussianInt.Units
