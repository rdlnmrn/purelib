import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzTrace

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace RFAP.HurwitzGeometry

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Stage := RFAP.HurwitzTrace.Stage

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzRational
open RFAP.HurwitzApproximation

/-- The Gaussian integer `i`. -/
def imaginaryUnit : GaussianInt := ⟨0, 1⟩

@[simp] theorem imaginaryUnit_re : imaginaryUnit.re = 0 := rfl

@[simp] theorem imaginaryUnit_im : imaginaryUnit.im = 1 := rfl

/-- The four Gaussian units, given as finite alternatives. -/
def IsGaussianUnit (value : GaussianInt) : Prop :=
  value = 1 ∨ value = -1 ∨
    value = imaginaryUnit ∨ value = -imaginaryUnit

/-- The four diagonal Gaussian integers of quadrance two. -/
def IsDiagonal (value : GaussianInt) : Prop :=
  value = ⟨1, 1⟩ ∨ value = ⟨1, -1⟩ ∨
    value = ⟨-1, 1⟩ ∨ value = ⟨-1, -1⟩

/-- Integral complex conjugation. -/
def conjugate (value : GaussianInt) : GaussianInt :=
  ⟨value.re, -value.im⟩

/-- The corner transform `s ↦ -conj(s)` used by the backward Hurwitz
succession. -/
def cornerTurn (value : GaussianInt) : GaussianInt :=
  -conjugate value

@[simp] theorem conjugate_re (value : GaussianInt) :
    (conjugate value).re = value.re := rfl

@[simp] theorem conjugate_im (value : GaussianInt) :
    (conjugate value).im = -value.im := rfl

@[simp] theorem cornerTurn_re (value : GaussianInt) :
    (cornerTurn value).re = -value.re := rfl

@[simp] theorem cornerTurn_im (value : GaussianInt) :
    (cornerTurn value).im = value.im := by
  simp only [cornerTurn, conjugate,
    RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im]
  ring1

theorem normInt_eq_natCast_normNat (value : GaussianInt) :
    normInt value = (normNat value : Int) := by
  rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg value)]

theorem normNat_mul (left right : GaussianInt) :
    normNat (left * right) = normNat left * normNat right := by
  apply RFAP.ConstructiveFraction.natCast_injective_direct
  rw [Nat.cast_mul, ← normSq_toGaussian, toGaussian_mul, normSq_mul,
    normSq_toGaussian, normSq_toGaussian]

@[simp] theorem normNat_conjugate (value : GaussianInt) :
    normNat (conjugate value) = normNat value := by
  apply RFAP.ConstructiveFraction.natCast_injective_direct
  rw [← normSq_toGaussian, ← normSq_toGaussian]
  change (value.re : Coordinate) ^ 2 + (-value.im : Int) ^ 2 =
    (value.re : Coordinate) ^ 2 + (value.im : Coordinate) ^ 2
  rw [Int.cast_neg]
  ring1

private theorem int_mul_self_nonneg (value : Int) :
    0 ≤ value * value := by
  by_cases nonnegative : 0 ≤ value
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : value ≤ 0 :=
      Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

private theorem coordinate_cases_of_square_lt_four {value : Int}
    (small : value * value < 4) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  have lower : -(2 : Int) < value := by
    apply Int.lt_of_not_ge
    intro valueAtMost
    have twoLeNegative : (2 : Int) ≤ -value := by
      have negated := Int.neg_le_neg valueAtMost
      change (2 : Int) ≤ -value at negated
      exact negated
    have squareAtLeastFour : (4 : Int) ≤ value * value := by
      calc
        (4 : Int) = 2 * 2 := rfl
        _ ≤ (-value) * (-value) :=
          Int.mul_self_le_mul_self (by decide) twoLeNegative
        _ = value * value := by ring1
    exact (not_lt_of_ge squareAtLeastFour small)
  have upper : value < 2 := by
    apply Int.lt_of_not_ge
    intro twoLeValue
    have squareAtLeastFour : (4 : Int) ≤ value * value := by
      calc
        (4 : Int) = 2 * 2 := rfl
        _ ≤ value * value :=
          Int.mul_self_le_mul_self (by decide) twoLeValue
    exact (not_lt_of_ge squareAtLeastFour small)
  have lowerLe : (-1 : Int) ≤ value := by
    change (-(2 : Int) + 1) ≤ value
    exact Int.add_one_le_iff.mpr lower
  have upperLe : value ≤ (1 : Int) := by
    change value ≤ (2 : Int) - 1
    exact Int.le_sub_one_iff.mpr upper
  by_cases negative : value = -1
  · exact Or.inl negative
  · have zeroLe : (0 : Int) ≤ value := by
      change (-1 : Int) + 1 ≤ value
      exact Int.add_one_le_iff.mpr
        (lt_of_le_of_ne lowerLe (Ne.symm negative))
    by_cases zero : value = 0
    · exact Or.inr (Or.inl zero)
    · have oneLe : (1 : Int) ≤ value := by
        change (0 : Int) + 1 ≤ value
        exact Int.add_one_le_iff.mpr
          (lt_of_le_of_ne zeroLe (Ne.symm zero))
      exact Or.inr (Or.inr (Int.le_antisymm upperLe oneLe))

private theorem coordinate_cases_of_neg_two_lt_lt_two {value : Int}
    (lower : -(2 : Int) < value) (upper : value < 2) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  have lowerLe : (-1 : Int) ≤ value := by
    change (-(2 : Int) + 1) ≤ value
    exact Int.add_one_le_iff.mpr lower
  have upperLe : value ≤ (1 : Int) := by
    change value ≤ (2 : Int) - 1
    exact Int.le_sub_one_iff.mpr upper
  by_cases negative : value = -1
  · exact Or.inl negative
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne lowerLe (Ne.symm negative))
  by_cases zero : value = 0
  · exact Or.inr (Or.inl zero)
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne zeroLe (Ne.symm zero))
  exact Or.inr (Or.inr (Int.le_antisymm upperLe oneLe))

private theorem coordinate_cases_of_square_lt_nine {value : Int}
    (small : value * value < 9) :
    value = -2 ∨ value = -1 ∨ value = 0 ∨ value = 1 ∨ value = 2 := by
  have lower : -(3 : Int) < value := by
    apply Int.lt_of_not_ge
    intro valueAtMost
    have threeLeNegative : (3 : Int) ≤ -value := by
      have negated := Int.neg_le_neg valueAtMost
      change (3 : Int) ≤ -value at negated
      exact negated
    have squareAtLeastNine : (9 : Int) ≤ value * value := by
      calc
        (9 : Int) = 3 * 3 := rfl
        _ ≤ (-value) * (-value) :=
          Int.mul_self_le_mul_self (by decide) threeLeNegative
        _ = value * value := by ring1
    exact (not_lt_of_ge squareAtLeastNine small)
  have upper : value < 3 := by
    apply Int.lt_of_not_ge
    intro threeLeValue
    have squareAtLeastNine : (9 : Int) ≤ value * value := by
      calc
        (9 : Int) = 3 * 3 := rfl
        _ ≤ value * value :=
          Int.mul_self_le_mul_self (by decide) threeLeValue
    exact (not_lt_of_ge squareAtLeastNine small)
  have lowerLe : (-2 : Int) ≤ value := by
    change (-(3 : Int) + 1) ≤ value
    exact Int.add_one_le_iff.mpr lower
  have upperLe : value ≤ (2 : Int) := by
    change value ≤ (3 : Int) - 1
    exact Int.le_sub_one_iff.mpr upper
  by_cases negativeTwo : value = -2
  · exact Or.inl negativeTwo
  have negativeOneLe : (-1 : Int) ≤ value := by
    change (-2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne lowerLe (Ne.symm negativeTwo))
  by_cases negativeOne : value = -1
  · exact Or.inr (Or.inl negativeOne)
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negativeOneLe (Ne.symm negativeOne))
  by_cases zero : value = 0
  · exact Or.inr (Or.inr (Or.inl zero))
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne zeroLe (Ne.symm zero))
  by_cases one : value = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inl one)))
  have twoLe : (2 : Int) ≤ value := by
    change (1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne oneLe (Ne.symm one))
  exact Or.inr (Or.inr (Or.inr (Or.inr
    (Int.le_antisymm upperLe twoLe))))

/-- A Gaussian integer of quadrance below four has quadrance `0`, `1`, or
`2`.  This is the finite classification behind Lakein's small-`t` branch. -/
theorem normNat_eq_zero_or_one_or_two_of_lt_four (value : GaussianInt)
    (small : normNat value < 4) :
    normNat value = 0 ∨ normNat value = 1 ∨ normNat value = 2 := by
  have normIntSmall : normInt value < 4 := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_lt.mpr small
  have realSmall : value.re * value.re < 4 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    exact (Int.le_add_of_nonneg_right imaginaryNonnegative).trans_lt
      normIntSmall
  have imaginarySmall : value.im * value.im < 4 := by
    have realNonnegative := int_mul_self_nonneg value.re
    exact (Int.le_add_of_nonneg_left realNonnegative).trans_lt
      normIntSmall
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary; decide

/-- The five quadrances represented by a Gaussian integer below six. -/
theorem normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
    (value : GaussianInt) (small : normNat value < 6) :
    normNat value = 0 ∨ normNat value = 1 ∨ normNat value = 2 ∨
      normNat value = 4 ∨ normNat value = 5 := by
  have normIntSmall : normInt value < 6 := by
    rw [normInt_eq_natCast_normNat]
    exact Int.ofNat_lt.mpr small
  have realSmall : value.re * value.re < 9 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntSmall
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ < 6 := normIntSmall
      _ < 9 := by decide
  have imaginarySmall : value.im * value.im < 9 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntSmall
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ < 6 := normIntSmall
      _ < 9 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 9 at realSmall
  change imaginary * imaginary < 9 at imaginarySmall
  rcases coordinate_cases_of_square_lt_nine realSmall with
      realNegativeTwo | realNegativeOne | realZero | realPositiveOne |
        realPositiveTwo <;>
    rcases coordinate_cases_of_square_lt_nine imaginarySmall with
      imaginaryNegativeTwo | imaginaryNegativeOne | imaginaryZero |
        imaginaryPositiveOne | imaginaryPositiveTwo
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntSmall
  all_goals try cases normIntSmall
  all_goals decide

theorem eq_zero_of_normNat_eq_zero {value : GaussianInt}
    (zeroNorm : normNat value = 0) : value = 0 := by
  apply normInt_eq_zero.mp
  rw [normInt_eq_natCast_normNat, zeroNorm]
  rfl

theorem isGaussianUnit_of_normNat_eq_one {value : GaussianInt}
    (unitNorm : normNat value = 1) : IsGaussianUnit value := by
  have normIntOne : normInt value = 1 := by
    rw [normInt_eq_natCast_normNat, unitNorm]
    rfl
  have realSmall : value.re * value.re < 4 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntOne
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ = 1 := normIntOne
      _ < 4 := by decide
  have imaginarySmall : value.im * value.im < 4 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntOne
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ = 1 := normIntOne
      _ < 4 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntOne
  all_goals try cases normIntOne
  · right
    left
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;> rfl
  · right
    right
    right
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;> rfl
  · right
    right
    left
    rfl
  · left
    rfl

theorem isDiagonal_of_normNat_eq_two {value : GaussianInt}
    (diagonalNorm : normNat value = 2) : IsDiagonal value := by
  have normIntTwo : normInt value = 2 := by
    rw [normInt_eq_natCast_normNat, diagonalNorm]
    rfl
  have realSmall : value.re * value.re < 4 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntTwo
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ = 2 := normIntTwo
      _ < 4 := by decide
  have imaginarySmall : value.im * value.im < 4 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntTwo
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ = 2 := normIntTwo
      _ < 4 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntTwo
  all_goals try cases normIntTwo
  · right
    right
    right
    rfl
  · right
    right
    left
    rfl
  · right
    left
    rfl
  · left
    rfl

theorem normNat_eq_two_of_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) : normNat value = 2 := by
  rcases diagonal with rfl | rfl | rfl | rfl <;> decide

/-- The Gaussian integers of quadrance four are the four doubled units. -/
theorem axisDouble_cases_of_normNat_eq_four {value : GaussianInt}
    (fourNorm : normNat value = 4) :
    value = ⟨2, 0⟩ ∨ value = ⟨-2, 0⟩ ∨
      value = ⟨0, 2⟩ ∨ value = ⟨0, -2⟩ := by
  have normIntFour : normInt value = 4 := by
    rw [normInt_eq_natCast_normNat, fourNorm]
    rfl
  have realSmall : value.re * value.re < 9 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntFour
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ = 4 := normIntFour
      _ < 9 := by decide
  have imaginarySmall : value.im * value.im < 9 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntFour
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ = 4 := normIntFour
      _ < 9 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 9 at realSmall
  change imaginary * imaginary < 9 at imaginarySmall
  rcases coordinate_cases_of_square_lt_nine realSmall with
      realNegativeTwo | realNegativeOne | realZero | realPositiveOne |
        realPositiveTwo <;>
    rcases coordinate_cases_of_square_lt_nine imaginarySmall with
      imaginaryNegativeTwo | imaginaryNegativeOne | imaginaryZero |
        imaginaryPositiveOne | imaginaryPositiveTwo
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntFour
  all_goals try cases normIntFour
  all_goals decide

/-- The Gaussian integers of quadrance eight are the four doubled
diagonals. -/
theorem doubledDiagonal_cases_of_normNat_eq_eight {value : GaussianInt}
    (eightNorm : normNat value = 8) :
    value = ⟨2, 2⟩ ∨ value = ⟨2, -2⟩ ∨
      value = ⟨-2, 2⟩ ∨ value = ⟨-2, -2⟩ := by
  have normIntEight : normInt value = 8 := by
    rw [normInt_eq_natCast_normNat, eightNorm]
    rfl
  have realSmall : value.re * value.re < 9 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntEight
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ = 8 := normIntEight
      _ < 9 := by decide
  have imaginarySmall : value.im * value.im < 9 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntEight
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ = 8 := normIntEight
      _ < 9 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 9 at realSmall
  change imaginary * imaginary < 9 at imaginarySmall
  rcases coordinate_cases_of_square_lt_nine realSmall with
      realNegativeTwo | realNegativeOne | realZero | realPositiveOne |
        realPositiveTwo <;>
    rcases coordinate_cases_of_square_lt_nine imaginarySmall with
      imaginaryNegativeTwo | imaginaryNegativeOne | imaginaryZero |
        imaginaryPositiveOne | imaginaryPositiveTwo
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntEight
  all_goals try cases normIntEight
  all_goals decide

/-- The eight Gaussian integers of quadrance five. -/
theorem normFive_cases_of_normNat_eq_five {value : GaussianInt}
    (fiveNorm : normNat value = 5) :
    value = ⟨2, 1⟩ ∨ value = ⟨2, -1⟩ ∨
      value = ⟨-2, 1⟩ ∨ value = ⟨-2, -1⟩ ∨
      value = ⟨1, 2⟩ ∨ value = ⟨1, -2⟩ ∨
      value = ⟨-1, 2⟩ ∨ value = ⟨-1, -2⟩ := by
  have normIntFive : normInt value = 5 := by
    rw [normInt_eq_natCast_normNat, fiveNorm]
    rfl
  have realSmall : value.re * value.re < 9 := by
    have imaginaryNonnegative := int_mul_self_nonneg value.im
    dsimp only [normInt] at normIntFive
    calc
      value.re * value.re ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_right imaginaryNonnegative
      _ = 5 := normIntFive
      _ < 9 := by decide
  have imaginarySmall : value.im * value.im < 9 := by
    have realNonnegative := int_mul_self_nonneg value.re
    dsimp only [normInt] at normIntFive
    calc
      value.im * value.im ≤
          value.re * value.re + value.im * value.im :=
        Int.le_add_of_nonneg_left realNonnegative
      _ = 5 := normIntFive
      _ < 9 := by decide
  rcases value with ⟨real, imaginary⟩
  change real * real < 9 at realSmall
  change imaginary * imaginary < 9 at imaginarySmall
  rcases coordinate_cases_of_square_lt_nine realSmall with
      realNegativeTwo | realNegativeOne | realZero | realPositiveOne |
        realPositiveTwo <;>
    rcases coordinate_cases_of_square_lt_nine imaginarySmall with
      imaginaryNegativeTwo | imaginaryNegativeOne | imaginaryZero |
        imaginaryPositiveOne | imaginaryPositiveTwo
  all_goals subst real; subst imaginary
  all_goals simp only [normInt] at normIntFive
  all_goals try cases normIntFive
  all_goals decide

/-- A quadrance-four Gaussian integer is a diagonal Gaussian integer times
any prescribed diagonal associate. -/
theorem exists_diagonal_right_factor_of_four_and_diagonal
    {value diagonal : GaussianInt} (valueNorm : normNat value = 4)
    (diagonalProperty : IsDiagonal diagonal) :
    ∃ factor, IsDiagonal factor ∧ value = diagonal * factor := by
  have valueCases := axisDouble_cases_of_normNat_eq_four valueNorm
  rcases diagonalProperty with diagonalCase | diagonalCase | diagonalCase |
      diagonalCase <;>
    rcases valueCases with valueCase | valueCase | valueCase | valueCase <;>
    subst diagonal <;> subst value
  all_goals first
    | exact ⟨⟨1, 1⟩, Or.inl rfl, by decide⟩
    | exact ⟨⟨1, -1⟩, Or.inr (Or.inl rfl), by decide⟩
    | exact ⟨⟨-1, 1⟩, Or.inr (Or.inr (Or.inl rfl)), by decide⟩
    | exact ⟨⟨-1, -1⟩, Or.inr (Or.inr (Or.inr rfl)), by decide⟩

theorem cornerTurn_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) : IsDiagonal (cornerTurn value) := by
  rcases diagonal with rfl | rfl | rfl | rfl
  · right; right; left; rfl
  · right; right; right; rfl
  · left; rfl
  · right; left; rfl

theorem conjugate_cornerTurn_eq_neg (value : GaussianInt) :
    conjugate (cornerTurn value) = -value := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [conjugate, cornerTurn,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im] ;
    ring1

theorem mul_cornerTurn_eq_neg_two_of_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) :
    value * cornerTurn value = -ofNat 2 := by
  rcases diagonal with rfl | rfl | rfl | rfl <;> decide

theorem conjugate_mul_self_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : conjugate value * value = 1 := by
  rcases unit with positive | negative | positiveImaginary | negativeImaginary
  · rw [positive]
    rfl
  · rw [negative]
    rfl
  · rw [positiveImaginary]
    rfl
  · rw [negativeImaginary]
    rfl

theorem self_mul_conjugate_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : value * conjugate value = 1 := by
  rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm]
  exact conjugate_mul_self_of_isGaussianUnit unit

theorem normSq_toGaussian_eq_one_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : normSq (toGaussian value) = 1 := by
  rcases unit with positive | negative | positiveImaginary | negativeImaginary
  · rw [positive, toGaussian_one, normSq_one]
  · rw [negative, toGaussian_neg,
      toGaussian_one, normSq_neg, normSq_one]
  · rw [positiveImaginary]
    rfl
  · rw [negativeImaginary, toGaussian_neg]
    rfl

private theorem one_isGaussianUnit : IsGaussianUnit 1 := Or.inl rfl

private theorem negOne_isGaussianUnit : IsGaussianUnit (-1) :=
  Or.inr (Or.inl rfl)

private theorem imaginaryUnit_isGaussianUnit :
    IsGaussianUnit imaginaryUnit := Or.inr (Or.inr (Or.inl rfl))

private theorem negImaginaryUnit_isGaussianUnit :
    IsGaussianUnit (-imaginaryUnit) := Or.inr (Or.inr (Or.inr rfl))

theorem exists_unit_right_factor_of_units {left right : GaussianInt}
    (leftUnit : IsGaussianUnit left) (rightUnit : IsGaussianUnit right) :
    ∃ unit, IsGaussianUnit unit ∧ left = right * unit := by
  let unit := conjugate right * left
  have unitNorm : normNat unit = 1 := by
    dsimp only [unit]
    rw [normNat_mul, normNat_conjugate]
    have leftNorm := normSq_toGaussian_eq_one_of_isGaussianUnit leftUnit
    have rightNorm := normSq_toGaussian_eq_one_of_isGaussianUnit rightUnit
    rw [normSq_toGaussian] at leftNorm rightNorm
    have leftNormNat : normNat left = 1 :=
      RFAP.ConstructiveFraction.natCast_injective_direct leftNorm
    have rightNormNat : normNat right = 1 :=
      RFAP.ConstructiveFraction.natCast_injective_direct rightNorm
    rw [leftNormNat, rightNormNat]
  refine ⟨unit, isGaussianUnit_of_normNat_eq_one unitNorm, ?_⟩
  dsimp only [unit]
  calc
    left = 1 * left :=
      (RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul left).symm
    _ = (right * conjugate right) * left := by
      rw [self_mul_conjugate_of_isGaussianUnit rightUnit]
    _ = right * (conjugate right * left) :=
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_assoc _ _ _

theorem exists_unit_right_factor_of_diagonals {left right : GaussianInt}
    (leftDiagonal : IsDiagonal left) (rightDiagonal : IsDiagonal right) :
    ∃ unit, IsGaussianUnit unit ∧ left = right * unit := by
  rcases leftDiagonal with rfl | rfl | rfl | rfl <;>
    rcases rightDiagonal with rfl | rfl | rfl | rfl
  · exact ⟨1, one_isGaussianUnit, rfl⟩
  · exact ⟨imaginaryUnit, imaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨-imaginaryUnit, negImaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨-1, negOne_isGaussianUnit, rfl⟩
  · exact ⟨-imaginaryUnit, negImaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨1, one_isGaussianUnit, rfl⟩
  · exact ⟨-1, negOne_isGaussianUnit, rfl⟩
  · exact ⟨imaginaryUnit, imaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨imaginaryUnit, imaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨-1, negOne_isGaussianUnit, rfl⟩
  · exact ⟨1, one_isGaussianUnit, rfl⟩
  · exact ⟨-imaginaryUnit, negImaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨-1, negOne_isGaussianUnit, rfl⟩
  · exact ⟨-imaginaryUnit, negImaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨imaginaryUnit, imaginaryUnit_isGaussianUnit, rfl⟩
  · exact ⟨1, one_isGaussianUnit, rfl⟩

theorem normSq_sub_comm (left right : Gaussian) :
    normSq (left - right) = normSq (right - left) := by
  simp only [normSq,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im]
  ring1

/-- A Gaussian value of quadrance at least four remains at quadrance at
least one from every embedded Gaussian unit. -/
theorem one_le_normSq_sub_unit_of_four_le {value : Gaussian}
    {unit : GaussianInt} (unitProperty : IsGaussianUnit unit)
    (large : 4 ≤ normSq value) :
    1 ≤ normSq (value - toGaussian unit) := by
  let dot : Coordinate :=
    value.re * (toGaussian unit).re + value.im * (toGaussian unit).im
  have unitNorm := normSq_toGaussian_eq_one_of_isGaussianUnit unitProperty
  have valueNonnegative := normSq_nonneg value
  have dotCauchy : dot ^ 2 ≤ normSq value := by
    have squareNonnegative :
        0 ≤
          (value.re * (toGaussian unit).im -
            value.im * (toGaussian unit).re) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    have differenceNonnegative :
        0 ≤ normSq value * normSq (toGaussian unit) - dot ^ 2 := by
      calc
        0 ≤
            (value.re * (toGaussian unit).im -
              value.im * (toGaussian unit).re) ^ 2 := squareNonnegative
        _ = normSq value * normSq (toGaussian unit) - dot ^ 2 := by
          dsimp only [dot]
          simp only [normSq]
          ring1
    rw [unitNorm] at differenceNonnegative
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      differenceNonnegative (dot ^ 2)
    calc
      dot ^ 2 = 0 + dot ^ 2 := by ring1
      _ ≤ (normSq value * 1 - dot ^ 2) + dot ^ 2 := shifted
      _ = normSq value := by ring1
  have twiceDotLe : 2 * dot ≤ normSq value := by
    by_cases dotNonpositive : dot ≤ 0
    · have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotNonpositive (show (0 : Coordinate) ≤ 2 by decide)
      calc
        2 * dot ≤ 2 * 0 := scaled
        _ = 0 := by ring1
        _ ≤ normSq value := valueNonnegative
    · have fourDotSquares : 4 * dot ^ 2 ≤ 4 * normSq value :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotCauchy (show (0 : Coordinate) ≤ 4 by decide)
      have fourNormLeSquare :
          4 * normSq value ≤ normSq value * normSq value :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          large valueNonnegative
      have squares : (2 * dot) ^ 2 ≤ normSq value ^ 2 := by
        calc
          (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
          _ ≤ 4 * normSq value := fourDotSquares
          _ ≤ normSq value * normSq value := fourNormLeSquare
          _ = normSq value ^ 2 := by ring1
      exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
        valueNonnegative squares
  have gap : 0 ≤ normSq value - 2 * dot :=
    RFAP.ConstructiveFraction.sub_nonneg_direct twiceDotLe
  calc
    1 ≤ (normSq value - 2 * dot) + 1 := le_add_of_nonneg_left gap
    _ = normSq value + 1 - 2 * dot := by ring1
    _ = normSq value + normSq (toGaussian unit) - 2 * dot := by
      rw [unitNorm]
    _ = normSq (value - toGaussian unit) := by
      dsimp only [dot]
      simp only [normSq,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im]
      ring1

private theorem twice_le_one_of_lt_half {value : Coordinate}
    (upper : value < 1 / 2) : 2 * value ≤ 1 := by
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    upper.le (show (0 : Coordinate) ≤ 2 by decide)
  calc
    2 * value ≤ 2 * (1 / 2 : Coordinate) := scaled
    _ = 1 := by decide

private theorem neg_one_le_twice_of_neg_half_le {value : Coordinate}
    (lower : -(1 / 2 : Coordinate) ≤ value) : -1 ≤ 2 * value := by
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    lower (show (0 : Coordinate) ≤ 2 by decide)
  calc
    (-1 : Coordinate) = 2 * (-(1 / 2 : Coordinate)) := by decide
    _ ≤ 2 * value := scaled

private theorem one_sub_twice_nonneg_of_lt_half {value : Coordinate}
    (upper : value < 1 / 2) : 0 ≤ 1 - 2 * value :=
  RFAP.ConstructiveFraction.sub_nonneg_direct
    (twice_le_one_of_lt_half upper)

private theorem one_add_twice_nonneg_of_neg_half_le {value : Coordinate}
    (lower : -(1 / 2 : Coordinate) ≤ value) : 0 ≤ 1 + 2 * value := by
  have translated := RFAP.ConstructiveFraction.add_le_add_right_direct
    (neg_one_le_twice_of_neg_half_le lower) 1
  calc
    0 = (-1 : Coordinate) + 1 := by ring1
    _ ≤ 2 * value + 1 := translated
    _ = 1 + 2 * value := by ring1

/-- A residual in the selected half-open square is no nearer to the inverse
of a Gaussian unit than it is to zero.  This is Lakein's elementary unit
exterior law with no square roots. -/
theorem residual_normSq_le_unit_mul_sub_one (fraction : Fraction)
    {unit : GaussianInt} (unitProperty : IsGaussianUnit unit) :
    normSq (residual fraction) ≤
      normSq (toGaussian unit * residual fraction - 1) := by
  have square := RFAP.HurwitzNearest.remainder_mem fraction.value
  rcases unitProperty with positive | negative |
      positiveImaginary | negativeImaginary
  · rw [positive, toGaussian_one,
      RFAP.ConstructiveGaussian.Gaussian.one_mul]
    have gap : 0 ≤ 1 - 2 * (residual fraction).re :=
      RFAP.ConstructiveFraction.sub_nonneg_direct
        (twice_le_one_of_lt_half square.2.1)
    calc
      normSq (residual fraction) ≤
          normSq (residual fraction) +
            (1 - 2 * (residual fraction).re) :=
        le_add_of_nonneg_right gap
      _ = normSq (residual fraction - 1) := by
        simp only [normSq,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
        ring1
  · rw [negative, toGaussian_neg, toGaussian_one]
    have gap : 0 ≤ 1 + 2 * (residual fraction).re := by
      have lower := neg_one_le_twice_of_neg_half_le square.1
      have translated := RFAP.ConstructiveFraction.add_le_add_right_direct
        lower 1
      calc
        0 = (-1 : Coordinate) + 1 := by ring1
        _ ≤ 2 * (residual fraction).re + 1 := translated
        _ = 1 + 2 * (residual fraction).re := by ring1
    calc
      normSq (residual fraction) ≤
          normSq (residual fraction) +
            (1 + 2 * (residual fraction).re) :=
        le_add_of_nonneg_right gap
      _ = normSq (-1 * residual fraction - 1) := by
        simp only [normSq,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
        ring1
  · rw [positiveImaginary]
    have gap : 0 ≤ 1 + 2 * (residual fraction).im := by
      have lower := neg_one_le_twice_of_neg_half_le square.2.2.1
      have translated := RFAP.ConstructiveFraction.add_le_add_right_direct
        lower 1
      calc
        0 = (-1 : Coordinate) + 1 := by ring1
        _ ≤ 2 * (residual fraction).im + 1 := translated
        _ = 1 + 2 * (residual fraction).im := by ring1
    calc
      normSq (residual fraction) ≤
          normSq (residual fraction) +
            (1 + 2 * (residual fraction).im) :=
        le_add_of_nonneg_right gap
      _ = normSq
          (toGaussian imaginaryUnit * residual fraction - 1) := by
        simp only [normSq, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          Int.cast_zero, Int.cast_one]
        ring1
  · rw [negativeImaginary, toGaussian_neg]
    have gap : 0 ≤ 1 - 2 * (residual fraction).im :=
      RFAP.ConstructiveFraction.sub_nonneg_direct
        (twice_le_one_of_lt_half square.2.2.2)
    calc
      normSq (residual fraction) ≤
          normSq (residual fraction) +
            (1 - 2 * (residual fraction).im) :=
        le_add_of_nonneg_right gap
      _ = normSq
          (-toGaussian imaginaryUnit * residual fraction - 1) := by
        simp only [normSq, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          Int.cast_zero, Int.cast_one]
        ring1

/-- Every next complete quotient lies in the closed exterior of the unit
disc about each Gaussian unit. -/
theorem one_le_next_sub_unit_normSq (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) {unit : GaussianInt}
    (unitProperty : IsGaussianUnit unit) :
    1 ≤ normSq ((next fraction nonterminal).value - toGaussian unit) := by
  have residualNonzero := residual_ne_zero nonterminal
  have residualNormPositive : 0 < normSq (residual fraction) :=
    normSq_pos residualNonzero
  have reciprocal :
      (next fraction nonterminal).value * residual fraction = 1 := by
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  have factorIdentity :
      ((next fraction nonterminal).value - toGaussian unit) *
          residual fraction =
        -(toGaussian unit * residual fraction - 1) := by
    calc
      ((next fraction nonterminal).value - toGaussian unit) *
            residual fraction =
          (next fraction nonterminal).value * residual fraction -
            toGaussian unit * residual fraction := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = 1 - toGaussian unit * residual fraction := by rw [reciprocal]
      _ = -(toGaussian unit * residual fraction - 1) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.neg_re,
            RFAP.ConstructiveGaussian.Gaussian.neg_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
  have productExterior :
      1 * normSq (residual fraction) ≤
        normSq ((next fraction nonterminal).value - toGaussian unit) *
          normSq (residual fraction) := by
    calc
      1 * normSq (residual fraction) = normSq (residual fraction) := by ring1
      _ ≤ normSq (toGaussian unit * residual fraction - 1) :=
        residual_normSq_le_unit_mul_sub_one fraction unitProperty
      _ = normSq
          (((next fraction nonterminal).value - toGaussian unit) *
            residual fraction) := by
        rw [factorIdentity, normSq_neg]
      _ = normSq ((next fraction nonterminal).value - toGaussian unit) *
          normSq (residual fraction) := normSq_mul _ _
  exact RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    productExterior residualNormPositive

/-- A strict corner approach by the next complete quotient becomes the
corresponding strict corner approach by the current residual. -/
theorem residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    {corner : GaussianInt} (cornerDiagonal : IsDiagonal corner)
    (nextCloser :
      normSq ((next fraction nonterminal).value - toGaussian corner) < 1) :
    normSq (residual fraction + toGaussian (cornerTurn corner)) < 1 := by
  have residualNonzero := residual_ne_zero nonterminal
  have residualPositive : 0 < normSq (residual fraction) :=
    normSq_pos residualNonzero
  have reciprocal :
      (next fraction nonterminal).value * residual fraction = 1 := by
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  have factorIdentity :
      ((next fraction nonterminal).value - toGaussian corner) *
          residual fraction =
        1 - toGaussian corner * residual fraction := by
    calc
      ((next fraction nonterminal).value - toGaussian corner) *
            residual fraction =
          (next fraction nonterminal).value * residual fraction -
            toGaussian corner * residual fraction := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = 1 - toGaussian corner * residual fraction := by rw [reciprocal]
  have scaledCloser :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      nextCloser residualPositive
  have transformedCloser :
      normSq (1 - toGaussian corner * residual fraction) <
        normSq (residual fraction) := by
    calc
      normSq (1 - toGaussian corner * residual fraction) =
          normSq
            (((next fraction nonterminal).value - toGaussian corner) *
              residual fraction) := by rw [factorIdentity]
      _ = normSq ((next fraction nonterminal).value - toGaussian corner) *
          normSq (residual fraction) := normSq_mul _ _
      _ < 1 * normSq (residual fraction) := scaledCloser
      _ = normSq (residual fraction) := by ring1
  have differenceIdentity :
      normSq (1 - toGaussian corner * residual fraction) -
          normSq (residual fraction) =
        normSq (residual fraction + toGaussian (cornerTurn corner)) - 1 := by
    rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
      simp only [cornerTurn, conjugate, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.normSq,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
        Int.cast_neg, Int.cast_one] <;>
      ring1
  have negativeDifference :
      normSq (1 - toGaussian corner * residual fraction) -
          normSq (residual fraction) < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct transformedCloser
  rw [differenceIdentity] at negativeDifference
  exact RFAP.ConstructiveFraction.lt_of_sub_neg_direct negativeDifference

/-- The two discs used in one backward Lakein step have the same signed
quadrance difference. -/
theorem corner_norm_difference_identity {corner : GaussianInt}
    (cornerDiagonal : IsDiagonal corner) (value base : Gaussian) :
    normSq value - normSq (toGaussian corner * value + base) =
      normSq base -
        normSq (value - toGaussian (cornerTurn corner) * base) := by
  rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
    simp only [cornerTurn, conjugate, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.normSq,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      Int.cast_neg, Int.cast_one] <;>
    ring1

/-- A corner non-growth condition for `a q + q₋` is equivalently a unit
disc condition for `(a-cornerTurn s) q + q₋`. -/
theorem corner_combination_norm_le_iff {corner : GaussianInt}
    (cornerDiagonal : IsDiagonal corner)
    (coefficient current previous : GaussianInt) :
    normNat
          (corner * (coefficient * current + previous) + current) ≤
        normNat (coefficient * current + previous) ↔
      normNat
          ((coefficient - cornerTurn corner) * current + previous) ≤
        normNat current := by
  have transformedIdentity :
      toGaussian ((coefficient - cornerTurn corner) * current + previous) =
        toGaussian (coefficient * current + previous) -
          toGaussian (cornerTurn corner) * toGaussian current := by
    simp only [toGaussian_add, toGaussian_mul, toGaussian_sub]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  have cornerIdentity :
      toGaussian
          (corner * (coefficient * current + previous) + current) =
        toGaussian corner *
            toGaussian (coefficient * current + previous) +
          toGaussian current := by
    rw [toGaussian_add, toGaussian_mul]
  have differenceIdentity := corner_norm_difference_identity
    cornerDiagonal (toGaussian (coefficient * current + previous))
      (toGaussian current)
  rw [← cornerIdentity, ← transformedIdentity,
    normSq_toGaussian, normSq_toGaussian,
    normSq_toGaussian, normSq_toGaussian] at differenceIdentity
  constructor
  · intro original
    have originalCast := RFAP.ConstructiveFraction.natCast_le_direct original
    have originalGap :
        0 ≤
          (normNat (coefficient * current + previous) : Coordinate) -
            (normNat
              (corner * (coefficient * current + previous) + current) :
                Coordinate) :=
      RFAP.ConstructiveFraction.sub_nonneg_direct originalCast
    rw [differenceIdentity] at originalGap
    exact (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
      (sub_nonneg.mp originalGap)
  · intro transformed
    have transformedCast := RFAP.ConstructiveFraction.natCast_le_direct transformed
    have transformedGap :
        0 ≤ (normNat current : Coordinate) -
          (normNat
            ((coefficient - cornerTurn corner) * current + previous) :
              Coordinate) :=
      RFAP.ConstructiveFraction.sub_nonneg_direct transformedCast
    rw [← differenceIdentity] at transformedGap
    exact (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
      (sub_nonneg.mp transformedGap)

/-- The finite corner calculation which rules out every diagonal difference
except the one continuing the backward succession. -/
theorem diagonal_eq_cornerTurn_of_local_geometry
    (rho : Gaussian) (rhoSquare : RFAP.HurwitzNearest.InFundamentalSquare rho)
    (rhoNorm : normSq rho ≤ 1 / 2)
    {corner difference : GaussianInt}
    (cornerDiagonal : IsDiagonal corner)
    (differenceDiagonal : IsDiagonal difference)
    (cornerApproach :
      normSq (rho + toGaussian (cornerTurn corner)) < 1)
    (completeLower :
      2 ≤ normSq (toGaussian (difference + cornerTurn corner) + rho))
    (unitExterior : ∀ unit, IsGaussianUnit unit →
      1 ≤ normSq
        (toGaussian (difference + cornerTurn corner) + rho -
          toGaussian unit)) :
    difference = cornerTurn corner := by
  have zeroImpossible
      (sumZero : difference + cornerTurn corner = 0) : False := by
    have lower : 2 ≤ normSq rho := by
      calc
        2 ≤ normSq (toGaussian (difference + cornerTurn corner) + rho) :=
          completeLower
        _ = normSq rho := by
          rw [sumZero, toGaussian_zero,
            RFAP.ConstructiveGaussian.Gaussian.zero_add]
    exact (not_lt_of_ge lower
      (rhoNorm.trans_lt (show (1 / 2 : Coordinate) < 2 by decide)))
  have unitImpossible (unit : GaussianInt)
      (unitProperty : IsGaussianUnit unit)
      (sumTwice : difference + cornerTurn corner = unit + unit)
      (comparison :
        normSq (rho + toGaussian unit) ≤
          normSq (rho + toGaussian (cornerTurn corner))) : False := by
    have exterior := unitExterior unit unitProperty
    have valueDifference :
        toGaussian (difference + cornerTurn corner) + rho - toGaussian unit =
          rho + toGaussian unit := by
      rw [sumTwice, toGaussian_add]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
        ring1

    rw [valueDifference] at exterior
    exact (not_lt_of_ge exterior (comparison.trans_lt cornerApproach))
  rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
    rcases differenceDiagonal with rfl | rfl | rfl | rfl
  · apply False.elim
    apply (unitImpossible imaginaryUnit imaginaryUnit_isGaussianUnit (by decide))
    have gap := one_sub_twice_nonneg_of_lt_half rhoSquare.2.1
    calc
      normSq (rho + toGaussian imaginaryUnit) ≤
          normSq (rho + toGaussian imaginaryUnit) +
            (1 - 2 * rho.re) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨1, 1⟩)) := by
        simp only [cornerTurn, conjugate, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · rfl
  · apply False.elim
    apply (unitImpossible (-1) negOne_isGaussianUnit (by decide))
    have gap := one_add_twice_nonneg_of_neg_half_le rhoSquare.2.2.1
    calc
      normSq (rho + toGaussian (-1)) ≤
          normSq (rho + toGaussian (-1)) +
            (1 + 2 * rho.im) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨1, 1⟩)) := by
        simp only [cornerTurn, conjugate, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible (-imaginaryUnit)
      negImaginaryUnit_isGaussianUnit (by decide))
    have gap := one_sub_twice_nonneg_of_lt_half rhoSquare.2.1
    calc
      normSq (rho + toGaussian (-imaginaryUnit)) ≤
          normSq (rho + toGaussian (-imaginaryUnit)) +
            (1 - 2 * rho.re) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨1, -1⟩)) := by
        simp only [cornerTurn, conjugate, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  · apply False.elim
    apply (unitImpossible (-1) negOne_isGaussianUnit (by decide))
    have gap := one_sub_twice_nonneg_of_lt_half rhoSquare.2.2.2
    calc
      normSq (rho + toGaussian (-1)) ≤
          normSq (rho + toGaussian (-1)) +
            (1 - 2 * rho.im) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨1, -1⟩)) := by
        simp only [cornerTurn, conjugate, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one]
        ring1
  · rfl
  · rfl
  · apply False.elim
    apply (unitImpossible 1 one_isGaussianUnit (by decide))
    have gap := one_add_twice_nonneg_of_neg_half_le rhoSquare.2.2.1
    calc
      normSq (rho + toGaussian 1) ≤
          normSq (rho + toGaussian 1) +
            (1 + 2 * rho.im) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨-1, 1⟩)) := by
        simp only [cornerTurn, conjugate, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one]
        ring1
  · apply False.elim
    apply (unitImpossible imaginaryUnit imaginaryUnit_isGaussianUnit
      (by decide))
    have gap := one_add_twice_nonneg_of_neg_half_le rhoSquare.1
    calc
      normSq (rho + toGaussian imaginaryUnit) ≤
          normSq (rho + toGaussian imaginaryUnit) +
            (1 + 2 * rho.re) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨-1, 1⟩)) := by
        simp only [cornerTurn, conjugate, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible 1 one_isGaussianUnit (by decide))
    have gap := one_sub_twice_nonneg_of_lt_half rhoSquare.2.2.2
    calc
      normSq (rho + toGaussian 1) ≤
          normSq (rho + toGaussian 1) +
            (1 - 2 * rho.im) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨-1, -1⟩)) := by
        simp only [cornerTurn, conjugate, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one]
        ring1
  · rfl
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible (-imaginaryUnit)
      negImaginaryUnit_isGaussianUnit (by decide))
    have gap := one_add_twice_nonneg_of_neg_half_le rhoSquare.1
    calc
      normSq (rho + toGaussian (-imaginaryUnit)) ≤
          normSq (rho + toGaussian (-imaginaryUnit)) +
            (1 + 2 * rho.re) := le_add_of_nonneg_right gap
      _ = normSq (rho + toGaussian (cornerTurn ⟨-1, -1⟩)) := by
        simp only [cornerTurn, conjugate, imaginaryUnit, toGaussian,
          RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1

/-- Multiplying a unit-centred exterior factor by any nonzero integral
associate preserves the quadrance-one lower bound. -/
theorem one_le_associated_factor_normSq (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) (s t unit : GaussianInt)
    (unitProperty : IsGaussianUnit unit) (associated : s = t * unit)
    (oneLeMultiplierNorm : 1 ≤ normNat t) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next fraction nonterminal).value) := by
  have factorIdentity :
      toGaussian s -
          toGaussian t * (next fraction nonterminal).value =
        toGaussian t *
          (toGaussian unit - (next fraction nonterminal).value) := by
    rw [associated, toGaussian_mul]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  have multiplierCast :
      (1 : Coordinate) ≤ (normNat t : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct oneLeMultiplierNorm
  have unitExterior :
      1 ≤ normSq
        (toGaussian unit - (next fraction nonterminal).value) := by
    rw [normSq_sub_comm]
    exact one_le_next_sub_unit_normSq fraction nonterminal unitProperty
  have productExterior := RFAP.ConstructiveFraction.mul_le_mul_direct
    multiplierCast unitExterior (show (0 : Coordinate) ≤ 1 by decide)
    (show (0 : Coordinate) ≤ (normNat t : Coordinate) by
      exact RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _))
  rw [factorIdentity, normSq_mul, normSq_toGaussian]
  calc
    1 = (1 : Coordinate) * 1 := by ring1
    _ ≤ (normNat t : Coordinate) *
        normSq (toGaussian unit - (next fraction nonterminal).value) :=
      productExterior

theorem one_le_factor_normSq_of_unit_coefficients (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) {s t : GaussianInt}
    (sNorm : normNat s = 1) (tNorm : normNat t = 1) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next fraction nonterminal).value) := by
  have sUnit := isGaussianUnit_of_normNat_eq_one sNorm
  have tUnit := isGaussianUnit_of_normNat_eq_one tNorm
  rcases exists_unit_right_factor_of_units sUnit tUnit with
    ⟨unit, unitProperty, associated⟩
  apply one_le_associated_factor_normSq fraction nonterminal s t unit
    unitProperty associated
  rw [tNorm]

theorem one_le_factor_normSq_of_diagonal_coefficients (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) {s t : GaussianInt}
    (sNorm : normNat s = 2) (tNorm : normNat t = 2) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next fraction nonterminal).value) := by
  have sDiagonal := isDiagonal_of_normNat_eq_two sNorm
  have tDiagonal := isDiagonal_of_normNat_eq_two tNorm
  rcases exists_unit_right_factor_of_diagonals sDiagonal tDiagonal with
    ⟨unit, unitProperty, associated⟩
  apply one_le_associated_factor_normSq fraction nonterminal s t unit
    unitProperty associated
  rw [tNorm]
  decide

/-- The next complete quotient has quadrance at least two.  This is just the
reciprocal of a nonzero residual of quadrance at most one half. -/
theorem next_normSq_ge_two (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) :
    2 ≤ normSq (next fraction nonterminal).value := by
  have residualNonzero := residual_ne_zero nonterminal
  have reciprocal :
      (next fraction nonterminal).value * residual fraction = 1 := by
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  have productIdentity :
      normSq (next fraction nonterminal).value *
          normSq (residual fraction) = 1 := by
    rw [← normSq_mul, reciprocal, normSq_one]
  have nextPositive : 0 < normSq (next fraction nonterminal).value :=
    normSq_pos (fun zero => by
      have productZero := congrArg
        (fun value => value * residual fraction) zero
      rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.zero_mul] at productZero
      exact (show (1 : Gaussian) ≠ 0 by decide) productZero)
  have scaledResidual :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (RFAP.HurwitzNearest.remainder_normSq_le_half fraction.value)
      nextPositive.le
  have oneLeHalf :
      1 ≤ normSq (next fraction nonterminal).value * (1 / 2) := by
    calc
      1 = normSq (next fraction nonterminal).value *
          normSq (residual fraction) := productIdentity.symm
      _ ≤ normSq (next fraction nonterminal).value * (1 / 2) :=
        scaledResidual
  have doubled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct oneLeHalf
      (show (0 : Coordinate) ≤ 2 by decide)
  calc
    2 = 1 * 2 := by ring1
    _ ≤ (normSq (next fraction nonterminal).value * (1 / 2)) * 2 :=
      doubled
    _ = normSq (next fraction nonterminal).value * 1 := by
      rw [_root_.mul_assoc,
        show (1 / 2 : Coordinate) * 2 = 1 by decide]
    _ = normSq (next fraction nonterminal).value := by ring1

/-- A noninitial Hurwitz partial quotient cannot be zero or a Gaussian unit. -/
theorem two_le_next_digit_normNat (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) :
    2 ≤ normNat (digit (next fraction nonterminal)) := by
  apply Nat.le_of_not_gt
  intro digitSmall
  have zeroOrOne : normNat (digit (next fraction nonterminal)) = 0 ∨
      normNat (digit (next fraction nonterminal)) = 1 := by
    generalize normEquality :
      normNat (digit (next fraction nonterminal)) = norm
    cases norm with
    | zero => exact Or.inl rfl
    | succ remaining =>
        cases remaining with
        | zero => exact Or.inr rfl
        | succ tail =>
            rw [normEquality] at digitSmall
            have twoLe : 2 ≤ Nat.succ (Nat.succ tail) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le tail))
            exact (Nat.not_lt_of_ge twoLe digitSmall).elim
  rcases zeroOrOne with zeroNorm | unitNorm
  · have digitZero := eq_zero_of_normNat_eq_zero zeroNorm
    have valueResidual : (next fraction nonterminal).value =
        residual (next fraction nonterminal) := by
      calc
        (next fraction nonterminal).value =
            toGaussian (digit (next fraction nonterminal)) +
              residual (next fraction nonterminal) :=
          value_eq_digit_add_residual (next fraction nonterminal)
        _ = residual (next fraction nonterminal) := by
          rw [digitZero, toGaussian_zero,
            RFAP.ConstructiveGaussian.Gaussian.zero_add]
    have lower := next_normSq_ge_two fraction nonterminal
    have upper :=
      RFAP.HurwitzNearest.remainder_normSq_le_half
        (next fraction nonterminal).value
    rw [valueResidual] at lower
    exact (not_lt_of_ge lower
      (upper.trans_lt (show (1 / 2 : Coordinate) < 2 by decide)))
  · have digitUnit := isGaussianUnit_of_normNat_eq_one unitNorm
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal digitUnit
    have differenceResidual :
        (next fraction nonterminal).value -
            toGaussian (digit (next fraction nonterminal)) =
          residual (next fraction nonterminal) := by
      rw [value_eq_digit_add_residual]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
        ring1
    rw [differenceResidual] at exterior
    have upper :=
      RFAP.HurwitzNearest.remainder_normSq_le_half
        (next fraction nonterminal).value
    exact (not_lt_of_ge exterior
      (upper.trans_lt (show (1 / 2 : Coordinate) < 1 by decide)))

/-- If adding an integral multiple of a shorter previous denominator does
not increase quadrance, that multiplier has quadrance below four. -/
theorem coefficient_normNat_lt_four_of_combination_norm_le
    (coefficient current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    (combinationNotLarger :
      normNat (coefficient * current + previous) ≤ normNat current) :
    normNat coefficient < 4 := by
  have currentPositiveNat : 0 < normNat current :=
    (Nat.zero_le (normNat previous)).trans_lt previousShorter
  have currentPositive :
      (0 : Coordinate) < (normNat current : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct currentPositiveNat
  have previousCastShorter :
      (normNat previous : Coordinate) < (normNat current : Coordinate) :=
    (RFAP.ConstructiveFraction.natCast_lt_iff_direct).2 previousShorter
  have combinationCastNotLarger :
      (normNat (coefficient * current + previous) : Coordinate) ≤
        (normNat current : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct combinationNotLarger
  have coefficientDifference :
      toGaussian (coefficient * current) =
        toGaussian (coefficient * current + previous) - toGaussian previous := by
    rw [toGaussian_add]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
      ring1
  have normBound :
      (normNat coefficient : Coordinate) * (normNat current : Coordinate) ≤
        2 *
          ((normNat (coefficient * current + previous) : Coordinate) +
            (normNat previous : Coordinate)) := by
    calc
      (normNat coefficient : Coordinate) * (normNat current : Coordinate) =
          normSq (toGaussian (coefficient * current)) := by
        rw [normSq_toGaussian, normNat_mul, Nat.cast_mul]
      _ = normSq
          (toGaussian (coefficient * current + previous) -
            toGaussian previous) := by rw [coefficientDifference]
      _ ≤ 2 *
          (normSq (toGaussian (coefficient * current + previous)) +
            normSq (toGaussian previous)) := normSq_sub_le_two _ _
      _ = 2 *
          ((normNat (coefficient * current + previous) : Coordinate) +
            (normNat previous : Coordinate)) := by
        rw [normSq_toGaussian, normSq_toGaussian]
  have sumStrict :
      (normNat (coefficient * current + previous) : Coordinate) +
          (normNat previous : Coordinate) <
        2 * (normNat current : Coordinate) := by
    have firstLeg := RFAP.ConstructiveFraction.add_le_add_right_direct
      combinationCastNotLarger (normNat previous : Coordinate)
    have secondLeg := RFAP.ConstructiveFraction.add_lt_add_right_direct
      previousCastShorter (normNat current : Coordinate)
    have secondLegOrdered :
        (normNat current : Coordinate) + (normNat previous : Coordinate) <
          (normNat current : Coordinate) + (normNat current : Coordinate) := by
      calc
        (normNat current : Coordinate) + (normNat previous : Coordinate) =
            (normNat previous : Coordinate) +
              (normNat current : Coordinate) := by ring1
        _ < (normNat current : Coordinate) +
            (normNat current : Coordinate) := secondLeg
    calc
      (normNat (coefficient * current + previous) : Coordinate) +
          (normNat previous : Coordinate) <
        (normNat current : Coordinate) +
          (normNat current : Coordinate) := firstLeg.trans_lt secondLegOrdered
      _ = 2 * (normNat current : Coordinate) := by ring1
  have scaledStrict :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) sumStrict
  have productStrict :
      (normNat coefficient : Coordinate) * (normNat current : Coordinate) <
        4 * (normNat current : Coordinate) := by
    exact normBound.trans_lt (by
      calc
        2 *
            ((normNat (coefficient * current + previous) : Coordinate) +
              (normNat previous : Coordinate)) <
          2 * (2 * (normNat current : Coordinate)) := scaledStrict
        _ = 4 * (normNat current : Coordinate) := by ring1)
  have coefficientCastSmall :
      (normNat coefficient : Coordinate) < 4 :=
    RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      productStrict currentPositive
  exact (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1 coefficientCastSmall

/-- With a diagonal coefficient on the previous denominator, a strictly
shorter combination forces the current coefficient to have quadrance below
six.  This is the square-root-free triangle estimate used before the two
exceptional lattice shapes are analysed. -/
theorem currentCoefficient_normNat_lt_six_of_diagonal_previous
    (s t current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    (tNorm : normNat t = 2)
    (combinationShorter :
      normNat (s * current + t * previous) < normNat current) :
    normNat s < 6 := by
  have currentPositiveNat : 0 < normNat current :=
    (Nat.zero_le (normNat previous)).trans_lt previousShorter
  have currentPositive :
      (0 : Coordinate) < (normNat current : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct currentPositiveNat
  have previousCastShorter :
      (normNat previous : Coordinate) < (normNat current : Coordinate) :=
    (RFAP.ConstructiveFraction.natCast_lt_iff_direct).2 previousShorter
  have combinationCastShorter :
      (normNat (s * current + t * previous) : Coordinate) <
        (normNat current : Coordinate) :=
    (RFAP.ConstructiveFraction.natCast_lt_iff_direct).2 combinationShorter
  have coefficientDifference :
      toGaussian (s * current) =
        toGaussian (s * current + t * previous) -
          toGaussian (t * previous) := by
    rw [toGaussian_add]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
      ring1
  have normBound :
      (normNat s : Coordinate) * (normNat current : Coordinate) ≤
        2 *
          ((normNat (s * current + t * previous) : Coordinate) +
            2 * (normNat previous : Coordinate)) := by
    calc
      (normNat s : Coordinate) * (normNat current : Coordinate) =
          normSq (toGaussian (s * current)) := by
        rw [normSq_toGaussian, normNat_mul, Nat.cast_mul]
      _ = normSq
          (toGaussian (s * current + t * previous) -
            toGaussian (t * previous)) := by rw [coefficientDifference]
      _ ≤ 2 *
          (normSq (toGaussian (s * current + t * previous)) +
            normSq (toGaussian (t * previous))) :=
        normSq_sub_le_two _ _
      _ = 2 *
          ((normNat (s * current + t * previous) : Coordinate) +
            2 * (normNat previous : Coordinate)) := by
        rw [normSq_toGaussian, normSq_toGaussian, normNat_mul, tNorm,
          Nat.cast_mul, Nat.cast_ofNat]
  have twicePreviousShorter :
      2 * (normNat previous : Coordinate) <
        2 * (normNat current : Coordinate) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) previousCastShorter
  have sumStrict :
      (normNat (s * current + t * previous) : Coordinate) +
          2 * (normNat previous : Coordinate) <
        3 * (normNat current : Coordinate) := by
    have sum := RFAP.ConstructiveFraction.add_lt_add_direct
      combinationCastShorter twicePreviousShorter
    calc
      (normNat (s * current + t * previous) : Coordinate) +
            2 * (normNat previous : Coordinate) <
          (normNat current : Coordinate) +
            2 * (normNat current : Coordinate) := sum
      _ = 3 * (normNat current : Coordinate) := by ring1
  have scaledStrict :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) sumStrict
  have productStrict :
      (normNat s : Coordinate) * (normNat current : Coordinate) <
        6 * (normNat current : Coordinate) := by
    exact normBound.trans_lt (by
      calc
        2 *
              ((normNat (s * current + t * previous) : Coordinate) +
                2 * (normNat previous : Coordinate)) <
            2 * (3 * (normNat current : Coordinate)) := scaledStrict
        _ = 6 * (normNat current : Coordinate) := by ring1)
  have coefficientCastSmall : (normNat s : Coordinate) < 6 :=
    RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      productStrict currentPositive
  exact (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1
    coefficientCastSmall

/-- The only possible noninitial digit in a non-growing continuant step is
a diagonal digit. -/
theorem next_digit_isDiagonal_of_combination_norm_le
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    (combinationNotLarger :
      normNat (digit (next fraction nonterminal) * current + previous) ≤
        normNat current) :
    IsDiagonal (digit (next fraction nonterminal)) := by
  have digitSmall := coefficient_normNat_lt_four_of_combination_norm_le
    (digit (next fraction nonterminal)) current previous
    previousShorter combinationNotLarger
  have digitAtLeastTwo := two_le_next_digit_normNat fraction nonterminal
  have digitCases := normNat_eq_zero_or_one_or_two_of_lt_four
    (digit (next fraction nonterminal)) digitSmall
  have digitNorm : normNat (digit (next fraction nonterminal)) = 2 := by
    rcases digitCases with zero | one | two
    · omega
    · omega
    · exact two
  exact isDiagonal_of_normNat_eq_two digitNorm

/-- A strict future corner approach together with denominator non-growth
forces the unique doubled-corner digit which continues the backward
succession. -/
theorem next_digit_eq_two_cornerTurn_of_corner_failure
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    {corner : GaussianInt} (cornerDiagonal : IsDiagonal corner)
    (denominatorFailure :
      normNat
          (corner *
              (digit (next fraction nonterminal) * current + previous) +
            current) ≤
        normNat (digit (next fraction nonterminal) * current + previous))
    (futureCorner :
      normSq
          ((next (next fraction nonterminal) nextNonterminal).value -
            toGaussian corner) < 1) :
    digit (next fraction nonterminal) =
      cornerTurn corner + cornerTurn corner := by
  let nextFraction := next fraction nonterminal
  let difference := digit nextFraction - cornerTurn corner
  have transformedFailure :
      normNat (difference * current + previous) ≤ normNat current := by
    dsimp only [difference, nextFraction]
    exact (corner_combination_norm_le_iff cornerDiagonal
      (digit (next fraction nonterminal)) current previous).1
        denominatorFailure
  have differenceSmall : normNat difference < 4 :=
    coefficient_normNat_lt_four_of_combination_norm_le
      difference current previous previousShorter transformedFailure
  have differenceCases :=
    normNat_eq_zero_or_one_or_two_of_lt_four difference differenceSmall
  have rhoApproach :
      normSq
          (residual nextFraction + toGaussian (cornerTurn corner)) < 1 := by
    dsimp only [nextFraction]
    exact residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
      (next fraction nonterminal) nextNonterminal cornerDiagonal futureCorner
  have coefficientRecovery :
      difference + cornerTurn corner = digit nextFraction := by
    dsimp only [difference]
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
      simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im] <;>
      ring1
  have valueAsDifference :
      nextFraction.value =
        toGaussian (difference + cornerTurn corner) + residual nextFraction := by
    calc
      nextFraction.value =
          toGaussian (digit nextFraction) + residual nextFraction :=
        value_eq_digit_add_residual nextFraction
      _ = toGaussian (difference + cornerTurn corner) +
          residual nextFraction := by rw [coefficientRecovery]
  have completeLower : 2 ≤ normSq nextFraction.value := by
    dsimp only [nextFraction]
    exact next_normSq_ge_two fraction nonterminal
  rcases differenceCases with differenceZero | differenceUnit | differenceDiagonal
  · have zero := eq_zero_of_normNat_eq_zero differenceZero
    have valueCorner : nextFraction.value =
        residual nextFraction + toGaussian (cornerTurn corner) := by
      rw [valueAsDifference, zero,
        RFAP.ConstructiveGaussianHeight.GaussianInt.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_comm]
    rw [valueCorner] at completeLower
    exact (not_lt_of_ge completeLower
      (rhoApproach.trans_le (by decide))).elim
  · have differenceIsUnit :=
      isGaussianUnit_of_normNat_eq_one differenceUnit
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      differenceIsUnit
    have valueSubDifference :
        nextFraction.value - toGaussian difference =
          residual nextFraction + toGaussian (cornerTurn corner) := by
      rw [valueAsDifference, toGaussian_add]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
        ring1
    rw [valueSubDifference] at exterior
    exact (not_lt_of_ge exterior rhoApproach).elim
  · have differenceIsDiagonal :=
      isDiagonal_of_normNat_eq_two differenceDiagonal
    have differenceTurn := diagonal_eq_cornerTurn_of_local_geometry
      (residual nextFraction)
      (RFAP.HurwitzNearest.remainder_mem nextFraction.value)
      (RFAP.HurwitzNearest.remainder_normSq_le_half nextFraction.value)
      cornerDiagonal differenceIsDiagonal rhoApproach
      (by rw [← valueAsDifference]; exact completeLower)
      (by
        intro unit unitProperty
        rw [← valueAsDifference]
        exact one_le_next_sub_unit_normSq fraction nonterminal unitProperty)
    calc
      digit (next fraction nonterminal) =
          difference + cornerTurn corner := by
        dsimp only [nextFraction] at coefficientRecovery
        exact coefficientRecovery.symm
      _ = cornerTurn corner + cornerTurn corner := by rw [differenceTurn]

/-- One exceptional corner failure transfers to the preceding continuant
with the transformed corner.  Iterating this lemma reaches the explicit
initial pair; no infinite continued fraction is introduced. -/
theorem corner_failure_transfers_backward
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (nextNonterminal : remainder (next fraction nonterminal) ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    {corner : GaussianInt} (cornerDiagonal : IsDiagonal corner)
    (denominatorFailure :
      normNat
          (corner *
              (digit (next fraction nonterminal) * current + previous) +
            current) ≤
        normNat (digit (next fraction nonterminal) * current + previous))
    (futureCorner :
      normSq
          ((next (next fraction nonterminal) nextNonterminal).value -
            toGaussian corner) < 1) :
    normNat (cornerTurn corner * current + previous) ≤ normNat current ∧
      normSq
          ((next fraction nonterminal).value -
            toGaussian (cornerTurn corner)) < 1 := by
  have digitForced := next_digit_eq_two_cornerTurn_of_corner_failure
    fraction nonterminal nextNonterminal current previous previousShorter
    cornerDiagonal denominatorFailure futureCorner
  have transformed := (corner_combination_norm_le_iff cornerDiagonal
    (digit (next fraction nonterminal)) current previous).1
      denominatorFailure
  have denominatorTransferred :
      normNat (cornerTurn corner * current + previous) ≤ normNat current := by
    have combinationIdentity :
        (digit (next fraction nonterminal) - cornerTurn corner) * current +
            previous =
          cornerTurn corner * current + previous := by
      rw [digitForced]
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
        ring1
    rw [combinationIdentity] at transformed
    exact transformed
  have residualTransferred :=
    residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
      (next fraction nonterminal) nextNonterminal cornerDiagonal futureCorner
  have futureTransferred :
      normSq
          ((next fraction nonterminal).value -
            toGaussian (cornerTurn corner)) < 1 := by
    have valueDifference :
        (next fraction nonterminal).value -
            toGaussian (cornerTurn corner) =
          residual (next fraction nonterminal) +
            toGaussian (cornerTurn corner) := by
      rw [value_eq_digit_add_residual, digitForced, toGaussian_add]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
        ring1
    rw [valueDifference]
    exact residualTransferred
  exact ⟨denominatorTransferred, futureTransferred⟩

/-- The finite natural-extension invariant needed for Hurwitz denominator
growth.  Besides strict growth of the adjacent denominator, it excludes the
four corner configurations which would start Lakein's exceptional backward
succession. -/
structure StageGeometry {source : Fraction} (stage : Stage source) : Prop where
  denominatorGrowth :
    normNat stage.previous.denominator < normNat stage.current.denominator
  cornerSafe : ∀ (nonterminal : remainder stage.quotient ≠ 0) corner,
    IsDiagonal corner → ¬
      (normNat
          (corner * stage.current.denominator + stage.previous.denominator) ≤
          normNat stage.current.denominator ∧
        normSq
          ((next stage.quotient nonterminal).value - toGaussian corner) < 1)

/-- The sole exceptional denominator shape left by the elementary Lakein
coefficient estimates.  It is finite up to the eight quadrance-five values
and four diagonal values. -/
def NormFiveDenominatorSafe {source : Fraction} (stage : Stage source) : Prop :=
  ∀ s t : GaussianInt, normNat s = 5 → normNat t = 2 →
    normNat stage.current.denominator ≤
      normNat
        (s * stage.current.denominator + t * stage.previous.denominator)

private theorem one_le_normFive_form_of_lower
    (x y : Coordinate) (lower : -(3 / 4 : Coordinate) ≤ x) :
    1 ≤ 5 + 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2 := by
  have scaledLower :
      4 * (-(3 / 4 : Coordinate)) ≤ 4 * x :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct lower
      (show (0 : Coordinate) ≤ 4 by decide)
  have linearLower : (3 : Coordinate) ≤ 4 * x + 6 := by
    calc
      (3 : Coordinate) = 4 * (-(3 / 4)) + 6 := by decide
      _ ≤ 4 * x + 6 :=
        RFAP.ConstructiveFraction.add_le_add_right_direct scaledLower 6
  have linearNonnegative : (0 : Coordinate) ≤ 4 * x + 6 :=
    (show (0 : Coordinate) ≤ 3 by decide).trans linearLower
  have squareLower : (9 : Coordinate) ≤ (4 * x + 6) ^ 2 := by
    rw [show (9 : Coordinate) = 3 * 3 by decide, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct linearLower linearLower
      (show (0 : Coordinate) ≤ 3 by decide) linearNonnegative
  have otherSquareNonnegative :
      (0 : Coordinate) ≤ (4 * y + 2) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have sumLower :
      (8 : Coordinate) ≤ (4 * x + 6) ^ 2 + (4 * y + 2) ^ 2 :=
    (show (8 : Coordinate) ≤ 9 by decide).trans
      (squareLower.trans (le_add_of_nonneg_right otherSquareNonnegative))
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 8)
  · calc
      (1 : Coordinate) * 8 = 8 := by ring1
      _ ≤ (4 * x + 6) ^ 2 + (4 * y + 2) ^ 2 := sumLower
      _ = (5 + 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2) * 8 := by
        ring1
  · decide

private theorem one_le_normFive_form_of_lower_negative
    (x y : Coordinate) (lower : -(3 / 4 : Coordinate) ≤ x) :
    1 ≤ 5 + 6 * x + 2 * x ^ 2 - 2 * y + 2 * y ^ 2 := by
  have bound := one_le_normFive_form_of_lower x (-y) lower
  convert bound using 1
  all_goals ring1

private theorem one_le_normFive_form_of_upper
    (x y : Coordinate) (upper : x ≤ (3 / 4 : Coordinate)) :
    1 ≤ 5 - 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2 := by
  have reflectedLower : -(3 / 4 : Coordinate) ≤ -x :=
    RFAP.ConstructiveFraction.neg_le_neg_direct upper
  have bound := one_le_normFive_form_of_lower (-x) y reflectedLower
  convert bound using 1
  all_goals ring1

private theorem one_le_normFive_form_of_upper_negative
    (x y : Coordinate) (upper : x ≤ (3 / 4 : Coordinate)) :
    1 ≤ 5 - 6 * x + 2 * x ^ 2 - 2 * y + 2 * y ^ 2 := by
  have bound := one_le_normFive_form_of_upper x (-y) upper
  convert bound using 1
  all_goals ring1

/-- The quadrance-five/diagonal combination is exterior whenever the
normalised preceding denominator lies in the coordinate box
`[-3/4,3/4]²`. -/
theorem one_le_normSq_normFive_add_diagonal_mul_of_coordinate_bounds
    (ratio : Gaussian) (s t : GaussianInt) (sNorm : normNat s = 5)
    (tNorm : normNat t = 2)
    (realLower : -(3 / 4 : Coordinate) ≤ ratio.re)
    (realUpper : ratio.re ≤ (3 / 4 : Coordinate))
    (imaginaryLower : -(3 / 4 : Coordinate) ≤ ratio.im)
    (imaginaryUpper : ratio.im ≤ (3 / 4 : Coordinate)) :
    1 ≤ normSq (toGaussian s + toGaussian t * ratio) := by
  have sCases := normFive_cases_of_normNat_eq_five sNorm
  have tCases := isDiagonal_of_normNat_eq_two tNorm
  rcases sCases with sCase | sCase | sCase | sCase | sCase | sCase |
      sCase | sCase <;>
    rcases tCases with tCase | tCase | tCase | tCase <;>
    subst s <;> subst t
  all_goals simp only [normSq, toGaussian,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_neg, Int.cast_one]
  all_goals solve
    | (convert one_le_normFive_form_of_lower ratio.re ratio.im realLower
        using 1; ring1)
    | (convert one_le_normFive_form_of_lower_negative ratio.re ratio.im
        realLower using 1; ring1)
    | (convert one_le_normFive_form_of_upper ratio.re ratio.im realUpper
        using 1; ring1)
    | (convert one_le_normFive_form_of_upper_negative ratio.re ratio.im
        realUpper using 1; ring1)
    | (convert one_le_normFive_form_of_lower ratio.im ratio.re imaginaryLower
        using 1; ring1)
    | (convert one_le_normFive_form_of_lower_negative ratio.im ratio.re
        imaginaryLower using 1; ring1)
    | (convert one_le_normFive_form_of_upper ratio.im ratio.re imaginaryUpper
        using 1; ring1)
    | (convert one_le_normFive_form_of_upper_negative ratio.im ratio.re
        imaginaryUpper using 1; ring1)

/-- Stages obtained by finitely iterating the executable transition. -/
inductive Generated (source : Fraction) : Stage source → Prop
  | first : Generated source (RFAP.HurwitzTrace.firstStage source)
  | advance {stage : Stage source} : Generated source stage →
      (nonterminal : remainder stage.quotient ≠ 0) →
      Generated source (RFAP.HurwitzTrace.advanceStage stage nonterminal)

theorem firstStage_geometry (source : Fraction) :
    StageGeometry (RFAP.HurwitzTrace.firstStage source) := by
  constructor
  · change normNat 0 < normNat 1
    decide
  · intro nonterminal corner cornerDiagonal failure
    have cornerNorm := normNat_eq_two_of_isDiagonal cornerDiagonal
    have denominatorFailure := failure.1
    change normNat (corner * 1 + 0) ≤ normNat 1 at denominatorFailure
    simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_one,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero,
      cornerNorm] at denominatorFailure
    change 2 ≤ 1 at denominatorFailure
    exact False.elim ((by decide : ¬(2 : Nat) ≤ 1) denominatorFailure)

theorem firstStage_normFiveDenominatorSafe (source : Fraction) :
    NormFiveDenominatorSafe (RFAP.HurwitzTrace.firstStage source) := by
  intro s t sNorm _tNorm
  change normNat 1 ≤ normNat (s * 1 + t * 0)
  rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_one,
    RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero,
    RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero, sNorm]
  decide

theorem advanceStage_geometry {source : Fraction} {stage : Stage source}
    (geometry : StageGeometry stage)
    (nonterminal : remainder stage.quotient ≠ 0) :
    StageGeometry (RFAP.HurwitzTrace.advanceStage stage nonterminal) := by
  let nextFraction := next stage.quotient nonterminal
  let nextDigit := digit nextFraction
  have nextDenominator :
      (RFAP.HurwitzTrace.advanceStage stage nonterminal).current.denominator =
        nextDigit * stage.current.denominator + stage.previous.denominator := rfl
  have nextPrevious :
      (RFAP.HurwitzTrace.advanceStage stage nonterminal).previous.denominator =
        stage.current.denominator := rfl
  have growth :
      normNat stage.current.denominator <
        normNat
          (RFAP.HurwitzTrace.advanceStage stage nonterminal).current.denominator := by
    apply Nat.lt_of_not_ge
    intro notGrowing
    have combinationNotLarger :
        normNat (nextDigit * stage.current.denominator +
            stage.previous.denominator) ≤
          normNat stage.current.denominator := by
      rw [← nextDenominator]
      exact notGrowing
    have digitDiagonal : IsDiagonal nextDigit := by
      dsimp only [nextDigit, nextFraction]
      exact next_digit_isDiagonal_of_combination_norm_le
        stage.quotient nonterminal stage.current.denominator
        stage.previous.denominator geometry.denominatorGrowth
        combinationNotLarger
    have futureClose :
        normSq (nextFraction.value - toGaussian nextDigit) < 1 := by
      have residualIdentity :
          nextFraction.value - toGaussian nextDigit = residual nextFraction := by
        rw [value_eq_digit_add_residual]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
      rw [residualIdentity]
      exact (RFAP.HurwitzNearest.remainder_normSq_le_half nextFraction.value).trans_lt
        (show (1 / 2 : Coordinate) < 1 by decide)
    exact (geometry.cornerSafe nonterminal nextDigit digitDiagonal
      ⟨combinationNotLarger, futureClose⟩)
  refine
    { denominatorGrowth := by rw [nextPrevious]; exact growth
      cornerSafe := ?_ }
  intro nextNonterminal corner cornerDiagonal failure
  have transferred := corner_failure_transfers_backward
    stage.quotient nonterminal
    (by
      change remainder nextFraction ≠ 0
      exact nextNonterminal)
    stage.current.denominator stage.previous.denominator
    geometry.denominatorGrowth cornerDiagonal
    (by
      change normNat
          (corner * (nextDigit * stage.current.denominator +
            stage.previous.denominator) + stage.current.denominator) ≤
        normNat (nextDigit * stage.current.denominator +
          stage.previous.denominator)
      rw [← nextDenominator, ← nextPrevious]
      exact failure.1)
    (by
      change normSq
          ((next nextFraction nextNonterminal).value - toGaussian corner) < 1
      exact failure.2)
  exact geometry.cornerSafe nonterminal (cornerTurn corner)
    (cornerTurn_isDiagonal cornerDiagonal) transferred

theorem geometry_of_generated {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) : StageGeometry stage := by
  induction generated with
  | first => exact firstStage_geometry source
  | advance generated nonterminal inductionHypothesis =>
      exact advanceStage_geometry inductionHypothesis nonterminal

private theorem generated_of_mem_stagesFromFuel {source : Fraction}
    (fuel : Nat)
    (stage : Stage source) (stageGenerated : Generated source stage)
    {candidate : Stage source}
    (member : candidate ∈
      RFAP.HurwitzTrace.stagesFromFuel fuel stage) :
    Generated source candidate := by
  induction fuel generalizing stage with
  | zero =>
      simp only [RFAP.HurwitzTrace.stagesFromFuel,
        List.mem_singleton] at member
      rw [member]
      exact stageGenerated
  | succ fuel inductionHypothesis =>
      by_cases terminal : remainder stage.quotient = 0
      · simp only [RFAP.HurwitzTrace.stagesFromFuel, dif_pos terminal,
          List.mem_singleton] at member
        rw [member]
        exact stageGenerated
      · simp only [RFAP.HurwitzTrace.stagesFromFuel, dif_neg terminal,
          List.mem_cons] at member
        rcases member with current | later
        · rw [current]
          exact stageGenerated
        · exact inductionHypothesis
            (RFAP.HurwitzTrace.advanceStage stage terminal)
            (Generated.advance stageGenerated terminal) later

theorem generated_of_mem_stagesFrom {source : Fraction}
    (stage : Stage source) (stageGenerated : Generated source stage)
    {candidate : Stage source}
    (member : candidate ∈ RFAP.HurwitzTrace.stagesFrom stage) :
    Generated source candidate := by
  exact generated_of_mem_stagesFromFuel
    (Nat.succ (normNat stage.quotient.denominator))
    stage stageGenerated member

theorem generated_of_mem_stages {source : Fraction} {stage : Stage source}
    (member : stage ∈ RFAP.HurwitzTrace.stages source) :
    Generated source stage := by
  exact generated_of_mem_stagesFrom (RFAP.HurwitzTrace.firstStage source)
    Generated.first member

theorem stage_denominatorGrowth {source : Fraction} {stage : Stage source}
    (generated : Generated source stage) :
    normNat stage.previous.denominator < normNat stage.current.denominator :=
  (geometry_of_generated generated).denominatorGrowth

theorem stage_denominatorGrowth_of_mem_stages
    {source : Fraction} {stage : Stage source}
    (member : stage ∈ RFAP.HurwitzTrace.stages source) :
    normNat stage.previous.denominator < normNat stage.current.denominator :=
  stage_denominatorGrowth (generated_of_mem_stages member)

/-- Advancing once multiplies the old complete denominator by the new
complete quotient.  This is the finite continuant identity
`xₙ₊₂ (xₙ₊₁ qₙ + qₙ₋₁) = xₙ₊₂ qₙ₊₁ + qₙ`. -/
theorem advanceStage_completeDenominator {source : Fraction}
    (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0)
    (nextNonterminal :
      remainder (RFAP.HurwitzTrace.advanceStage stage nonterminal).quotient ≠
        0) :
    (RFAP.HurwitzTrace.advanceStage stage nonterminal).completeDenominator
        nextNonterminal =
      (next (next stage.quotient nonterminal) nextNonterminal).value *
        stage.completeDenominator nonterminal := by
  let nextFraction := next stage.quotient nonterminal
  let nextValue := (next nextFraction nextNonterminal).value
  have residualNonzero : residual nextFraction ≠ 0 :=
    residual_ne_zero nextNonterminal
  have reciprocal : nextValue * residual nextFraction = 1 := by
    dsimp only [nextValue]
    rw [next_value, RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_mul _ residualNonzero]
  have decomposition :
      (next stage.quotient nonterminal).value =
        toGaussian (digit nextFraction) + residual nextFraction := by
    dsimp only [nextFraction]
    exact value_eq_digit_add_residual (next stage.quotient nonterminal)
  change nextValue *
        toGaussian
          (digit nextFraction * stage.current.denominator +
            stage.previous.denominator) +
      toGaussian stage.current.denominator =
    nextValue *
      ((next stage.quotient nonterminal).value *
          toGaussian stage.current.denominator +
        toGaussian stage.previous.denominator)
  rw [toGaussian_add, toGaussian_mul, decomposition]
  calc
    nextValue *
          (toGaussian (digit nextFraction) *
              toGaussian stage.current.denominator +
            toGaussian stage.previous.denominator) +
        toGaussian stage.current.denominator =
      nextValue *
          (toGaussian (digit nextFraction) *
              toGaussian stage.current.denominator +
            toGaussian stage.previous.denominator) +
        (nextValue * residual nextFraction) *
          toGaussian stage.current.denominator := by
      rw [reciprocal, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = nextValue *
        ((toGaussian (digit nextFraction) + residual nextFraction) *
            toGaussian stage.current.denominator +
          toGaussian stage.previous.denominator) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1

/-- If the complete denominator at a generated step were no larger than its
current continuant denominator, the next complete quotient would have
quadrance below three.  The hypothesis involving `x * previous` is exactly
what the preceding complete-denominator inequality becomes after one Hurwitz
transition. -/
theorem quotient_normSq_lt_three_of_complete_failure
    (x current previous : Gaussian)
    (currentNonzero : current ≠ 0)
    (scaledPreviousStrict :
      normSq x * normSq previous <
        normSq (x * current + previous))
    (completeFailure :
      normSq (x * current + previous) ≤ normSq current) :
    normSq x < 3 := by
  have currentPositive : 0 < normSq current := normSq_pos currentNonzero
  have previousNonnegative : 0 ≤ normSq previous := normSq_nonneg previous
  have currentNonnegative : 0 ≤ normSq current := currentPositive.le
  apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
  intro threeLe
  have threePreviousLe :
      3 * normSq previous ≤ normSq x * normSq previous :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      threeLe previousNonnegative
  have threePreviousLtCurrent :
      3 * normSq previous < normSq current :=
    threePreviousLe.trans_lt
      (scaledPreviousStrict.trans_le completeFailure)
  have twoPreviousLeThreePrevious :
      2 * normSq previous ≤ 3 * normSq previous := by
    have oneLeThree : (2 : Coordinate) ≤ 3 := by decide
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      oneLeThree previousNonnegative
  have twoPreviousLtCurrent :
      2 * normSq previous < normSq current :=
    twoPreviousLeThreePrevious.trans_lt threePreviousLtCurrent
  have sumStrict :
      2 * (normSq current + normSq previous) <
        3 * normSq current := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct
        twoPreviousLtCurrent (2 * normSq current)
    calc
      2 * (normSq current + normSq previous) =
          2 * normSq current + 2 * normSq previous := by ring1
      _ < 2 * normSq current + normSq current := shifted
      _ = 3 * normSq current := by ring1
  have productUpper :
      normSq x * normSq current < 3 * normSq current := by
    calc
      normSq x * normSq current = normSq (x * current) := by
        rw [normSq_mul]
      _ = normSq ((x * current + previous) - previous) := by
        congr 1
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
      _ ≤ 2 *
          (normSq (x * current + previous) + normSq previous) :=
        normSq_sub_le_two _ _
      _ ≤ 2 * (normSq current + normSq previous) := by
        have sumLe := add_le_add_right completeFailure (normSq previous)
        have reordered :
            normSq (x * current + previous) + normSq previous ≤
              normSq current + normSq previous := by
          calc
            normSq (x * current + previous) + normSq previous =
                normSq previous + normSq (x * current + previous) := by ring1
            _ ≤ normSq previous + normSq current := sumLe
            _ = normSq current + normSq previous := by ring1
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          reordered (show (0 : Coordinate) ≤ 2 by decide)
      _ < 3 * normSq current := sumStrict
  have productLower :
      3 * normSq current ≤ normSq x * normSq current :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      threeLe currentNonnegative
  exact (not_lt_of_ge productLower productUpper)

/-- A noninitial complete quotient of quadrance below three must have a
diagonal nearest Gaussian integer.  The exterior tests against the four
units rule out a rounded coordinate of magnitude at least two. -/
theorem next_digit_isDiagonal_of_normSq_lt_three
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (small : normSq (next fraction nonterminal).value < 3) :
    IsDiagonal (digit (next fraction nonterminal)) := by
  let nextFraction := next fraction nonterminal
  let nextValue := nextFraction.value
  let nextDigit := digit nextFraction
  let rho := residual nextFraction
  have decomposition :
      nextValue = toGaussian nextDigit + rho :=
    value_eq_digit_add_residual nextFraction
  have realDecomposition :
      nextValue.re = (nextDigit.re : Coordinate) + rho.re := by
    exact congrArg RFAP.ConstructiveGaussian.Gaussian.re decomposition
  have imaginaryDecomposition :
      nextValue.im = (nextDigit.im : Coordinate) + rho.im := by
    exact congrArg RFAP.ConstructiveGaussian.Gaussian.im decomposition
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem nextFraction.value
  have realUpper : nextDigit.re < 2 := by
    apply Int.lt_of_not_ge
    intro twoLeDigit
    have castTwoLe :
        (2 : Coordinate) ≤ (nextDigit.re : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct 2
        nextDigit.re).2 twoLeDigit
    have nextRealLower : (3 / 2 : Coordinate) ≤ nextValue.re := by
      calc
        (3 / 2 : Coordinate) = 2 + (-(1 / 2 : Coordinate)) := by decide
        _ ≤ (nextDigit.re : Coordinate) + rho.re := by
          exact RFAP.ConstructiveFraction.add_le_add_direct
            castTwoLe rhoSquare.1
        _ = nextValue.re := realDecomposition.symm
    have doubledRealLower :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        nextRealLower (show (0 : Coordinate) ≤ 2 by decide)
    have radialGap : (2 : Coordinate) ≤ 2 * nextValue.re - 1 := by
      calc
        (2 : Coordinate) = 2 * (3 / 2 : Coordinate) - 1 := by decide
        _ ≤ 2 * nextValue.re - 1 :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            doubledRealLower 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := 1) one_isGaussianUnit
    have threeLe : (3 : Coordinate) ≤ normSq nextValue := by
      calc
        (3 : Coordinate) = 1 + 2 := by ring1
        _ ≤ normSq (nextValue - toGaussian 1) +
            (2 * nextValue.re - 1) :=
          RFAP.ConstructiveFraction.add_le_add_direct exterior radialGap
        _ = normSq nextValue := by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_one]
          ring1
    exact (not_lt_of_ge threeLe small)
  have realLower : -(2 : Int) < nextDigit.re := by
    apply Int.lt_of_not_ge
    intro digitLeNegTwo
    have castLeNegTwo :
        (nextDigit.re : Coordinate) ≤ (-2 : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
        nextDigit.re (-2)).2 digitLeNegTwo
    have nextRealUpper : nextValue.re < -(3 / 2 : Coordinate) := by
      calc
        nextValue.re = (nextDigit.re : Coordinate) + rho.re :=
          realDecomposition
        _ < (-2 : Coordinate) + (1 / 2 : Coordinate) := by
          have first := RFAP.ConstructiveFraction.add_le_add_right_direct
            castLeNegTwo rho.re
          have second := RFAP.ConstructiveFraction.add_lt_add_left_direct
            rhoSquare.2.1 (-2)
          exact first.trans_lt second
        _ = -(3 / 2 : Coordinate) := by decide
    have doubledRealUpper :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : Coordinate) < 2 by decide) nextRealUpper
    have radialGap : (2 : Coordinate) < -(2 * nextValue.re) - 1 := by
      have negated :
          -(2 * (-(3 / 2 : Coordinate))) < -(2 * nextValue.re) :=
        RFAP.ConstructiveFraction.neg_lt_neg_direct doubledRealUpper
      calc
        (2 : Coordinate) = -(2 * (-(3 / 2 : Coordinate))) - 1 := by decide
        _ < -(2 * nextValue.re) - 1 :=
          RFAP.ConstructiveFraction.sub_lt_sub_right_direct negated 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := -1) negOne_isGaussianUnit
    have threeLt : (3 : Coordinate) < normSq nextValue := by
      calc
        (3 : Coordinate) = 1 + 2 := by ring1
        _ < normSq (nextValue - toGaussian (-1)) +
            (-(2 * nextValue.re) - 1) := by
          have first := RFAP.ConstructiveFraction.add_le_add_right_direct
            exterior 2
          have second := RFAP.ConstructiveFraction.add_lt_add_left_direct
            radialGap (normSq (nextValue - toGaussian (-1)))
          exact first.trans_lt second
        _ = normSq nextValue := by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_neg, Int.cast_one]
          ring1
    exact (not_lt_of_ge threeLt.le small)
  have imaginaryUpper : nextDigit.im < 2 := by
    apply Int.lt_of_not_ge
    intro twoLeDigit
    have castTwoLe :
        (2 : Coordinate) ≤ (nextDigit.im : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct 2
        nextDigit.im).2 twoLeDigit
    have nextImaginaryLower : (3 / 2 : Coordinate) ≤ nextValue.im := by
      calc
        (3 / 2 : Coordinate) = 2 + (-(1 / 2 : Coordinate)) := by decide
        _ ≤ (nextDigit.im : Coordinate) + rho.im := by
          exact RFAP.ConstructiveFraction.add_le_add_direct
            castTwoLe rhoSquare.2.2.1
        _ = nextValue.im := imaginaryDecomposition.symm
    have doubledImaginaryLower :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        nextImaginaryLower (show (0 : Coordinate) ≤ 2 by decide)
    have radialGap : (2 : Coordinate) ≤ 2 * nextValue.im - 1 := by
      calc
        (2 : Coordinate) = 2 * (3 / 2 : Coordinate) - 1 := by decide
        _ ≤ 2 * nextValue.im - 1 :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            doubledImaginaryLower 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := imaginaryUnit) imaginaryUnit_isGaussianUnit
    have threeLe : (3 : Coordinate) ≤ normSq nextValue := by
      calc
        (3 : Coordinate) = 1 + 2 := by ring1
        _ ≤ normSq (nextValue - toGaussian imaginaryUnit) +
            (2 * nextValue.im - 1) :=
          RFAP.ConstructiveFraction.add_le_add_direct exterior radialGap
        _ = normSq nextValue := by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian, Int.cast_zero, Int.cast_one]
          ring1
    exact (not_lt_of_ge threeLe small)
  have imaginaryLower : -(2 : Int) < nextDigit.im := by
    apply Int.lt_of_not_ge
    intro digitLeNegTwo
    have castLeNegTwo :
        (nextDigit.im : Coordinate) ≤ (-2 : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
        nextDigit.im (-2)).2 digitLeNegTwo
    have nextImaginaryUpper : nextValue.im < -(3 / 2 : Coordinate) := by
      calc
        nextValue.im = (nextDigit.im : Coordinate) + rho.im :=
          imaginaryDecomposition
        _ < (-2 : Coordinate) + (1 / 2 : Coordinate) := by
          have first := RFAP.ConstructiveFraction.add_le_add_right_direct
            castLeNegTwo rho.im
          have second := RFAP.ConstructiveFraction.add_lt_add_left_direct
            rhoSquare.2.2.2 (-2)
          exact first.trans_lt second
        _ = -(3 / 2 : Coordinate) := by decide
    have doubledImaginaryUpper :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : Coordinate) < 2 by decide) nextImaginaryUpper
    have radialGap : (2 : Coordinate) < -(2 * nextValue.im) - 1 := by
      have negated :
          -(2 * (-(3 / 2 : Coordinate))) < -(2 * nextValue.im) :=
        RFAP.ConstructiveFraction.neg_lt_neg_direct doubledImaginaryUpper
      calc
        (2 : Coordinate) = -(2 * (-(3 / 2 : Coordinate))) - 1 := by decide
        _ < -(2 * nextValue.im) - 1 :=
          RFAP.ConstructiveFraction.sub_lt_sub_right_direct negated 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := -imaginaryUnit) negImaginaryUnit_isGaussianUnit
    have threeLt : (3 : Coordinate) < normSq nextValue := by
      calc
        (3 : Coordinate) = 1 + 2 := by ring1
        _ < normSq (nextValue - toGaussian (-imaginaryUnit)) +
            (-(2 * nextValue.im) - 1) := by
          have first := RFAP.ConstructiveFraction.add_le_add_right_direct
            exterior 2
          have second := RFAP.ConstructiveFraction.add_lt_add_left_direct
            radialGap (normSq (nextValue - toGaussian (-imaginaryUnit)))
          exact first.trans_lt second
        _ = normSq nextValue := by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            Int.cast_neg, Int.cast_zero, Int.cast_one]
          ring1
    exact (not_lt_of_ge threeLt.le small)
  have realCases : nextDigit.re = -1 ∨ nextDigit.re = 0 ∨
      nextDigit.re = 1 :=
    coordinate_cases_of_neg_two_lt_lt_two realLower realUpper
  have imaginaryCases : nextDigit.im = -1 ∨ nextDigit.im = 0 ∨
      nextDigit.im = 1 :=
    coordinate_cases_of_neg_two_lt_lt_two imaginaryLower imaginaryUpper
  have realSquareLe : nextDigit.re * nextDigit.re ≤ 1 := by
    rcases realCases with real | real | real <;> rw [real] <;> decide
  have imaginarySquareLe : nextDigit.im * nextDigit.im ≤ 1 := by
    rcases imaginaryCases with imaginary | imaginary | imaginary <;>
      rw [imaginary] <;> decide
  have digitNormLeTwo : normNat nextDigit ≤ 2 := by
    have normIntLe : normInt nextDigit ≤ 2 := by
      dsimp only [normInt]
      exact (Int.add_le_add realSquareLe imaginarySquareLe).trans_eq rfl
    rw [normInt_eq_natCast_normNat] at normIntLe
    exact Int.ofNat_le.mp normIntLe
  have digitNormAtLeastTwo := two_le_next_digit_normNat fraction nonterminal
  change 2 ≤ normNat nextDigit at digitNormAtLeastTwo
  have digitNorm : normNat nextDigit = 2 :=
    Nat.le_antisymm digitNormLeTwo digitNormAtLeastTwo
  exact isDiagonal_of_normNat_eq_two digitNorm

private theorem neg_one_lt_of_square_lt_one {value : Coordinate}
    (small : value ^ 2 < 1) : -1 < value := by
  have lower : (-1 : Coordinate) ≤ value :=
    RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
      (show (0 : Coordinate) ≤ 1 by decide) small.le
  refine ⟨lower, ?_⟩
  intro reverse
  have equal : value = -1 := le_antisymm reverse lower
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Coordinate) ≤ 1 by decide) small)

private theorem square_lt_square_of_nonneg_of_lt
    {left right : Coordinate} (leftNonnegative : 0 ≤ left)
    (strict : left < right) : left ^ 2 < right ^ 2 := by
  have rightPositive : 0 < right := leftNonnegative.trans_lt strict
  have first : left * left ≤ left * right :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      strict.le leftNonnegative
  have second : left * right < right * right :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      strict rightPositive
  simpa only [pow_two] using first.trans_lt second

/-- The elementary lune inclusion behind the diagonal case of Lakein's
first inequality.  A point in the open unit disc about `(1,1)` but outside
the unit disc about zero cannot be moved into the latter disc by a vector in
the closed half-square whose translated corner is exterior to the two
adjacent unit discs. -/
private theorem northeast_lune_exterior
    (rhoReal rhoImaginary yReal yImaginary : Coordinate)
    (rhoRealLower : -(1 / 2 : Coordinate) ≤ rhoReal)
    (rhoImaginaryLower : -(1 / 2 : Coordinate) ≤ rhoImaginary)
    (yInside : yReal ^ 2 + yImaginary ^ 2 < 1)
    (realExterior :
      1 ≤ (1 + rhoReal) ^ 2 + rhoImaginary ^ 2)
    (imaginaryExterior :
      1 ≤ rhoReal ^ 2 + (1 + rhoImaginary) ^ 2)
    (translatedInside :
      (1 + rhoReal + yReal) ^ 2 +
          (1 + rhoImaginary + yImaginary) ^ 2 ≤ 1) :
    (1 + yReal) ^ 2 + (1 + yImaginary) ^ 2 ≤ 1 := by
  let rhoNorm := rhoReal ^ 2 + rhoImaginary ^ 2
  let realCoordinate := 1 + yReal
  let imaginaryCoordinate := 1 + yImaginary
  have yRealSquareLt : yReal ^ 2 < 1 := by
    exact (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct yImaginary)).trans_lt
        yInside
  have yImaginarySquareLt : yImaginary ^ 2 < 1 := by
    have reordered : yImaginary ^ 2 + yReal ^ 2 < 1 := by
      calc
        yImaginary ^ 2 + yReal ^ 2 =
            yReal ^ 2 + yImaginary ^ 2 := by ring1
        _ < 1 := yInside
    exact (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct yReal)).trans_lt
        reordered
  have realCoordinatePositive : 0 < realCoordinate := by
    have lower := neg_one_lt_of_square_lt_one yRealSquareLt
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct lower 1
    calc
      0 = (-1 : Coordinate) + 1 := by ring1
      _ < yReal + 1 := shifted
      _ = realCoordinate := by dsimp only [realCoordinate]; ring1
  have imaginaryCoordinatePositive : 0 < imaginaryCoordinate := by
    have lower := neg_one_lt_of_square_lt_one yImaginarySquareLt
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct lower 1
    calc
      0 = (-1 : Coordinate) + 1 := by ring1
      _ < yImaginary + 1 := shifted
      _ = imaginaryCoordinate := by dsimp only [imaginaryCoordinate]; ring1
  have realExteriorGap : 0 ≤ rhoNorm + 2 * rhoReal := by
    have gap := RFAP.ConstructiveFraction.sub_nonneg_direct realExterior
    calc
      0 ≤ ((1 + rhoReal) ^ 2 + rhoImaginary ^ 2) - 1 := gap
      _ = rhoNorm + 2 * rhoReal := by
        dsimp only [rhoNorm]
        ring1
  have imaginaryExteriorGap : 0 ≤ rhoNorm + 2 * rhoImaginary := by
    have gap := RFAP.ConstructiveFraction.sub_nonneg_direct imaginaryExterior
    calc
      0 ≤ (rhoReal ^ 2 + (1 + rhoImaginary) ^ 2) - 1 := gap
      _ = rhoNorm + 2 * rhoImaginary := by
        dsimp only [rhoNorm]
        ring1
  have notBothNegative : ¬ (rhoReal < 0 ∧ rhoImaginary < 0) := by
    rintro ⟨rhoRealNegative, rhoImaginaryNegative⟩
    have negRealNonnegative : 0 ≤ -rhoReal :=
      (neg_pos.mpr rhoRealNegative).le
    have negImaginaryNonnegative : 0 ≤ -rhoImaginary :=
      (neg_pos.mpr rhoImaginaryNegative).le
    have negRealLeHalf : -rhoReal ≤ (1 / 2 : Coordinate) := by
      have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct rhoRealLower
      simpa only [neg_neg] using reversed
    have negImaginaryLeHalf :
        -rhoImaginary ≤ (1 / 2 : Coordinate) := by
      have reversed :=
        RFAP.ConstructiveFraction.neg_le_neg_direct rhoImaginaryLower
      simpa only [neg_neg] using reversed
    have realSquareBound : 2 * rhoReal ^ 2 ≤ -rhoReal := by
      have factorNonnegative : 0 ≤ 2 * (-rhoReal) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          (show (0 : Coordinate) ≤ 2 by decide) negRealNonnegative
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          negRealLeHalf factorNonnegative
      calc
        2 * rhoReal ^ 2 = (-rhoReal) * (2 * (-rhoReal)) := by ring1
        _ ≤ (1 / 2 : Coordinate) * (2 * (-rhoReal)) := scaled
        _ = -rhoReal := by
          calc
            (1 / 2 : Coordinate) * (2 * (-rhoReal)) =
                ((1 / 2 : Coordinate) * 2) * (-rhoReal) := by
              exact (_root_.mul_assoc (1 / 2 : Coordinate) 2 (-rhoReal)).symm
            _ = 1 * (-rhoReal) := by
              rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
            _ = -rhoReal := one_mul _
    have imaginarySquareBound :
        2 * rhoImaginary ^ 2 ≤ -rhoImaginary := by
      have factorNonnegative : 0 ≤ 2 * (-rhoImaginary) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          (show (0 : Coordinate) ≤ 2 by decide) negImaginaryNonnegative
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          negImaginaryLeHalf factorNonnegative
      calc
        2 * rhoImaginary ^ 2 =
            (-rhoImaginary) * (2 * (-rhoImaginary)) := by ring1
        _ ≤ (1 / 2 : Coordinate) * (2 * (-rhoImaginary)) := scaled
        _ = -rhoImaginary := by
          calc
            (1 / 2 : Coordinate) * (2 * (-rhoImaginary)) =
                ((1 / 2 : Coordinate) * 2) * (-rhoImaginary) := by
              exact (_root_.mul_assoc
                (1 / 2 : Coordinate) 2 (-rhoImaginary)).symm
            _ = 1 * (-rhoImaginary) := by
              rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
            _ = -rhoImaginary := one_mul _
    have twiceRhoNormUpper :
        2 * rhoNorm ≤ -(rhoReal + rhoImaginary) := by
      calc
        2 * rhoNorm = 2 * rhoReal ^ 2 +
            2 * rhoImaginary ^ 2 := by
          dsimp only [rhoNorm]
          ring1
        _ ≤ -rhoReal + -rhoImaginary :=
          RFAP.ConstructiveFraction.add_le_add_direct
            realSquareBound imaginarySquareBound
        _ = -(rhoReal + rhoImaginary) := by ring1
    have summedGap :
        0 ≤ (rhoNorm + 2 * rhoReal) +
          (rhoNorm + 2 * rhoImaginary) :=
      add_nonneg realExteriorGap imaginaryExteriorGap
    have sumNegative : rhoReal + rhoImaginary < 0 :=
      RFAP.ConstructiveFraction.add_lt_add_direct
        rhoRealNegative rhoImaginaryNegative
    have impossible :
        (rhoNorm + 2 * rhoReal) +
            (rhoNorm + 2 * rhoImaginary) < 0 := by
      calc
        (rhoNorm + 2 * rhoReal) +
              (rhoNorm + 2 * rhoImaginary) =
            2 * rhoNorm + 2 * (rhoReal + rhoImaginary) := by ring1
        _ ≤ -(rhoReal + rhoImaginary) +
            2 * (rhoReal + rhoImaginary) :=
          RFAP.ConstructiveFraction.add_le_add_right_direct
            twiceRhoNormUpper (2 * (rhoReal + rhoImaginary))
        _ = rhoReal + rhoImaginary := by ring1
        _ < 0 := sumNegative
    exact (not_lt_of_ge summedGap impossible)
  apply RFAP.ConstructiveFraction.le_of_not_gt_direct
  intro outside
  have translatedStrict :
      (1 + rhoReal + yReal) ^ 2 +
          (1 + rhoImaginary + yImaginary) ^ 2 <
        (1 + yReal) ^ 2 + (1 + yImaginary) ^ 2 :=
    translatedInside.trans_lt outside
  have differenceNegative :
      rhoNorm + 2 * realCoordinate * rhoReal +
          2 * imaginaryCoordinate * rhoImaginary < 0 := by
    have difference :=
      RFAP.ConstructiveFraction.sub_neg_direct translatedStrict
    calc
      rhoNorm + 2 * realCoordinate * rhoReal +
            2 * imaginaryCoordinate * rhoImaginary =
          ((1 + rhoReal + yReal) ^ 2 +
              (1 + rhoImaginary + yImaginary) ^ 2) -
            ((1 + yReal) ^ 2 + (1 + yImaginary) ^ 2) := by
        dsimp only [rhoNorm, realCoordinate, imaginaryCoordinate]
        ring1
      _ < 0 := difference
  by_cases realNonnegative : 0 ≤ rhoReal
  · by_cases imaginaryNonnegative : 0 ≤ rhoImaginary
    · have realTerm :
          0 ≤ 2 * realCoordinate * rhoReal := by
        exact RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (show (0 : Coordinate) ≤ 2 by decide)
            realCoordinatePositive.le) realNonnegative
      have imaginaryTerm :
          0 ≤ 2 * imaginaryCoordinate * rhoImaginary := by
        exact RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (show (0 : Coordinate) ≤ 2 by decide)
            imaginaryCoordinatePositive.le) imaginaryNonnegative
      have nonnegative := add_nonneg
        (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct rhoReal)
          (RFAP.ConstructiveFraction.sq_nonneg_direct rhoImaginary))
        (add_nonneg realTerm imaginaryTerm)
      have reordered :
          0 ≤ rhoNorm + 2 * realCoordinate * rhoReal +
            2 * imaginaryCoordinate * rhoImaginary := by
        calc
          0 ≤ (rhoReal ^ 2 + rhoImaginary ^ 2) +
              (2 * realCoordinate * rhoReal +
                2 * imaginaryCoordinate * rhoImaginary) := nonnegative
          _ = rhoNorm + 2 * realCoordinate * rhoReal +
              2 * imaginaryCoordinate * rhoImaginary := by
            dsimp only [rhoNorm]
            ring1
      exact (not_lt_of_ge reordered differenceNegative)
    · have imaginaryNegative : rhoImaginary < 0 :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct imaginaryNonnegative
      by_cases coordinateLeOne : imaginaryCoordinate ≤ 1
      · have productComparison :
            rhoImaginary ≤ imaginaryCoordinate * rhoImaginary := by
          have coordinateGap : 0 ≤ 1 - imaginaryCoordinate :=
            RFAP.ConstructiveFraction.sub_nonneg_direct coordinateLeOne
          have productNonnegative :=
            RFAP.ConstructiveFraction.mul_nonneg_direct
              (neg_nonneg.mpr imaginaryNegative.le) coordinateGap
          calc
            rhoImaginary ≤ rhoImaginary +
                ((-rhoImaginary) * (1 - imaginaryCoordinate)) :=
              le_add_of_nonneg_right productNonnegative
            _ = imaginaryCoordinate * rhoImaginary := by ring1
        have scaledComparison :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            productComparison (show (0 : Coordinate) ≤ 2 by decide)
        have imaginaryPart :
            0 ≤ rhoNorm + 2 * imaginaryCoordinate * rhoImaginary := by
          calc
            0 ≤ rhoNorm + 2 * rhoImaginary := imaginaryExteriorGap
            _ ≤ rhoNorm + 2 * imaginaryCoordinate * rhoImaginary :=
              calc
                rhoNorm + 2 * rhoImaginary =
                    2 * rhoImaginary + rhoNorm := by ring1
                _ ≤ 2 * (imaginaryCoordinate * rhoImaginary) + rhoNorm :=
                  RFAP.ConstructiveFraction.add_le_add_direct
                    scaledComparison le_rfl
                _ = rhoNorm + 2 * imaginaryCoordinate * rhoImaginary := by
                  ring1
        have realPart :
            0 ≤ 2 * realCoordinate * rhoReal :=
          RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (show (0 : Coordinate) ≤ 2 by decide)
              realCoordinatePositive.le) realNonnegative
        have reordered := add_nonneg imaginaryPart realPart
        have final :
            0 ≤ rhoNorm + 2 * realCoordinate * rhoReal +
              2 * imaginaryCoordinate * rhoImaginary := by
          calc
            0 ≤ (rhoNorm + 2 * imaginaryCoordinate * rhoImaginary) +
                2 * realCoordinate * rhoReal := reordered
            _ = rhoNorm + 2 * realCoordinate * rhoReal +
                2 * imaginaryCoordinate * rhoImaginary := by ring1
        exact (not_lt_of_ge final differenceNegative)
      · have coordinateGreater : 1 < imaginaryCoordinate :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct coordinateLeOne
        have yImaginaryPositive : 0 < yImaginary := by
          have shifted :=
            RFAP.ConstructiveFraction.sub_lt_sub_right_direct
              coordinateGreater 1
          calc
            0 = (1 : Coordinate) - 1 := by ring1
            _ < imaginaryCoordinate - 1 := shifted
            _ = yImaginary := by
              dsimp only [imaginaryCoordinate]
              ring1
        have baseImaginaryNonnegative : 0 ≤ 1 + rhoImaginary := by
          calc
            0 ≤ 1 + (-(1 / 2 : Coordinate)) := by decide
            _ ≤ 1 + rhoImaginary := by
              calc
                1 + (-(1 / 2 : Coordinate)) =
                    (-(1 / 2 : Coordinate)) + 1 := by ring1
                _ ≤ rhoImaginary + 1 :=
                  RFAP.ConstructiveFraction.add_le_add_direct
                    rhoImaginaryLower le_rfl
                _ = 1 + rhoImaginary := by ring1
        have baseRealSquareLe : rhoReal ^ 2 ≤
            (rhoReal + realCoordinate) ^ 2 := by
          have strict : rhoReal < rhoReal + realCoordinate := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
              realCoordinatePositive rhoReal
            calc
              rhoReal = rhoReal + 0 := by ring1
              _ < rhoReal + realCoordinate := shifted
          exact (square_lt_square_of_nonneg_of_lt realNonnegative strict).le
        have baseImaginaryStrict :
            1 + rhoImaginary < 1 + rhoImaginary + yImaginary := by
          have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
            yImaginaryPositive (1 + rhoImaginary)
          calc
            1 + rhoImaginary = 1 + rhoImaginary + 0 := by ring1
            _ < 1 + rhoImaginary + yImaginary := shifted
        have baseImaginarySquareStrict :=
          square_lt_square_of_nonneg_of_lt baseImaginaryNonnegative
            baseImaginaryStrict
        have exteriorStrict :
            1 < (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 := by
          calc
            1 ≤ rhoReal ^ 2 + (1 + rhoImaginary) ^ 2 :=
              imaginaryExterior
            _ < (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 :=
              calc
                rhoReal ^ 2 + (1 + rhoImaginary) ^ 2 ≤
                    (rhoReal + realCoordinate) ^ 2 +
                      (1 + rhoImaginary) ^ 2 :=
                  RFAP.ConstructiveFraction.add_le_add_direct
                    baseRealSquareLe le_rfl
                _ < (rhoReal + realCoordinate) ^ 2 +
                    (1 + rhoImaginary + yImaginary) ^ 2 :=
                  RFAP.ConstructiveFraction.add_lt_add_left_direct
                    baseImaginarySquareStrict
                    ((rhoReal + realCoordinate) ^ 2)
        have translatedIdentity :
            (rhoReal + realCoordinate) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 =
              (1 + rhoReal + yReal) ^ 2 +
                (1 + rhoImaginary + yImaginary) ^ 2 := by
          dsimp only [realCoordinate]
          ring1
        rw [translatedIdentity] at exteriorStrict
        exact (not_lt_of_ge translatedInside exteriorStrict)
  · have realNegative : rhoReal < 0 :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct realNonnegative
    have imaginaryNonnegative : 0 ≤ rhoImaginary := by
      apply RFAP.ConstructiveFraction.le_of_not_gt_direct
      intro imaginaryNegative
      exact notBothNegative ⟨realNegative, imaginaryNegative⟩
    by_cases coordinateLeOne : realCoordinate ≤ 1
    · have productComparison :
          rhoReal ≤ realCoordinate * rhoReal := by
        have coordinateGap : 0 ≤ 1 - realCoordinate :=
          RFAP.ConstructiveFraction.sub_nonneg_direct coordinateLeOne
        have productNonnegative :=
          RFAP.ConstructiveFraction.mul_nonneg_direct
            (neg_nonneg.mpr realNegative.le) coordinateGap
        calc
          rhoReal ≤ rhoReal + ((-rhoReal) * (1 - realCoordinate)) :=
            le_add_of_nonneg_right productNonnegative
          _ = realCoordinate * rhoReal := by ring1
      have scaledComparison :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productComparison (show (0 : Coordinate) ≤ 2 by decide)
      have realPart :
          0 ≤ rhoNorm + 2 * realCoordinate * rhoReal := by
        calc
          0 ≤ rhoNorm + 2 * rhoReal := realExteriorGap
          _ ≤ rhoNorm + 2 * realCoordinate * rhoReal :=
            calc
              rhoNorm + 2 * rhoReal = 2 * rhoReal + rhoNorm := by ring1
              _ ≤ 2 * (realCoordinate * rhoReal) + rhoNorm :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  scaledComparison le_rfl
              _ = rhoNorm + 2 * realCoordinate * rhoReal := by ring1
      have imaginaryPart :
          0 ≤ 2 * imaginaryCoordinate * rhoImaginary :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (show (0 : Coordinate) ≤ 2 by decide)
            imaginaryCoordinatePositive.le) imaginaryNonnegative
      have final := add_nonneg realPart imaginaryPart
      exact (not_lt_of_ge final differenceNegative)
    · have coordinateGreater : 1 < realCoordinate :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct coordinateLeOne
      have yRealPositive : 0 < yReal := by
        have shifted :=
          RFAP.ConstructiveFraction.sub_lt_sub_right_direct
            coordinateGreater 1
        calc
          0 = (1 : Coordinate) - 1 := by ring1
          _ < realCoordinate - 1 := shifted
          _ = yReal := by
            dsimp only [realCoordinate]
            ring1
      have baseRealNonnegative : 0 ≤ 1 + rhoReal := by
        calc
          0 ≤ 1 + (-(1 / 2 : Coordinate)) := by decide
          _ ≤ 1 + rhoReal := by
            calc
              1 + (-(1 / 2 : Coordinate)) =
                  (-(1 / 2 : Coordinate)) + 1 := by ring1
              _ ≤ rhoReal + 1 :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  rhoRealLower le_rfl
              _ = 1 + rhoReal := by ring1
      have baseRealStrict :
          1 + rhoReal < 1 + rhoReal + yReal := by
        have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
          yRealPositive (1 + rhoReal)
        calc
          1 + rhoReal = 1 + rhoReal + 0 := by ring1
          _ < 1 + rhoReal + yReal := shifted
      have baseRealSquareStrict :=
        square_lt_square_of_nonneg_of_lt baseRealNonnegative baseRealStrict
      have baseImaginarySquareLe : rhoImaginary ^ 2 ≤
          (rhoImaginary + imaginaryCoordinate) ^ 2 := by
        have strict :
            rhoImaginary < rhoImaginary + imaginaryCoordinate := by
          have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
            imaginaryCoordinatePositive rhoImaginary
          calc
            rhoImaginary = rhoImaginary + 0 := by ring1
            _ < rhoImaginary + imaginaryCoordinate := shifted
        exact (square_lt_square_of_nonneg_of_lt imaginaryNonnegative strict).le
      have exteriorStrict :
          1 < (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 := by
        calc
          1 ≤ (1 + rhoReal) ^ 2 + rhoImaginary ^ 2 := realExterior
          _ < (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 :=
            calc
              (1 + rhoReal) ^ 2 + rhoImaginary ^ 2 <
                  (1 + rhoReal + yReal) ^ 2 + rhoImaginary ^ 2 :=
                RFAP.ConstructiveFraction.add_lt_add_right_direct
                  baseRealSquareStrict (rhoImaginary ^ 2)
              _ ≤ (1 + rhoReal + yReal) ^ 2 +
                  (rhoImaginary + imaginaryCoordinate) ^ 2 :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  le_rfl baseImaginarySquareLe
      have translatedIdentity :
          (1 + rhoReal + yReal) ^ 2 +
              (rhoImaginary + imaginaryCoordinate) ^ 2 =
            (1 + rhoReal + yReal) ^ 2 +
              (1 + rhoImaginary + yImaginary) ^ 2 := by
        dsimp only [imaginaryCoordinate]
        ring1
      rw [translatedIdentity] at exteriorStrict
      exact (not_lt_of_ge translatedInside exteriorStrict)

/-- In the diagonal case, failure of complete-denominator growth would force
the following ordinary continuant step not to grow.  This is the integral
form of the four reflected copies of `northeast_lune_exterior`. -/
theorem diagonal_combination_norm_le_of_complete_failure
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : normNat previous < normNat current)
    (digitDiagonal : IsDiagonal (digit (next fraction nonterminal)))
    (completeFailure :
      normSq
          ((next fraction nonterminal).value * toGaussian current +
            toGaussian previous) ≤
        (normNat current : Coordinate)) :
    normNat
        (digit (next fraction nonterminal) * current + previous) ≤
      normNat current := by
  let nextFraction := next fraction nonterminal
  let nextValue := nextFraction.value
  let nextDigit := digit nextFraction
  let rho := residual nextFraction
  let currentValue := toGaussian current
  let previousValue := toGaussian previous
  have currentNonzero : current ≠ 0 := by
    intro currentZero
    rw [currentZero] at previousShorter
    change normNat previous < 0 at previousShorter
    omega
  have currentValueNonzero : currentValue ≠ 0 := by
    intro currentValueZero
    exact currentNonzero (toGaussian_eq_zero.mp currentValueZero)
  let ratio := previousValue * currentValue⁻¹
  have ratioMulCurrent : ratio * currentValue = previousValue := by
    dsimp only [ratio]
    calc
      (previousValue * currentValue⁻¹) * currentValue =
          previousValue * (currentValue⁻¹ * currentValue) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
      _ = previousValue * 1 := by
        rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
          RFAP.ConstructiveGaussian.Gaussian.inv_mul _ currentValueNonzero]
      _ = previousValue :=
        RFAP.ConstructiveGaussian.Gaussian.mul_one _
  have ratioInside : normSq ratio < 1 := by
    have currentNormPositive : 0 < normSq currentValue :=
      normSq_pos currentValueNonzero
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := normSq currentValue) _ currentNormPositive
    calc
      normSq ratio * normSq currentValue =
          normSq (ratio * currentValue) := by
        exact (normSq_mul ratio currentValue).symm
      _ = normSq previousValue := by rw [ratioMulCurrent]
      _ = (normNat previous : Coordinate) := normSq_toGaussian previous
      _ < (normNat current : Coordinate) :=
        RFAP.ConstructiveFraction.natCast_lt_direct previousShorter
      _ = normSq currentValue := (normSq_toGaussian current).symm
      _ = 1 * normSq currentValue := by ring1
  have decomposition : nextValue = toGaussian nextDigit + rho :=
    value_eq_digit_add_residual nextFraction
  have completeIdentity :
      (nextValue + ratio) * currentValue =
        nextValue * currentValue + previousValue := by
    rw [← ratioMulCurrent]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  have normalizedComplete : normSq (nextValue + ratio) ≤ 1 := by
    have currentNormPositive : 0 < normSq currentValue :=
      normSq_pos currentValueNonzero
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := normSq currentValue) _ currentNormPositive
    calc
      normSq (nextValue + ratio) * normSq currentValue =
          normSq ((nextValue + ratio) * currentValue) := by rw [normSq_mul]
      _ = normSq (nextValue * currentValue + previousValue) := by
        rw [completeIdentity]
      _ ≤ (normNat current : Coordinate) := completeFailure
      _ = normSq currentValue := (normSq_toGaussian current).symm
      _ = 1 * normSq currentValue := by ring1
  have rhoSquare := RFAP.HurwitzNearest.remainder_mem nextFraction.value
  have rhoRealUpper : rho.re ≤ (1 / 2 : Coordinate) := rhoSquare.2.1.le
  have rhoImaginaryUpper :
      rho.im ≤ (1 / 2 : Coordinate) := rhoSquare.2.2.2.le
  have ratioCoordinates : ratio.re ^ 2 + ratio.im ^ 2 < 1 := by
    exact ratioInside
  have baseNorm : normSq (toGaussian nextDigit + ratio) ≤ 1 := by
    change IsDiagonal nextDigit at digitDiagonal
    rcases digitDiagonal with digitCase | digitCase | digitCase | digitCase
    · rw [digitCase] at decomposition ⊢
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := imaginaryUnit) imaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := 1) one_isGaussianUnit
      change 1 ≤ normSq (nextValue - toGaussian imaginaryUnit) at verticalExterior
      change 1 ≤ normSq (nextValue - toGaussian 1) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := northeast_lune_exterior
        rho.re rho.im ratio.re ratio.im rhoSquare.1 rhoSquare.2.2.1
        ratioCoordinates
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian, Int.cast_zero, Int.cast_one] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_one] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
            Int.cast_one] at normalizedComplete
          exact normalizedComplete)
      simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        Int.cast_one]
      exact lune
    · rw [digitCase] at decomposition ⊢
      have reflectedImaginaryLower :
          -(1 / 2 : Coordinate) ≤ -rho.im := by
        have reversed :=
          RFAP.ConstructiveFraction.neg_le_neg_direct rhoImaginaryUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -imaginaryUnit) negImaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := 1) one_isGaussianUnit
      change 1 ≤ normSq (nextValue - toGaussian (-imaginaryUnit)) at verticalExterior
      change 1 ≤ normSq (nextValue - toGaussian 1) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := northeast_lune_exterior
        rho.re (-rho.im) ratio.re (-ratio.im) rhoSquare.1
        reflectedImaginaryLower
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            Int.cast_neg, Int.cast_zero, Int.cast_one] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_one] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
            Int.cast_neg, Int.cast_one] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        Int.cast_neg, Int.cast_one]
      convert lune using 1
      all_goals ring1
    · rw [digitCase] at decomposition ⊢
      have reflectedRealLower :
          -(1 / 2 : Coordinate) ≤ -rho.re := by
        have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct rhoRealUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := imaginaryUnit) imaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -1) negOne_isGaussianUnit
      change 1 ≤ normSq (nextValue - toGaussian imaginaryUnit) at verticalExterior
      change 1 ≤ normSq (nextValue - toGaussian (-1)) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := northeast_lune_exterior
        (-rho.re) rho.im (-ratio.re) ratio.im reflectedRealLower
        rhoSquare.2.2.1
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian, Int.cast_neg, Int.cast_zero, Int.cast_one] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_neg, Int.cast_one] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
            Int.cast_neg, Int.cast_one] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        Int.cast_neg, Int.cast_one]
      convert lune using 1
      all_goals ring1
    · rw [digitCase] at decomposition ⊢
      have reflectedRealLower :
          -(1 / 2 : Coordinate) ≤ -rho.re := by
        have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct rhoRealUpper
        simpa only [neg_neg] using reversed
      have reflectedImaginaryLower :
          -(1 / 2 : Coordinate) ≤ -rho.im := by
        have reversed :=
          RFAP.ConstructiveFraction.neg_le_neg_direct rhoImaginaryUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -imaginaryUnit) negImaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -1) negOne_isGaussianUnit
      change 1 ≤ normSq (nextValue - toGaussian (-imaginaryUnit)) at verticalExterior
      change 1 ≤ normSq (nextValue - toGaussian (-1)) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := northeast_lune_exterior
        (-rho.re) (-rho.im) (-ratio.re) (-ratio.im) reflectedRealLower
        reflectedImaginaryLower
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, imaginaryUnit,
            toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            Int.cast_neg, Int.cast_zero, Int.cast_one] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im, toGaussian,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_neg, Int.cast_one] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [normSq,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
            Int.cast_neg, Int.cast_one] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        Int.cast_neg, Int.cast_one]
      convert lune using 1
      all_goals ring1
  change normNat (nextDigit * current + previous) ≤ normNat current
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  have combinationIdentity :
      (toGaussian nextDigit + ratio) * currentValue =
        toGaussian (nextDigit * current + previous) := by
    calc
      (toGaussian nextDigit + ratio) * currentValue =
          toGaussian nextDigit * currentValue + ratio * currentValue := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = toGaussian nextDigit * currentValue + previousValue := by
        rw [ratioMulCurrent]
      _ = toGaussian (nextDigit * current + previous) := by
        rw [toGaussian_add, toGaussian_mul]
  have currentNormNonnegative : 0 ≤ normSq currentValue :=
    normSq_nonneg currentValue
  calc
    (normNat (nextDigit * current + previous) : Coordinate) =
        normSq (toGaussian (nextDigit * current + previous)) :=
      (normSq_toGaussian _).symm
    _ = normSq ((toGaussian nextDigit + ratio) * currentValue) := by
      rw [combinationIdentity]
    _ = normSq (toGaussian nextDigit + ratio) * normSq currentValue :=
      normSq_mul _ _
    _ ≤ 1 * normSq currentValue :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        baseNorm currentNormNonnegative
    _ = normSq currentValue := by ring1
    _ = (normNat current : Coordinate) := normSq_toGaussian current

/-- Every nonterminal stage of the finite Hurwitz trace has a complete
denominator strictly larger than its current continuant denominator.  The
proof is induction on the displayed trace: a hypothetical failure forces a
diagonal digit, the lune calculation forces the following ordinary
continuant not to grow, and finite denominator growth rules that out. -/
theorem completeDenominatorGrowth_of_generated
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0) :
    (normNat stage.current.denominator : Coordinate) <
      normSq (stage.completeDenominator nonterminal) := by
  induction generated with
  | first =>
      have nextLarge := next_normSq_ge_two source nonterminal
      change (1 : Coordinate) <
        normSq
          ((next source nonterminal).value * toGaussian 1 + toGaussian 0)
      rw [toGaussian_one, toGaussian_zero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      exact (show (1 : Coordinate) < 2 by decide).trans_le nextLarge
  | @advance previousStage generated previousNonterminal inductionHypothesis =>
      let advanced :=
        RFAP.HurwitzTrace.advanceStage previousStage previousNonterminal
      let nextValue := (next advanced.quotient nonterminal).value
      have previousCompleteGrowth :=
        inductionHypothesis previousNonterminal
      have nextNormPositive : 0 < normSq nextValue := by
        have nextLarge := next_normSq_ge_two advanced.quotient nonterminal
        exact (show (0 : Coordinate) < 2 by decide).trans_le nextLarge
      have scaledPreviousGrowth :
          normSq nextValue *
              normSq (toGaussian advanced.previous.denominator) <
            normSq
              (nextValue * toGaussian advanced.current.denominator +
                toGaussian advanced.previous.denominator) := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            nextNormPositive previousCompleteGrowth
        calc
          normSq nextValue *
                normSq (toGaussian advanced.previous.denominator) =
              normSq nextValue *
                (normNat previousStage.current.denominator : Coordinate) := by
            change normSq nextValue *
                normSq (toGaussian previousStage.current.denominator) =
              normSq nextValue *
                (normNat previousStage.current.denominator : Coordinate)
            rw [normSq_toGaussian]
          _ < normSq nextValue *
                normSq
                  (previousStage.completeDenominator previousNonterminal) :=
            scaled
          _ = normSq
                (nextValue *
                  previousStage.completeDenominator previousNonterminal) := by
            rw [normSq_mul]
          _ = normSq (advanced.completeDenominator nonterminal) := by
            change normSq
                ((next (next previousStage.quotient previousNonterminal)
                    nonterminal).value *
                  previousStage.completeDenominator previousNonterminal) =
              normSq
                ((RFAP.HurwitzTrace.advanceStage previousStage
                  previousNonterminal).completeDenominator nonterminal)
            rw [advanceStage_completeDenominator previousStage
              previousNonterminal nonterminal]
          _ = normSq
                (nextValue * toGaussian advanced.current.denominator +
                  toGaussian advanced.previous.denominator) := rfl
      have currentNonzero : advanced.current.denominator ≠ 0 := by
        intro currentZero
        have growth := stage_denominatorGrowth
          (Generated.advance generated previousNonterminal)
        rw [currentZero] at growth
        change normNat advanced.previous.denominator < 0 at growth
        omega
      have currentValueNonzero :
          toGaussian advanced.current.denominator ≠ 0 := by
        intro currentValueZero
        exact currentNonzero (toGaussian_eq_zero.mp currentValueZero)
      apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
      intro completeFailure
      have completeFailureValue :
          normSq
                (nextValue * toGaussian advanced.current.denominator +
                  toGaussian advanced.previous.denominator) ≤
            normSq (toGaussian advanced.current.denominator) := by
        calc
          normSq
                (nextValue * toGaussian advanced.current.denominator +
                  toGaussian advanced.previous.denominator) =
              normSq (advanced.completeDenominator nonterminal) := rfl
          _ ≤ (normNat advanced.current.denominator : Coordinate) :=
            completeFailure
          _ = normSq (toGaussian advanced.current.denominator) :=
            (normSq_toGaussian advanced.current.denominator).symm
      have nextSmall : normSq nextValue < 3 :=
        quotient_normSq_lt_three_of_complete_failure
          nextValue (toGaussian advanced.current.denominator)
          (toGaussian advanced.previous.denominator) currentValueNonzero
          scaledPreviousGrowth completeFailureValue
      have nextDiagonal :
          IsDiagonal (digit (next advanced.quotient nonterminal)) :=
        next_digit_isDiagonal_of_normSq_lt_three advanced.quotient
          nonterminal nextSmall
      have followingFailure :=
        diagonal_combination_norm_le_of_complete_failure advanced.quotient
          nonterminal advanced.current.denominator
          advanced.previous.denominator
          (stage_denominatorGrowth
            (Generated.advance generated previousNonterminal))
          nextDiagonal
          (by
            exact completeFailure)
      have followingGrowth := stage_denominatorGrowth
        (Generated.advance
          (Generated.advance generated previousNonterminal) nonterminal)
      change normNat advanced.current.denominator <
        normNat
          (digit (next advanced.quotient nonterminal) *
              advanced.current.denominator +
            advanced.previous.denominator) at followingGrowth
      exact (not_lt_of_ge followingFailure followingGrowth)

theorem one_le_factor_normSq_of_unit_and_diagonal
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    {s t : GaussianInt} (sNorm : normNat s = 1)
    (tNorm : normNat t = 2) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next fraction nonterminal).value) := by
  have sUnit := isGaussianUnit_of_normNat_eq_one sNorm
  have productLarge :
      4 ≤ normSq
        (toGaussian t * (next fraction nonterminal).value) := by
    rw [normSq_mul, normSq_toGaussian, tNorm]
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (next_normSq_ge_two fraction nonterminal)
      (show (0 : Coordinate) ≤ 2 by decide)
    calc
      4 = (2 : Coordinate) * 2 := by ring1
      _ ≤ 2 * normSq (next fraction nonterminal).value := scaled
  rw [normSq_sub_comm]
  exact one_le_normSq_sub_unit_of_four_le sUnit productLarge

/-- If the previous-basis coefficient is a unit, a denominator shorter than
the current continuant forces the Lakein factor outside the unit circle.
After multiplying by the conjugate unit, the only nontrivial coefficient is
a diagonal corner; that case is exactly `StageGeometry.cornerSafe`. -/
theorem one_le_factor_normSq_of_unit_previousCoefficient
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (tNorm : normNat t = 1)
    (denominatorSmaller :
      normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        normNat stage.current.denominator) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next stage.quotient nonterminal).value) := by
  let coefficient := conjugate t * s
  have tUnit := isGaussianUnit_of_normNat_eq_one tNorm
  have unitCancellation : t * conjugate t = 1 :=
    self_mul_conjugate_of_isGaussianUnit tUnit
  have associated : t * coefficient = s := by
    dsimp only [coefficient]
    calc
      t * (conjugate t * s) = (t * conjugate t) * s := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      _ = 1 * s := by rw [unitCancellation]
      _ = s := RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul s
  have normalizedDenominator :
      normNat
          (coefficient * stage.current.denominator +
            stage.previous.denominator) <
        normNat stage.current.denominator := by
    have multipliedIdentity :
        t *
            (coefficient * stage.current.denominator +
              stage.previous.denominator) =
          s * stage.current.denominator +
            t * stage.previous.denominator := by
      rw [← associated]
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
        ring1
    have multipliedNorm :
        normNat
            (t *
              (coefficient * stage.current.denominator +
                stage.previous.denominator)) =
          normNat
            (coefficient * stage.current.denominator +
              stage.previous.denominator) := by
      rw [normNat_mul, tNorm, Nat.one_mul]
    rw [← multipliedIdentity] at denominatorSmaller
    rw [multipliedNorm] at denominatorSmaller
    exact denominatorSmaller
  have coefficientSmall : normNat coefficient < 4 :=
    coefficient_normNat_lt_four_of_combination_norm_le coefficient
      stage.current.denominator stage.previous.denominator
      (stage_denominatorGrowth generated) normalizedDenominator.le
  have coefficientCases :=
    normNat_eq_zero_or_one_or_two_of_lt_four coefficient coefficientSmall
  rcases coefficientCases with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientIsZero := eq_zero_of_normNat_eq_zero coefficientZero
    have sIsZero : s = 0 := by
      rw [← associated, coefficientIsZero,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero]
    rw [sIsZero, toGaussian_zero]
    have nextLarge := next_normSq_ge_two stage.quotient nonterminal
    have factorNorm :
        normSq
            (0 - toGaussian t *
              (next stage.quotient nonterminal).value) =
          normSq (next stage.quotient nonterminal).value := by
      rw [RFAP.ConstructiveGaussian.Gaussian.zero_sub, normSq_neg,
        normSq_mul, normSq_toGaussian, tNorm]
      ring1
    rw [factorNorm]
    exact (show (1 : Coordinate) ≤ 2 by decide).trans nextLarge
  · have sNorm : normNat s = 1 := by
      rw [← associated, normNat_mul, tNorm, Nat.one_mul,
        coefficientUnit]
    exact one_le_factor_normSq_of_unit_coefficients stage.quotient
      nonterminal sNorm tNorm
  · have coefficientIsDiagonal :=
      isDiagonal_of_normNat_eq_two coefficientDiagonal
    apply RFAP.ConstructiveFraction.le_of_not_gt_direct
    intro factorInside
    have factorIdentity :
        toGaussian s -
            toGaussian t * (next stage.quotient nonterminal).value =
          toGaussian t *
            (toGaussian coefficient -
              (next stage.quotient nonterminal).value) := by
      rw [← associated, toGaussian_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    have futureCorner :
        normSq
            ((next stage.quotient nonterminal).value -
              toGaussian coefficient) < 1 := by
      rw [factorIdentity, normSq_mul, normSq_toGaussian, tNorm,
        Nat.cast_one] at factorInside
      rw [normSq_sub_comm]
      calc
        normSq
            (toGaussian coefficient -
              (next stage.quotient nonterminal).value) =
          1 * normSq
            (toGaussian coefficient -
              (next stage.quotient nonterminal).value) := by ring1
        _ < 1 := factorInside
    exact (geometry_of_generated generated).cornerSafe nonterminal
      coefficient coefficientIsDiagonal
      ⟨normalizedDenominator.le, futureCorner⟩

/-- The quadrance-four current coefficient in the diagonal-previous branch
also reduces to `cornerSafe`: it factors as the prescribed diagonal times a
second diagonal. -/
theorem one_le_factor_normSq_of_four_and_diagonal
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (sNorm : normNat s = 4)
    (tNorm : normNat t = 2)
    (denominatorSmaller :
      normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        normNat stage.current.denominator) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next stage.quotient nonterminal).value) := by
  have tDiagonal := isDiagonal_of_normNat_eq_two tNorm
  rcases exists_diagonal_right_factor_of_four_and_diagonal sNorm tDiagonal with
    ⟨corner, cornerDiagonal, associated⟩
  have denominatorIdentity :
      s * stage.current.denominator + t * stage.previous.denominator =
        t *
          (corner * stage.current.denominator +
            stage.previous.denominator) := by
    rw [associated]
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
      simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
      ring1
  have cornerCombinationNotLarger :
      normNat
          (corner * stage.current.denominator +
            stage.previous.denominator) ≤
        normNat stage.current.denominator := by
    rw [denominatorIdentity, normNat_mul, tNorm] at denominatorSmaller
    omega
  apply RFAP.ConstructiveFraction.le_of_not_gt_direct
  intro factorInside
  have factorIdentity :
      toGaussian s -
          toGaussian t * (next stage.quotient nonterminal).value =
        toGaussian t *
          (toGaussian corner -
            (next stage.quotient nonterminal).value) := by
    rw [associated, toGaussian_mul]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  rw [factorIdentity, normSq_mul, normSq_toGaussian, tNorm,
    Nat.cast_ofNat] at factorInside
  have cornerDistanceNonnegative :
      0 ≤ normSq
        (toGaussian corner -
          (next stage.quotient nonterminal).value) :=
    normSq_nonneg _
  have cornerDistanceScaled :
      normSq
          (toGaussian corner -
            (next stage.quotient nonterminal).value) ≤
        2 * normSq
          (toGaussian corner -
            (next stage.quotient nonterminal).value) := by
    calc
      normSq
            (toGaussian corner -
              (next stage.quotient nonterminal).value) =
          1 * normSq
            (toGaussian corner -
              (next stage.quotient nonterminal).value) := by ring1
      _ ≤ 2 * normSq
            (toGaussian corner -
              (next stage.quotient nonterminal).value) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) cornerDistanceNonnegative
  have futureCorner :
      normSq
          ((next stage.quotient nonterminal).value -
            toGaussian corner) < 1 := by
    rw [normSq_sub_comm]
    exact cornerDistanceScaled.trans_lt factorInside
  exact (geometry_of_generated generated).cornerSafe nonterminal corner
    cornerDiagonal ⟨cornerCombinationNotLarger, futureCorner⟩

/-- All nonexceptional current coefficients in the diagonal-previous branch.
The only omitted lattice shape is quadrance five. -/
theorem one_le_factor_normSq_of_diagonal_previousCoefficient_of_not_five
    {source : Fraction} {stage : Stage source}
    (generated : Generated source stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (tNorm : normNat t = 2)
    (sSmall : normNat s < 6) (sNotFive : normNat s ≠ 5)
    (denominatorSmaller :
      normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        normNat stage.current.denominator) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next stage.quotient nonterminal).value) := by
  have coefficientCases :=
    normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six s sSmall
  rcases coefficientCases with sZero | sUnit | sDiagonal | sFour | sFive
  · have sIsZero := eq_zero_of_normNat_eq_zero sZero
    rw [sIsZero, toGaussian_zero,
      RFAP.ConstructiveGaussian.Gaussian.zero_sub, normSq_neg, normSq_mul,
      normSq_toGaussian, tNorm, Nat.cast_ofNat]
    have nextLarge := next_normSq_ge_two stage.quotient nonterminal
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      nextLarge (show (0 : Coordinate) ≤ 2 by decide)
    calc
      1 ≤ (4 : Coordinate) := by decide
      _ = 2 * 2 := by ring1
      _ ≤ 2 * normSq (next stage.quotient nonterminal).value := scaled
  · exact one_le_factor_normSq_of_unit_and_diagonal stage.quotient
      nonterminal sUnit tNorm
  · exact one_le_factor_normSq_of_diagonal_coefficients stage.quotient
      nonterminal sDiagonal tNorm
  · exact one_le_factor_normSq_of_four_and_diagonal generated nonterminal
      s t sFour tNorm denominatorSmaller
  · exact (sNotFive sFive).elim

/-- Once the complete denominator is strictly larger than the current
continuant denominator, failure of Lakein's large-`t` test leaves only the
three integral quadrances below four. -/
theorem previousCoefficient_normNat_lt_four_of_not_large
    {source : Fraction} (stage : Stage source)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : RFAP.HurwitzRational.ConvergentPair)
    (completeDenominatorGrowth :
      (normNat stage.current.denominator : Coordinate) <
        normSq (stage.completeDenominator nonterminal))
    (notLarge : ¬
      (4 : Coordinate) *
          (normNat stage.current.denominator : Coordinate) <
        (normNat
            (previousCoefficient stage.current stage.previous competitor) :
              Coordinate) *
          normSq (stage.completeDenominator nonterminal)) :
    normNat
        (previousCoefficient stage.current stage.previous competitor) < 4 := by
  let coefficient :=
    previousCoefficient stage.current stage.previous competitor
  have smallProduct :
      (normNat coefficient : Coordinate) *
          normSq (stage.completeDenominator nonterminal) ≤
        4 * (normNat stage.current.denominator : Coordinate) :=
    RFAP.ConstructiveFraction.le_of_not_gt_direct notLarge
  apply Nat.lt_of_not_ge
  intro fourLeCoefficient
  have castFourLeCoefficient :
      (4 : Coordinate) ≤ (normNat coefficient : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct fourLeCoefficient
  have fourPositive : (0 : Coordinate) < 4 := by decide
  have completeNonnegative :=
    normSq_nonneg (stage.completeDenominator nonterminal)
  have scaledGrowth :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      fourPositive completeDenominatorGrowth
  have scaledCoefficient :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      castFourLeCoefficient completeNonnegative
  have impossible :
      4 * (normNat stage.current.denominator : Coordinate) <
        (normNat coefficient : Coordinate) *
          normSq (stage.completeDenominator nonterminal) :=
    scaledGrowth.trans_le scaledCoefficient
  exact (not_lt_of_ge smallProduct impossible)

/-- Clearing the next complete quotient denominator turns a Lakein factor
into an exact Gaussian-integer numerator. -/
theorem factor_mul_remainder (fraction : Fraction)
    (nonterminal : remainder fraction ≠ 0) (s t : GaussianInt) :
    (toGaussian s - toGaussian t * (next fraction nonterminal).value) *
        toGaussian (remainder fraction) =
      toGaussian (s * remainder fraction - t * fraction.denominator) := by
  have nextClears :
      (next fraction nonterminal).value * toGaussian (remainder fraction) =
        toGaussian fraction.denominator :=
    (next fraction nonterminal).value_mul_denominator
  calc
    (toGaussian s - toGaussian t * (next fraction nonterminal).value) *
          toGaussian (remainder fraction) =
        toGaussian s * toGaussian (remainder fraction) -
          toGaussian t *
            ((next fraction nonterminal).value *
              toGaussian (remainder fraction)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = toGaussian s * toGaussian (remainder fraction) -
          toGaussian t * toGaussian fraction.denominator := by
      rw [nextClears]
    _ = toGaussian (s * remainder fraction - t * fraction.denominator) := by
      rw [toGaussian_sub, toGaussian_mul, toGaussian_mul]

theorem factor_normSq_mul_remainder_norm
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (s t : GaussianInt) :
    normSq
          (toGaussian s -
            toGaussian t * (next fraction nonterminal).value) *
        (normNat (remainder fraction) : Coordinate) =
      (normNat (s * remainder fraction - t * fraction.denominator) :
        Coordinate) := by
  rw [← normSq_toGaussian, ← normSq_mul,
    factor_mul_remainder, normSq_toGaussian]

/-- Square-root-free cancellation after clearing the nonzero Euclidean
remainder. -/
theorem one_le_factor_normSq_of_remainder_norm_le
    (fraction : Fraction) (nonterminal : remainder fraction ≠ 0)
    (s t : GaussianInt)
    (clearedExterior :
      normNat (remainder fraction) ≤
        normNat (s * remainder fraction - t * fraction.denominator)) :
    1 ≤ normSq
      (toGaussian s -
        toGaussian t * (next fraction nonterminal).value) := by
  have remainderPositive :
      (0 : Coordinate) < (normNat (remainder fraction) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct (normNat_pos nonterminal)
  have castExterior :
      (normNat (remainder fraction) : Coordinate) ≤
        (normNat (s * remainder fraction - t * fraction.denominator) :
          Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct clearedExterior
  have productExterior :
      1 * (normNat (remainder fraction) : Coordinate) ≤
        normSq
            (toGaussian s -
              toGaussian t * (next fraction nonterminal).value) *
          (normNat (remainder fraction) : Coordinate) := by
    calc
      1 * (normNat (remainder fraction) : Coordinate) =
          (normNat (remainder fraction) : Coordinate) := by ring1
      _ ≤ (normNat
            (s * remainder fraction - t * fraction.denominator) :
              Coordinate) := castExterior
      _ = normSq
            (toGaussian s -
              toGaussian t * (next fraction nonterminal).value) *
          (normNat (remainder fraction) : Coordinate) :=
        (factor_normSq_mul_remainder_norm fraction nonterminal s t).symm
  exact RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    productExterior remainderPositive

/-- Lakein's second-kind comparison, conditional only on the finite
quadrance-five denominator certificate.  All other branches are discharged
by complete-denominator growth and the explicit unit/diagonal geometry. -/
theorem Stage.atLeastAsGoodAs_of_generated_of_normFiveDenominatorSafe
    {source : Fraction} (stage : Stage source)
    (generated : Generated source stage)
    (exceptionalSafe : NormFiveDenominatorSafe stage)
    (nonterminal : remainder stage.quotient ≠ 0)
    (competitor : RFAP.HurwitzRational.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      normNat competitor.denominator < normNat stage.current.denominator) :
    AtLeastAsGoodAs source.value stage.current competitor := by
  let s := currentCoefficient stage.current stage.previous competitor
  let t := previousCoefficient stage.current stage.previous competitor
  have denominatorDecomposition :
      s * stage.current.denominator + t * stage.previous.denominator =
        competitor.denominator := by
    dsimp only [s, t]
    exact competitor_denominator_decomposition stage.unitDeterminant
  have coefficientDenominatorSmaller :
      normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        normNat stage.current.denominator := by
    rw [denominatorDecomposition]
    exact denominatorSmaller
  have completeGrowth :=
    completeDenominatorGrowth_of_generated generated nonterminal
  by_cases large :
      (4 : Coordinate) *
            (normNat stage.current.denominator : Coordinate) <
          (normNat t : Coordinate) *
            normSq (stage.completeDenominator nonterminal)
  · exact stage.atLeastAsGoodAs_of_large_previousCoefficient nonterminal
      competitor competitorDenominatorNonzero denominatorSmaller (by
        change (4 : Coordinate) *
              (normNat stage.current.denominator : Coordinate) <
            (normNat t : Coordinate) *
              normSq (stage.completeDenominator nonterminal)
        exact large)
  · have tSmall : normNat t < 4 :=
      previousCoefficient_normNat_lt_four_of_not_large stage nonterminal
        competitor completeGrowth (by
          change ¬ ((4 : Coordinate) *
                (normNat stage.current.denominator : Coordinate) <
              (normNat t : Coordinate) *
                normSq (stage.completeDenominator nonterminal))
          exact large)
    have tCases := normNat_eq_zero_or_one_or_two_of_lt_four t tSmall
    have factorExterior :
        1 ≤ normSq
          (toGaussian s -
            toGaussian t * (next stage.quotient nonterminal).value) := by
      rcases tCases with tZero | tUnit | tDiagonal
      · have tIsZero := eq_zero_of_normNat_eq_zero tZero
        have denominatorAsMultiple :
            competitor.denominator = s * stage.current.denominator := by
          rw [← denominatorDecomposition, tIsZero,
            RFAP.ConstructiveGaussianHeight.GaussianInt.zero_mul,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero]
        have multipleNormSmaller :
            normNat s * normNat stage.current.denominator <
              normNat stage.current.denominator := by
          rw [← normNat_mul, ← denominatorAsMultiple]
          exact denominatorSmaller
        have sZero : normNat s = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro sPositive
          have oneLeS : 1 ≤ normNat s := sPositive
          have currentLeMultiple :
              normNat stage.current.denominator ≤
                normNat s * normNat stage.current.denominator := by
            have scaled := Nat.mul_le_mul_right
              (normNat stage.current.denominator) oneLeS
            rw [Nat.one_mul] at scaled
            exact scaled
          exact (not_lt_of_ge currentLeMultiple multipleNormSmaller)
        have sIsZero := eq_zero_of_normNat_eq_zero sZero
        have denominatorZero : competitor.denominator = 0 := by
          rw [denominatorAsMultiple, sIsZero,
            RFAP.ConstructiveGaussianHeight.GaussianInt.zero_mul]
        exact (competitorDenominatorNonzero denominatorZero).elim
      · exact one_le_factor_normSq_of_unit_previousCoefficient generated
          nonterminal s t tUnit coefficientDenominatorSmaller
      · have sSmall :=
          currentCoefficient_normNat_lt_six_of_diagonal_previous s t
            stage.current.denominator stage.previous.denominator
            (stage_denominatorGrowth generated) tDiagonal
            coefficientDenominatorSmaller
        by_cases sFive : normNat s = 5
        · have notShorter := exceptionalSafe s t sFive tDiagonal
          exact (not_lt_of_ge notShorter coefficientDenominatorSmaller).elim
        · exact
            one_le_factor_normSq_of_diagonal_previousCoefficient_of_not_five
              generated nonterminal s t tDiagonal sSmall sFive
              coefficientDenominatorSmaller
    exact stage.atLeastAsGoodAs_of_one_le_factor_normSq nonterminal competitor
      (by
        change 1 ≤ normSq
          (toGaussian s -
            toGaussian t * (next stage.quotient nonterminal).value)
        exact factorExterior)

end RFAP.HurwitzGeometry
