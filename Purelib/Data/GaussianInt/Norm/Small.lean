module
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Gaussian integers of small quadrance

Displayed coordinate bounds classify the small integral quadrances and construct
explicit unit or diagonal factors. The same retained coordinates give exact
Gaussian-rational norm comparisons without square roots or infinite lattices.
-/

namespace Purelib.Data.GaussianInt.Norm.Small

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.GaussianInt
open Purelib.Data.GaussianInt.Norm
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Cast
open Purelib.Data.Rat.Fraction.Order

public section

/-- The Gaussian integer with real coordinate zero and imaginary coordinate one. -/
@[expose] def imaginaryUnit : GaussianInt := ⟨0, 1⟩

/-- The real coordinate of the integral imaginary unit is zero. -/
@[simp] theorem imaginaryUnit_re : imaginaryUnit.re = 0 := rfl

/-- The imaginary coordinate of the integral imaginary unit is one. -/
@[simp] theorem imaginaryUnit_im : imaginaryUnit.im = 1 := rfl

/-- The Gaussian integer is one of the four displayed units 1, -1, i and -i. -/
@[expose] def IsGaussianUnit (value : GaussianInt) : Prop :=
  value = 1 ∨ value = -1 ∨
    value = imaginaryUnit ∨ value = -imaginaryUnit

/-- Both integral Gaussian coordinates are independently one or minus one. -/
@[expose] def IsDiagonal (value : GaussianInt) : Prop :=
  value = ⟨1, 1⟩ ∨ value = ⟨1, -1⟩ ∨
    value = ⟨-1, 1⟩ ∨ value = ⟨-1, -1⟩

/-- Negate the conjugate of the retained Gaussian integer. -/
@[expose] def cornerTurn (value : GaussianInt) : GaussianInt :=
  -Norm.Basic.conjugate value

/-- The corner turn negates the original real coordinate. -/
@[simp] theorem cornerTurn_re (value : GaussianInt) :
    (cornerTurn value).re = -value.re := rfl

/-- The corner turn retains the original imaginary coordinate. -/
@[simp] theorem cornerTurn_im (value : GaussianInt) :
    (cornerTurn value).im = value.im := by
  simp only [cornerTurn, Norm.Basic.conjugate,
    GaussianInt.neg_im]
  ring1

/-- An integer of square below four is minus one, zero or one.

The strict square bound forces both coordinate bounds; the resulting integral interval has exactly these three values.
-/
private theorem coordinate_cases_of_square_lt_four {value : Int}
    (small : value * value < 4) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  have lower : -(2 : Int) < value := by
    apply Int.Order.lt_of_not_le
    intro reverse
    have magnitude : (2 : Int) ≤ -value := by omega
    have first : (4 : Int) ≤ 2 * (-value) :=
      Int.Order.mul_le_mul_of_nonneg_left magnitude (by decide)
    have second : 2 * (-value) ≤ (-value) * (-value) :=
      Int.Order.mul_le_mul_of_nonneg_right magnitude (by omega)
    have squareBound : (4 : Int) ≤ value * value := by
      have retained := Int.Order.le_trans first second
      have scalar : (-value) * (-value) = value * value := by ring1
      exact scalar ▸ retained
    omega
  have upper : value < 2 := by
    apply Int.Order.lt_of_not_le
    intro magnitude
    have first : (4 : Int) ≤ 2 * value :=
      Int.Order.mul_le_mul_of_nonneg_left magnitude (by decide)
    have second : 2 * value ≤ value * value :=
      Int.Order.mul_le_mul_of_nonneg_right magnitude (by omega)
    have squareBound := Int.Order.le_trans first second
    omega
  omega

/-- An integer strictly between minus two and two is minus one, zero or one.

The two strict integral bounds exclude every other integer without requiring an enumeration of an unbounded carrier. -/
public theorem coordinate_cases_of_neg_two_lt_lt_two {value : Int}
    (lower : -(2 : Int) < value) (upper : value < 2) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  omega

/-- An integer of square below nine is one of minus two, minus one, zero, one and two.

The strict square bound forces the coordinate into the five displayed integral values, including both signs and zero. -/
private theorem coordinate_cases_of_square_lt_nine {value : Int}
    (small : value * value < 9) :
    value = -2 ∨ value = -1 ∨ value = 0 ∨ value = 1 ∨ value = 2 := by
  have lower : -(3 : Int) < value := by
    apply Int.Order.lt_of_not_le
    intro reverse
    have magnitude : (3 : Int) ≤ -value := by omega
    have first : (9 : Int) ≤ 3 * (-value) :=
      Int.Order.mul_le_mul_of_nonneg_left magnitude (by decide)
    have second : 3 * (-value) ≤ (-value) * (-value) :=
      Int.Order.mul_le_mul_of_nonneg_right magnitude (by omega)
    have squareBound : (9 : Int) ≤ value * value := by
      have retained := Int.Order.le_trans first second
      have scalar : (-value) * (-value) = value * value := by ring1
      exact scalar ▸ retained
    omega
  have upper : value < 3 := by
    apply Int.Order.lt_of_not_le
    intro magnitude
    have first : (9 : Int) ≤ 3 * value :=
      Int.Order.mul_le_mul_of_nonneg_left magnitude (by decide)
    have second : 3 * value ≤ value * value :=
      Int.Order.mul_le_mul_of_nonneg_right magnitude (by omega)
    have squareBound := Int.Order.le_trans first second
    omega
  omega

/-- Gaussian integral quadrance below four is exactly zero, one or two.

Each coordinate square is nonnegative and smaller than four. Combining their three possible coordinates gives the
displayed quadrances. -/
theorem normNat_eq_zero_or_one_or_two_of_lt_four (value : GaussianInt)
    (small : GaussianInt.normNat value < 4) :
    GaussianInt.normNat value = 0 ∨ GaussianInt.normNat value = 1 ∨ GaussianInt.normNat value = 2 := by
  have normIntSmall : GaussianInt.normInt value < 4 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_lt_iff.mpr small
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntSmall
  have realSmall : value.re * value.re < 4 := by omega
  have imaginarySmall : value.im * value.im < 4 := by omega
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary; decide

/-- Gaussian integral quadrance below six is exactly zero, one, two, four or five.

Each coordinate belongs to the five displayed values from the square bound. The strict total bound excludes every other
resulting quadrance. -/
theorem normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
    (value : GaussianInt) (small : GaussianInt.normNat value < 6) :
    GaussianInt.normNat value = 0 ∨ GaussianInt.normNat value = 1 ∨ GaussianInt.normNat value = 2 ∨
      GaussianInt.normNat value = 4 ∨ GaussianInt.normNat value = 5 := by
  have normIntSmall : GaussianInt.normInt value < 6 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_lt_iff.mpr small
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntSmall
  have realSmall : value.re * value.re < 9 := by omega
  have imaginarySmall : value.im * value.im < 9 := by omega
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
  all_goals dsimp only [GaussianInt.normInt] at normIntSmall
  all_goals try omega
  all_goals decide

/-- A Gaussian integer of quadrance one is one of the four displayed units.

The positive quadrance permits precisely one unit coordinate and one zero coordinate, retaining the original real and
imaginary signs. -/
theorem isGaussianUnit_of_normNat_eq_one {value : GaussianInt}
    (unitNorm : GaussianInt.normNat value = 1) : IsGaussianUnit value := by
  have normIntOne : GaussianInt.normInt value = 1 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat, unitNorm]
    rfl
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntOne
  have realSmall : value.re * value.re < 4 := by omega
  have imaginarySmall : value.im * value.im < 4 := by omega
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary
  all_goals dsimp only [GaussianInt.normInt] at normIntOne
  all_goals try (exfalso; revert normIntOne; decide)
  · right
    left
    apply GaussianInt.ext <;> rfl
  · right
    right
    right
    apply GaussianInt.ext <;> rfl
  · right
    right
    left
    rfl
  · left
    rfl

/-- A Gaussian integer of quadrance two has both coordinates equal to one or minus one.

The coordinate square bounds leave the four signed diagonal pairs as the only possible realizations of the stated
quadrance. -/
theorem isDiagonal_of_normNat_eq_two {value : GaussianInt}
    (diagonalNorm : GaussianInt.normNat value = 2) : IsDiagonal value := by
  have normIntTwo : GaussianInt.normInt value = 2 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat, diagonalNorm]
    rfl
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntTwo
  have realSmall : value.re * value.re < 4 := by omega
  have imaginarySmall : value.im * value.im < 4 := by omega
  rcases value with ⟨real, imaginary⟩
  change real * real < 4 at realSmall
  change imaginary * imaginary < 4 at imaginarySmall
  rcases coordinate_cases_of_square_lt_four realSmall with
      realNegative | realZero | realPositive <;>
    rcases coordinate_cases_of_square_lt_four imaginarySmall with
      imaginaryNegative | imaginaryZero | imaginaryPositive
  all_goals subst real; subst imaginary
  all_goals dsimp only [GaussianInt.normInt] at normIntTwo
  all_goals try (exfalso; revert normIntTwo; decide)
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

/-- Every displayed integral Gaussian diagonal has quadrance two. -/
theorem normNat_eq_two_of_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) : GaussianInt.normNat value = 2 := by
  rcases diagonal with rfl | rfl | rfl | rfl <;> decide

/-- A Gaussian integer of quadrance four is a doubled coordinate-axis unit.

The finite coordinate cases retain the nonzero axis, its sign and its factor two exactly. -/
theorem axisDouble_cases_of_normNat_eq_four {value : GaussianInt}
    (fourNorm : GaussianInt.normNat value = 4) :
    value = ⟨2, 0⟩ ∨ value = ⟨-2, 0⟩ ∨
      value = ⟨0, 2⟩ ∨ value = ⟨0, -2⟩ := by
  have normIntFour : GaussianInt.normInt value = 4 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat, fourNorm]
    rfl
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntFour
  have realSmall : value.re * value.re < 9 := by omega
  have imaginarySmall : value.im * value.im < 9 := by omega
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
  all_goals dsimp only [GaussianInt.normInt] at normIntFour
  all_goals try omega
  all_goals decide

/-- A Gaussian integer of quadrance eight has both coordinates equal to two or minus two.

Both retained coordinates have square four; the displayed cases distinguish their original signs independently. -/
theorem doubledDiagonal_cases_of_normNat_eq_eight {value : GaussianInt}
    (eightNorm : GaussianInt.normNat value = 8) :
    value = ⟨2, 2⟩ ∨ value = ⟨2, -2⟩ ∨
      value = ⟨-2, 2⟩ ∨ value = ⟨-2, -2⟩ := by
  have normIntEight : GaussianInt.normInt value = 8 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat, eightNorm]
    rfl
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntEight
  have realSmall : value.re * value.re < 9 := by omega
  have imaginarySmall : value.im * value.im < 9 := by omega
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
  all_goals dsimp only [GaussianInt.normInt] at normIntEight
  all_goals try omega
  all_goals decide

/-- A Gaussian integer of quadrance five has coordinate magnitudes two and one in either
order. -/
theorem normFive_cases_of_normNat_eq_five {value : GaussianInt}
    (fiveNorm : GaussianInt.normNat value = 5) :
    value = ⟨2, 1⟩ ∨ value = ⟨2, -1⟩ ∨
      value = ⟨-2, 1⟩ ∨ value = ⟨-2, -1⟩ ∨
      value = ⟨1, 2⟩ ∨ value = ⟨1, -2⟩ ∨
      value = ⟨-1, 2⟩ ∨ value = ⟨-1, -2⟩ := by
  have normIntFive : GaussianInt.normInt value = 5 := by
    rw [Norm.Basic.normInt_eq_natCast_normNat, fiveNorm]
    rfl
  have imaginaryNonnegative := Int.Order.mul_self_nonneg value.im
  have realNonnegative := Int.Order.mul_self_nonneg value.re
  dsimp only [GaussianInt.normInt] at normIntFive
  have realSmall : value.re * value.re < 9 := by omega
  have imaginarySmall : value.im * value.im < 9 := by omega
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
  all_goals dsimp only [GaussianInt.normInt] at normIntFive
  all_goals try omega
  all_goals decide

/-- Every Gaussian integer of quadrance four has a displayed diagonal quotient by each
prescribed diagonal.

The quadrance-four input is one of the four doubled units. Exhausting its displayed
coordinates and the prescribed diagonal constructs an actual diagonal factor with the
required product identity. -/
theorem exists_diagonal_right_factor_of_four_and_diagonal
    {value diagonal : GaussianInt} (valueNorm : GaussianInt.normNat value = 4)
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

/-- The corner turn preserves the four integral Gaussian diagonals. -/
theorem cornerTurn_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) : IsDiagonal (cornerTurn value) := by
  rcases diagonal with rfl | rfl | rfl | rfl
  · right; right; left; rfl
  · right; right; right; rfl
  · left; rfl
  · right; left; rfl

/-- Conjugating the corner turn gives the negation of the original Gaussian integer.

The real and imaginary coordinate identities are proved separately using the retained conjugation and negation
operations. -/
theorem conjugate_cornerTurn_eq_neg (value : GaussianInt) :
    Norm.Basic.conjugate (cornerTurn value) = -value := by
  apply GaussianInt.ext
  · exact Eq.refl _
  · change -(-(-value.im)) = -value.im
    ring1

/-- A diagonal Gaussian integer times its corner turn is the real Gaussian integer minus
two. -/
theorem mul_cornerTurn_eq_neg_two_of_isDiagonal {value : GaussianInt}
    (diagonal : IsDiagonal value) :
    value * cornerTurn value = -GaussianInt.ofNat 2 := by
  rcases diagonal with rfl | rfl | rfl | rfl <;> decide

/-- The conjugate of each displayed Gaussian unit multiplied by that unit equals one. -/
theorem conjugate_mul_self_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : Norm.Basic.conjugate value * value = 1 := by
  rcases unit with positive | negative | positiveImaginary | negativeImaginary
  · rw [positive]
    rfl
  · rw [negative]
    rfl
  · rw [positiveImaginary]
    rfl
  · rw [negativeImaginary]
    rfl

/-- Each displayed Gaussian unit multiplied by its conjugate equals one. -/
theorem self_mul_conjugate_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : value * Norm.Basic.conjugate value = 1 := by
  rw [GaussianInt.mul_comm]
  exact conjugate_mul_self_of_isGaussianUnit unit

/-- The exact Gaussian-rational embedding of each displayed integral unit has squared
norm one. -/
theorem normSq_toGaussian_eq_one_of_isGaussianUnit {value : GaussianInt}
    (unit : IsGaussianUnit value) : Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) = 1 := by
  rcases unit with positive | negative | positiveImaginary | negativeImaginary
  · rw [positive, GaussianInt.toGaussian_one, Norm.Basic.normSq_one]
  · rw [negative, GaussianInt.toGaussian_neg,
      GaussianInt.toGaussian_one, Norm.Basic.normSq_neg, Norm.Basic.normSq_one]
  · rw [positiveImaginary]
    rfl
  · rw [negativeImaginary, GaussianInt.toGaussian_neg]
    rfl

/-- The real Gaussian integer one is a displayed unit. -/
public theorem one_isGaussianUnit : IsGaussianUnit 1 := Or.inl rfl

/-- The real Gaussian integer minus one is a displayed unit. -/
public theorem negOne_isGaussianUnit : IsGaussianUnit (-1) :=
  Or.inr (Or.inl rfl)

/-- The integral imaginary unit is a displayed Gaussian unit. -/
public theorem imaginaryUnit_isGaussianUnit :
    IsGaussianUnit imaginaryUnit := Or.inr (Or.inr (Or.inl rfl))

/-- The negated integral imaginary unit is a displayed Gaussian unit. -/
public theorem negImaginaryUnit_isGaussianUnit :
    IsGaussianUnit (-imaginaryUnit) := Or.inr (Or.inr (Or.inr rfl))

/-- Any two displayed Gaussian units differ by an explicitly constructed right unit
factor. -/
theorem exists_unit_right_factor_of_units {left right : GaussianInt}
    (leftUnit : IsGaussianUnit left) (rightUnit : IsGaussianUnit right) :
    ∃ unit, IsGaussianUnit unit ∧ left = right * unit := by
  let unit := Norm.Basic.conjugate right * left
  have unitNorm : GaussianInt.normNat unit = 1 := by
    dsimp only [unit]
    rw [Embedding.normNat_mul, Embedding.normNat_conjugate]
    have leftNorm := normSq_toGaussian_eq_one_of_isGaussianUnit leftUnit
    have rightNorm := normSq_toGaussian_eq_one_of_isGaussianUnit rightUnit
    rw [GaussianInt.normSq_toGaussian] at leftNorm rightNorm
    have leftNormNat : GaussianInt.normNat left = 1 :=
      Compatibility.natCast_injective_direct leftNorm
    have rightNormNat : GaussianInt.normNat right = 1 :=
      Compatibility.natCast_injective_direct rightNorm
    rw [leftNormNat, rightNormNat]
  refine ⟨unit, isGaussianUnit_of_normNat_eq_one unitNorm, ?_⟩
  dsimp only [unit]
  calc
    left = 1 * left :=
      (_root_.one_mul left).symm
    _ = (right * Norm.Basic.conjugate right) * left := by
      rw [self_mul_conjugate_of_isGaussianUnit rightUnit]
    _ = right * (Norm.Basic.conjugate right * left) :=
      GaussianInt.mul_assoc _ _ _

/-- Any two integral Gaussian diagonals differ by an explicit right unit factor. -/
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

/-- Reversing a Gaussian-rational difference preserves its squared norm. -/
theorem normSq_sub_comm (left right : Canonical) :
    Gaussian.Norm.Basic.normSq (left - right) = Gaussian.Norm.Basic.normSq (right - left) := by
  simp only [Gaussian.Norm.Basic.normSq,
    Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im]
  ring1

/-- A Gaussian rational of squared norm at least four has squared distance at least one
from every integral unit.

The comparison uses the exact rational squared norm and the original embedded unit. A
finite dot-product square bound supplies the distance inequality without taking
square roots. -/
theorem one_le_normSq_sub_unit_of_four_le {value : Canonical}
    {unit : GaussianInt} (unitProperty : IsGaussianUnit unit)
    (large : 4 ≤ Gaussian.Norm.Basic.normSq value) :
    1 ≤ Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian unit) := by
  let dot : Rational :=
    value.re * (GaussianInt.toGaussian unit).re + value.im * (GaussianInt.toGaussian unit).im
  have unitNorm := normSq_toGaussian_eq_one_of_isGaussianUnit unitProperty
  have valueNonnegative := Norm.Basic.normSq_nonneg value
  have dotCauchy : dot ^ 2 ≤ Gaussian.Norm.Basic.normSq value := by
    have squareNonnegative :
        0 ≤
          (value.re * (GaussianInt.toGaussian unit).im -
            value.im * (GaussianInt.toGaussian unit).re) ^ 2 :=
      Arithmetic.sq_nonneg_direct _
    have differenceNonnegative :
        0 ≤ Gaussian.Norm.Basic.normSq value * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit) - dot ^ 2 := by
      calc
        0 ≤
            (value.re * (GaussianInt.toGaussian unit).im -
              value.im * (GaussianInt.toGaussian unit).re) ^ 2 := squareNonnegative
        _ = Gaussian.Norm.Basic.normSq value * Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit) - dot ^ 2 := by
          dsimp only [dot]
          simp only [Gaussian.Norm.Basic.normSq]
          ring1
    rw [unitNorm] at differenceNonnegative
    have shifted := Arithmetic.add_le_add_right_direct
      differenceNonnegative (dot ^ 2)
    calc
      dot ^ 2 = 0 + dot ^ 2 := by ring1
      _ ≤ (Gaussian.Norm.Basic.normSq value * 1 - dot ^ 2) + dot ^ 2 := shifted
      _ = Gaussian.Norm.Basic.normSq value := by ring1
  have twiceDotLe : 2 * dot ≤ Gaussian.Norm.Basic.normSq value := by
    by_cases dotNonpositive : dot ≤ 0
    · have scaled :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotNonpositive (show (0 : Rational) ≤ 2 by decide)
      calc
        2 * dot ≤ 2 * 0 := scaled
        _ = 0 := by ring1
        _ ≤ Gaussian.Norm.Basic.normSq value := valueNonnegative
    · have fourDotSquares : 4 * dot ^ 2 ≤ 4 * Gaussian.Norm.Basic.normSq value :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotCauchy (show (0 : Rational) ≤ 4 by decide)
      have fourNormLeSquare :
          4 * Gaussian.Norm.Basic.normSq value ≤ Gaussian.Norm.Basic.normSq value * Gaussian.Norm.Basic.normSq value :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          large valueNonnegative
      have squares : (2 * dot) ^ 2 ≤ Gaussian.Norm.Basic.normSq value ^ 2 := by
        calc
          (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
          _ ≤ 4 * Gaussian.Norm.Basic.normSq value := fourDotSquares
          _ ≤ Gaussian.Norm.Basic.normSq value * Gaussian.Norm.Basic.normSq value := fourNormLeSquare
          _ = Gaussian.Norm.Basic.normSq value ^ 2 := by ring1
      exact Arithmetic.le_of_sq_le_sq_direct
        valueNonnegative squares
  have gap : 0 ≤ Gaussian.Norm.Basic.normSq value - 2 * dot :=
    Arithmetic.sub_nonneg_direct twiceDotLe
  calc
    1 ≤ (Gaussian.Norm.Basic.normSq value - 2 * dot) + 1 := le_add_of_nonneg_left gap
    _ = Gaussian.Norm.Basic.normSq value + 1 - 2 * dot := by ring1
    _ = Gaussian.Norm.Basic.normSq value + Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit) - 2 * dot := by
      rw [unitNorm]
    _ = Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian unit) := by
      dsimp only [dot]
      simp only [Gaussian.Norm.Basic.normSq,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im]
      ring1
/-- Every quadrance-two residue modulo a quadrance-five Gaussian integer has an explicit
quadrance-one representative.

The finite coordinate cases provide both the retained unit and integral shift, with
an exact identity expressing the original residue as that unit plus modulus times
shift. -/
theorem exists_unit_shift_of_norm_five_and_two
    {modulus residue : GaussianInt}
    (modulusNorm : GaussianInt.normNat modulus = 5)
    (residueNorm : GaussianInt.normNat residue = 2) :
    ∃ unit shift : GaussianInt,
      GaussianInt.normNat unit = 1 ∧ residue = unit + modulus * shift := by
  have modulusCases :=
    normFive_cases_of_normNat_eq_five modulusNorm
  have residueCases :=
    isDiagonal_of_normNat_eq_two residueNorm
  rcases modulusCases with modulusCase | modulusCase | modulusCase |
      modulusCase | modulusCase | modulusCase | modulusCase | modulusCase <;>
    rcases residueCases with residueCase | residueCase | residueCase |
      residueCase <;>
    subst modulus <;> subst residue
  all_goals first
    | exact ⟨1, 1, by decide, by decide⟩
    | exact ⟨1, -1, by decide, by decide⟩
    | exact ⟨1, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨1, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨-1, 1, by decide, by decide⟩
    | exact ⟨-1, -1, by decide, by decide⟩
    | exact ⟨-1, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨-1, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, 1, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, -1, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, 1, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, -1, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, ⟨0, -1⟩, by decide, by decide⟩

/-- A nonzero Gaussian integer of quadrance at most four has quadrance one, two or four. -/
theorem normNat_eq_one_or_two_or_four_of_nonzero_of_le_four
    (step : GaussianInt) (stepNonzero : step ≠ 0)
    (stepBound : GaussianInt.normNat step ≤ 4) :
    GaussianInt.normNat step = 1 ∨ GaussianInt.normNat step = 2 ∨ GaussianInt.normNat step = 4 := by
  have stepSmall : GaussianInt.normNat step < 6 := by omega
  rcases
      normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
        step stepSmall with
    stepZero | stepOne | stepTwo | stepFour | stepFive
  · have actualZero :=
      Norm.Basic.eq_zero_of_normNat_eq_zero stepZero
    exact False.elim (stepNonzero actualZero)
  · exact Or.inl stepOne
  · exact Or.inr (Or.inl stepTwo)
  · exact Or.inr (Or.inr stepFour)
  · omega
end

end Purelib.Data.GaussianInt.Norm.Small
