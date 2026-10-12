module
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Nearest
public import Purelib.Data.GaussianInt.Norm.DotCross
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Division

open Purelib.Data.GaussianInt.Norm

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Cast

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Nearest-remainder coordinate geometry

The original nearest Gaussian remainder has denominator-scaled dot and cross
bounds. Its half-open integer window gives doubled-norm clearance or an
explicit diagonal factor of the retained denominator.
-/

namespace Purelib.Data.GaussianInt.Division.NearestGeometry

/-- The dot and cross coordinates of the nearest Gaussian remainder lie in the
denominator-scaled half-open square.

Twice each retained integral product is at least minus denominator quadrance and
strictly below denominator quadrance. The original nearest residual and denominator
are used in both coordinate identities. -/
theorem remainder_dot_cross_bounds (fraction : Fraction) :
    - (GaussianInt.normNat fraction.denominator : Int) ≤
        2 * DotCross.dot (Nearest.remainder fraction) fraction.denominator ∧
      2 * DotCross.dot (Nearest.remainder fraction) fraction.denominator <
        (GaussianInt.normNat fraction.denominator : Int) ∧
      - (GaussianInt.normNat fraction.denominator : Int) ≤
        2 * DotCross.cross (Nearest.remainder fraction) fraction.denominator ∧
      2 * DotCross.cross (Nearest.remainder fraction) fraction.denominator <
        (GaussianInt.normNat fraction.denominator : Int) := by
  let remainderValue := Nearest.remainder fraction
  let denominatorNorm : Int := GaussianInt.normNat fraction.denominator
  let residualValue := Nearest.residual fraction
  have embeddedRemainder := Nearest.remainder_toGaussian fraction
  have realEmbedded := congrArg
    Gaussian.Basic.re embeddedRemainder
  have imaginaryEmbedded := congrArg
    Gaussian.Basic.im embeddedRemainder
  simp only [-eq_self, -iff_self, GaussianInt.toGaussian,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im, ← Rat.Fraction.Cast.intCast_eq_fromInt] at realEmbedded imaginaryEmbedded
  change ((Nearest.remainder fraction).re : Rational) =
      (Nearest.residual fraction).re * (fraction.denominator.re : Rational) -
        (Nearest.residual fraction).im * (fraction.denominator.im : Rational)
    at realEmbedded
  change ((Nearest.remainder fraction).im : Rational) =
      (Nearest.residual fraction).re * (fraction.denominator.im : Rational) +
        (Nearest.residual fraction).im * (fraction.denominator.re : Rational)
    at imaginaryEmbedded
  have denominatorNormIdentity := GaussianInt.normSq_toGaussian fraction.denominator
  simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
    ← Rat.Fraction.Cast.intCast_eq_fromInt] at denominatorNormIdentity
  change
    (fraction.denominator.re : Rational) ^ 2 +
        (fraction.denominator.im : Rational) ^ 2 =
      (denominatorNorm : Rational) at denominatorNormIdentity
  have dotIdentity :
      (DotCross.dot remainderValue fraction.denominator : Rational) =
        residualValue.re * (denominatorNorm : Rational) := by
    change
      ((remainderValue.re * fraction.denominator.re +
          remainderValue.im * fraction.denominator.im : Int) : Rational) = _
    rw [Ring.IntCast.add,
      Cast.intCast_mul_direct,
      Cast.intCast_mul_direct]
    change
      (remainderValue.re : Rational) * fraction.denominator.re +
          (remainderValue.im : Rational) * fraction.denominator.im = _
    dsimp only [-eq_self, -iff_self, remainderValue, residualValue]
    rw [realEmbedded, imaginaryEmbedded, ← denominatorNormIdentity]
    ring1
  have crossIdentity :
      (DotCross.cross remainderValue fraction.denominator : Rational) =
        residualValue.im * (denominatorNorm : Rational) := by
    change
      ((remainderValue.im * fraction.denominator.re -
          remainderValue.re * fraction.denominator.im : Int) : Rational) = _
    rw [Ring.IntCast.sub,
      Cast.intCast_mul_direct,
      Cast.intCast_mul_direct]
    change
      (remainderValue.im : Rational) * fraction.denominator.re -
          (remainderValue.re : Rational) * fraction.denominator.im = _
    dsimp only [-eq_self, -iff_self, remainderValue, residualValue]
    rw [realEmbedded, imaginaryEmbedded, ← denominatorNormIdentity]
    ring1
  have denominatorPositiveNat := GaussianInt.normNat_pos fraction.denominatorNonzero
  have denominatorPositive :
      (0 : Rational) < (denominatorNorm : Rational) := by
    exact Order.natCast_pos_direct denominatorPositiveNat
  have inside := Nearest.remainder_mem fraction.value
  have scaleLower {coordinate : Rational}
      (lower : -(1 / 2 : Rational) ≤ coordinate) :
      ((-denominatorNorm : Int) : Rational) ≤
        2 * (coordinate * (denominatorNorm : Rational)) := by
    have scaled :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        lower denominatorPositive.le
    have doubled :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct scaled
        (show (0 : Rational) ≤ 2 by decide)
    calc
      ((-denominatorNorm : Int) : Rational) =
          2 * (-(1 / 2 : Rational) *
            (denominatorNorm : Rational)) := by
        have negated : ((-denominatorNorm : Int) : Rational) = -(denominatorNorm : Rational) :=
          Ring.IntCast.neg denominatorNorm
        rw [negated]
        calc
          -(denominatorNorm : Rational) =
              (-1 : Rational) * (denominatorNorm : Rational) := by ring1
          _ = ((2 : Rational) * (-(1 / 2 : Rational))) *
              (denominatorNorm : Rational) := by
            rw [show (2 : Rational) * (-(1 / 2 : Rational)) = -1 by
              decide]
          _ = 2 * (-(1 / 2 : Rational) *
              (denominatorNorm : Rational)) := by ring1
      _ ≤ 2 * (coordinate * (denominatorNorm : Rational)) := doubled
  have scaleUpper {coordinate : Rational}
      (upper : coordinate < 1 / 2) :
      2 * (coordinate * (denominatorNorm : Rational)) <
        (denominatorNorm : Rational) := by
    have scaled :=
      Arithmetic.mul_lt_mul_of_pos_right_direct
        upper denominatorPositive
    have doubled :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Rational) < 2 by decide) scaled
    calc
      2 * (coordinate * (denominatorNorm : Rational)) <
          2 * ((1 / 2 : Rational) *
            (denominatorNorm : Rational)) := doubled
      _ = ((2 : Rational) * (1 / 2)) *
          (denominatorNorm : Rational) := by ring1
      _ = (denominatorNorm : Rational) := by
        rw [show (2 : Rational) * (1 / 2) = 1 by decide]
        exact Field.one_mul _
  have realLowerCast :
      ((-denominatorNorm : Int) : Rational) ≤
        ((2 * DotCross.dot remainderValue fraction.denominator : Int) : Rational) := by
    rw [Ring.IntCast.intCast_mul, Int.cast_ofNat, dotIdentity]
    exact scaleLower inside.1
  have realUpperCast :
      ((2 * DotCross.dot remainderValue fraction.denominator : Int) : Rational) <
        (denominatorNorm : Rational) := by
    rw [Ring.IntCast.intCast_mul, Int.cast_ofNat, dotIdentity]
    exact scaleUpper inside.2.1
  have imaginaryLowerCast :
      ((-denominatorNorm : Int) : Rational) ≤
        ((2 * DotCross.cross remainderValue fraction.denominator : Int) : Rational) := by
    rw [Ring.IntCast.intCast_mul, Int.cast_ofNat, crossIdentity]
    exact scaleLower inside.2.2.1
  have imaginaryUpperCast :
      ((2 * DotCross.cross remainderValue fraction.denominator : Int) : Rational) <
        (denominatorNorm : Rational) := by
    rw [Ring.IntCast.intCast_mul, Int.cast_ofNat, crossIdentity]
    exact scaleUpper inside.2.2.2
  exact
    ⟨(Order.intCast_le_intCast_iff_direct _ _).1
        realLowerCast,
      (Order.intCast_lt_intCast_iff_direct _ _).mp realUpperCast,
      (Order.intCast_le_intCast_iff_direct _ _).1
        imaginaryLowerCast,
      (Order.intCast_lt_intCast_iff_direct _ _).mp imaginaryUpperCast⟩

/-- An integer whose doubled value lies in a half-open even window lies in the
corresponding half-open integer interval.

The same radius and value are retained in both scalar inequalities. -/
private theorem coordinate_bounds_of_even_window (radius value : Int)
    (lower : -(2 * radius) ≤ 2 * value)
    (upper : 2 * value < 2 * radius) :
    -radius ≤ value ∧ value < radius := by
  constructor <;> omega0

/-- An integer whose doubled value lies in a half-open odd window lies in the
corresponding closed integer interval.

The one-unit odd window admits both endpoints of the retained integer interval. -/
private theorem coordinate_bounds_of_odd_window (radius value : Int)
    (lower : -(2 * radius + 1) ≤ 2 * value)
    (upper : 2 * value < 2 * radius + 1) :
    -radius ≤ value ∧ value ≤ radius := by
  constructor <;> omega0

/-- A nearest Gaussian remainder has one unit of doubled-norm clearance or yields an
explicit diagonal denominator factor.

For denominator quadrance at least four, either twice the remainder quadrance plus
two is bounded by denominator quadrance, or the denominator equals the remainder
times a displayed quadrance-two factor. The boundary case constructs the factor -1+i
explicitly. -/
theorem remainder_clearance_or_diagonal_factor
    (fraction : Fraction)
    (denominatorAtLeastFour : 4 ≤ GaussianInt.normNat fraction.denominator) :
    2 * (GaussianInt.normNat (Nearest.remainder fraction) + 1) ≤
        GaussianInt.normNat fraction.denominator ∨
      ∃ factor : GaussianInt,
        GaussianInt.normNat factor = 2 ∧
          fraction.denominator = Nearest.remainder fraction * factor := by
  let remainderValue := Nearest.remainder fraction
  let denominatorNorm := GaussianInt.normNat fraction.denominator
  let remainderNorm := GaussianInt.normNat remainderValue
  let realProduct := DotCross.dot remainderValue fraction.denominator
  let imaginaryProduct := DotCross.cross remainderValue fraction.denominator
  change 4 ≤ denominatorNorm at denominatorAtLeastFour
  have basicBound : 2 * remainderNorm ≤ denominatorNorm :=
    Nearest.twice_remainder_norm_le_denominator fraction
  by_cases clearance : 2 * (remainderNorm + 1) ≤ denominatorNorm
  · exact Or.inl clearance
  · right
    have denominatorBelow : denominatorNorm < 2 * (remainderNorm + 1) :=
      Nat.lt_of_not_ge clearance
    have normCases :
        denominatorNorm = 2 * remainderNorm ∨
          denominatorNorm = 2 * remainderNorm + 1 := by
      rcases Nat.eq_or_lt_of_le basicBound with exactEven | aboveEven
      · exact Or.inl exactEven.symm
      · right
        apply Nat.le_antisymm
        · apply Nat.lt_succ_iff.mp
          calc
            denominatorNorm < 2 * (remainderNorm + 1) := denominatorBelow
            _ = (2 * remainderNorm + 1) + 1 := by ring1
        · exact Nat.succ_le_of_lt aboveEven
    have coordinateBounds := NearestGeometry.remainder_dot_cross_bounds fraction
    change
      -(denominatorNorm : Int) ≤ 2 * realProduct ∧
        2 * realProduct < (denominatorNorm : Int) ∧
        -(denominatorNorm : Int) ≤ 2 * imaginaryProduct ∧
        2 * imaginaryProduct < (denominatorNorm : Int)
      at coordinateBounds
    have lagrange := DotCross.dot_sq_add_cross_sq
      remainderValue fraction.denominator
    change
      realProduct * realProduct + imaginaryProduct * imaginaryProduct =
        (remainderNorm : Int) * (denominatorNorm : Int) at lagrange
    rcases normCases with normEven | normOdd
    · have remainderPositive : 0 < remainderNorm := by
        apply Nat.pos_of_ne_zero
        intro remainderZero
        rw [normEven, remainderZero, Nat.mul_zero] at denominatorAtLeastFour
        exact (show ¬4 ≤ 0 by decide) denominatorAtLeastFour
      have evenRealBounds :
          -(remainderNorm : Int) ≤ realProduct ∧
            realProduct < (remainderNorm : Int) := by
        rw [normEven] at coordinateBounds
        rw [NatCast.mul, Nat.cast_ofNat] at coordinateBounds
        apply NearestGeometry.coordinate_bounds_of_even_window
        · exact coordinateBounds.1
        · exact coordinateBounds.2.1
      have evenImaginaryBounds :
          -(remainderNorm : Int) ≤ imaginaryProduct ∧
            imaginaryProduct < (remainderNorm : Int) := by
        rw [normEven] at coordinateBounds
        rw [NatCast.mul, Nat.cast_ofNat] at coordinateBounds
        apply NearestGeometry.coordinate_bounds_of_even_window
        · exact coordinateBounds.2.2.1
        · exact coordinateBounds.2.2.2
      have realLower := evenRealBounds.1
      have realUpper := evenRealBounds.2
      have imaginaryLower := evenImaginaryBounds.1
      have imaginaryUpper := evenImaginaryBounds.2
      have squareLe (value : Int)
          (lower : -(remainderNorm : Int) ≤ value)
          (upper : value ≤ (remainderNorm : Int)) :
          value * value ≤
            (remainderNorm : Int) * (remainderNorm : Int) := by
        have productNonnegative :
            0 ≤ ((remainderNorm : Int) - value) *
              ((remainderNorm : Int) + value) :=
          Int.Order.mul_nonneg (Int.Order.sub_nonneg_of_le upper) (by
            calc
              (0 : Int) = (remainderNorm : Int) +
                  (-(remainderNorm : Int)) := by ring1
              _ ≤ (remainderNorm : Int) + value :=
                Int.Order.add_le_add (Int.Order.le_refl _) lower)
        have productIdentity :
            ((remainderNorm : Int) - value) *
                ((remainderNorm : Int) + value) =
              (remainderNorm : Int) * (remainderNorm : Int) -
                value * value := by ring1
        rw [productIdentity] at productNonnegative
        omega0
      have realSquareLe := squareLe realProduct realLower (Int.Order.le_of_lt realUpper)
      have imaginarySquareLe :=
        squareLe imaginaryProduct imaginaryLower (Int.Order.le_of_lt imaginaryUpper)
      have lagrangeEven :
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
            2 * ((remainderNorm : Int) * (remainderNorm : Int)) := by
        calc
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
              (remainderNorm : Int) * (denominatorNorm : Int) := lagrange
          _ = 2 * ((remainderNorm : Int) *
              (remainderNorm : Int)) := by
            rw [normEven, NatCast.mul, Nat.cast_ofNat]
            ring1
      have realSquareEq :
          realProduct * realProduct =
            (remainderNorm : Int) * (remainderNorm : Int) := by omega0
      have imaginarySquareEq :
          imaginaryProduct * imaginaryProduct =
            (remainderNorm : Int) * (remainderNorm : Int) := by omega0
      have realFactorZero :
          (realProduct - (remainderNorm : Int)) *
              (realProduct + (remainderNorm : Int)) = 0 := by
        calc
          (realProduct - (remainderNorm : Int)) *
              (realProduct + (remainderNorm : Int)) =
            realProduct * realProduct -
              (remainderNorm : Int) * (remainderNorm : Int) := by ring1
          _ = 0 := by rw [realSquareEq]; ring1
      have imaginaryFactorZero :
          (imaginaryProduct - (remainderNorm : Int)) *
              (imaginaryProduct + (remainderNorm : Int)) = 0 := by
        calc
          (imaginaryProduct - (remainderNorm : Int)) *
              (imaginaryProduct + (remainderNorm : Int)) =
            imaginaryProduct * imaginaryProduct -
              (remainderNorm : Int) * (remainderNorm : Int) := by ring1
          _ = 0 := by rw [imaginarySquareEq]; ring1
      have realEq : realProduct = -(remainderNorm : Int) := by
        rcases Int.Arithmetic.eq_zero_of_mul_eq_zero realFactorZero with positive | negative
        · have equal : realProduct = (remainderNorm : Int) :=
            by omega0
          exact (by omega0 : False).elim
        · omega0
      have imaginaryEq : imaginaryProduct = -(remainderNorm : Int) := by
        rcases Int.Arithmetic.eq_zero_of_mul_eq_zero imaginaryFactorZero with positive | negative
        · have equal : imaginaryProduct = (remainderNorm : Int) :=
            by omega0
          exact (by omega0 : False).elim
        · omega0
      have remainderNormIdentity :
          (remainderNorm : Int) = GaussianInt.normInt remainderValue := by
        dsimp only [-eq_self, -iff_self, remainderNorm]
        rw [GaussianInt.normNat, Int.Order.natAbs_of_nonneg
          (GaussianInt.normInt_nonneg remainderValue)]
      have realScaled :
          (remainderNorm : Int) * fraction.denominator.re =
            (remainderNorm : Int) *
              (-remainderValue.re - remainderValue.im) := by
        calc
          (remainderNorm : Int) * fraction.denominator.re =
              (remainderValue.re * remainderValue.re +
                remainderValue.im * remainderValue.im) *
                  fraction.denominator.re := by
            rw [remainderNormIdentity]
            rfl
          _ = remainderValue.re * realProduct +
              remainderValue.im * imaginaryProduct := by
            simp only [-eq_self, -iff_self, realProduct, imaginaryProduct, DotCross.dot, DotCross.cross]
            ring1
          _ = remainderValue.re * (-(remainderNorm : Int)) +
              remainderValue.im * (-(remainderNorm : Int)) := by
            rw [realEq, imaginaryEq]
          _ = (remainderNorm : Int) *
              (-remainderValue.re - remainderValue.im) := by ring1
      have imaginaryScaled :
          (remainderNorm : Int) * fraction.denominator.im =
            (remainderNorm : Int) *
              (remainderValue.re - remainderValue.im) := by
        calc
          (remainderNorm : Int) * fraction.denominator.im =
              (remainderValue.re * remainderValue.re +
                remainderValue.im * remainderValue.im) *
                  fraction.denominator.im := by
            rw [remainderNormIdentity]
            rfl
          _ = remainderValue.im * realProduct -
              remainderValue.re * imaginaryProduct := by
            simp only [-eq_self, -iff_self, realProduct, imaginaryProduct, DotCross.dot, DotCross.cross]
            ring1
          _ = remainderValue.im * (-(remainderNorm : Int)) -
              remainderValue.re * (-(remainderNorm : Int)) := by
            rw [realEq, imaginaryEq]
          _ = (remainderNorm : Int) *
              (remainderValue.re - remainderValue.im) := by ring1
      have remainderNormCastNonzero : (remainderNorm : Int) ≠ 0 :=
        Int.ofNat_ne_zero.mpr (Nat.ne_of_gt remainderPositive)
      have denominatorReal :
          fraction.denominator.re =
            -remainderValue.re - remainderValue.im :=
        Int.Arithmetic.eq_of_mul_eq_mul_left remainderNormCastNonzero realScaled
      have denominatorImaginary :
          fraction.denominator.im =
            remainderValue.re - remainderValue.im :=
        Int.Arithmetic.eq_of_mul_eq_mul_left remainderNormCastNonzero imaginaryScaled
      let factor : GaussianInt := ⟨-1, 1⟩
      refine ⟨factor, by decide, ?_⟩
      apply GaussianInt.ext
      · change fraction.denominator.re =
          remainderValue.re * (-1) - remainderValue.im * 1
        calc
          fraction.denominator.re =
              -remainderValue.re - remainderValue.im := denominatorReal
          _ = remainderValue.re * (-1) - remainderValue.im * 1 := by ring1
      · change fraction.denominator.im =
          remainderValue.re * 1 + remainderValue.im * (-1)
        calc
          fraction.denominator.im =
              remainderValue.re - remainderValue.im := denominatorImaginary
          _ = remainderValue.re * 1 + remainderValue.im * (-1) := by ring1
    · have remainderPositive : 0 < remainderNorm := by
        apply Nat.pos_of_ne_zero
        intro remainderZero
        rw [normOdd, remainderZero, Nat.mul_zero, Nat.zero_add] at denominatorAtLeastFour
        exact (show ¬4 ≤ 1 by decide) denominatorAtLeastFour
      have oddRealBounds :
          -(remainderNorm : Int) ≤ realProduct ∧
            realProduct ≤ (remainderNorm : Int) := by
        rw [normOdd] at coordinateBounds
        rw [NatCast.add, NatCast.mul, Nat.cast_ofNat, Nat.cast_one] at coordinateBounds
        apply NearestGeometry.coordinate_bounds_of_odd_window
        · exact coordinateBounds.1
        · exact coordinateBounds.2.1
      have oddImaginaryBounds :
          -(remainderNorm : Int) ≤ imaginaryProduct ∧
            imaginaryProduct ≤ (remainderNorm : Int) := by
        rw [normOdd] at coordinateBounds
        rw [NatCast.add, NatCast.mul, Nat.cast_ofNat, Nat.cast_one] at coordinateBounds
        apply NearestGeometry.coordinate_bounds_of_odd_window
        · exact coordinateBounds.2.2.1
        · exact coordinateBounds.2.2.2
      have realLower := oddRealBounds.1
      have realUpper := oddRealBounds.2
      have imaginaryLower := oddImaginaryBounds.1
      have imaginaryUpper := oddImaginaryBounds.2
      have squareLe (value : Int)
          (lower : -(remainderNorm : Int) ≤ value)
          (upper : value ≤ (remainderNorm : Int)) :
          value * value ≤
            (remainderNorm : Int) * (remainderNorm : Int) := by
        have productNonnegative :
            0 ≤ ((remainderNorm : Int) - value) *
              ((remainderNorm : Int) + value) :=
          Int.Order.mul_nonneg (Int.Order.sub_nonneg_of_le upper) (by
            calc
              (0 : Int) = (remainderNorm : Int) +
                  (-(remainderNorm : Int)) := by ring1
              _ ≤ (remainderNorm : Int) + value :=
                Int.Order.add_le_add (Int.Order.le_refl _) lower)
        have productIdentity :
            ((remainderNorm : Int) - value) *
                ((remainderNorm : Int) + value) =
              (remainderNorm : Int) * (remainderNorm : Int) -
                value * value := by ring1
        rw [productIdentity] at productNonnegative
        omega0
      have realSquareLe := squareLe realProduct realLower realUpper
      have imaginarySquareLe :=
        squareLe imaginaryProduct imaginaryLower imaginaryUpper
      have lagrangeOdd :
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
            2 * ((remainderNorm : Int) * (remainderNorm : Int)) +
              remainderNorm := by
        calc
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
              (remainderNorm : Int) * (denominatorNorm : Int) := lagrange
          _ = 2 * ((remainderNorm : Int) *
                (remainderNorm : Int)) + remainderNorm := by
            rw [normOdd, NatCast.add, NatCast.mul, Nat.cast_ofNat,
              Nat.cast_one]
            ring1
      have imaginaryAndRealBound := Int.Order.add_le_add realSquareLe imaginarySquareLe
      have impossible : (remainderNorm : Int) ≤ 0 := by omega0
      have castPositive : (0 : Int) < (remainderNorm : Int) :=
        Int.Order.natCast_pos remainderPositive
      exact (by omega0 : False).elim

end Purelib.Data.GaussianInt.Division.NearestGeometry

end
