import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzRational

/-!
# Constructive extended Euclidean certificates over the Gaussian integers

Nearest-Gaussian-integer division gives a Euclidean recursion whose measure is
the displayed natural quadrance.  This file packages that recursion with all
of the data needed downstream: a Bezout identity and explicit quotients
showing that the returned gcd divides both inputs.  The construction is a
finite program and introduces neither choice nor a completed carrier.
-/

namespace RFAP.GaussianEuclidean

abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Coordinate := RFAP.ConstructiveFraction.Rational

open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzRational

/-- A proof-carrying result of the extended Gaussian Euclidean algorithm. -/
structure Certificate (left right : GaussianInt) where
  gcd : GaussianInt
  leftCoefficient : GaussianInt
  rightCoefficient : GaussianInt
  leftQuotient : GaussianInt
  rightQuotient : GaussianInt
  bezout :
    gcd = leftCoefficient * left + rightCoefficient * right
  left_factor : left = gcd * leftQuotient
  right_factor : right = gcd * rightQuotient

/-- Extended Euclidean recursion using the deterministic Hurwitz remainder. -/
def extendedGCD (left right : GaussianInt) : Certificate left right := by
  by_cases rightZero : right = 0
  · exact
      { gcd := left
        leftCoefficient := 1
        rightCoefficient := 0
        leftQuotient := 1
        rightQuotient := 0
        bezout := by rw [rightZero]; ring1
        left_factor := by ring1
        right_factor := by rw [rightZero]; ring1 }
  · let fraction : RFAP.HurwitzRational.Fraction :=
      { numerator := left
        denominator := right
        denominatorNonzero := rightZero }
    let quotient := digit fraction
    let remainderValue := remainder fraction
    let recursive := extendedGCD right remainderValue
    exact
      { gcd := recursive.gcd
        leftCoefficient := recursive.rightCoefficient
        rightCoefficient :=
          recursive.leftCoefficient - recursive.rightCoefficient * quotient
        leftQuotient :=
          quotient * recursive.leftQuotient + recursive.rightQuotient
        rightQuotient := recursive.leftQuotient
        bezout := by
          have recursiveBezout := recursive.bezout
          have division := digit_mul_denominator_add_remainder fraction
          dsimp only [fraction, quotient, remainderValue] at recursiveBezout division
          rw [recursiveBezout]
          calc
            recursive.leftCoefficient * right +
                recursive.rightCoefficient * remainderValue =
              recursive.rightCoefficient *
                  (quotient * right + remainderValue) +
                (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right := by
              apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
                simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
                ring1
            _ = recursive.rightCoefficient * left +
                (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right :=
              congrArg
                (fun value => recursive.rightCoefficient * value +
                  (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right)
                division
        left_factor := by
          have recursiveLeft := recursive.left_factor
          have recursiveRight := recursive.right_factor
          have division := digit_mul_denominator_add_remainder fraction
          dsimp only [fraction, quotient, remainderValue] at recursiveLeft recursiveRight division
          calc
            left = quotient * right + remainderValue := division.symm
            _ = quotient * (recursive.gcd * recursive.leftQuotient) +
                remainderValue :=
              congrArg (fun value => quotient * value + remainderValue)
                recursiveLeft
            _ = quotient * (recursive.gcd * recursive.leftQuotient) +
                recursive.gcd * recursive.rightQuotient :=
              congrArg
                (fun value => quotient *
                    (recursive.gcd * recursive.leftQuotient) + value)
                recursiveRight
            _ = recursive.gcd *
                (quotient * recursive.leftQuotient +
                  recursive.rightQuotient) := by
              apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
                simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
                ring1
        right_factor := by
          exact recursive.left_factor }
termination_by normNat right
decreasing_by
  exact remainder_norm_lt_denominator fraction

/-! ## Arithmetic at the boundary of the nearest-remainder square -/

/-- Integral real scalar product. -/
def dot (left right : GaussianInt) : Int :=
  left.re * right.re + left.im * right.im

/-- Integral oriented scalar product, the imaginary coordinate of
`left * conj right`. -/
def cross (left right : GaussianInt) : Int :=
  left.im * right.re - left.re * right.im

private theorem intCast_lt_intCast_iff_direct (left right : Int) :
    ((left : Int) : Coordinate) < ((right : Int) : Coordinate) ↔
      left < right := by
  constructor
  · intro castStrict
    apply Int.lt_of_not_ge
    intro reverse
    have castReverse :
        ((right : Int) : Coordinate) ≤ ((left : Int) : Coordinate) :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct right left).2
        reverse
    exact (not_lt_of_ge castReverse) castStrict
  · intro strict
    apply lt_of_not_ge
    intro castReverse
    have reverse : right ≤ left :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct right left).1
        castReverse
    exact (not_lt_of_ge reverse) strict

/-- The integral dot and cross coordinates of a Hurwitz remainder lie in the
scaled half-open square. -/
theorem remainder_dot_cross_bounds (fraction : Fraction) :
    - (normNat fraction.denominator : Int) ≤
        2 * dot (remainder fraction) fraction.denominator ∧
      2 * dot (remainder fraction) fraction.denominator <
        (normNat fraction.denominator : Int) ∧
      - (normNat fraction.denominator : Int) ≤
        2 * cross (remainder fraction) fraction.denominator ∧
      2 * cross (remainder fraction) fraction.denominator <
        (normNat fraction.denominator : Int) := by
  let remainderValue := remainder fraction
  let denominatorNorm : Int := normNat fraction.denominator
  let residualValue := residual fraction
  have embeddedRemainder := remainder_toGaussian fraction
  have realEmbedded := congrArg
    RFAP.ConstructiveGaussian.Gaussian.re embeddedRemainder
  have imaginaryEmbedded := congrArg
    RFAP.ConstructiveGaussian.Gaussian.im embeddedRemainder
  simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im] at realEmbedded imaginaryEmbedded
  change ((remainder fraction).re : Coordinate) =
      (residual fraction).re * (fraction.denominator.re : Coordinate) -
        (residual fraction).im * (fraction.denominator.im : Coordinate)
    at realEmbedded
  change ((remainder fraction).im : Coordinate) =
      (residual fraction).re * (fraction.denominator.im : Coordinate) +
        (residual fraction).im * (fraction.denominator.re : Coordinate)
    at imaginaryEmbedded
  have denominatorNormIdentity := normSq_toGaussian fraction.denominator
  change
    (fraction.denominator.re : Coordinate) ^ 2 +
        (fraction.denominator.im : Coordinate) ^ 2 =
      (denominatorNorm : Coordinate) at denominatorNormIdentity
  have dotIdentity :
      (dot remainderValue fraction.denominator : Coordinate) =
        residualValue.re * (denominatorNorm : Coordinate) := by
    change
      ((remainderValue.re * fraction.denominator.re +
          remainderValue.im * fraction.denominator.im : Int) : Coordinate) = _
    rw [Int.cast_add,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct]
    change
      (remainderValue.re : Coordinate) * fraction.denominator.re +
          (remainderValue.im : Coordinate) * fraction.denominator.im = _
    dsimp only [remainderValue, residualValue]
    rw [realEmbedded, imaginaryEmbedded, ← denominatorNormIdentity]
    ring1
  have crossIdentity :
      (cross remainderValue fraction.denominator : Coordinate) =
        residualValue.im * (denominatorNorm : Coordinate) := by
    change
      ((remainderValue.im * fraction.denominator.re -
          remainderValue.re * fraction.denominator.im : Int) : Coordinate) = _
    rw [Int.cast_sub,
      RFAP.ConstructiveFraction.intCast_mul_direct,
      RFAP.ConstructiveFraction.intCast_mul_direct]
    change
      (remainderValue.im : Coordinate) * fraction.denominator.re -
          (remainderValue.re : Coordinate) * fraction.denominator.im = _
    dsimp only [remainderValue, residualValue]
    rw [realEmbedded, imaginaryEmbedded, ← denominatorNormIdentity]
    ring1
  have denominatorPositiveNat := normNat_pos fraction.denominatorNonzero
  have denominatorPositive :
      (0 : Coordinate) < (denominatorNorm : Coordinate) := by
    exact RFAP.ConstructiveFraction.natCast_pos_direct denominatorPositiveNat
  have inside := RFAP.HurwitzNearest.remainder_mem fraction.value
  have scaleLower {coordinate : Coordinate}
      (lower : -(1 / 2 : Coordinate) ≤ coordinate) :
      ((-denominatorNorm : Int) : Coordinate) ≤
        2 * (coordinate * (denominatorNorm : Coordinate)) := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        lower denominatorPositive.le
    have doubled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct scaled
        (show (0 : Coordinate) ≤ 2 by decide)
    calc
      ((-denominatorNorm : Int) : Coordinate) =
          2 * (-(1 / 2 : Coordinate) *
            (denominatorNorm : Coordinate)) := by
        rw [Int.cast_neg]
        calc
          -(denominatorNorm : Coordinate) =
              (-1 : Coordinate) * (denominatorNorm : Coordinate) := by ring1
          _ = ((2 : Coordinate) * (-(1 / 2 : Coordinate))) *
              (denominatorNorm : Coordinate) := by
            rw [show (2 : Coordinate) * (-(1 / 2 : Coordinate)) = -1 by
              decide]
          _ = 2 * (-(1 / 2 : Coordinate) *
              (denominatorNorm : Coordinate)) := by ring1
      _ ≤ 2 * (coordinate * (denominatorNorm : Coordinate)) := doubled
  have scaleUpper {coordinate : Coordinate}
      (upper : coordinate < 1 / 2) :
      2 * (coordinate * (denominatorNorm : Coordinate)) <
        (denominatorNorm : Coordinate) := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        upper denominatorPositive
    have doubled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : Coordinate) < 2 by decide) scaled
    calc
      2 * (coordinate * (denominatorNorm : Coordinate)) <
          2 * ((1 / 2 : Coordinate) *
            (denominatorNorm : Coordinate)) := doubled
      _ = ((2 : Coordinate) * (1 / 2)) *
          (denominatorNorm : Coordinate) := by ring1
      _ = (denominatorNorm : Coordinate) := by
        rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
        exact RFAP.ConstructiveFraction.one_mul _
  have realLowerCast :
      ((-denominatorNorm : Int) : Coordinate) ≤
        ((2 * dot remainderValue fraction.denominator : Int) : Coordinate) := by
    rw [QuotientFreeRing.intCast_mul, Int.cast_ofNat, dotIdentity]
    exact scaleLower inside.1
  have realUpperCast :
      ((2 * dot remainderValue fraction.denominator : Int) : Coordinate) <
        (denominatorNorm : Coordinate) := by
    rw [QuotientFreeRing.intCast_mul, Int.cast_ofNat, dotIdentity]
    exact scaleUpper inside.2.1
  have imaginaryLowerCast :
      ((-denominatorNorm : Int) : Coordinate) ≤
        ((2 * cross remainderValue fraction.denominator : Int) : Coordinate) := by
    rw [QuotientFreeRing.intCast_mul, Int.cast_ofNat, crossIdentity]
    exact scaleLower inside.2.2.1
  have imaginaryUpperCast :
      ((2 * cross remainderValue fraction.denominator : Int) : Coordinate) <
        (denominatorNorm : Coordinate) := by
    rw [QuotientFreeRing.intCast_mul, Int.cast_ofNat, crossIdentity]
    exact scaleUpper inside.2.2.2
  exact
    ⟨(RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).1
        realLowerCast,
      (intCast_lt_intCast_iff_direct _ _).1 realUpperCast,
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct _ _).1
        imaginaryLowerCast,
      (intCast_lt_intCast_iff_direct _ _).1 imaginaryUpperCast⟩

/-- Lagrange's identity for the displayed dot and cross products. -/
theorem dot_sq_add_cross_sq (left right : GaussianInt) :
    dot left right * dot left right + cross left right * cross left right =
      (normNat left : Int) * (normNat right : Int) := by
  have leftNorm : (normNat left : Int) = normInt left := by
    rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg left)]
  have rightNorm : (normNat right : Int) = normInt right := by
    rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg right)]
  rw [leftNorm, rightNorm]
  simp only [dot, cross, normInt]
  ring1

private theorem coordinate_bounds_of_even_window (radius value : Int)
    (lower : -(2 * radius) ≤ 2 * value)
    (upper : 2 * value < 2 * radius) :
    -radius ≤ value ∧ value < radius := by
  constructor
  · have scaled : 2 * (-radius) ≤ 2 * value := by
      calc
        2 * (-radius) = -(2 * radius) := by ring1
        _ ≤ 2 * value := lower
    exact Int.le_of_mul_le_mul_left scaled (by decide)
  · exact Int.lt_of_mul_lt_mul_left upper (by decide)

private theorem coordinate_bounds_of_odd_window (radius value : Int)
    (lower : -(2 * radius + 1) ≤ 2 * value)
    (upper : 2 * value < 2 * radius + 1) :
    -radius ≤ value ∧ value ≤ radius := by
  constructor
  · apply Int.le_of_not_gt
    intro below
    have nextLe : value + 1 ≤ -radius := Int.add_one_le_iff.mpr below
    have doubled := Int.mul_le_mul_of_nonneg_left nextLe
      (show (0 : Int) ≤ 2 by decide)
    have twoValueUpper : 2 * value ≤ -(2 * radius + 2) := by
      apply Int.le_of_add_le_add_right (b := 2)
      calc
        2 * value + 2 = 2 * (value + 1) := by ring1
        _ ≤ 2 * (-radius) := doubled
        _ = -(2 * radius + 2) + 2 := by ring1
    have impossible : -(2 * radius + 1) ≤ -(2 * radius + 2) :=
      lower.trans twoValueUpper
    have strict : -(2 * radius + 2) < -(2 * radius + 1) := by
      apply Int.neg_lt_neg
      calc
        2 * radius + 1 < (2 * radius + 1) + 1 :=
          Int.lt_add_one_iff.mpr (Int.le_refl _)
        _ = 2 * radius + 2 := by ring1
    exact (not_le_of_gt strict impossible).elim
  · apply Int.le_of_not_gt
    intro above
    have nextLe : radius + 1 ≤ value := Int.add_one_le_iff.mpr above
    have doubled := Int.mul_le_mul_of_nonneg_left nextLe
      (show (0 : Int) ≤ 2 by decide)
    have strict : 2 * radius + 1 < 2 * (radius + 1) := by
      calc
        2 * radius + 1 < (2 * radius + 1) + 1 :=
          Int.lt_add_one_iff.mpr (Int.le_refl _)
        _ = 2 * (radius + 1) := by ring1
    have reverse : 2 * radius + 1 < 2 * value := strict.trans_le doubled
    exact (not_lt_of_ge reverse.le upper).elim

/-- Away from the two smallest nonunit quadrances, a nearest remainder has
one full integral quadrance of clearance from the half-square boundary.  The
only possible equality case is the lower-left corner, where the denominator
is the remainder times the displayed diagonal `-1+i`. -/
theorem remainder_clearance_or_diagonal_factor
    (fraction : Fraction)
    (denominatorAtLeastFour : 4 ≤ normNat fraction.denominator) :
    2 * (normNat (remainder fraction) + 1) ≤
        normNat fraction.denominator ∨
      ∃ factor : GaussianInt,
        normNat factor = 2 ∧
          fraction.denominator = remainder fraction * factor := by
  let remainderValue := remainder fraction
  let denominatorNorm := normNat fraction.denominator
  let remainderNorm := normNat remainderValue
  let realProduct := dot remainderValue fraction.denominator
  let imaginaryProduct := cross remainderValue fraction.denominator
  change 4 ≤ denominatorNorm at denominatorAtLeastFour
  have basicBound : 2 * remainderNorm ≤ denominatorNorm :=
    twice_remainder_norm_le_denominator fraction
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
    have coordinateBounds := remainder_dot_cross_bounds fraction
    change
      -(denominatorNorm : Int) ≤ 2 * realProduct ∧
        2 * realProduct < (denominatorNorm : Int) ∧
        -(denominatorNorm : Int) ≤ 2 * imaginaryProduct ∧
        2 * imaginaryProduct < (denominatorNorm : Int)
      at coordinateBounds
    have lagrange := dot_sq_add_cross_sq
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
        push_cast at coordinateBounds
        apply coordinate_bounds_of_even_window
        · exact coordinateBounds.1
        · exact coordinateBounds.2.1
      have evenImaginaryBounds :
          -(remainderNorm : Int) ≤ imaginaryProduct ∧
            imaginaryProduct < (remainderNorm : Int) := by
        rw [normEven] at coordinateBounds
        push_cast at coordinateBounds
        apply coordinate_bounds_of_even_window
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
          Int.mul_nonneg (Int.sub_nonneg.mpr upper) (by
            calc
              (0 : Int) = (remainderNorm : Int) +
                  (-(remainderNorm : Int)) := by ring1
              _ ≤ (remainderNorm : Int) + value :=
                Int.add_le_add_left lower _)
        have productIdentity :
            ((remainderNorm : Int) - value) *
                ((remainderNorm : Int) + value) =
              (remainderNorm : Int) * (remainderNorm : Int) -
                value * value := by ring1
        rw [productIdentity] at productNonnegative
        exact Int.sub_nonneg.mp productNonnegative
      have realSquareLe := squareLe realProduct realLower realUpper.le
      have imaginarySquareLe :=
        squareLe imaginaryProduct imaginaryLower imaginaryUpper.le
      have lagrangeEven :
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
            2 * ((remainderNorm : Int) * (remainderNorm : Int)) := by
        calc
          realProduct * realProduct + imaginaryProduct * imaginaryProduct =
              (remainderNorm : Int) * (denominatorNorm : Int) := lagrange
          _ = 2 * ((remainderNorm : Int) *
              (remainderNorm : Int)) := by
            rw [normEven, Nat.cast_mul, Nat.cast_ofNat]
            ring1
      have realSquareEq :
          realProduct * realProduct =
            (remainderNorm : Int) * (remainderNorm : Int) := by
        apply Int.le_antisymm realSquareLe
        apply Int.le_of_add_le_add_right
        calc
          (remainderNorm : Int) * (remainderNorm : Int) +
                imaginaryProduct * imaginaryProduct ≤
              (remainderNorm : Int) * (remainderNorm : Int) +
                ((remainderNorm : Int) * (remainderNorm : Int)) :=
            Int.add_le_add_left imaginarySquareLe _
          _ = realProduct * realProduct +
                imaginaryProduct * imaginaryProduct := by
            rw [lagrangeEven]
            ring1
      have imaginarySquareEq :
          imaginaryProduct * imaginaryProduct =
            (remainderNorm : Int) * (remainderNorm : Int) := by
        apply Int.le_antisymm imaginarySquareLe
        apply Int.le_of_add_le_add_left
        calc
          realProduct * realProduct +
                (remainderNorm : Int) * (remainderNorm : Int) ≤
              (remainderNorm : Int) * (remainderNorm : Int) +
                ((remainderNorm : Int) * (remainderNorm : Int)) :=
            Int.add_le_add_right realSquareLe _
          _ = realProduct * realProduct +
                imaginaryProduct * imaginaryProduct := by
            rw [lagrangeEven]
            ring1
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
        rcases Int.mul_eq_zero.mp realFactorZero with positive | negative
        · have equal : realProduct = (remainderNorm : Int) :=
            Int.sub_eq_zero.mp positive
          exact (ne_of_lt realUpper equal).elim
        · exact add_eq_zero_iff_eq_neg.mp negative
      have imaginaryEq : imaginaryProduct = -(remainderNorm : Int) := by
        rcases Int.mul_eq_zero.mp imaginaryFactorZero with positive | negative
        · have equal : imaginaryProduct = (remainderNorm : Int) :=
            Int.sub_eq_zero.mp positive
          exact (ne_of_lt imaginaryUpper equal).elim
        · exact add_eq_zero_iff_eq_neg.mp negative
      have remainderNormIdentity :
          (remainderNorm : Int) = normInt remainderValue := by
        dsimp only [remainderNorm]
        rw [normNat, Int.ofNat_natAbs_of_nonneg
          (normInt_nonneg remainderValue)]
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
            simp only [realProduct, imaginaryProduct, dot, cross]
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
            simp only [realProduct, imaginaryProduct, dot, cross]
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
        Int.eq_of_mul_eq_mul_left remainderNormCastNonzero realScaled
      have denominatorImaginary :
          fraction.denominator.im =
            remainderValue.re - remainderValue.im :=
        Int.eq_of_mul_eq_mul_left remainderNormCastNonzero imaginaryScaled
      let factor : GaussianInt := ⟨-1, 1⟩
      refine ⟨factor, by decide, ?_⟩
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
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
        push_cast at coordinateBounds
        apply coordinate_bounds_of_odd_window
        · exact coordinateBounds.1
        · exact coordinateBounds.2.1
      have oddImaginaryBounds :
          -(remainderNorm : Int) ≤ imaginaryProduct ∧
            imaginaryProduct ≤ (remainderNorm : Int) := by
        rw [normOdd] at coordinateBounds
        push_cast at coordinateBounds
        apply coordinate_bounds_of_odd_window
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
          Int.mul_nonneg (Int.sub_nonneg.mpr upper) (by
            calc
              (0 : Int) = (remainderNorm : Int) +
                  (-(remainderNorm : Int)) := by ring1
              _ ≤ (remainderNorm : Int) + value :=
                Int.add_le_add_left lower _)
        have productIdentity :
            ((remainderNorm : Int) - value) *
                ((remainderNorm : Int) + value) =
              (remainderNorm : Int) * (remainderNorm : Int) -
                value * value := by ring1
        rw [productIdentity] at productNonnegative
        exact Int.sub_nonneg.mp productNonnegative
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
            rw [normOdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_one]
            ring1
      have impossible : (remainderNorm : Int) ≤ 0 := by
        apply Int.le_of_add_le_add_left (a :=
          2 * ((remainderNorm : Int) * (remainderNorm : Int)))
        calc
          2 * ((remainderNorm : Int) * (remainderNorm : Int)) +
                (remainderNorm : Int) =
              realProduct * realProduct +
                imaginaryProduct * imaginaryProduct := lagrangeOdd.symm
          _ ≤ (remainderNorm : Int) * (remainderNorm : Int) +
                ((remainderNorm : Int) * (remainderNorm : Int)) :=
            Int.add_le_add realSquareLe imaginarySquareLe
          _ = 2 * ((remainderNorm : Int) * (remainderNorm : Int)) + 0 := by
            ring1
      have castPositive : (0 : Int) < (remainderNorm : Int) :=
        Int.ofNat_lt.mpr remainderPositive
      exact (not_le_of_gt castPositive impossible).elim

end RFAP.GaussianEuclidean
