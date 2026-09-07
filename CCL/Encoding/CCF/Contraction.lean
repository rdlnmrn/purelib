import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.CCF.CoordinateFloor

/-!
# Constructive finite CCF contraction certificate

This file isolates the finite integer and half-open-square estimates used by
the three-step coordinate-floor CCF contraction theorem.  The exceptional
digit set is an eight-constructor type; no unbounded search or ambient
quantifier-elimination principle is involved.
-/

namespace CCL.CCFContraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := CCL.Integral.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Integral.GaussianInt

/-- The eight digits left by the cone and `lambda(t) < 8`. -/
inductive SmallDigit where
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7
deriving DecidableEq, Repr

/-- The exceptional digit list from the manuscript's finite table. -/
def tau : SmallDigit → GaussianInt
  | .d0 => ⟨1, -2⟩
  | .d1 => ⟨1, -1⟩
  | .d2 => ⟨1, 0⟩
  | .d3 => ⟨1, 1⟩
  | .d4 => ⟨2, -2⟩
  | .d5 => ⟨2, -1⟩
  | .d6 => ⟨2, 0⟩
  | .d7 => ⟨2, 1⟩

/-- The piecewise integer lower bound used in the coarse estimate. -/
def lambda (t : GaussianInt) : Int :=
  if 0 ≤ t.im then t.re ^ 2 + t.im ^ 2
  else if t.im = -1 then t.re ^ 2
  else t.re ^ 2 + (t.im + 1) ^ 2

@[simp] theorem lambda_tau :
    lambda (tau .d0) = 2 ∧ lambda (tau .d1) = 1 ∧
    lambda (tau .d2) = 1 ∧ lambda (tau .d3) = 2 ∧
    lambda (tau .d4) = 5 ∧ lambda (tau .d5) = 4 ∧
    lambda (tau .d6) = 4 ∧ lambda (tau .d7) = 5 := by
  decide

private theorem square_le_lambda (t : GaussianInt) : t.re ^ 2 ≤ lambda t := by
  rw [lambda]
  split
  · exact Int.le_add_of_nonneg_right (Int.sq_nonneg t.im)
  · split
    · exact Int.le_refl _
    · exact Int.le_add_of_nonneg_right (Int.sq_nonneg (t.im + 1))

theorem lambda_nonnegative (t : GaussianInt) : 0 ≤ lambda t :=
  (Int.sq_nonneg t.re).trans (square_le_lambda t)

theorem one_le_lambda_of_cone (t : GaussianInt)
    (cone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re) :
    1 ≤ lambda t := by
  have realNonnegative : 0 ≤ t.re :=
    (show (0 : Int) ≤ 1 by decide).trans cone.1
  have squareOne : 1 ≤ t.re ^ 2 := by
    rw [pow_two]
    calc
      1 = 1 * 1 := by decide
      _ ≤ 1 * t.re :=
        Int.mul_le_mul_of_nonneg_left cone.1 (by decide)
      _ ≤ t.re * t.re :=
        Int.mul_le_mul_of_nonneg_right cone.1 realNonnegative
  exact squareOne.trans (square_le_lambda t)

private theorem int_cases_neg_two_to_one {value : Int}
    (lower : (-2 : Int) ≤ value) (upper : value ≤ 1) :
    value = -2 ∨ value = -1 ∨ value = 0 ∨ value = 1 := by
  by_cases negTwo : value = -2
  · exact Or.inl negTwo
  have negOneLe : (-1 : Int) ≤ value := by
    change (-2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne lower (Ne.symm negTwo))
  by_cases negOne : value = -1
  · exact Or.inr (Or.inl negOne)
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negOneLe (Ne.symm negOne))
  by_cases zero : value = 0
  · exact Or.inr (Or.inr (Or.inl zero))
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne zeroLe (Ne.symm zero))
  exact Or.inr (Or.inr (Or.inr (Int.le_antisymm upper oneLe)))

private theorem int_cases_neg_three_to_two {value : Int}
    (lower : (-3 : Int) ≤ value) (upper : value ≤ 2) :
    value = -3 ∨ value = -2 ∨ value = -1 ∨ value = 0 ∨
      value = 1 ∨ value = 2 := by
  by_cases negThree : value = -3
  · exact Or.inl negThree
  have negTwoLe : (-2 : Int) ≤ value := by
    change (-3 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne lower (Ne.symm negThree))
  by_cases negTwo : value = -2
  · exact Or.inr (Or.inl negTwo)
  have negOneLe : (-1 : Int) ≤ value := by
    change (-2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negTwoLe (Ne.symm negTwo))
  by_cases negOne : value = -1
  · exact Or.inr (Or.inr (Or.inl negOne))
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne negOneLe (Ne.symm negOne))
  by_cases zero : value = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inl zero)))
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne zeroLe (Ne.symm zero))
  by_cases one : value = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one))))
  have twoLe : (2 : Int) ≤ value := by
    change (1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (lt_of_le_of_ne oneLe (Ne.symm one))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Int.le_antisymm upper twoLe)))))

/-- The digit cone plus `lambda(t) < 8` leaves exactly the eight displayed
exceptional digits. -/
theorem exists_small_of_cone (t : GaussianInt)
    (cone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re)
    (small : lambda t < 8) : ∃ digit : SmallDigit, t = tau digit := by
  have realSquareSmall : t.re ^ 2 < 8 :=
    (square_le_lambda t).trans_lt small
  have realAtMostTwo : t.re ≤ 2 := by
    apply Int.le_of_not_gt
    intro threeOrMore
    have realNonnegative : 0 ≤ t.re :=
      (show (0 : Int) ≤ 1 by decide).trans cone.1
    have threeLe : (3 : Int) ≤ t.re := by
      change (2 : Int) + 1 ≤ t.re
      exact Int.add_one_le_iff.mpr threeOrMore
    have nineAtMost : 9 ≤ t.re * t.re := by
      calc
        9 = 3 * 3 := by decide
        _ ≤ t.re * 3 :=
          Int.mul_le_mul_of_nonneg_right threeLe (by decide)
        _ ≤ t.re * t.re :=
          Int.mul_le_mul_of_nonneg_left threeLe realNonnegative
    rw [pow_two] at realSquareSmall
    exact (not_lt_of_ge
      ((show (8 : Int) ≤ 9 by decide).trans nineAtMost)
      realSquareSmall).elim
  have realCases : t.re = 1 ∨ t.re = 2 := by
    by_cases realOne : t.re = 1
    · exact Or.inl realOne
    · have twoLe : (2 : Int) ≤ t.re := by
        change (1 : Int) + 1 ≤ t.re
        exact Int.add_one_le_iff.mpr
          (lt_of_le_of_ne cone.1 (Ne.symm realOne))
      exact Or.inr (Int.le_antisymm realAtMostTwo twoLe)
  rcases realCases with realOne | realTwo
  · have imagCases :
        t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨ t.im = 1 := by
      have imagLower : (-2 : Int) ≤ t.im := by
        calc
          (-2 : Int) = -t.re - 1 := by rw [realOne]; ring1
          _ ≤ t.im := cone.2.1
      have imagUpper : t.im ≤ (1 : Int) := cone.2.2.trans_eq realOne
      exact int_cases_neg_two_to_one imagLower imagUpper
    rcases imagCases with imagNegTwo | imagNegOne | imagZero | imagOne
    · refine ⟨.d0, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d1, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d2, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d3, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
  · have imagCases :
        t.im = -3 ∨ t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨
          t.im = 1 ∨ t.im = 2 := by
      have imagLower : (-3 : Int) ≤ t.im := by
        calc
          (-3 : Int) = -t.re - 1 := by rw [realTwo]; ring1
          _ ≤ t.im := cone.2.1
      have imagUpper : t.im ≤ (2 : Int) := cone.2.2.trans_eq realTwo
      exact int_cases_neg_three_to_two imagLower imagUpper
    rcases imagCases with imagNegThree | imagNegTwo | imagNegOne |
      imagZero | imagOne | imagTwo
    · have value : t = ⟨2, -3⟩ := by
        apply CCL.Integral.GaussianInt.ext <;> assumption
      rw [value] at small
      change (8 : Int) < 8 at small
      exact (Int.lt_irrefl 8 small).elim
    · refine ⟨.d4, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d5, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d6, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · refine ⟨.d7, ?_⟩
      apply CCL.Integral.GaussianInt.ext <;>
        simp only [tau] <;> assumption
    · have value : t = ⟨2, 2⟩ := by
        apply CCL.Integral.GaussianInt.ext <;> assumption
      rw [value] at small
      change (8 : Int) < 8 at small
      exact (Int.lt_irrefl 8 small).elim

private theorem cast_int_nonnegative {value : Int} (nonnegative : 0 ≤ value) :
    (0 : Coordinate) ≤ (value : Coordinate) := by
  simpa only [Int.cast_zero] using
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct 0 value).2
      nonnegative

private theorem square_le_square_add_of_nonnegative
    (base increment : Coordinate) (baseNonnegative : 0 ≤ base)
    (incrementNonnegative : 0 ≤ increment) :
    base ^ 2 ≤ (base + increment) ^ 2 := by
  have twiceBaseNonnegative : 0 ≤ base + base :=
    add_nonneg baseNonnegative baseNonnegative
  have secondFactorNonnegative : 0 ≤ base + base + increment :=
    add_nonneg twiceBaseNonnegative incrementNonnegative
  have productNonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
    incrementNonnegative secondFactorNonnegative
  calc
    base ^ 2 ≤ base ^ 2 + increment * (base + base + increment) :=
      le_add_of_nonneg_right productNonnegative
    _ = (base + increment) ^ 2 := by ring1

private theorem negative_square_growth
    (base increment : Coordinate) (incrementAtMostOne : increment ≤ 1)
    (basePlusOneNonpositive : base + 1 ≤ 0) :
    (base + 1) ^ 2 ≤ (base + increment) ^ 2 := by
  have shiftedOrder : base + increment ≤ base + 1 := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      incrementAtMostOne base
    calc
      base + increment = increment + base := add_comm _ _
      _ ≤ 1 + base := shifted
      _ = base + 1 := add_comm _ _
  have firstNonnegative :=
    RFAP.ConstructiveFraction.sub_nonneg_direct shiftedOrder
  have sumNonpositive : (base + 1) + (base + increment) ≤ 0 :=
    calc
      (base + 1) + (base + increment) ≤ 0 + 0 :=
        add_le_add basePlusOneNonpositive
          (shiftedOrder.trans basePlusOneNonpositive)
      _ = 0 := add_zero 0
  have secondNonnegative :
      0 ≤ -((base + 1) + (base + increment)) := by
    have difference := RFAP.ConstructiveFraction.sub_nonneg_direct
      sumNonpositive
    rw [show (0 : Coordinate) -
        ((base + 1) + (base + increment)) =
          -((base + 1) + (base + increment)) by ring1] at difference
    exact difference
  have productNonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
    firstNonnegative secondNonnegative
  calc
    (base + 1) ^ 2 ≤ (base + 1) ^ 2 +
        ((base + 1) - (base + increment)) *
          (-((base + 1) + (base + increment))) :=
      le_add_of_nonneg_right productNonnegative
    _ = (base + increment) ^ 2 := by ring1

/-- The piecewise `lambda` is a uniform lower bound for translating any point
of the coordinate square by a cone digit. -/
theorem lambda_le_norm_translate (t : GaussianInt) (realNonnegative : 0 ≤ t.re)
    (q : Gaussian) (inside : CCL.CoordinateFloor.Sq q) :
    (lambda t : Coordinate) ≤ normSq (toGaussian t + q) := by
  rcases inside with ⟨realQNonnegative, realQSmall,
    imagQNonnegative, imagQSmall⟩
  have realCastNonnegative : (0 : Coordinate) ≤ (t.re : Coordinate) :=
    cast_int_nonnegative realNonnegative
  have realGrowth := square_le_square_add_of_nonnegative
    (t.re : Coordinate) q.re realCastNonnegative realQNonnegative
  by_cases imagNonnegative : 0 ≤ t.im
  · have imagCastNonnegative : (0 : Coordinate) ≤ (t.im : Coordinate) :=
      cast_int_nonnegative imagNonnegative
    have imagGrowth := square_le_square_add_of_nonnegative
      (t.im : Coordinate) q.im imagCastNonnegative imagQNonnegative
    simp only [lambda, if_pos imagNonnegative, normSq,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
      Int.cast_add, QuotientFreeRing.intCast_pow]
    exact add_le_add realGrowth imagGrowth
  · by_cases imagNegOne : t.im = -1
    · simp only [lambda, if_neg imagNonnegative, if_pos imagNegOne,
        normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        QuotientFreeRing.intCast_pow]
      exact realGrowth.trans
        (le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct
            ((t.im : Coordinate) + q.im)))
    · have imagNegative : t.im < 0 := Int.lt_of_not_ge imagNonnegative
      have imagAtMostNegOne : t.im ≤ (-1 : Int) := by
        change t.im ≤ (0 : Int) - 1
        exact Int.le_sub_one_iff.mpr imagNegative
      have imagPlusOneNonpositive : t.im + 1 ≤ 0 := by
        calc
          t.im + 1 ≤ (-1 : Int) + 1 :=
            Int.add_le_add_right imagAtMostNegOne 1
          _ = 0 := by ring1
      have basePlusOneNonpositive : (t.im : Coordinate) + 1 ≤ 0 := by
        have castOrder :=
          (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
            (t.im + 1) 0).2 imagPlusOneNonpositive
        simpa only [Int.cast_add, Int.cast_one, Int.cast_zero] using castOrder
      have imagGrowth := negative_square_growth
        (t.im : Coordinate) q.im imagQSmall.le basePlusOneNonpositive
      simp only [lambda, if_neg imagNonnegative, if_neg imagNegOne,
        normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im, toGaussian,
        Int.cast_add, Int.cast_one, QuotientFreeRing.intCast_pow]
      exact add_le_add realGrowth imagGrowth

/-- The constant Gaussian integer `t*t' + gamma` in the expanded table
polynomial. -/
def center (t t' : GaussianInt) : GaussianInt :=
  t * t' + CCL.Integral.GaussianInt.gammaInt

/-- Quadratic coefficient `Norm(t)-4`. -/
def alpha (t : GaussianInt) : Int :=
  CCL.Integral.GaussianInt.normInt t - 4

/-- Real linear coefficient in the expanded table polynomial. -/
def beta (t t' : GaussianInt) : Int :=
  2 * (t.re * (center t t').re + t.im * (center t t').im)

/-- Imaginary linear coefficient in the expanded table polynomial. -/
def eta (t t' : GaussianInt) : Int :=
  2 * (-t.im * (center t t').re + t.re * (center t t').im)

/-- Constant coefficient in the expanded table polynomial. -/
def kappa (t t' : GaussianInt) : Int :=
  CCL.Integral.GaussianInt.normInt (center t t')

/-- The exact polynomial whose positivity supplies the exceptional-table
contraction estimate. -/
def delta (t t' : GaussianInt) (w : Gaussian) : Coordinate :=
  normSq (toGaussian t * (toGaussian t' + w) + gamma) - 4 * normSq w

/-- Direct coordinate expansion of the finite table polynomial. -/
theorem delta_expansion (t t' : GaussianInt) (w : Gaussian) :
    delta t t' w =
      (alpha t : Coordinate) * (w.re ^ 2 + w.im ^ 2) +
        (beta t t' : Coordinate) * w.re +
        (eta t t' : Coordinate) * w.im +
        (kappa t t' : Coordinate) := by
  simp only [delta, alpha, beta, eta, kappa, center,
    CCL.Integral.GaussianInt.normInt,
    RFAP.ConstructiveGaussian.Gaussian.normSq,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.gamma,
    RFAP.CanonicalGaussian.Gaussian.gamma,
    CCL.Integral.GaussianInt.toGaussian,
    CCL.Integral.GaussianInt.mul_re,
    CCL.Integral.GaussianInt.mul_im,
    CCL.Integral.GaussianInt.add_re,
    CCL.Integral.GaussianInt.add_im,
    CCL.Integral.GaussianInt.gammaInt,
    Int.cast_sub, Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_neg]
  ring1

/-- A checked integer certificate for one entry of the finite CCF table.
Concave rows record their four nonnegative corners and a positive origin.
Convex rows record monotonicity toward either `(0,0)` or `(0,1)`. -/
def TableCertificate (r c : SmallDigit) : Prop :=
  let t := tau r
  let t' := tau c
  let A := alpha t
  let B := beta t t'
  let C := eta t t'
  let D := kappa t t'
  if A ≤ 0 then
    0 < D ∧ 0 ≤ A + B + D ∧ 0 ≤ A + C + D ∧
      0 ≤ 2 * A + B + C + D
  else
    0 ≤ B ∧
      ((0 ≤ C ∧ 0 < D) ∨
        ((2 * A + C ≤ 0 ∧ 0 < A + C + D) ∨
          (2 * A + C < 0 ∧ 0 ≤ A + C + D)))

instance tableCertificateDecidable (r c : SmallDigit) :
    Decidable (TableCertificate r c) := by
  unfold TableCertificate
  infer_instance

/-- All finite table entries needed after the coarse product test carry the
displayed integer certificate.  The crossed-out pair is the sole exception. -/
theorem table_certificate (r c : SmallDigit) :
    lambda (tau r) * lambda (tau c) < 8 →
      ¬ (r = .d1 ∧ c = .d0) → TableCertificate r c := by
  cases r <;> cases c <;> decide

private theorem cast_int_positive {value : Int} (positive : 0 < value) :
    (0 : Coordinate) < (value : Coordinate) := by
  apply lt_of_not_ge
  intro reverse
  have integerReverse :=
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct value 0).1
      (by simpa only [Int.cast_zero] using reverse)
  exact (Int.not_le_of_gt positive) integerReverse

private theorem cast_int_nonpositive {value : Int} (nonpositive : value ≤ 0) :
    (value : Coordinate) ≤ 0 := by
  simpa only [Int.cast_zero] using
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct value 0).2
      nonpositive

private theorem cast_int_negative {value : Int} (negative : value < 0) :
    (value : Coordinate) < 0 := by
  apply lt_of_not_ge
  intro reverse
  have integerReverse :=
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct 0 value).1
      (by simpa only [Int.cast_zero] using reverse)
  exact (Int.not_le_of_gt negative) integerReverse

private def tablePolynomial
    (A B C D x y : Coordinate) : Coordinate :=
  A * (x ^ 2 + y ^ 2) + B * x + C * y + D

private theorem concave_table_positive
    {A B C D x y : Coordinate}
    (alphaNonpositive : A ≤ 0)
    (originPositive : 0 < D)
    (realCornerNonnegative : 0 ≤ A + B + D)
    (imagCornerNonnegative : 0 ≤ A + C + D)
    (farCornerNonnegative : 0 ≤ 2 * A + B + C + D)
    (realNonnegative : 0 ≤ x) (realSmall : x < 1)
    (imagNonnegative : 0 ≤ y) (imagSmall : y < 1) :
    0 < tablePolynomial A B C D x y := by
  have oneMinusRealPositive : 0 < 1 - x :=
    RFAP.ConstructiveFraction.sub_pos_direct realSmall
  have oneMinusImagPositive : 0 < 1 - y :=
    RFAP.ConstructiveFraction.sub_pos_direct imagSmall
  have originTermPositive : 0 < D * (1 - x) * (1 - y) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct originPositive
        oneMinusRealPositive)
      oneMinusImagPositive
  have realCornerTermNonnegative :
      0 ≤ (A + B + D) * x * (1 - y) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        realCornerNonnegative realNonnegative)
      oneMinusImagPositive.le
  have imagCornerTermNonnegative :
      0 ≤ (A + C + D) * (1 - x) * y :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        imagCornerNonnegative oneMinusRealPositive.le)
      imagNonnegative
  have farCornerTermNonnegative :
      0 ≤ (2 * A + B + C + D) * x * y :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        farCornerNonnegative realNonnegative)
      imagNonnegative
  have negativeAlphaNonnegative : 0 ≤ -A := by
    have difference := RFAP.ConstructiveFraction.sub_nonneg_direct
      alphaNonpositive
    rw [show (0 : Coordinate) - A = -A by ring1] at difference
    exact difference
  have interiorSumNonnegative :
      0 ≤ x * (1 - x) + y * (1 - y) :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct realNonnegative
        oneMinusRealPositive.le)
      (RFAP.ConstructiveFraction.mul_nonneg_direct imagNonnegative
        oneMinusImagPositive.le)
  have correctionNonnegative :
      0 ≤ (-A) * (x * (1 - x) + y * (1 - y)) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct negativeAlphaNonnegative
      interiorSumNonnegative
  have remainingNonnegative :
      0 ≤ (A + B + D) * x * (1 - y) +
        (A + C + D) * (1 - x) * y +
        (2 * A + B + C + D) * x * y +
        (-A) * (x * (1 - x) + y * (1 - y)) :=
    add_nonneg
      (add_nonneg (add_nonneg realCornerTermNonnegative
        imagCornerTermNonnegative) farCornerTermNonnegative)
      correctionNonnegative
  calc
    0 < D * (1 - x) * (1 - y) +
        ((A + B + D) * x * (1 - y) +
          (A + C + D) * (1 - x) * y +
          (2 * A + B + C + D) * x * y +
          (-A) * (x * (1 - x) + y * (1 - y))) :=
      add_pos_of_pos_of_nonneg originTermPositive remainingNonnegative
    _ = tablePolynomial A B C D x y := by
      simp only [tablePolynomial]
      ring1

private theorem convex_x_term_nonnegative
    {A B x : Coordinate} (alphaNonnegative : 0 ≤ A)
    (betaNonnegative : 0 ≤ B) (realNonnegative : 0 ≤ x) :
    0 ≤ x * (A * x + B) := by
  exact RFAP.ConstructiveFraction.mul_nonneg_direct realNonnegative
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct alphaNonnegative
        realNonnegative)
      betaNonnegative)

private theorem convex_table_positive_up
    {A B C D x y : Coordinate}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (etaNonnegative : 0 ≤ C) (originPositive : 0 < D)
    (realNonnegative : 0 ≤ x) (imagNonnegative : 0 ≤ y) :
    0 < tablePolynomial A B C D x y := by
  have xTermNonnegative := convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have yTermNonnegative : 0 ≤ y * (A * y + C) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct imagNonnegative
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct alphaPositive.le
          imagNonnegative)
        etaNonnegative)
  calc
    0 < D + y * (A * y + C) + x * (A * x + B) :=
      add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg originPositive yTermNonnegative)
        xTermNonnegative
    _ = tablePolynomial A B C D x y := by
      simp only [tablePolynomial]
      ring1

private theorem y_plus_one_le_two {y : Coordinate} (small : y < 1) :
    y + 1 ≤ 2 := by
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    small.le 1
  calc
    y + 1 ≤ 1 + 1 := shifted
    _ = 2 := by ring1

private theorem down_second_le_slope
    {A C y : Coordinate} (alphaNonnegative : 0 ≤ A)
    (imagSmall : y < 1) :
    A * (y + 1) + C ≤ 2 * A + C := by
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (y_plus_one_le_two imagSmall) alphaNonnegative
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct scaled C
  exact shifted.trans_eq (by ring1)

private theorem down_second_nonpositive
    {A C y : Coordinate} (alphaNonnegative : 0 ≤ A)
    (imagSmall : y < 1) (slopeNonpositive : 2 * A + C ≤ 0) :
    A * (y + 1) + C ≤ 0 :=
  (down_second_le_slope alphaNonnegative imagSmall).trans slopeNonpositive

private theorem product_nonnegative_of_both_nonpositive
    {x y : Coordinate} (xNonpositive : x ≤ 0) (yNonpositive : y ≤ 0) :
    0 ≤ x * y := by
  have negXNonnegative := RFAP.ConstructiveFraction.neg_le_neg_direct
    xNonpositive
  have negYNonnegative := RFAP.ConstructiveFraction.neg_le_neg_direct
    yNonpositive
  have product := RFAP.ConstructiveFraction.mul_nonneg_direct
    (by simpa only [neg_zero] using negXNonnegative)
    (by simpa only [neg_zero] using negYNonnegative)
  calc
    0 ≤ (-x) * (-y) := product
    _ = x * y := by ring1

private theorem product_positive_of_both_negative
    {x y : Coordinate} (xNegative : x < 0) (yNegative : y < 0) :
    0 < x * y := by
  have negXPositive := RFAP.ConstructiveFraction.neg_lt_neg_direct xNegative
  have negYPositive := RFAP.ConstructiveFraction.neg_lt_neg_direct yNegative
  have product := RFAP.ConstructiveFraction.mul_pos_direct
    (by simpa only [neg_zero] using negXPositive)
    (by simpa only [neg_zero] using negYPositive)
  calc
    0 < (-x) * (-y) := product
    _ = x * y := by ring1

private theorem convex_table_positive_down_corner
    {A B C D x y : Coordinate}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (slopeNonpositive : 2 * A + C ≤ 0)
    (cornerPositive : 0 < A + C + D)
    (realNonnegative : 0 ≤ x)
    (imagSmall : y < 1) :
    0 < tablePolynomial A B C D x y := by
  have xTermNonnegative := convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have firstNonpositive : y - 1 ≤ 0 :=
    (RFAP.ConstructiveFraction.sub_neg_direct imagSmall).le
  have secondNonpositive := down_second_nonpositive alphaPositive.le
    imagSmall slopeNonpositive
  have yDifferenceNonnegative := product_nonnegative_of_both_nonpositive
    firstNonpositive secondNonpositive
  calc
    0 < (A + C + D) +
        (y - 1) * (A * (y + 1) + C) + x * (A * x + B) :=
      add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg cornerPositive yDifferenceNonnegative)
        xTermNonnegative
    _ = tablePolynomial A B C D x y := by
      simp only [tablePolynomial]
      ring1

private theorem convex_table_positive_down_slope
    {A B C D x y : Coordinate}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (slopeNegative : 2 * A + C < 0)
    (cornerNonnegative : 0 ≤ A + C + D)
    (realNonnegative : 0 ≤ x)
    (imagSmall : y < 1) :
    0 < tablePolynomial A B C D x y := by
  have xTermNonnegative := convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have firstNegative := RFAP.ConstructiveFraction.sub_neg_direct imagSmall
  have secondNegative : A * (y + 1) + C < 0 :=
    (down_second_le_slope alphaPositive.le imagSmall).trans_lt slopeNegative
  have yDifferencePositive := product_positive_of_both_negative
    firstNegative secondNegative
  have basePositive := add_pos_of_nonneg_of_pos cornerNonnegative
    yDifferencePositive
  calc
    0 < (A + C + D) +
        (y - 1) * (A * (y + 1) + C) + x * (A * x + B) :=
      add_pos_of_pos_of_nonneg basePositive xTermNonnegative
    _ = tablePolynomial A B C D x y := by
      simp only [tablePolynomial]
      ring1

/-- Positivity of every needed numerical entry in the exceptional table,
apart from the separately impossible crossed-out pair. -/
theorem delta_pos_of_small (r c : SmallDigit) (w : Gaussian)
    (inside : CCL.CoordinateFloor.Sq w)
    (productSmall : lambda (tau r) * lambda (tau c) < 8)
    (notCrossed : ¬ (r = .d1 ∧ c = .d0)) :
    0 < delta (tau r) (tau c) w := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have certificate := table_certificate r c productSmall notCrossed
  rw [delta_expansion]
  change 0 < tablePolynomial
    (alpha (tau r) : Coordinate)
    (beta (tau r) (tau c) : Coordinate)
    (eta (tau r) (tau c) : Coordinate)
    (kappa (tau r) (tau c) : Coordinate) w.re w.im
  unfold TableCertificate at certificate
  dsimp only at certificate
  split at certificate
  · rename_i alphaNonpositive
    rcases certificate with ⟨originPositive, realCorner,
      imagCorner, farCorner⟩
    apply concave_table_positive
      (cast_int_nonpositive alphaNonpositive)
      (cast_int_positive originPositive)
      (by simpa only [Int.cast_add] using cast_int_nonnegative realCorner)
      (by simpa only [Int.cast_add] using cast_int_nonnegative imagCorner)
      (by simpa only [Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_ofNat] using
        cast_int_nonnegative farCorner)
      realNonnegative realSmall imagNonnegative imagSmall
  · rename_i alphaNotNonpositive
    have alphaPositive : 0 < alpha (tau r) :=
      Int.lt_of_not_ge alphaNotNonpositive
    rcases certificate with ⟨betaNonnegative,
      ⟨etaUp, originPositive⟩ | down⟩
    · apply convex_table_positive_up
        (cast_int_positive alphaPositive)
        (cast_int_nonnegative betaNonnegative)
        (cast_int_nonnegative etaUp)
        (cast_int_positive originPositive)
        realNonnegative imagNonnegative
    · rcases down with downCorner | downSlope
      · apply convex_table_positive_down_corner
          (cast_int_positive alphaPositive)
          (cast_int_nonnegative betaNonnegative)
          (by simpa only [Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_ofNat] using
            cast_int_nonpositive downCorner.1)
          (by simpa only [Int.cast_add] using
            cast_int_positive downCorner.2)
          realNonnegative imagSmall
      · apply convex_table_positive_down_slope
          (cast_int_positive alphaPositive)
          (cast_int_nonnegative betaNonnegative)
          (by simpa only [Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_ofNat] using
            cast_int_negative downSlope.1)
          (by simpa only [Int.cast_add] using
            cast_int_nonnegative downSlope.2)
          realNonnegative imagSmall

private theorem mul_quotient_eq_gamma (z : Gaussian) (nonzero : z ≠ 0) :
    z * (gamma * z⁻¹) = gamma := by
  rw [← RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    RFAP.ConstructiveGaussian.Gaussian.mul_comm z gamma,
    RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.mul_inv z nonzero,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- The crossed-out entry `(1-i,1-2i)` cannot occur for three successive
half-open-square states. -/
theorem cross_pair_impossible (u v w : Gaussian)
    (uNonzero : u ≠ 0) (vNonzero : v ≠ 0)
    (uInside : CCL.CoordinateFloor.Sq u)
    (vInside : CCL.CoordinateFloor.Sq v)
    (wInside : CCL.CoordinateFloor.Sq w)
    (uBranch : gamma * u⁻¹ = toGaussian (tau .d1) + v)
    (vBranch : gamma * v⁻¹ = toGaussian (tau .d0) + w) : False := by
  rcases uInside with ⟨_, _, _, uImagSmall⟩
  rcases vInside with ⟨vRealNonnegative, _, _, _⟩
  rcases wInside with ⟨_, _, _, wImagSmall⟩
  have vProduct : v * (toGaussian (tau .d0) + w) = gamma := by
    rw [← vBranch]
    exact mul_quotient_eq_gamma v vNonzero
  have vRealEquation :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re vProduct
  have vImagEquation :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im vProduct
  change v.re * (1 + w.re) - v.im * (-2 + w.im) = 1 at vRealEquation
  change v.re * (-2 + w.im) + v.im * (1 + w.re) = 1 at vImagEquation
  let A : Coordinate := 1 + w.re
  let B : Coordinate := 2 - w.im
  let R : Coordinate := A ^ 2 + B ^ 2
  have realLinear : v.re * A + v.im * B = 1 := by
    calc
      v.re * A + v.im * B =
          v.re * (1 + w.re) - v.im * (-2 + w.im) := by
        dsimp only [A, B]
        ring1
      _ = 1 := vRealEquation
  have imagLinear : -v.re * B + v.im * A = 1 := by
    calc
      -v.re * B + v.im * A =
          v.re * (-2 + w.im) + v.im * (1 + w.re) := by
        dsimp only [A, B]
        ring1
      _ = 1 := vImagEquation
  have bGreaterOne : 1 < B := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    dsimp only [B]
    have positive := RFAP.ConstructiveFraction.sub_pos_direct wImagSmall
    calc
      (2 - w.im) - 1 = 1 - w.im := by ring1
      _ > 0 := positive
  have bPositive : 0 < B := (by decide : (0 : Coordinate) < 1).trans
    bGreaterOne
  have rPositive : 0 < R := by
    have aSquareNonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct A
    have bSquarePositive : 0 < B ^ 2 := by
      rw [pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct bPositive bPositive
    exact add_pos_of_nonneg_of_pos aSquareNonnegative bSquarePositive
  have realTimesR : v.re * R = A - B := by
    calc
      v.re * R = A * (v.re * A + v.im * B) -
          B * (-v.re * B + v.im * A) := by
        dsimp only [R]
        ring1
      _ = A * 1 - B * 1 := by rw [realLinear, imagLinear]
      _ = A - B := by ring1
  have imagTimesR : v.im * R = A + B := by
    calc
      v.im * R = B * (v.re * A + v.im * B) +
          A * (-v.re * B + v.im * A) := by
        dsimp only [R]
        ring1
      _ = B * 1 + A * 1 := by rw [realLinear, imagLinear]
      _ = A + B := by ring1
  have normTimesR : (v.re ^ 2 + v.im ^ 2) * R = 2 := by
    calc
      (v.re ^ 2 + v.im ^ 2) * R =
          v.re * (v.re * R) + v.im * (v.im * R) := by ring1
      _ = v.re * (A - B) + v.im * (A + B) := by
        rw [realTimesR, imagTimesR]
      _ = (v.re * A + v.im * B) + (-v.re * B + v.im * A) := by
        ring1
      _ = 1 + 1 := by rw [realLinear, imagLinear]
      _ = 2 := by ring1
  let numerator : Coordinate :=
    v.im * (1 - v.im) - v.re * (1 + v.re)
  have numeratorTimesR : numerator * R = 2 * (B - 1) := by
    calc
      numerator * R = v.im * R - v.re * R -
          (v.re ^ 2 + v.im ^ 2) * R := by
        dsimp only [numerator]
        ring1
      _ = (A + B) - (A - B) - 2 := by
        rw [imagTimesR, realTimesR, normTimesR]
      _ = 2 * (B - 1) := by ring1
  have numeratorProductPositive : 0 < numerator * R := by
    rw [numeratorTimesR]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.sub_pos_direct bGreaterOne)
  have numeratorPositive : 0 < numerator := by
    have reordered : 0 < R * numerator := by
      rwa [RFAP.ConstructiveFraction.mul_comm]
    exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      reordered rPositive.le
  have uProduct : u * (toGaussian (tau .d1) + v) = gamma := by
    rw [← uBranch]
    exact mul_quotient_eq_gamma u uNonzero
  have uRealEquation :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re uProduct
  have uImagEquation :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im uProduct
  change u.re * (1 + v.re) - u.im * (-1 + v.im) = 1 at uRealEquation
  change u.re * (-1 + v.im) + u.im * (1 + v.re) = 1 at uImagEquation
  let D : Coordinate := (1 + v.re) ^ 2 + (v.im - 1) ^ 2
  have onePlusRealPositive : 0 < 1 + v.re := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      vRealNonnegative 1
    have oneLe : (1 : Coordinate) ≤ 1 + v.re := by
      calc
        (1 : Coordinate) = 0 + 1 := by ring1
        _ ≤ v.re + 1 := shifted
        _ = 1 + v.re := by ring1
    exact (by decide : (0 : Coordinate) < 1).trans_le oneLe
  have dPositive : 0 < D := by
    have firstPositive : 0 < (1 + v.re) ^ 2 := by
      rw [pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        onePlusRealPositive onePlusRealPositive
    exact add_pos_of_pos_of_nonneg firstPositive
      (RFAP.ConstructiveFraction.sq_nonneg_direct (v.im - 1))
  have imagTimesD : u.im * D = 2 + v.re - v.im := by
    calc
      u.im * D = -(v.im - 1) *
          (u.re * (1 + v.re) - u.im * (-1 + v.im)) +
          (1 + v.re) *
            (u.re * (-1 + v.im) + u.im * (1 + v.re)) := by
        dsimp only [D]
        ring1
      _ = -(v.im - 1) * 1 + (1 + v.re) * 1 := by
        rw [uRealEquation, uImagEquation]
      _ = 2 + v.re - v.im := by ring1
  have shiftedTimesD : (u.im - 1) * D = numerator := by
    calc
      (u.im - 1) * D = u.im * D - D := by ring1
      _ = (2 + v.re - v.im) - D := by rw [imagTimesD]
      _ = numerator := by
        dsimp only [D, numerator]
        ring1
  have shiftedProductPositive : 0 < (u.im - 1) * D := by
    rw [shiftedTimesD]
    exact numeratorPositive
  have shiftedPositive : 0 < u.im - 1 := by
    have reordered : 0 < D * (u.im - 1) := by
      rwa [RFAP.ConstructiveFraction.mul_comm]
    exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      reordered dPositive.le
  have oneLessImag := RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    shiftedPositive
  exact (lt_asymm oneLessImag uImagSmall).elim

/-- Three successive nonterminal coordinate-floor remainders contract their
norm product strictly below one. -/
theorem three_step_contraction (u : Gaussian) (uNonzero : u ≠ 0)
    (uInside : CCL.CoordinateFloor.Sq u)
    (vNonzero : CCL.CoordinateFloor.step u ≠ 0) :
    normSq (u * CCL.CoordinateFloor.step u *
      CCL.CoordinateFloor.step
        (CCL.CoordinateFloor.step u)) < 1 := by
  let v := CCL.CoordinateFloor.step u
  let w := CCL.CoordinateFloor.step v
  let t := CCL.CoordinateFloor.floor (gamma * u⁻¹)
  let t' := CCL.CoordinateFloor.floor (gamma * v⁻¹)
  have vInside : CCL.CoordinateFloor.Sq v := by
    dsimp only [v]
    exact CCL.CoordinateFloor.step_sq u
  have wInside : CCL.CoordinateFloor.Sq w := by
    dsimp only [w]
    exact CCL.CoordinateFloor.step_sq v
  have uBranch : gamma * u⁻¹ = toGaussian t + v := by
    symm
    simpa only [t, v] using
      CCL.CoordinateFloor.floor_add_step u
  have vBranch : gamma * v⁻¹ = toGaussian t' + w := by
    symm
    simpa only [t', w] using
      CCL.CoordinateFloor.floor_add_step v
  have tCone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
    simpa only [t] using CCL.CoordinateFloor.digit_cone
      u uNonzero uInside
  have t'Cone : 1 ≤ t'.re ∧ -t'.re - 1 ≤ t'.im ∧ t'.im ≤ t'.re := by
    simpa only [t'] using CCL.CoordinateFloor.digit_cone
      v vNonzero vInside
  have uProduct : u * (toGaussian t + v) = gamma := by
    rw [← uBranch]
    exact mul_quotient_eq_gamma u uNonzero
  have vProduct : v * (toGaussian t' + w) = gamma := by
    rw [← vBranch]
    exact mul_quotient_eq_gamma v vNonzero
  have uNorm := congrArg normSq uProduct
  have vNorm := congrArg normSq vProduct
  rw [normSq_mul, normSq_gamma] at uNorm vNorm
  have denominatorInequality :
      4 * normSq w <
        normSq (toGaussian t + v) * normSq (toGaussian t' + w) := by
    by_cases coarse : 8 ≤ lambda t * lambda t'
    · have tLower := lambda_le_norm_translate t (by omega) v vInside
      have t'Lower := lambda_le_norm_translate t' (by omega) w wInside
      have productLower :
          ((lambda t * lambda t' : Int) : Coordinate) ≤
            normSq (toGaussian t + v) * normSq (toGaussian t' + w) := by
        rw [QuotientFreeRing.intCast_mul]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct tLower t'Lower
          (cast_int_nonnegative (lambda_nonnegative t'))
          (normSq_nonneg (toGaussian t + v))
      have coarseCast : (8 : Coordinate) ≤
          ((lambda t * lambda t' : Int) : Coordinate) := by
        have cast :=
          (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct
            8 (lambda t * lambda t')).2 coarse
        simpa only [Int.cast_ofNat] using cast
      have fourTimesNormLess : 4 * normSq w < 8 := by
        have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Coordinate) < 4)
          (CCL.CoordinateFloor.normSq_lt_two_of_sq wInside)
        calc
          4 * normSq w < 4 * 2 := scaled
          _ = 8 := by ring1
      exact fourTimesNormLess.trans_le (coarseCast.trans productLower)
    · have productSmall : lambda t * lambda t' < 8 :=
        Int.lt_of_not_ge coarse
      have tOne := one_le_lambda_of_cone t tCone
      have t'One := one_le_lambda_of_cone t' t'Cone
      have tSmall : lambda t < 8 := by
        have factorOrder : lambda t ≤ lambda t * lambda t' := by
          calc
            lambda t = lambda t * 1 := (Int.mul_one _).symm
            _ ≤ lambda t * lambda t' :=
              Int.mul_le_mul_of_nonneg_left t'One (lambda_nonnegative t)
        exact factorOrder.trans_lt productSmall
      have t'Small : lambda t' < 8 := by
        have factorOrder : lambda t' ≤ lambda t * lambda t' := by
          calc
            lambda t' = 1 * lambda t' := (Int.one_mul _).symm
            _ ≤ lambda t * lambda t' :=
              Int.mul_le_mul_of_nonneg_right tOne (lambda_nonnegative t')
        exact factorOrder.trans_lt productSmall
      obtain ⟨r, tEqual⟩ := exists_small_of_cone t tCone tSmall
      obtain ⟨c, t'Equal⟩ := exists_small_of_cone t' t'Cone t'Small
      have notCrossed : ¬ (r = .d1 ∧ c = .d0) := by
        rintro ⟨rfl, rfl⟩
        apply cross_pair_impossible u v w uNonzero vNonzero
          uInside vInside wInside
        · simpa only [tEqual] using uBranch
        · simpa only [t'Equal] using vBranch
      have tablePositive := delta_pos_of_small r c w wInside
        (by simpa only [← tEqual, ← t'Equal] using productSmall)
        notCrossed
      have vProduct' : v * (toGaussian (tau c) + w) = gamma := by
        simpa only [t'Equal] using vProduct
      have factorIdentity :
          toGaussian (tau r) * (toGaussian (tau c) + w) + gamma =
            (toGaussian (tau r) + v) * (toGaussian (tau c) + w) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.right_distrib, vProduct']
      rw [delta, factorIdentity, normSq_mul] at tablePositive
      have translated := RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        tablePositive
      simpa only [tEqual, t'Equal] using translated
  have productIdentity :
      normSq (u * v * w) *
          (normSq (toGaussian t + v) * normSq (toGaussian t' + w)) =
        4 * normSq w := by
    rw [normSq_mul, normSq_mul]
    calc
      (normSq u * normSq v * normSq w) *
          (normSq (toGaussian t + v) * normSq (toGaussian t' + w)) =
          (normSq u * normSq (toGaussian t + v)) *
            (normSq v * normSq (toGaussian t' + w)) * normSq w := by
        ring1
      _ = 2 * 2 * normSq w := by rw [uNorm, vNorm]
      _ = 4 * normSq w := by ring1
  have denominatorPositive :
      0 < normSq (toGaussian t + v) * normSq (toGaussian t' + w) := by
    have leftNonnegative : 0 ≤ 4 * normSq w :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg w)
    exact leftNonnegative.trans_lt denominatorInequality
  have scaledResult :
      normSq (u * v * w) *
          (normSq (toGaussian t + v) * normSq (toGaussian t' + w)) <
        1 * (normSq (toGaussian t + v) * normSq (toGaussian t' + w)) := by
    rw [productIdentity]
    simpa only [RFAP.ConstructiveFraction.one_mul] using denominatorInequality
  have result := RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    scaledResult denominatorPositive
  simpa only [v, w] using result

end CCL.CCFContraction
