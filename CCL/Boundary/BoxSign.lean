import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Geometry
import RFAP.Sturm.IntervalSign

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace CCL.CCLBoxSign

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm

open RFAP.ConstructiveGaussian.Gaussian
open CCL.CCLGeometry

private theorem add_sq_le_two (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (left - right) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = 2 * (left ^ 2 + right ^ 2) - (left + right) ^ 2 := by
      ring1

private theorem add_sq_le_three (first second third : Coordinate) :
    (first + second + third) ^ 2 ≤
      3 * (first ^ 2 + second ^ 2 + third ^ 2) := by
  apply sub_nonneg.mp
  have firstSecond : 0 ≤ (first - second) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have firstThird : 0 ≤ (first - third) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have secondThird : 0 ≤ (second - third) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  calc
    0 ≤ (first - second) ^ 2 + (first - third) ^ 2 +
        (second - third) ^ 2 :=
      add_nonneg (add_nonneg firstSecond firstThird) secondThird
    _ = 3 * (first ^ 2 + second ^ 2 + third ^ 2) -
        (first + second + third) ^ 2 := by
      ring1

/-- The fixed coefficient multiplying the current squared diagonal in the
Hermitian variation estimate. -/
def variationCoefficient (form : HermitianForm) (bounding : Box) : Coordinate :=
  3 * (16 * form.radial ^ 2 * bounding.coordinateSqBound +
    form.realLinear ^ 2 + form.imagLinear ^ 2)

/-- Squared variation margin for a current box inside `bounding`. -/
def variationSqBound
    (form : HermitianForm) (bounding current : Box) : Coordinate :=
  variationCoefficient form bounding * current.diagonalSq

theorem variationCoefficient_nonneg (form : HermitianForm) (bounding : Box) :
    0 ≤ variationCoefficient form bounding := by
  have sixteenNonnegative : (0 : Coordinate) ≤ 16 := by decide
  have threeNonnegative : (0 : Coordinate) ≤ 3 := by decide
  have radialSquare :=
    RFAP.ConstructiveFraction.sq_nonneg_direct form.radial
  have radialCoordinateNonnegative :
      0 ≤ 16 * form.radial ^ 2 * bounding.coordinateSqBound :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct sixteenNonnegative
        radialSquare)
      bounding.coordinateSqBound_nonneg
  exact RFAP.ConstructiveFraction.mul_nonneg_direct threeNonnegative
    (add_nonneg
      (add_nonneg radialCoordinateNonnegative
        (RFAP.ConstructiveFraction.sq_nonneg_direct form.realLinear))
      (RFAP.ConstructiveFraction.sq_nonneg_direct form.imagLinear))

theorem variationSqBound_nonneg
    (form : HermitianForm) (bounding current : Box) :
    0 ≤ variationSqBound form bounding current :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (variationCoefficient_nonneg form bounding) current.diagonalSq_nonneg

private theorem real_sub_sq_le_diagonalSq
    {current : Box} {left right : Gaussian}
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.re - right.re) ^ 2 ≤ current.diagonalSq := by
  have distance := current.normSq_sub_le_diagonalSq leftInside rightInside
  have imaginaryNonnegative :
      0 ≤ (left.im - right.im) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  calc
    (left.re - right.re) ^ 2 =
        (left.re - right.re) ^ 2 + 0 := by ring1
    _ ≤ (left.re - right.re) ^ 2 +
        (left.im - right.im) ^ 2 :=
      add_le_add le_rfl imaginaryNonnegative
    _ = normSq (left - right) := by
      simp only [normSq, sub_re, sub_im]
    _ ≤ current.diagonalSq := distance

private theorem imag_sub_sq_le_diagonalSq
    {current : Box} {left right : Gaussian}
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.im - right.im) ^ 2 ≤ current.diagonalSq := by
  have distance := current.normSq_sub_le_diagonalSq leftInside rightInside
  have realNonnegative :
      0 ≤ (left.re - right.re) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  calc
    (left.im - right.im) ^ 2 =
        0 + (left.im - right.im) ^ 2 := by ring1
    _ ≤ (left.re - right.re) ^ 2 +
        (left.im - right.im) ^ 2 :=
      add_le_add realNonnegative le_rfl
    _ = normSq (left - right) := by
      simp only [normSq, sub_re, sub_im]
    _ ≤ current.diagonalSq := distance

private theorem real_add_sq_le_coordinateSqBound
    {bounding current : Box} {left right : Gaussian}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.re + right.re) ^ 2 ≤ 4 * bounding.coordinateSqBound := by
  have leftBounding := refines.contains leftInside
  have rightBounding := refines.contains rightInside
  have leftSquare : left.re ^ 2 ≤ bounding.coordinateSqBound :=
    (RFAP.Boxes.Box.sq_le_endpoint_max
      leftBounding.1 leftBounding.2.1).trans
      (le_max_left _ _)
  have rightSquare : right.re ^ 2 ≤ bounding.coordinateSqBound :=
    (RFAP.Boxes.Box.sq_le_endpoint_max
      rightBounding.1 rightBounding.2.1).trans
      (le_max_left _ _)
  have sumSquares :
      left.re ^ 2 + right.re ^ 2 ≤
        bounding.coordinateSqBound + bounding.coordinateSqBound :=
    add_le_add leftSquare rightSquare
  have twoNonnegative : (0 : Coordinate) ≤ 2 := by decide
  calc
    (left.re + right.re) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) :=
      add_sq_le_two _ _
    _ ≤ 2 * (bounding.coordinateSqBound +
        bounding.coordinateSqBound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        sumSquares twoNonnegative
    _ = 4 * bounding.coordinateSqBound := by ring1

private theorem imag_add_sq_le_coordinateSqBound
    {bounding current : Box} {left right : Gaussian}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (left.im + right.im) ^ 2 ≤ 4 * bounding.coordinateSqBound := by
  have leftBounding := refines.contains leftInside
  have rightBounding := refines.contains rightInside
  have leftSquare : left.im ^ 2 ≤ bounding.coordinateSqBound :=
    (RFAP.Boxes.Box.sq_le_endpoint_max
      leftBounding.2.2.1 leftBounding.2.2.2).trans
      (le_max_right _ _)
  have rightSquare : right.im ^ 2 ≤ bounding.coordinateSqBound :=
    (RFAP.Boxes.Box.sq_le_endpoint_max
      rightBounding.2.2.1 rightBounding.2.2.2).trans
      (le_max_right _ _)
  have sumSquares :
      left.im ^ 2 + right.im ^ 2 ≤
        bounding.coordinateSqBound + bounding.coordinateSqBound :=
    add_le_add leftSquare rightSquare
  have twoNonnegative : (0 : Coordinate) ≤ 2 := by decide
  calc
    (left.im + right.im) ^ 2 ≤
        2 * (left.im ^ 2 + right.im ^ 2) :=
      add_sq_le_two _ _
    _ ≤ 2 * (bounding.coordinateSqBound +
        bounding.coordinateSqBound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        sumSquares twoNonnegative
    _ = 4 * bounding.coordinateSqBound := by ring1

private theorem normSq_sub_sq_le
    {bounding current : Box} {left right : Gaussian}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (normSq left - normSq right) ^ 2 ≤
      16 * bounding.coordinateSqBound * current.diagonalSq := by
  have realDifference := real_sub_sq_le_diagonalSq leftInside rightInside
  have imaginaryDifference := imag_sub_sq_le_diagonalSq leftInside rightInside
  have realSum := real_add_sq_le_coordinateSqBound refines
    leftInside rightInside
  have imaginarySum := imag_add_sq_le_coordinateSqBound refines
    leftInside rightInside
  have realProduct :
      ((left.re - right.re) * (left.re + right.re)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) := by
    rw [mul_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      realDifference realSum
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      current.diagonalSq_nonneg
  have imaginaryProduct :
      ((left.im - right.im) * (left.im + right.im)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) := by
    rw [mul_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      imaginaryDifference imaginarySum
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      current.diagonalSq_nonneg
  have productSum :
      ((left.re - right.re) * (left.re + right.re)) ^ 2 +
          ((left.im - right.im) * (left.im + right.im)) ^ 2 ≤
        current.diagonalSq * (4 * bounding.coordinateSqBound) +
          current.diagonalSq * (4 * bounding.coordinateSqBound) :=
    add_le_add realProduct imaginaryProduct
  have twoNonnegative : (0 : Coordinate) ≤ 2 := by decide
  calc
    (normSq left - normSq right) ^ 2 =
        ((left.re - right.re) * (left.re + right.re) +
          (left.im - right.im) * (left.im + right.im)) ^ 2 := by
      simp only [normSq]
      ring1
    _ ≤ 2 *
        (((left.re - right.re) * (left.re + right.re)) ^ 2 +
          ((left.im - right.im) * (left.im + right.im)) ^ 2) :=
      add_sq_le_two _ _
    _ ≤ 2 *
        (current.diagonalSq * (4 * bounding.coordinateSqBound) +
          current.diagonalSq * (4 * bounding.coordinateSqBound)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        productSum twoNonnegative
    _ = 16 * bounding.coordinateSqBound * current.diagonalSq := by
      ring1

/-- The squared change in a Hermitian form between any two points of the
current box is bounded by a displayed rational multiple of its squared
diagonal. -/
theorem eval_sub_sq_le
    (form : HermitianForm) {bounding current : Box} {left right : Gaussian}
    (refines : current.Refines bounding)
    (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    (form.eval left - form.eval right) ^ 2 ≤
      variationSqBound form bounding current := by
  have normDifference := normSq_sub_sq_le refines leftInside rightInside
  have realDifference := real_sub_sq_le_diagonalSq leftInside rightInside
  have imaginaryDifference := imag_sub_sq_le_diagonalSq leftInside rightInside
  have radialSquare := RFAP.ConstructiveFraction.sq_nonneg_direct form.radial
  have realSquare :=
    RFAP.ConstructiveFraction.sq_nonneg_direct form.realLinear
  have imaginarySquare :=
    RFAP.ConstructiveFraction.sq_nonneg_direct form.imagLinear
  have radialTerm :
      (form.radial * (normSq left - normSq right)) ^ 2 ≤
        form.radial ^ 2 *
          (16 * bounding.coordinateSqBound * current.diagonalSq) := by
    rw [mul_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      normDifference radialSquare
  have realTerm :
      (form.realLinear * (left.re - right.re)) ^ 2 ≤
        form.realLinear ^ 2 * current.diagonalSq := by
    rw [mul_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      realDifference realSquare
  have imaginaryTerm :
      (form.imagLinear * (left.im - right.im)) ^ 2 ≤
        form.imagLinear ^ 2 * current.diagonalSq := by
    rw [mul_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      imaginaryDifference imaginarySquare
  have termSum :
      (form.radial * (normSq left - normSq right)) ^ 2 +
          (form.realLinear * (left.re - right.re)) ^ 2 +
          (form.imagLinear * (left.im - right.im)) ^ 2 ≤
        form.radial ^ 2 *
            (16 * bounding.coordinateSqBound * current.diagonalSq) +
          form.realLinear ^ 2 * current.diagonalSq +
          form.imagLinear ^ 2 * current.diagonalSq :=
    add_le_add (add_le_add radialTerm realTerm) imaginaryTerm
  have threeNonnegative : (0 : Coordinate) ≤ 3 := by decide
  calc
    (form.eval left - form.eval right) ^ 2 =
        (form.radial * (normSq left - normSq right) +
          form.realLinear * (left.re - right.re) +
          form.imagLinear * (left.im - right.im)) ^ 2 := by
      simp only [HermitianForm.eval]
      ring1
    _ ≤ 3 *
        ((form.radial * (normSq left - normSq right)) ^ 2 +
          (form.realLinear * (left.re - right.re)) ^ 2 +
          (form.imagLinear * (left.im - right.im)) ^ 2) :=
      add_sq_le_three _ _ _
    _ ≤ 3 *
        (form.radial ^ 2 *
            (16 * bounding.coordinateSqBound * current.diagonalSq) +
          form.realLinear ^ 2 * current.diagonalSq +
          form.imagLinear ^ 2 * current.diagonalSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        termSum threeNonnegative
    _ = variationSqBound form bounding current := by
      simp only [variationSqBound, variationCoefficient]
      ring1

/-- A proof-bearing finite certificate that one displayed sample is farther
from zero than the form can vary across the current box. -/
structure Certificate
    (form : HermitianForm) (bounding current : Box) where
  refines : current.Refines bounding
  sample : Gaussian
  sampleInside : current.Contains sample
  margin : variationSqBound form bounding current < form.eval sample ^ 2

namespace Certificate

theorem eval_mul_sample_pos
    {form : HermitianForm} {bounding current : Box}
    (certificate : Certificate form bounding current)
    {value : Gaussian} (inside : current.Contains value) :
    0 < form.eval value * form.eval certificate.sample := by
  have difference := eval_sub_sq_le form certificate.refines inside
    certificate.sampleInside
  exact RFAP.IntervalSign.mul_pos_of_sub_sq_lt_sq
    (difference.trans_lt certificate.margin)

private theorem negative_of_mul_pos_right_neg
    {left right : Coordinate} (product : 0 < left * right)
    (rightNegative : right < 0) : left < 0 := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · exact leftNegative
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        leftPositive rightNegative
    exact (lt_asymm product negative).elim

private theorem positive_of_mul_pos_right_pos
    {left right : Coordinate} (product : 0 < left * right)
    (rightPositive : 0 < right) : 0 < left := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        leftNegative rightPositive
    exact (lt_asymm product negative).elim
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · exact leftPositive

/-- A successful margin certificate produces one strict sign over the whole
box. -/
inductive StrictSign (form : HermitianForm) (current : Box) where
  | negative (holds : ∀ value, current.Contains value → form.eval value < 0)
  | positive (holds : ∀ value, current.Contains value → 0 < form.eval value)

def strictSign
    {form : HermitianForm} {bounding current : Box}
    (certificate : Certificate form bounding current) :
    StrictSign form current := by
  if sampleNegative : form.eval certificate.sample < 0 then
    exact .negative (by
      intro value inside
      exact negative_of_mul_pos_right_neg
        (certificate.eval_mul_sample_pos inside) sampleNegative)
  else
    have sampleNonzero : form.eval certificate.sample ≠ 0 := by
      intro sampleZero
      have impossible : variationSqBound form bounding current < 0 := by
        have margin := certificate.margin
        rw [sampleZero] at margin
        have zeroSquare : (0 : Coordinate) ^ 2 = 0 := by ring1
        rw [zeroSquare] at margin
        exact margin
      exact (not_lt_of_ge
        (variationSqBound_nonneg form bounding current) impossible).elim
    have sampleNonnegative : 0 ≤ form.eval certificate.sample :=
      le_of_not_gt sampleNegative
    have samplePositive : 0 < form.eval certificate.sample :=
      lt_of_le_of_ne sampleNonnegative (Ne.symm sampleNonzero)
    exact .positive (by
      intro value inside
      exact positive_of_mul_pos_right_pos
        (certificate.eval_mul_sample_pos inside) samplePositive)

end Certificate

/-- Execute the one rational margin comparison. -/
def certificate?
    (form : HermitianForm) (bounding current : Box)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    Option (Certificate form bounding current) :=
  if margin : variationSqBound form bounding current < form.eval sample ^ 2 then
    some ⟨refines, sample, sampleInside, margin⟩
  else
    none

theorem certificate?_isSome_iff
    (form : HermitianForm) (bounding current : Box)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    (certificate? form bounding current refines sample sampleInside).isSome =
        true ↔
      variationSqBound form bounding current < form.eval sample ^ 2 := by
  unfold certificate?
  split <;> simp_all

end CCL.CCLBoxSign
