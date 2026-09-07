import FTA.CCLMultiOwnerGrid
import FTA.CCLParserGeometry

/-!
# Parser-sector tangent cones through decoder homographies

The eight CCL sector rows have one or two weak owner boundaries.  At a corner,
the pulled-back real and imaginary comparison gradients are orthogonal and
have the same positive squared norm when the decoder matrix is invertible.
Their appropriately signed sum therefore enters every selected owner side.
A positive rational shrink puts that computed direction inside the unit norm
bound used by the simultaneous owner grid.  This proves the parser-specific
tangent-cone availability left open by the generic finite search.
-/

namespace FTA
namespace CCLSectorTangent

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLOwnerDirection
open FTA.CCLMultiOwnerGrid

abbrev QI := CCL.GaussianRat

/-- Gradient represented as a Gaussian rational vector. -/
def gradientVector (form : HermitianForm) (z : QI) : QI :=
  ⟨gradientX form z, gradientY form z⟩

/-- Counterclockwise rational quarter-turn of a planar direction. -/
def quarterTurn (direction : QI) : QI :=
  ⟨-direction.im, direction.re⟩

@[simp] theorem quarterTurn_re (direction : QI) :
    (quarterTurn direction).re = -direction.im := rfl

@[simp] theorem quarterTurn_im (direction : QI) :
    (quarterTurn direction).im = direction.re := rfl

@[simp] theorem quarterTurn_neg_quarterTurn (direction : QI) :
    quarterTurn (-(quarterTurn direction)) = direction := by
  ext <;> simp [quarterTurn]

/-- Two nonzero rational vectors with equal squared norm and zero dot product
differ by exactly one of the two rational quarter-turns. -/
theorem eq_quarterTurn_or_neg_quarterTurn
    (left right : QI)
    (leftPositive : 0 < normSq left)
    (equalNorm : normSq right = normSq left)
    (orthogonal : left.re * right.re + left.im * right.im = 0) :
    right = quarterTurn left ∨ right = -(quarterTurn left) := by
  let cross := left.re * right.im - left.im * right.re
  have lagrange :
      (left.re * right.re + left.im * right.im) ^ 2 + cross ^ 2 =
        normSq left * normSq right := by
    dsimp only [cross, normSq]
    ring
  have crossSquare : cross ^ 2 = (normSq left) ^ 2 := by
    rw [orthogonal, zero_pow (by norm_num)] at lagrange
    calc
      cross ^ 2 = normSq left * normSq right := by linarith
      _ = (normSq left) ^ 2 := by rw [equalNorm]; ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp crossSquare) with
      crossPositive | crossNegative
  · left
    have first : left.re * (right.re + left.im) +
        left.im * (right.im - left.re) = 0 := by
      nlinarith [orthogonal]
    have second : -left.im * (right.re + left.im) +
        left.re * (right.im - left.re) = 0 := by
      dsimp only [cross, normSq] at crossPositive
      nlinarith [crossPositive]
    have realProduct : (left.re ^ 2 + left.im ^ 2) *
        (right.re + left.im) = 0 := by
      linear_combination left.re * first - left.im * second
    have imagProduct : (left.re ^ 2 + left.im ^ 2) *
        (right.im - left.re) = 0 := by
      linear_combination left.im * first + left.re * second
    have normNonzero : left.re ^ 2 + left.im ^ 2 ≠ 0 := by
      dsimp only [normSq] at leftPositive
      exact leftPositive.ne'
    have realZero := (mul_eq_zero.mp realProduct).resolve_left normNonzero
    have imagZero := (mul_eq_zero.mp imagProduct).resolve_left normNonzero
    ext <;> simp only [quarterTurn_re, quarterTurn_im] <;> linarith
  · right
    have first : left.re * (right.re - left.im) +
        left.im * (right.im + left.re) = 0 := by
      nlinarith [orthogonal]
    have second : -left.im * (right.re - left.im) +
        left.re * (right.im + left.re) = 0 := by
      dsimp only [cross, normSq] at crossNegative
      nlinarith [crossNegative]
    have realProduct : (left.re ^ 2 + left.im ^ 2) *
        (right.re - left.im) = 0 := by
      linear_combination left.re * first - left.im * second
    have imagProduct : (left.re ^ 2 + left.im ^ 2) *
        (right.im + left.re) = 0 := by
      linear_combination left.im * first + left.re * second
    have normNonzero : left.re ^ 2 + left.im ^ 2 ≠ 0 := by
      dsimp only [normSq] at leftPositive
      exact leftPositive.ne'
    have realZero := (mul_eq_zero.mp realProduct).resolve_left normNonzero
    have imagZero := (mul_eq_zero.mp imagProduct).resolve_left normNonzero
    ext <;> simp only [neg_re, neg_im, quarterTurn_re, quarterTurn_im] <;>
      linarith

/-- One of the eight executable compass directions lies strictly between a
nonzero rational vector and its counterclockwise quarter-turn. -/
theorem exists_coordinateDirection_slopes_quarterTurn
    (left : QI) (leftPositive : 0 < normSq left) :
    ∃ direction ∈ coordinateDirections,
      0 < left.re * direction.re + left.im * direction.im ∧
      0 < (quarterTurn left).re * direction.re +
        (quarterTurn left).im * direction.im := by
  by_cases xZero : left.re = 0
  · have yNonzero : left.im ≠ 0 := by
      intro yZero
      simp [normSq, xZero, yZero] at leftPositive
    by_cases yPositive : 0 < left.im
    · refine ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · simp
        linarith
      · simp [quarterTurn, xZero]
        linarith
    · have yNegative : left.im < 0 :=
        lt_of_le_of_ne (le_of_not_gt yPositive) yNonzero
      refine ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · simp
        linarith
      · simp [quarterTurn, xZero]
        linarith
  · by_cases yZero : left.im = 0
    · by_cases xPositive : 0 < left.re
      · refine ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
        · simp [yZero]
          linarith
        · simp [quarterTurn]
          linarith
      · have xNegative : left.re < 0 :=
          lt_of_le_of_ne (le_of_not_gt xPositive) xZero
        refine ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
        · simp [yZero]
          linarith
        · simp [quarterTurn]
          linarith
    · by_cases xPositive : 0 < left.re
      · by_cases yPositive : 0 < left.im
        · refine ⟨⟨0, 1⟩, by simp [coordinateDirections], ?_, ?_⟩
          · simp
            exact yPositive
          · simpa [quarterTurn] using xPositive
        · have yNegative : left.im < 0 :=
            lt_of_le_of_ne (le_of_not_gt yPositive) yZero
          refine ⟨⟨1, 0⟩, by simp [coordinateDirections], ?_, ?_⟩
          · simpa using xPositive
          · simp [quarterTurn]
            linarith
      · have xNegative : left.re < 0 :=
          lt_of_le_of_ne (le_of_not_gt xPositive) xZero
        by_cases yPositive : 0 < left.im
        · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_, ?_⟩
          · simp
            linarith
          · simpa [quarterTurn] using yPositive
        · have yNegative : left.im < 0 :=
            lt_of_le_of_ne (le_of_not_gt yPositive) yZero
          refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_, ?_⟩
          · simp
            linarith
          · simp [quarterTurn]
            linarith

/-- If two rational vectors make an angle strictly smaller than 135 degrees,
one of the eight compass directions has positive dot product with both.  The
strict hypothesis is written without square roots. -/
theorem exists_coordinateDirection_slopes_of_angleGap_pos
    (left right : QI)
    (angleGap :
      0 < normSq left * normSq right -
        2 * (left.re * right.re + left.im * right.im) ^ 2) :
    ∃ direction ∈ coordinateDirections,
      0 < left.re * direction.re + left.im * direction.im ∧
        0 < right.re * direction.re + right.im * direction.im := by
  by_cases eastProduct : 0 < left.re * right.re
  · rcases mul_pos_iff.mp eastProduct with positive | negative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], by simpa using positive.1,
        by simpa using positive.2⟩
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
        simp <;> linarith
  · by_cases northProduct : 0 < left.im * right.im
    · rcases mul_pos_iff.mp northProduct with positive | negative
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], by simpa using positive.1,
          by simpa using positive.2⟩
      · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
          simp <;> linarith
    · by_cases northEastProduct :
        0 < (left.re + left.im) * (right.re + right.im)
      · rcases mul_pos_iff.mp northEastProduct with positive | negative
        · refine ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
            simp <;> linarith
        · refine ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
            simp <;> linarith
      · by_cases southEastProduct :
          0 < (left.re - left.im) * (right.re - right.im)
        · rcases mul_pos_iff.mp southEastProduct with positive | negative
          · refine ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
              simp <;> linarith
          · refine ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩ <;>
              simp <;> linarith
        · have eastNonpositive : left.re * right.re ≤ 0 :=
            le_of_not_gt eastProduct
          have northNonpositive : left.im * right.im ≤ 0 :=
            le_of_not_gt northProduct
          have northEastNonpositive :
              (left.re + left.im) * (right.re + right.im) ≤ 0 :=
            le_of_not_gt northEastProduct
          have southEastNonpositive :
              (left.re - left.im) * (right.re - right.im) ≤ 0 :=
            le_of_not_gt southEastProduct
          have axisProductsNonnegative :
              0 ≤ (left.re * right.re) * (left.im * right.im) :=
            mul_nonneg_of_nonpos_of_nonpos eastNonpositive northNonpositive
          have diagonalProductsNonnegative :
              0 ≤ ((left.re + left.im) * (right.re + right.im)) *
                ((left.re - left.im) * (right.re - right.im)) :=
            mul_nonneg_of_nonpos_of_nonpos northEastNonpositive
              southEastNonpositive
          have identity :
              2 * (left.re * right.re + left.im * right.im) ^ 2 -
                  normSq left * normSq right =
                ((left.re + left.im) * (right.re + right.im)) *
                    ((left.re - left.im) * (right.re - right.im)) +
                  4 * (left.re * right.re) * (left.im * right.im) := by
            simp only [normSq]
            ring
          nlinarith

private theorem mul_le_delta_mul_upper_of_no_common_large
    (left right delta upper : ℚ)
    (deltaNonnegative : 0 ≤ delta) (upperNonnegative : 0 ≤ upper)
    (leftBound : |left| ≤ upper) (rightBound : |right| ≤ upper)
    (positiveFailure : ¬(delta < left ∧ delta < right))
    (negativeFailure : ¬(delta < -left ∧ delta < -right)) :
    left * right ≤ delta * upper := by
  by_cases productPositive : 0 < left * right
  · rcases mul_pos_iff.mp productPositive with positive | negative
    · have oneSmall : left ≤ delta ∨ right ≤ delta := by
        by_cases leftLarge : delta < left
        · right
          exact le_of_not_gt fun rightLarge =>
            positiveFailure ⟨leftLarge, rightLarge⟩
        · exact Or.inl (le_of_not_gt leftLarge)
      have leftUpper : left ≤ upper := (le_abs_self left).trans leftBound
      have rightUpper : right ≤ upper := (le_abs_self right).trans rightBound
      rcases oneSmall with leftSmall | rightSmall
      · exact (mul_le_mul_of_nonneg_right leftSmall positive.2.le).trans
          (mul_le_mul_of_nonneg_left rightUpper deltaNonnegative)
      · calc
          left * right ≤ left * delta :=
            mul_le_mul_of_nonneg_left rightSmall positive.1.le
          _ = delta * left := by ring
          _ ≤ delta * upper :=
            mul_le_mul_of_nonneg_left leftUpper deltaNonnegative
    · have oneSmall : -left ≤ delta ∨ -right ≤ delta := by
        by_cases leftLarge : delta < -left
        · right
          exact le_of_not_gt fun rightLarge =>
            negativeFailure ⟨leftLarge, rightLarge⟩
        · exact Or.inl (le_of_not_gt leftLarge)
      have leftUpper : -left ≤ upper := by
        simpa only [abs_of_neg negative.1] using leftBound
      have rightUpper : -right ≤ upper := by
        simpa only [abs_of_neg negative.2] using rightBound
      rcases oneSmall with leftSmall | rightSmall
      · calc
          left * right = (-left) * (-right) := by ring
          _ ≤ delta * (-right) :=
            mul_le_mul_of_nonneg_right leftSmall (neg_nonneg.mpr negative.2.le)
          _ ≤ delta * upper :=
            mul_le_mul_of_nonneg_left rightUpper deltaNonnegative
      · calc
          left * right = (-right) * (-left) := by ring
          _ ≤ delta * (-left) :=
            mul_le_mul_of_nonneg_right rightSmall (neg_nonneg.mpr negative.1.le)
          _ ≤ delta * upper :=
            mul_le_mul_of_nonneg_left leftUpper deltaNonnegative
  · exact (le_of_not_gt productPositive).trans
      (mul_nonneg deltaNonnegative upperNonnegative)

private theorem neg_mul_le_delta_mul_cube
    (left right delta upper : ℚ)
    (deltaNonnegative : 0 ≤ delta) (upperNonnegative : 0 ≤ upper)
    (leftUpper : left ≤ delta * upper)
    (rightUpper : right ≤ delta * upper)
    (leftAbs : |left| ≤ upper ^ 2)
    (rightAbs : |right| ≤ upper ^ 2) :
    -left * right ≤ delta * upper ^ 3 := by
  have deltaUpperNonnegative : 0 ≤ delta * upper :=
    mul_nonneg deltaNonnegative upperNonnegative
  by_cases leftNonnegative : 0 ≤ left
  · by_cases rightNonnegative : 0 ≤ right
    · have productNonnegative : 0 ≤ left * right :=
        mul_nonneg leftNonnegative rightNonnegative
      have targetNonnegative : 0 ≤ delta * upper ^ 3 := by positivity
      nlinarith
    · have rightNegative : right < 0 := lt_of_not_ge rightNonnegative
      have negRightUpper : -right ≤ upper ^ 2 := by
        simpa only [abs_of_neg rightNegative] using rightAbs
      calc
        -left * right = left * (-right) := by ring
        _ ≤ (delta * upper) * (-right) :=
          mul_le_mul_of_nonneg_right leftUpper (neg_nonneg.mpr rightNegative.le)
        _ ≤ (delta * upper) * upper ^ 2 :=
          mul_le_mul_of_nonneg_left negRightUpper deltaUpperNonnegative
        _ = delta * upper ^ 3 := by ring
  · have leftNegative : left < 0 := lt_of_not_ge leftNonnegative
    by_cases rightNonnegative : 0 ≤ right
    · have negLeftUpper : -left ≤ upper ^ 2 := by
        simpa only [abs_of_neg leftNegative] using leftAbs
      calc
        -left * right ≤ (upper ^ 2) * right :=
          mul_le_mul_of_nonneg_right negLeftUpper rightNonnegative
        _ ≤ (upper ^ 2) * (delta * upper) :=
          mul_le_mul_of_nonneg_left rightUpper (sq_nonneg upper)
        _ = delta * upper ^ 3 := by ring
    · have rightNegative : right < 0 := lt_of_not_ge rightNonnegative
      have productPositive : 0 < left * right :=
        mul_pos_of_neg_of_neg leftNegative rightNegative
      have targetNonnegative : 0 ≤ delta * upper ^ 3 := by positivity
      nlinarith

/-- Quantitative one-face compass lemma.  A rational upper bound for the two
gradient coordinates converts a squared-norm lower bound into a common
strict slope floor for one of the four axis directions. -/
theorem exists_coordinateDirection_slope_above_of_norm
    (vector : QI) (delta upper : ℚ)
    (deltaNonnegative : 0 ≤ delta)
    (realBound : |vector.re| ≤ upper)
    (imagBound : |vector.im| ≤ upper)
    (normLarge : 2 * delta * upper < normSq vector) :
    ∃ direction ∈ coordinateDirections,
      delta < vector.re * direction.re + vector.im * direction.im := by
  by_cases east : delta < vector.re
  · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], by simpa using east⟩
  · by_cases west : delta < -vector.re
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_⟩
      simpa using west
    · by_cases north : delta < vector.im
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], by simpa using north⟩
      · by_cases south : delta < -vector.im
        · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_⟩
          simpa using south
        · have realDelta : |vector.re| ≤ delta :=
            abs_le.mpr ⟨by linarith [le_of_not_gt west], le_of_not_gt east⟩
          have imagDelta : |vector.im| ≤ delta :=
            abs_le.mpr ⟨by linarith [le_of_not_gt south], le_of_not_gt north⟩
          have realSquare : vector.re ^ 2 ≤ delta * upper := by
            have product := mul_le_mul realDelta realBound
              (abs_nonneg vector.re) deltaNonnegative
            calc
              vector.re ^ 2 = |vector.re| ^ 2 := (sq_abs vector.re).symm
              _ = |vector.re| * |vector.re| := by ring
              _ ≤ delta * upper := product
          have imagSquare : vector.im ^ 2 ≤ delta * upper := by
            have product := mul_le_mul imagDelta imagBound
              (abs_nonneg vector.im) deltaNonnegative
            calc
              vector.im ^ 2 = |vector.im| ^ 2 := (sq_abs vector.im).symm
              _ = |vector.im| * |vector.im| := by ring
              _ ≤ delta * upper := product
          simp only [normSq] at normLarge
          nlinarith

/-- Quantitative two-face compass lemma.  The invariant angle gap supplies a
uniform slope floor once all four gradient coordinates have a common rational
upper bound.  The constant is deliberately conservative and square-root free. -/
theorem exists_coordinateDirection_slopes_above_of_angleGap
    (left right : QI) (delta upper : ℚ)
    (deltaNonnegative : 0 ≤ delta) (upperPositive : 0 < upper)
    (leftRealBound : |left.re| ≤ upper)
    (leftImagBound : |left.im| ≤ upper)
    (rightRealBound : |right.re| ≤ upper)
    (rightImagBound : |right.im| ≤ upper)
    (gapLarge : 20 * delta * upper ^ 3 <
      normSq left * normSq right -
        2 * (left.re * right.re + left.im * right.im) ^ 2) :
    ∃ direction ∈ coordinateDirections,
      delta < left.re * direction.re + left.im * direction.im ∧
        delta < right.re * direction.re + right.im * direction.im := by
  let leftNorthEast := (left.re + left.im) / 2
  let rightNorthEast := (right.re + right.im) / 2
  let leftSouthEast := (left.re - left.im) / 2
  let rightSouthEast := (right.re - right.im) / 2
  have upperNonnegative : 0 ≤ upper := upperPositive.le
  have leftNorthEastBound : |leftNorthEast| ≤ upper := by
    dsimp only [leftNorthEast]
    rw [abs_div]
    norm_num
    calc
      (|left.re + left.im|) / 2 ≤
          (|left.re| + |left.im|) / 2 := by gcongr; exact abs_add_le _ _
      _ ≤ upper := by linarith
  have rightNorthEastBound : |rightNorthEast| ≤ upper := by
    dsimp only [rightNorthEast]
    rw [abs_div]
    norm_num
    calc
      (|right.re + right.im|) / 2 ≤
          (|right.re| + |right.im|) / 2 := by gcongr; exact abs_add_le _ _
      _ ≤ upper := by linarith
  have leftSouthEastBound : |leftSouthEast| ≤ upper := by
    dsimp only [leftSouthEast]
    rw [abs_div]
    norm_num
    calc
      (|left.re - left.im|) / 2 ≤
          (|left.re| + |left.im|) / 2 := by
            gcongr
            calc
              |left.re - left.im| = |left.re + -left.im| := by ring_nf
              _ ≤ |left.re| + |-left.im| := abs_add_le _ _
              _ = |left.re| + |left.im| := by rw [abs_neg]
      _ ≤ upper := by linarith
  have rightSouthEastBound : |rightSouthEast| ≤ upper := by
    dsimp only [rightSouthEast]
    rw [abs_div]
    norm_num
    calc
      (|right.re - right.im|) / 2 ≤
          (|right.re| + |right.im|) / 2 := by
            gcongr
            calc
              |right.re - right.im| = |right.re + -right.im| := by ring_nf
              _ ≤ |right.re| + |-right.im| := abs_add_le _ _
              _ = |right.re| + |right.im| := by rw [abs_neg]
      _ ≤ upper := by linarith
  by_cases east : delta < left.re ∧ delta < right.re
  · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], by simpa using east⟩
  · by_cases west : delta < -left.re ∧ delta < -right.re
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_⟩
      simpa using west
    · by_cases north : delta < left.im ∧ delta < right.im
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], by simpa using north⟩
      · by_cases south : delta < -left.im ∧ delta < -right.im
        · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_⟩
          simpa using south
        · by_cases northEast :
            delta < leftNorthEast ∧ delta < rightNorthEast
          · refine ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_⟩
            rcases northEast with ⟨leftLarge, rightLarge⟩
            constructor <;>
              dsimp only [leftNorthEast, rightNorthEast] at leftLarge rightLarge <;>
              norm_num at leftLarge rightLarge ⊢ <;> linarith
          · by_cases southWest :
              delta < -leftNorthEast ∧ delta < -rightNorthEast
            · refine ⟨⟨-1 / 2, -1 / 2⟩,
                by simp [coordinateDirections], ?_⟩
              rcases southWest with ⟨leftLarge, rightLarge⟩
              constructor <;>
                dsimp only [leftNorthEast, rightNorthEast] at leftLarge rightLarge <;>
                norm_num at leftLarge rightLarge ⊢ <;> linarith
            · by_cases southEast :
                delta < leftSouthEast ∧ delta < rightSouthEast
              · refine ⟨⟨1 / 2, -1 / 2⟩,
                  by simp [coordinateDirections], ?_⟩
                rcases southEast with ⟨leftLarge, rightLarge⟩
                constructor <;>
                  dsimp only [leftSouthEast, rightSouthEast] at leftLarge rightLarge <;>
                  norm_num at leftLarge rightLarge ⊢ <;> linarith
              · by_cases northWest :
                  delta < -leftSouthEast ∧ delta < -rightSouthEast
                · refine ⟨⟨-1 / 2, 1 / 2⟩,
                    by simp [coordinateDirections], ?_⟩
                  rcases northWest with ⟨leftLarge, rightLarge⟩
                  constructor <;>
                    dsimp only [leftSouthEast, rightSouthEast] at leftLarge rightLarge <;>
                    norm_num at leftLarge rightLarge ⊢ <;> linarith
                · let eastProduct := left.re * right.re
                  let northProduct := left.im * right.im
                  let northEastProduct := leftNorthEast * rightNorthEast
                  let southEastProduct := leftSouthEast * rightSouthEast
                  have eastUpper : eastProduct ≤ delta * upper :=
                    mul_le_delta_mul_upper_of_no_common_large left.re right.re
                      delta upper deltaNonnegative upperNonnegative
                      leftRealBound rightRealBound east west
                  have northUpper : northProduct ≤ delta * upper :=
                    mul_le_delta_mul_upper_of_no_common_large left.im right.im
                      delta upper deltaNonnegative upperNonnegative
                      leftImagBound rightImagBound north south
                  have northEastUpper : northEastProduct ≤ delta * upper :=
                    mul_le_delta_mul_upper_of_no_common_large leftNorthEast
                      rightNorthEast delta upper deltaNonnegative
                      upperNonnegative leftNorthEastBound rightNorthEastBound
                      northEast southWest
                  have southEastUpper : southEastProduct ≤ delta * upper :=
                    mul_le_delta_mul_upper_of_no_common_large leftSouthEast
                      rightSouthEast delta upper deltaNonnegative
                      upperNonnegative leftSouthEastBound rightSouthEastBound
                      southEast northWest
                  have eastAbs : |eastProduct| ≤ upper ^ 2 := by
                    dsimp only [eastProduct]
                    rw [abs_mul]
                    exact (mul_le_mul leftRealBound rightRealBound
                      (abs_nonneg _) upperNonnegative).trans_eq (by ring)
                  have northAbs : |northProduct| ≤ upper ^ 2 := by
                    dsimp only [northProduct]
                    rw [abs_mul]
                    exact (mul_le_mul leftImagBound rightImagBound
                      (abs_nonneg _) upperNonnegative).trans_eq (by ring)
                  have northEastAbs : |northEastProduct| ≤ upper ^ 2 := by
                    dsimp only [northEastProduct]
                    rw [abs_mul]
                    exact (mul_le_mul leftNorthEastBound rightNorthEastBound
                      (abs_nonneg _) upperNonnegative).trans_eq (by ring)
                  have southEastAbs : |southEastProduct| ≤ upper ^ 2 := by
                    dsimp only [southEastProduct]
                    rw [abs_mul]
                    exact (mul_le_mul leftSouthEastBound rightSouthEastBound
                      (abs_nonneg _) upperNonnegative).trans_eq (by ring)
                  have diagonalBound :
                      -northEastProduct * southEastProduct ≤
                        delta * upper ^ 3 :=
                    neg_mul_le_delta_mul_cube northEastProduct southEastProduct
                      delta upper deltaNonnegative upperNonnegative
                      northEastUpper southEastUpper northEastAbs southEastAbs
                  have axisBound : -eastProduct * northProduct ≤
                      delta * upper ^ 3 :=
                    neg_mul_le_delta_mul_cube eastProduct northProduct delta
                      upper deltaNonnegative upperNonnegative eastUpper
                      northUpper eastAbs northAbs
                  have identity :
                      normSq left * normSq right -
                          2 * (left.re * right.re +
                            left.im * right.im) ^ 2 =
                        16 * (-northEastProduct * southEastProduct) +
                          4 * (-eastProduct * northProduct) := by
                    dsimp only [eastProduct, northProduct, northEastProduct,
                      southEastProduct, leftNorthEast, rightNorthEast,
                      leftSouthEast, rightSouthEast, normSq]
                    ring
                  rw [identity] at gapLarge
                  nlinarith

/-- Equal-length orthogonal nonzero vectors admit a common strictly positive
direction in the executable eight-direction table. -/
theorem exists_coordinateDirection_slopes_of_equalNorm_orthogonal
    (left right : QI)
    (leftPositive : 0 < normSq left)
    (equalNorm : normSq right = normSq left)
    (orthogonal : left.re * right.re + left.im * right.im = 0) :
    ∃ direction ∈ coordinateDirections,
      0 < left.re * direction.re + left.im * direction.im ∧
      0 < right.re * direction.re + right.im * direction.im := by
  rcases eq_quarterTurn_or_neg_quarterTurn left right leftPositive
      equalNorm orthogonal with rightTurn | rightNegativeTurn
  · rcases exists_coordinateDirection_slopes_quarterTurn left leftPositive with
      ⟨direction, member, leftSlope, rightSlope⟩
    refine ⟨direction, member, leftSlope, ?_⟩
    simpa [rightTurn] using rightSlope
  · have rightPositive : 0 < normSq right := by
      rw [equalNorm]
      exact leftPositive
    rcases exists_coordinateDirection_slopes_quarterTurn right rightPositive with
      ⟨direction, member, rightSlope, leftSlope⟩
    have turnRight : quarterTurn right = left := by
      rw [rightNegativeTurn, quarterTurn_neg_quarterTurn]
    rw [turnRight] at leftSlope
    exact ⟨direction, member, leftSlope, rightSlope⟩

/-- Therefore the actual finite tangent-direction search succeeds on any two
active forms whose gradients are nonzero, equal-length, and orthogonal. -/
theorem tangentDirectionCertificate?_isSome_pair_of_equalNorm_orthogonal
    (left right : HermitianForm) (z : QI)
    (leftPositive : 0 < normSq (gradientVector left z))
    (equalNorm :
      normSq (gradientVector right z) = normSq (gradientVector left z))
    (orthogonal :
      (gradientVector left z).re * (gradientVector right z).re +
        (gradientVector left z).im * (gradientVector right z).im = 0) :
    (tangentDirectionCertificate? [left, right] z).isSome := by
  rcases exists_coordinateDirection_slopes_of_equalNorm_orthogonal
      (gradientVector left z) (gradientVector right z) leftPositive equalNorm
      orthogonal with ⟨direction, member, leftSlope, rightSlope⟩
  apply tangentDirectionCertificate?_isSome_of_mem member
  intro form formMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at formMember
  rcases formMember with rfl | rfl
  · simpa [directionalSlope, gradientVector] using leftSlope
  · simpa [directionalSlope, gradientVector] using rightSlope

theorem coordinates_nonzero_of_normSq_pos
    (direction : QI) (positive : 0 < normSq direction) :
    direction.re ≠ 0 ∨ direction.im ≠ 0 := by
  by_contra bothZero
  push Not at bothZero
  simp [normSq, bothZero.1, bothZero.2] at positive

theorem directionalSlope_gradientVector (form : HermitianForm) (z : QI) :
    directionalSlope form z (gradientVector form z) =
      normSq (gradientVector form z) := by
  simp [directionalSlope, gradientVector, normSq]
  ring

@[simp] theorem gradientX_neg (form : HermitianForm) (z : QI) :
    gradientX form.neg z = -gradientX form z := by
  simp [gradientX, HermitianForm.neg]
  ring

@[simp] theorem gradientY_neg (form : HermitianForm) (z : QI) :
    gradientY form.neg z = -gradientY form z := by
  simp [gradientY, HermitianForm.neg]
  ring

@[simp] theorem gradientVector_neg (form : HermitianForm) (z : QI) :
    gradientVector form.neg z = -gradientVector form z := by
  ext <;> simp [gradientVector]

/-- Rational scalar multiplication kept transparent at both coordinates. -/
def scaleDirection (scale : ℚ) (direction : QI) : QI :=
  ⟨scale * direction.re, scale * direction.im⟩

@[simp] theorem scaleDirection_re (scale : ℚ) (direction : QI) :
    (scaleDirection scale direction).re = scale * direction.re := rfl

@[simp] theorem scaleDirection_im (scale : ℚ) (direction : QI) :
    (scaleDirection scale direction).im = scale * direction.im := rfl

theorem normSq_scaleDirection (scale : ℚ) (direction : QI) :
    normSq (scaleDirection scale direction) = scale ^ 2 * normSq direction := by
  simp [scaleDirection, normSq]
  ring

theorem directionalSlope_scaleDirection
    (form : HermitianForm) (z direction : QI) (scale : ℚ) :
    directionalSlope form z (scaleDirection scale direction) =
      scale * directionalSlope form z direction := by
  simp [directionalSlope, scaleDirection]
  ring

/-- Positive rational shrink used instead of an irrational normalization. -/
def shrinkFactor (direction : QI) : ℚ := 1 / (normSq direction + 1)

def shrinkDirection (direction : QI) : QI :=
  scaleDirection (shrinkFactor direction) direction

theorem shrinkFactor_pos (direction : QI) : 0 < shrinkFactor direction := by
  exact div_pos zero_lt_one (by positivity [normSq_nonneg direction])

theorem normSq_shrinkDirection_le_one (direction : QI) :
    normSq (shrinkDirection direction) ≤ 1 := by
  let value := normSq direction
  have valueNonnegative : 0 ≤ value := normSq_nonneg direction
  have denominatorPositive : 0 < value + 1 := by positivity
  rw [shrinkDirection, normSq_scaleDirection]
  change (1 / (value + 1)) ^ 2 * value ≤ 1
  have quotientIdentity :
      (1 / (value + 1)) ^ 2 * value = value / (value + 1) ^ 2 := by
    field_simp
  rw [quotientIdentity]
  apply (div_le_iff₀ (sq_pos_of_pos denominatorPositive)).2
  nlinarith [sq_nonneg value]

theorem directionalSlope_shrinkDirection
    (form : HermitianForm) (z direction : QI) :
    directionalSlope form z (shrinkDirection direction) =
      shrinkFactor direction * directionalSlope form z direction := by
  exact directionalSlope_scaleDirection form z direction _

theorem gradientVector_normSq_realComparison
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (onBoundary : (realComparisonForm M threshold).eval z = 0) :
    normSq (gradientVector (realComparisonForm M threshold) z) =
      normSq (determinant M) := by
  have identity := gradient_discriminant_identity
    (realComparisonForm M threshold) z
  rw [onBoundary, boundaryDiscriminant_realComparisonForm] at identity
  calc
    normSq (gradientVector (realComparisonForm M threshold) z) =
        gradientX (realComparisonForm M threshold) z ^ 2 +
          gradientY (realComparisonForm M threshold) z ^ 2 := by
      rfl
    _ = normSq (determinant M) := by linarith [identity]

theorem gradientVector_normSq_imagComparison
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (onBoundary : (imagComparisonForm M threshold).eval z = 0) :
    normSq (gradientVector (imagComparisonForm M threshold) z) =
      normSq (determinant M) := by
  have identity := gradient_discriminant_identity
    (imagComparisonForm M threshold) z
  rw [onBoundary, boundaryDiscriminant_imagComparisonForm] at identity
  calc
    normSq (gradientVector (imagComparisonForm M threshold) z) =
        gradientX (imagComparisonForm M threshold) z ^ 2 +
          gradientY (imagComparisonForm M threshold) z ^ 2 := by
      rfl
    _ = normSq (determinant M) := by linarith [identity]

@[simp] theorem gradientX_add (left right : HermitianForm) (z : QI) :
    gradientX (left.add right) z = gradientX left z + gradientX right z := by
  simp [gradientX, HermitianForm.add]
  ring

@[simp] theorem gradientY_add (left right : HermitianForm) (z : QI) :
    gradientY (left.add right) z = gradientY left z + gradientY right z := by
  simp [gradientY, HermitianForm.add]
  ring

/-- The sum of pulled-back real and imaginary coordinate forms has the
expected norm-two discriminant, independently of both thresholds. -/
theorem boundaryDiscriminant_real_add_imag
    (M : Mat2 QI) (realThreshold imagThreshold : ℚ) :
    boundaryDiscriminant ((realComparisonForm M realThreshold).add
      (imagComparisonForm M imagThreshold)) =
      -2 * normSq (determinant M) := by
  simp only [boundaryDiscriminant, HermitianForm.add, realComparisonForm,
    imagComparisonForm, HermitianForm.sub, HermitianForm.neg,
    HermitianForm.scale, realCrossForm, imagCrossForm, affineNormForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

/-- At a pulled-back coordinate corner the real and imaginary comparison
gradients are exactly orthogonal. -/
theorem real_imag_gradient_orthogonal
    (M : Mat2 QI) (realThreshold imagThreshold : ℚ) (z : QI)
    (realBoundary : (realComparisonForm M realThreshold).eval z = 0)
    (imagBoundary : (imagComparisonForm M imagThreshold).eval z = 0) :
    gradientX (realComparisonForm M realThreshold) z *
        gradientX (imagComparisonForm M imagThreshold) z +
      gradientY (realComparisonForm M realThreshold) z *
        gradientY (imagComparisonForm M imagThreshold) z = 0 := by
  let realForm := realComparisonForm M realThreshold
  let imagForm := imagComparisonForm M imagThreshold
  have sumBoundary : (realForm.add imagForm).eval z = 0 := by
    dsimp only [realForm, imagForm]
    rw [HermitianForm.eval_add, realBoundary, imagBoundary]
    norm_num
  have sumIdentity := gradient_discriminant_identity (realForm.add imagForm) z
  rw [sumBoundary, boundaryDiscriminant_real_add_imag] at sumIdentity
  have realNorm := gradientVector_normSq_realComparison M realThreshold z realBoundary
  have imagNorm := gradientVector_normSq_imagComparison M imagThreshold z imagBoundary
  dsimp only [realForm, imagForm] at sumIdentity
  simp only [gradientX_add, gradientY_add] at sumIdentity
  simp only [normSq] at sumIdentity
  simp only [gradientVector, normSq] at realNorm imagNorm
  nlinarith

def gradientDot (left right : HermitianForm) (z : QI) : ℚ :=
  gradientX left z * gradientX right z +
    gradientY left z * gradientY right z

theorem gradientDot_comm (left right : HermitianForm) (z : QI) :
    gradientDot left right z = gradientDot right left z := by
  simp [gradientDot]
  ring

@[simp] theorem gradientDot_neg_left
    (left right : HermitianForm) (z : QI) :
    gradientDot left.neg right z = -gradientDot left right z := by
  simp [gradientDot]
  ring

@[simp] theorem gradientDot_neg_right
    (left right : HermitianForm) (z : QI) :
    gradientDot left right.neg z = -gradientDot left right z := by
  simp [gradientDot]
  ring

theorem directionalSlope_gradientVector_add
    (left right : HermitianForm) (z : QI) :
    directionalSlope left z (gradientVector left z + gradientVector right z) =
      normSq (gradientVector left z) + gradientDot left right z := by
  simp [directionalSlope, gradientVector, normSq, gradientDot]
  ring

theorem directionalSlope_gradientVector_add_right
    (left right : HermitianForm) (z : QI) :
    directionalSlope right z (gradientVector left z + gradientVector right z) =
      normSq (gradientVector right z) + gradientDot left right z := by
  simp [directionalSlope, gradientVector, normSq, gradientDot]
  ring

/-- One nonzero gradient gives a bounded rational tangent direction for a
single active owner boundary. -/
def singletonTangentDirection
    (form : HermitianForm) (z : QI)
    (gradientPositive : 0 < normSq (gradientVector form z)) :
    TangentDirection [form] z where
  vector := shrinkDirection (gradientVector form z)
  normSqLeOne := normSq_shrinkDirection_le_one _
  slopes := by
    intro item member
    simp only [List.mem_singleton] at member
    subst item
    rw [directionalSlope_shrinkDirection,
      directionalSlope_gradientVector]
    exact mul_pos (shrinkFactor_pos _) gradientPositive

/-- Two orthogonal nonzero gradients give the bounded rational corner
direction obtained from their sum. -/
def pairTangentDirection
    (left right : HermitianForm) (z : QI)
    (leftPositive : 0 < normSq (gradientVector left z))
    (rightPositive : 0 < normSq (gradientVector right z))
    (orthogonal : gradientDot left right z = 0) :
    TangentDirection [left, right] z where
  vector := shrinkDirection (gradientVector left z + gradientVector right z)
  normSqLeOne := normSq_shrinkDirection_le_one _
  slopes := by
    intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [directionalSlope_shrinkDirection,
        directionalSlope_gradientVector_add, orthogonal, _root_.add_zero]
      exact mul_pos (shrinkFactor_pos _) leftPositive
    · rw [directionalSlope_shrinkDirection,
        directionalSlope_gradientVector_add_right, orthogonal, _root_.add_zero]
      exact mul_pos (shrinkFactor_pos _) rightPositive

theorem gradientVector_normSq_neg_realComparison
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (onBoundary : (realComparisonForm M threshold).neg.eval z = 0) :
    normSq (gradientVector (realComparisonForm M threshold).neg z) =
      normSq (determinant M) := by
  have baseBoundary : (realComparisonForm M threshold).eval z = 0 := by
    simpa only [HermitianForm.eval_neg, neg_eq_zero] using onBoundary
  rw [gradientVector_neg, normSq_neg,
    gradientVector_normSq_realComparison M threshold z baseBoundary]

theorem gradientVector_normSq_neg_imagComparison
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (onBoundary : (imagComparisonForm M threshold).neg.eval z = 0) :
    normSq (gradientVector (imagComparisonForm M threshold).neg z) =
      normSq (determinant M) := by
  have baseBoundary : (imagComparisonForm M threshold).eval z = 0 := by
    simpa only [HermitianForm.eval_neg, neg_eq_zero] using onBoundary
  rw [gradientVector_neg, normSq_neg,
    gradientVector_normSq_imagComparison M threshold z baseBoundary]

def emptyTangentDirection (z : QI) : TangentDirection [] z where
  vector := 0
  normSqLeOne := by norm_num
  slopes := by simp

/-- Total active-set constructor for one possible weak owner boundary. -/
def activeSingletonTangentDirection
    (form : HermitianForm) (z : QI)
    (gradientPositive : form.eval z = 0 →
      0 < normSq (gradientVector form z)) :
    TangentDirection ([form].filter fun item => decide (item.eval z = 0)) z := by
  by_cases active : form.eval z = 0
  · simpa [active] using singletonTangentDirection form z (gradientPositive active)
  · simpa [active] using emptyTangentDirection z

/-- Total active-set constructor for a possible sector corner. -/
def activePairTangentDirection
    (left right : HermitianForm) (z : QI)
    (leftPositive : left.eval z = 0 →
      0 < normSq (gradientVector left z))
    (rightPositive : right.eval z = 0 →
      0 < normSq (gradientVector right z))
    (orthogonal : left.eval z = 0 → right.eval z = 0 →
      gradientDot left right z = 0) :
    TangentDirection ([left, right].filter fun item =>
      decide (item.eval z = 0)) z := by
  by_cases leftActive : left.eval z = 0
  · by_cases rightActive : right.eval z = 0
    · simpa [leftActive, rightActive] using pairTangentDirection left right z
        (leftPositive leftActive) (rightPositive rightActive)
        (orthogonal leftActive rightActive)
    · simpa [leftActive, rightActive] using singletonTangentDirection left z
        (leftPositive leftActive)
  · by_cases rightActive : right.eval z = 0
    · simpa [leftActive, rightActive] using singletonTangentDirection right z
        (rightPositive rightActive)
    · simpa [leftActive, rightActive] using emptyTangentDirection z

/-- The executable table succeeds for an optional single nondegenerate
boundary, including the vacuous inactive case. -/
theorem tangentDirectionCertificate?_isSome_activeSingleton
    (form : HermitianForm) (z : QI)
    (gradientPositive : form.eval z = 0 →
      0 < normSq (gradientVector form z)) :
    (tangentDirectionCertificate?
      ([form].filter fun item => decide (item.eval z = 0)) z).isSome := by
  by_cases active : form.eval z = 0
  · have filtered :
        [form].filter (fun item => decide (item.eval z = 0)) = [form] := by
      simp [active]
    rw [filtered]
    exact tangentDirectionCertificate?_isSome_singleton form z
      (coordinates_nonzero_of_normSq_pos _ (gradientPositive active))
  · have filtered :
        [form].filter (fun item => decide (item.eval z = 0)) = [] := by
      simp [active]
    rw [filtered]
    exact tangentDirectionCertificate?_isSome_empty z

/-- The executable table also succeeds for an optional orthogonal,
equal-gradient-norm pair. -/
theorem tangentDirectionCertificate?_isSome_activePair
    (left right : HermitianForm) (z : QI)
    (leftPositive : left.eval z = 0 →
      0 < normSq (gradientVector left z))
    (rightPositive : right.eval z = 0 →
      0 < normSq (gradientVector right z))
    (equalNorm : left.eval z = 0 → right.eval z = 0 →
      normSq (gradientVector right z) = normSq (gradientVector left z))
    (orthogonal : left.eval z = 0 → right.eval z = 0 →
      gradientDot left right z = 0) :
    (tangentDirectionCertificate?
      ([left, right].filter fun item => decide (item.eval z = 0)) z).isSome := by
  by_cases leftActive : left.eval z = 0
  · by_cases rightActive : right.eval z = 0
    · have filtered :
          [left, right].filter (fun item => decide (item.eval z = 0)) =
            [left, right] := by
        simp [leftActive, rightActive]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_pair_of_equalNorm_orthogonal
        left right z (leftPositive leftActive)
        (equalNorm leftActive rightActive) (by
          simpa [gradientDot, gradientVector] using
            orthogonal leftActive rightActive)
    · have filtered :
          [left, right].filter (fun item => decide (item.eval z = 0)) =
            [left] := by
        simp [leftActive, rightActive]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_singleton left z
        (coordinates_nonzero_of_normSq_pos _ (leftPositive leftActive))
  · by_cases rightActive : right.eval z = 0
    · have filtered :
          [left, right].filter (fun item => decide (item.eval z = 0)) =
            [right] := by
        simp [leftActive, rightActive]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_singleton right z
        (coordinates_nonzero_of_normSq_pos _ (rightPositive rightActive))
    · have filtered :
          [left, right].filter (fun item => decide (item.eval z = 0)) = [] := by
        simp [leftActive, rightActive]
      rw [filtered]
      exact tangentDirectionCertificate?_isSome_empty z

def positiveRealOwner (M : Mat2 QI) : HermitianForm :=
  realComparisonForm M (1 / 2)

def negativeRealOwner (M : Mat2 QI) : HermitianForm :=
  (realComparisonForm M (-1 / 2)).neg

def positiveImagOwner (M : Mat2 QI) : HermitianForm :=
  imagComparisonForm M (1 / 2)

def negativeImagOwner (M : Mat2 QI) : HermitianForm :=
  (imagComparisonForm M (-1 / 2)).neg

/-- Weak owner boundaries of each deterministic sector row, oriented toward
the row's strict interior. -/
def sectorOwnerForms : Sector → Mat2 QI → List HermitianForm
  | .east, M => [positiveRealOwner M]
  | .northEast, M => [positiveRealOwner M, positiveImagOwner M]
  | .north, M => [positiveImagOwner M]
  | .northWest, M => [negativeRealOwner M, positiveImagOwner M]
  | .west, M => [negativeRealOwner M]
  | .southWest, M => [negativeRealOwner M, negativeImagOwner M]
  | .south, M => [negativeImagOwner M]
  | .southEast, M => [positiveRealOwner M, negativeImagOwner M]

/-- Exact sublist of weak owner boundaries that are equalities at the current
rational point. -/
def activeSectorOwnerForms (sector : Sector) (M : Mat2 QI) (z : QI) :
    List HermitianForm :=
  (sectorOwnerForms sector M).filter fun form => decide (form.eval z = 0)

theorem positiveRealOwner_gradient_norm
    (M : Mat2 QI) (z : QI)
    (onBoundary : (positiveRealOwner M).eval z = 0) :
    normSq (gradientVector (positiveRealOwner M) z) =
      normSq (determinant M) := by
  exact gradientVector_normSq_realComparison M (1 / 2) z onBoundary

theorem negativeRealOwner_gradient_norm
    (M : Mat2 QI) (z : QI)
    (onBoundary : (negativeRealOwner M).eval z = 0) :
    normSq (gradientVector (negativeRealOwner M) z) =
      normSq (determinant M) := by
  exact gradientVector_normSq_neg_realComparison M (-1 / 2) z onBoundary

theorem positiveImagOwner_gradient_norm
    (M : Mat2 QI) (z : QI)
    (onBoundary : (positiveImagOwner M).eval z = 0) :
    normSq (gradientVector (positiveImagOwner M) z) =
      normSq (determinant M) := by
  exact gradientVector_normSq_imagComparison M (1 / 2) z onBoundary

theorem negativeImagOwner_gradient_norm
    (M : Mat2 QI) (z : QI)
    (onBoundary : (negativeImagOwner M).eval z = 0) :
    normSq (gradientVector (negativeImagOwner M) z) =
      normSq (determinant M) := by
  exact gradientVector_normSq_neg_imagComparison M (-1 / 2) z onBoundary

theorem positiveRealOwner_gradient_pos
    (M : Mat2 QI) (z : QI) (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (positiveRealOwner M).eval z = 0) :
    0 < normSq (gradientVector (positiveRealOwner M) z) := by
  rw [positiveRealOwner_gradient_norm M z onBoundary]
  exact normSq_pos determinantNonzero

theorem negativeRealOwner_gradient_pos
    (M : Mat2 QI) (z : QI) (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (negativeRealOwner M).eval z = 0) :
    0 < normSq (gradientVector (negativeRealOwner M) z) := by
  rw [negativeRealOwner_gradient_norm M z onBoundary]
  exact normSq_pos determinantNonzero

theorem positiveImagOwner_gradient_pos
    (M : Mat2 QI) (z : QI) (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (positiveImagOwner M).eval z = 0) :
    0 < normSq (gradientVector (positiveImagOwner M) z) := by
  rw [positiveImagOwner_gradient_norm M z onBoundary]
  exact normSq_pos determinantNonzero

theorem negativeImagOwner_gradient_pos
    (M : Mat2 QI) (z : QI) (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (negativeImagOwner M).eval z = 0) :
    0 < normSq (gradientVector (negativeImagOwner M) z) := by
  rw [negativeImagOwner_gradient_norm M z onBoundary]
  exact normSq_pos determinantNonzero

theorem positiveReal_positiveImag_orthogonal
    (M : Mat2 QI) (z : QI)
    (realBoundary : (positiveRealOwner M).eval z = 0)
    (imagBoundary : (positiveImagOwner M).eval z = 0) :
    gradientDot (positiveRealOwner M) (positiveImagOwner M) z = 0 := by
  exact real_imag_gradient_orthogonal M (1 / 2) (1 / 2) z
    realBoundary imagBoundary

theorem negativeReal_positiveImag_orthogonal
    (M : Mat2 QI) (z : QI)
    (realBoundary : (negativeRealOwner M).eval z = 0)
    (imagBoundary : (positiveImagOwner M).eval z = 0) :
    gradientDot (negativeRealOwner M) (positiveImagOwner M) z = 0 := by
  have baseReal : (realComparisonForm M (-1 / 2)).eval z = 0 := by
    simpa only [negativeRealOwner, HermitianForm.eval_neg, neg_eq_zero]
      using realBoundary
  have orthogonal := real_imag_gradient_orthogonal M (-1 / 2) (1 / 2) z
    baseReal imagBoundary
  simp only [negativeRealOwner, positiveImagOwner, gradientDot,
    gradientX_neg, gradientY_neg] at orthogonal ⊢
  linarith

theorem negativeReal_negativeImag_orthogonal
    (M : Mat2 QI) (z : QI)
    (realBoundary : (negativeRealOwner M).eval z = 0)
    (imagBoundary : (negativeImagOwner M).eval z = 0) :
    gradientDot (negativeRealOwner M) (negativeImagOwner M) z = 0 := by
  have baseReal : (realComparisonForm M (-1 / 2)).eval z = 0 := by
    simpa only [negativeRealOwner, HermitianForm.eval_neg, neg_eq_zero]
      using realBoundary
  have baseImag : (imagComparisonForm M (-1 / 2)).eval z = 0 := by
    simpa only [negativeImagOwner, HermitianForm.eval_neg, neg_eq_zero]
      using imagBoundary
  have orthogonal := real_imag_gradient_orthogonal M (-1 / 2) (-1 / 2) z
    baseReal baseImag
  simp only [negativeRealOwner, negativeImagOwner, gradientDot,
    gradientX_neg, gradientY_neg] at orthogonal ⊢
  linarith

theorem positiveReal_negativeImag_orthogonal
    (M : Mat2 QI) (z : QI)
    (realBoundary : (positiveRealOwner M).eval z = 0)
    (imagBoundary : (negativeImagOwner M).eval z = 0) :
    gradientDot (positiveRealOwner M) (negativeImagOwner M) z = 0 := by
  have baseImag : (imagComparisonForm M (-1 / 2)).eval z = 0 := by
    simpa only [negativeImagOwner, HermitianForm.eval_neg, neg_eq_zero]
      using imagBoundary
  have orthogonal := real_imag_gradient_orthogonal M (1 / 2) (-1 / 2) z
    realBoundary baseImag
  simp only [positiveRealOwner, negativeImagOwner, gradientDot,
    gradientX_neg, gradientY_neg] at orthogonal ⊢
  linarith

/-- The deterministic eight-sector convention always supplies a bounded
rational tangent direction for exactly the weak owner boundaries active at
the current point. -/
def sectorTangentDirection
    (sector : Sector) (M : Mat2 QI) (z : QI)
    (determinantNonzero : determinant M ≠ 0) :
    TangentDirection (activeSectorOwnerForms sector M z) z := by
  cases sector with
  | east =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activeSingletonTangentDirection (positiveRealOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
  | northEast =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activePairTangentDirection (positiveRealOwner M) (positiveImagOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
          (positiveImagOwner_gradient_pos M z determinantNonzero)
          (positiveReal_positiveImag_orthogonal M z)
  | north =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activeSingletonTangentDirection (positiveImagOwner M) z
          (positiveImagOwner_gradient_pos M z determinantNonzero)
  | northWest =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activePairTangentDirection (negativeRealOwner M) (positiveImagOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
          (positiveImagOwner_gradient_pos M z determinantNonzero)
          (negativeReal_positiveImag_orthogonal M z)
  | west =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activeSingletonTangentDirection (negativeRealOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
  | southWest =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activePairTangentDirection (negativeRealOwner M) (negativeImagOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
          (negativeImagOwner_gradient_pos M z determinantNonzero)
          (negativeReal_negativeImag_orthogonal M z)
  | south =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activeSingletonTangentDirection (negativeImagOwner M) z
          (negativeImagOwner_gradient_pos M z determinantNonzero)
  | southEast =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        activePairTangentDirection (positiveRealOwner M) (negativeImagOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
          (negativeImagOwner_gradient_pos M z determinantNonzero)
          (positiveReal_negativeImag_orthogonal M z)

/-- Unlike the abstract shrunk-gradient witness above, this theorem targets
the finite search used by `gridData?`: every deterministic sector active set
is found by the fixed eight-direction table. -/
theorem tangentDirectionCertificate?_isSome_activeSectorOwnerForms
    (sector : Sector) (M : Mat2 QI) (z : QI)
    (determinantNonzero : determinant M ≠ 0) :
    (tangentDirectionCertificate?
      (activeSectorOwnerForms sector M z) z).isSome := by
  cases sector with
  | east =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activeSingleton
          (positiveRealOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
  | northEast =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activePair
          (positiveRealOwner M) (positiveImagOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
          (positiveImagOwner_gradient_pos M z determinantNonzero)
          (fun realBoundary imagBoundary => by
            rw [positiveImagOwner_gradient_norm M z imagBoundary,
              positiveRealOwner_gradient_norm M z realBoundary])
          (positiveReal_positiveImag_orthogonal M z)
  | north =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activeSingleton
          (positiveImagOwner M) z
          (positiveImagOwner_gradient_pos M z determinantNonzero)
  | northWest =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activePair
          (negativeRealOwner M) (positiveImagOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
          (positiveImagOwner_gradient_pos M z determinantNonzero)
          (fun realBoundary imagBoundary => by
            rw [positiveImagOwner_gradient_norm M z imagBoundary,
              negativeRealOwner_gradient_norm M z realBoundary])
          (negativeReal_positiveImag_orthogonal M z)
  | west =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activeSingleton
          (negativeRealOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
  | southWest =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activePair
          (negativeRealOwner M) (negativeImagOwner M) z
          (negativeRealOwner_gradient_pos M z determinantNonzero)
          (negativeImagOwner_gradient_pos M z determinantNonzero)
          (fun realBoundary imagBoundary => by
            rw [negativeImagOwner_gradient_norm M z imagBoundary,
              negativeRealOwner_gradient_norm M z realBoundary])
          (negativeReal_negativeImag_orthogonal M z)
  | south =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activeSingleton
          (negativeImagOwner M) z
          (negativeImagOwner_gradient_pos M z determinantNonzero)
  | southEast =>
      simpa [activeSectorOwnerForms, sectorOwnerForms] using
        tangentDirectionCertificate?_isSome_activePair
          (positiveRealOwner M) (negativeImagOwner M) z
          (positiveRealOwner_gradient_pos M z determinantNonzero)
          (negativeImagOwner_gradient_pos M z determinantNonzero)
          (fun realBoundary imagBoundary => by
            rw [negativeImagOwner_gradient_norm M z imagBoundary,
              positiveRealOwner_gradient_norm M z realBoundary])
          (positiveReal_negativeImag_orthogonal M z)

end CCLSectorTangent
end FTA
