import FTA.CCLFormulaPullback
import FTA.CCLChordalEnvelope

/-!
# Explicit projective matrix stability bounds

Historical CCL block witnesses may be recomputed at different rational points
of one shrinking winding box.  This file gives the finite rational estimate
needed to compare their inverse decoder coordinates.  Every invertible
two-by-two Gaussian-rational matrix is globally Lipschitz for squared chordal
distance, with a deliberately coarse coefficient-computed constant.
-/

namespace FTA
namespace CCLProjectiveMatrixBounds

open CCL CCL.GaussianRat
open FTA.CCLChordalEnvelope
open FTA.CCLFormulaPullback
open FTA.CCLGeometry

abbrev QI := CCL.GaussianRat

/-- Sum of the four squared Gaussian-rational matrix coefficients. -/
def coefficientWeight (matrix : Mat2 QI) : ℚ :=
  normSq matrix.a + normSq matrix.b + normSq matrix.c + normSq matrix.d

theorem coefficientWeight_nonneg (matrix : Mat2 QI) :
    0 ≤ coefficientWeight matrix := by
  unfold coefficientWeight
  exact add_nonneg
    (add_nonneg
      (add_nonneg (normSq_nonneg matrix.a) (normSq_nonneg matrix.b))
      (normSq_nonneg matrix.c))
    (normSq_nonneg matrix.d)

theorem coefficientWeight_pos_of_det_ne
    (matrix : Mat2 QI) (determinantNonzero : matrix.det ≠ 0) :
    0 < coefficientWeight matrix := by
  by_cases firstNonzero : matrix.a ≠ 0
  · unfold coefficientWeight
    nlinarith [normSq_pos firstNonzero, normSq_nonneg matrix.b,
      normSq_nonneg matrix.c, normSq_nonneg matrix.d]
  · have firstZero : matrix.a = 0 := not_ne_iff.mp firstNonzero
    have secondNonzero : matrix.b ≠ 0 := by
      intro secondZero
      apply determinantNonzero
      simp [Mat2.det, firstZero, secondZero]
    unfold coefficientWeight
    nlinarith [normSq_pos secondNonzero, normSq_nonneg matrix.a,
      normSq_nonneg matrix.c, normSq_nonneg matrix.d]

/-- The homogeneous output weight is bounded by twice the coefficient weight
times the input weight. -/
theorem act_weight_le (matrix : Mat2 QI) (point : Proj QI) :
    (Mat2.act matrix point).weight ≤
      2 * coefficientWeight matrix * point.weight := by
  have first := normSq_add_le_two
    (matrix.a * point.p) (matrix.b * point.q)
  have second := normSq_add_le_two
    (matrix.c * point.p) (matrix.d * point.q)
  rw [normSq_mul, normSq_mul] at first second
  have combined :
      (Mat2.act matrix point).weight ≤
        2 * ((normSq matrix.a + normSq matrix.c) * normSq point.p +
          (normSq matrix.b + normSq matrix.d) * normSq point.q) := by
    simp only [Proj.weight, Mat2.act]
    linarith
  have omittedNonnegative :
      0 ≤ 2 * ((normSq matrix.a + normSq matrix.c) * normSq point.q +
        (normSq matrix.b + normSq matrix.d) * normSq point.p) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg
          (add_nonneg (normSq_nonneg matrix.a) (normSq_nonneg matrix.c))
          (normSq_nonneg point.q))
        (mul_nonneg
          (add_nonneg (normSq_nonneg matrix.b) (normSq_nonneg matrix.d))
          (normSq_nonneg point.p)))
  calc
    (Mat2.act matrix point).weight ≤
        2 * ((normSq matrix.a + normSq matrix.c) * normSq point.p +
          (normSq matrix.b + normSq matrix.d) * normSq point.q) := combined
    _ ≤ 2 * ((normSq matrix.a + normSq matrix.c) * normSq point.p +
          (normSq matrix.b + normSq matrix.d) * normSq point.q) +
        2 * ((normSq matrix.a + normSq matrix.c) * normSq point.q +
          (normSq matrix.b + normSq matrix.d) * normSq point.p) :=
      le_add_of_nonneg_right omittedNonnegative
    _ = 2 * coefficientWeight matrix * point.weight := by
      unfold coefficientWeight Proj.weight
      ring

theorem weight_scale (point : Proj QI) (scale : QI) :
    (point.scale scale).weight = normSq scale * point.weight := by
  simp only [Proj.scale, Proj.weight, normSq_mul]
  ring

/-- A matrix scales the alternating homogeneous product by its determinant. -/
theorem cross_act (matrix : Mat2 QI) (left right : Proj QI) :
    (Mat2.act matrix left).cross (Mat2.act matrix right) =
      matrix.det * left.cross right := by
  apply GaussianRat.ext <;>
    simp only [Proj.cross, Mat2.act, Mat2.det, mul_re, mul_im, add_re,
      add_im, sub_re, sub_im] <;>
    ring

theorem adjugate_act_act (matrix : Mat2 QI) (point : Proj QI) :
    Mat2.act (adjugate matrix) (Mat2.act matrix point) =
      point.scale (determinant matrix) := by
  calc
    Mat2.act (adjugate matrix) (Mat2.act matrix point) =
        Mat2.act (Mat2.mul (adjugate matrix) matrix) point :=
      (Mat2.act_mul (adjugate matrix) matrix point).symm
    _ = point.scale (determinant matrix) := by
      rw [adjugate_mul]
      ext <;>
        simp [Mat2.act, Proj.scale]

/-- Removing the last factor from an inverse projective coordinate multiplies
the remaining inverse coordinate only by that factor's determinant.  This
explicit homogeneous identity is the algebraic link between consecutive
independently sampled decoder blocks. -/
theorem act_right_adjugate_mul
    (outer inner : Mat2 QI) (point : Proj QI) :
    Mat2.act inner (Mat2.act (adjugate (Mat2.mul outer inner)) point) =
      (Mat2.act (adjugate outer) point).scale (determinant inner) := by
  ext <;>
    simp only [Mat2.act, Mat2.mul, adjugate, determinant, Proj.scale,
      mul_re, mul_im, add_re, add_im, sub_re, sub_im, neg_re, neg_im] <;>
    ring

/-- Applying an invertible matrix cannot reduce homogeneous weight below the
displayed adjugate-coefficient bound. -/
theorem determinant_mul_weight_le_act_weight
    (matrix : Mat2 QI) (point : Proj QI) :
    normSq matrix.det * point.weight ≤
      2 * coefficientWeight (adjugate matrix) *
        (Mat2.act matrix point).weight := by
  calc
    normSq matrix.det * point.weight =
        (point.scale (determinant matrix)).weight := by
      rw [weight_scale]
      rfl
    _ = (Mat2.act (adjugate matrix)
          (Mat2.act matrix point)).weight := by
      rw [adjugate_act_act]
    _ ≤ 2 * coefficientWeight (adjugate matrix) *
          (Mat2.act matrix point).weight :=
      act_weight_le (adjugate matrix) (Mat2.act matrix point)

/-- Coarse squared-chordal Lipschitz factor computed from the inverse
matrix's coefficient weight. -/
def lipschitzSq (matrix : Mat2 QI) : ℚ :=
  4 * coefficientWeight (adjugate matrix) ^ 2 / normSq matrix.det

theorem lipschitzSq_nonneg (matrix : Mat2 QI) :
    0 ≤ lipschitzSq matrix := by
  unfold lipschitzSq
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (sq_nonneg (coefficientWeight (adjugate matrix))))
    (normSq_nonneg matrix.det)

theorem det_adjugate (matrix : Mat2 QI) :
    (adjugate matrix).det = matrix.det := by
  apply GaussianRat.ext <;>
    simp only [adjugate, Mat2.det, mul_re, mul_im, sub_re, sub_im,
      neg_re, neg_im] <;>
    ring_nf

/-- Every invertible rational projective matrix is globally Lipschitz for
squared chordal distance with the explicit rational factor above. -/
theorem chordalSq_act_le
    (matrix : Mat2 QI) (determinantNonzero : matrix.det ≠ 0)
    (left right : Proj QI)
    (leftValid : left.HasNonzeroCoordinate)
    (rightValid : right.HasNonzeroCoordinate) :
    chordalSq (Mat2.act matrix left) (Mat2.act matrix right) ≤
      lipschitzSq matrix * chordalSq left right := by
  let determinantNorm := normSq matrix.det
  let inverseWeight := coefficientWeight (adjugate matrix)
  let leftWeight := left.weight
  let rightWeight := right.weight
  let outputLeftWeight := (Mat2.act matrix left).weight
  let outputRightWeight := (Mat2.act matrix right).weight
  have determinantPositive : 0 < determinantNorm := by
    exact normSq_pos determinantNonzero
  have inverseWeightPositive : 0 < inverseWeight := by
    apply coefficientWeight_pos_of_det_ne
    rw [det_adjugate]
    exact determinantNonzero
  have leftWeightPositive : 0 < leftWeight := Proj.weight_pos leftValid
  have rightWeightPositive : 0 < rightWeight := Proj.weight_pos rightValid
  have leftLower : determinantNorm * leftWeight ≤
      2 * inverseWeight * outputLeftWeight := by
    exact determinant_mul_weight_le_act_weight matrix left
  have rightLower : determinantNorm * rightWeight ≤
      2 * inverseWeight * outputRightWeight := by
    exact determinant_mul_weight_le_act_weight matrix right
  have outputLeftPositive : 0 < outputLeftWeight := by
    have positive : 0 < determinantNorm * leftWeight :=
      mul_pos determinantPositive leftWeightPositive
    have rhsPositive : 0 < 2 * inverseWeight * outputLeftWeight :=
      positive.trans_le leftLower
    rcases mul_pos_iff.mp rhsPositive with bothPositive | bothNegative
    · exact bothPositive.2
    · exact (not_lt_of_ge
        (mul_nonneg (by norm_num) inverseWeightPositive.le)
        bothNegative.1).elim
  have outputRightPositive : 0 < outputRightWeight := by
    have positive : 0 < determinantNorm * rightWeight :=
      mul_pos determinantPositive rightWeightPositive
    have rhsPositive : 0 < 2 * inverseWeight * outputRightWeight :=
      positive.trans_le rightLower
    rcases mul_pos_iff.mp rhsPositive with bothPositive | bothNegative
    · exact bothPositive.2
    · exact (not_lt_of_ge
        (mul_nonneg (by norm_num) inverseWeightPositive.le)
        bothNegative.1).elim
  have lowerProduct :
      determinantNorm ^ 2 * (leftWeight * rightWeight) ≤
        4 * inverseWeight ^ 2 *
          (outputLeftWeight * outputRightWeight) := by
    have product := mul_le_mul leftLower rightLower
      (mul_nonneg determinantPositive.le rightWeightPositive.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) inverseWeightPositive.le)
        outputLeftPositive.le)
    calc
      determinantNorm ^ 2 * (leftWeight * rightWeight) =
          (determinantNorm * leftWeight) *
            (determinantNorm * rightWeight) := by ring
      _ ≤ (2 * inverseWeight * outputLeftWeight) *
          (2 * inverseWeight * outputRightWeight) := product
      _ = 4 * inverseWeight ^ 2 *
          (outputLeftWeight * outputRightWeight) := by ring
  have denominatorRatio :
      determinantNorm /
          (outputLeftWeight * outputRightWeight) ≤
        (4 * inverseWeight ^ 2 / determinantNorm) /
          (leftWeight * rightWeight) := by
    apply (div_le_div_iff₀
      (mul_pos outputLeftPositive outputRightPositive)
      (mul_pos leftWeightPositive rightWeightPositive)).2
    have divided :
        determinantNorm * (leftWeight * rightWeight) ≤
          (4 * inverseWeight ^ 2 / determinantNorm) *
            (outputLeftWeight * outputRightWeight) := by
      calc
        determinantNorm * (leftWeight * rightWeight) ≤
            (4 * inverseWeight ^ 2 *
              (outputLeftWeight * outputRightWeight)) /
                determinantNorm := by
          apply (le_div_iff₀ determinantPositive).2
          calc
            determinantNorm * (leftWeight * rightWeight) *
                determinantNorm =
              determinantNorm ^ 2 * (leftWeight * rightWeight) := by ring
            _ ≤ 4 * inverseWeight ^ 2 *
                (outputLeftWeight * outputRightWeight) := lowerProduct
        _ = (4 * inverseWeight ^ 2 / determinantNorm) *
            (outputLeftWeight * outputRightWeight) := by ring
    exact divided
  have scaledRatio := mul_le_mul_of_nonneg_left denominatorRatio
    (normSq_nonneg (left.cross right))
  rw [chordalSq_eq_cross, chordalSq_eq_cross, cross_act, normSq_mul]
  change determinantNorm * normSq (left.cross right) /
      (outputLeftWeight * outputRightWeight) ≤
    lipschitzSq matrix *
      (normSq (left.cross right) / (leftWeight * rightWeight))
  unfold lipschitzSq
  dsimp only [determinantNorm, inverseWeight]
  calc
    normSq matrix.det * normSq (left.cross right) /
          (outputLeftWeight * outputRightWeight) =
        normSq (left.cross right) *
          (normSq matrix.det /
            (outputLeftWeight * outputRightWeight)) := by ring
    _ ≤ normSq (left.cross right) *
        ((4 * coefficientWeight (adjugate matrix) ^ 2 /
            normSq matrix.det) / (leftWeight * rightWeight)) := scaledRatio
    _ = (4 * coefficientWeight (adjugate matrix) ^ 2 /
          normSq matrix.det) *
        (normSq (left.cross right) / (leftWeight * rightWeight)) := by ring

/-- Two rational points in one box have inverse decoder coordinates whose
projective separation is bounded by box diameter times the explicit inverse
matrix factor. -/
theorem chordalSq_adjugate_affine_le_box
    (matrix : Mat2 QI) (determinantNonzero : matrix.det ≠ 0)
    {box : RatBox} {left right : QI}
    (leftInside : box.Contains left) (rightInside : box.Contains right) :
    chordalSq
        (Mat2.act (adjugate matrix) (Proj.affine left))
        (Mat2.act (adjugate matrix) (Proj.affine right)) ≤
      lipschitzSq (adjugate matrix) * box.diagonalSq := by
  have inverseLipschitz := chordalSq_act_le (adjugate matrix)
    (by rw [det_adjugate]; exact determinantNonzero)
    (Proj.affine left) (Proj.affine right)
    (Proj.affine_hasNonzeroCoordinate left)
    (Proj.affine_hasNonzeroCoordinate right)
  have affineBound := chordalSq_affine_le_normSq left right
  have boxBound := RatBox.normSq_sub_le_diagonalSq leftInside rightInside
  exact inverseLipschitz.trans
    (mul_le_mul_of_nonneg_left (affineBound.trans boxBound)
      (lipschitzSq_nonneg (adjugate matrix)))

/-- Square-root-free winding-box accuracy request which spends at most
`epsilon` on inverse-decoder projective motion.  The extra one keeps the
denominator positive even when the Lipschitz factor vanishes. -/
def inverseTailBoxRequest (matrix : Mat2 QI) (epsilon : ℚ) : ℚ :=
  min 1 (epsilon / (lipschitzSq (adjugate matrix) + 1))

theorem inverseTailBoxRequest_pos
    (matrix : Mat2 QI) {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    0 < inverseTailBoxRequest matrix epsilon := by
  apply lt_min
  · norm_num
  · exact div_pos epsilonPositive (by
      linarith [lipschitzSq_nonneg (adjugate matrix)])

theorem lipschitzSq_mul_inverseTailBoxRequest_sq_le
    (matrix : Mat2 QI) {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    lipschitzSq (adjugate matrix) *
        inverseTailBoxRequest matrix epsilon ^ 2 ≤ epsilon := by
  let factor := lipschitzSq (adjugate matrix)
  let request := inverseTailBoxRequest matrix epsilon
  have factorNonnegative : 0 ≤ factor := lipschitzSq_nonneg _
  have denominatorPositive : 0 < factor + 1 := by linarith
  have requestPositive : 0 < request :=
    inverseTailBoxRequest_pos matrix epsilonPositive
  have requestLeOne : request ≤ 1 := min_le_left _ _
  have requestLeRatio : request ≤ epsilon / (factor + 1) :=
    min_le_right _ _
  have requestSqLe : request ^ 2 ≤ request := by
    nlinarith [mul_nonneg requestPositive.le
      (sub_nonneg.mpr requestLeOne)]
  calc
    factor * request ^ 2 ≤ (factor + 1) * request ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg request)
    _ ≤ (factor + 1) * request :=
      mul_le_mul_of_nonneg_left requestSqLe denominatorPositive.le
    _ ≤ (factor + 1) * (epsilon / (factor + 1)) :=
      mul_le_mul_of_nonneg_left requestLeRatio denominatorPositive.le
    _ = epsilon := by field_simp [ne_of_gt denominatorPositive]

/-- Meeting the computed box request makes every pair of inverse decoder
coordinates in that box `epsilon`-close in squared chordal distance. -/
theorem chordalSq_adjugate_affine_le_of_request
    (matrix : Mat2 QI) (determinantNonzero : matrix.det ≠ 0)
    {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    {box : RatBox} (accurate : box.diagonalSq ≤
      inverseTailBoxRequest matrix epsilon ^ 2)
    {left right : QI}
    (leftInside : box.Contains left) (rightInside : box.Contains right) :
    chordalSq
        (Mat2.act (adjugate matrix) (Proj.affine left))
        (Mat2.act (adjugate matrix) (Proj.affine right)) ≤ epsilon := by
  exact (chordalSq_adjugate_affine_le_box matrix determinantNonzero
    leftInside rightInside).trans
      ((mul_le_mul_of_nonneg_left accurate
        (lipschitzSq_nonneg (adjugate matrix))).trans
        (lipschitzSq_mul_inverseTailBoxRequest_sq_le matrix epsilonPositive))

end CCLProjectiveMatrixBounds
end FTA
