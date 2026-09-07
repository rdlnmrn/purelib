import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.GaussianProjective
import RFAP.Geometry.Boxes

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `CCL.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace CCL.Chordal

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian

namespace Proj

/-- Multiply both homogeneous coordinates by a constructive Gaussian scalar. -/
def scale (scalar : Gaussian) (x : Proj) : Proj :=
  ⟨scalar * x.p, scalar * x.q⟩

/-- Squared Euclidean weight of a homogeneous coordinate pair. -/
def weight (x : Proj) : Coordinate := normSq x.p + normSq x.q

/-- Finite validity predicate for a homogeneous coordinate pair. -/
def HasNonzeroCoordinate (x : Proj) : Prop :=
  x.p ≠ 0 ∨ x.q ≠ 0

instance hasNonzeroCoordinateDecidable (x : Proj) :
    Decidable x.HasNonzeroCoordinate := by
  unfold HasNonzeroCoordinate
  infer_instance

/-- The Hermitian scalar product used in the rational quadrance estimates. -/
def hermitian (x y : Proj) : Gaussian :=
  conj x.p * y.p + conj x.q * y.q

/-- The alternating product in the numerator of `chordalSq`. -/
def cross (x y : Proj) : Gaussian :=
  x.p * y.q - y.p * x.q

theorem weight_nonneg (x : Proj) : 0 ≤ x.weight :=
  add_nonneg (normSq_nonneg x.p) (normSq_nonneg x.q)

theorem weight_pos {x : Proj} (valid : x.HasNonzeroCoordinate) :
    0 < x.weight := by
  rcases valid with hp | hq
  · exact add_pos_of_pos_of_nonneg (normSq_pos hp) (normSq_nonneg x.q)
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg x.p) (normSq_pos hq)

theorem affine_hasNonzeroCoordinate (z : Gaussian) :
    HasNonzeroCoordinate (CCL.Proj.affine z : Proj) :=
  Or.inr one_ne_zero

theorem omega_hasNonzeroCoordinate :
    HasNonzeroCoordinate (CCL.Proj.omega : Proj) :=
  Or.inl one_ne_zero

/-- The two-dimensional complex Lagrange identity. -/
theorem normSq_hermitian_add_normSq_cross (x y : Proj) :
    normSq (x.hermitian y) + normSq (x.cross y) =
      x.weight * y.weight := by
  simp only [hermitian, cross, weight, normSq, conj,
    add_re, add_im, sub_re, sub_im, mul_re, mul_im]
  ring1

theorem normSq_hermitian_le_weight_mul (x y : Proj) :
    normSq (x.hermitian y) ≤ x.weight * y.weight := by
  rw [← normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_right (normSq_nonneg (x.cross y))

/-- Determinant expansion through a third homogeneous coordinate pair. -/
theorem cross_mul_weight (x y z : Proj) :
    x.cross z * ⟨y.weight, 0⟩ =
      x.cross y * y.hermitian z + y.cross z * y.hermitian x := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [cross, weight, hermitian, normSq, conj,
      add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;>
    ring1

end Proj

/-- The paper's exact squared chordal expression `χ²`. -/
def chordalSq (x y : Proj) : Coordinate :=
  normSq (x.p * y.q - y.p * x.q) /
    ((normSq x.p + normSq x.q) * (normSq y.p + normSq y.q))

theorem chordalSq_eq_cross (x y : Proj) :
    chordalSq x y = normSq (x.cross y) / (x.weight * y.weight) :=
  rfl

theorem chordalSq_nonneg (x y : Proj) : 0 ≤ chordalSq x y := by
  rw [chordalSq_eq_cross]
  exact RFAP.ConstructiveFraction.div_nonneg_direct (normSq_nonneg _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct x.weight_nonneg
      y.weight_nonneg)

/-- Squared chordal error is at most one for valid homogeneous pairs. -/
theorem chordalSq_le_one {x y : Proj}
    (hx : x.HasNonzeroCoordinate) (hy : y.HasNonzeroCoordinate) :
    chordalSq x y ≤ 1 := by
  rw [chordalSq_eq_cross]
  have denominatorPositive : 0 < x.weight * y.weight :=
    RFAP.ConstructiveFraction.mul_pos_direct (Proj.weight_pos hx)
      (Proj.weight_pos hy)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  rw [RFAP.ConstructiveFraction.one_mul]
  rw [← Proj.normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_left (normSq_nonneg (x.hermitian y))

theorem chordalSq_eq_zero_of_equivalent {x y : Proj}
    (equivalent : x.Equivalent y) : chordalSq x y = 0 := by
  have crossZero : x.cross y = 0 := by
    dsimp [Proj.cross, CCL.Proj.Equivalent] at equivalent ⊢
    rw [equivalent]
    exact RFAP.ConstructiveGaussian.Gaussian.sub_self _
  rw [chordalSq_eq_cross, crossZero, normSq_zero]
  exact RFAP.ConstructiveFraction.zero_div_direct _

/-- Square-root-free triangle estimate for squared chordal quadrance.  The
factor two keeps the statement entirely inside constructive fractions. -/
theorem chordalSq_triangle_two {x y z : Proj}
    (hx : x.HasNonzeroCoordinate) (hy : y.HasNonzeroCoordinate)
    (hz : z.HasNonzeroCoordinate) :
    chordalSq x z ≤ 2 * (chordalSq x y + chordalSq y z) := by
  have hxWeight : 0 < x.weight := Proj.weight_pos hx
  have hyWeight : 0 < y.weight := Proj.weight_pos hy
  have hzWeight : 0 < z.weight := Proj.weight_pos hz
  have expansion := congrArg normSq (Proj.cross_mul_weight x y z)
  have sumBound := normSq_add_le_two
    (x.cross y * y.hermitian z) (y.cross z * y.hermitian x)
  have crossBound :
      normSq (x.cross z) * y.weight ^ 2 ≤
        2 * (normSq (x.cross y) * (y.weight * z.weight) +
          normSq (y.cross z) * (x.weight * y.weight)) := by
    calc
      normSq (x.cross z) * y.weight ^ 2 =
          normSq (x.cross z * ⟨y.weight, 0⟩) := by
            simp only [normSq, mul_re, mul_im]
            ring1
      _ = normSq
          (x.cross y * y.hermitian z + y.cross z * y.hermitian x) := expansion
      _ ≤ 2 *
          (normSq (x.cross y * y.hermitian z) +
            normSq (y.cross z * y.hermitian x)) := sumBound
      _ = 2 *
          (normSq (x.cross y) * normSq (y.hermitian z) +
            normSq (y.cross z) * normSq (y.hermitian x)) := by
              rw [normSq_mul, normSq_mul]
      _ ≤ 2 * (normSq (x.cross y) * (y.weight * z.weight) +
          normSq (y.cross z) * (x.weight * y.weight)) := by
            apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (c := 2) _ (by decide)
            apply add_le_add
            · exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (Proj.normSq_hermitian_le_weight_mul y z)
                (normSq_nonneg (x.cross y))
            · have bound := Proj.normSq_hermitian_le_weight_mul y x
              rw [RFAP.ConstructiveFraction.mul_comm y.weight x.weight] at bound
              exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                bound (normSq_nonneg (y.cross z))
  have cancelled :
      normSq (x.cross z) * y.weight ≤
        2 * (normSq (x.cross y) * z.weight +
          normSq (y.cross z) * x.weight) := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := y.weight) _ hyWeight
    calc
      (normSq (x.cross z) * y.weight) * y.weight =
          normSq (x.cross z) * y.weight ^ 2 := by ring1
      _ ≤ 2 * (normSq (x.cross y) * (y.weight * z.weight) +
          normSq (y.cross z) * (x.weight * y.weight)) := crossBound
      _ = (2 * (normSq (x.cross y) * z.weight +
          normSq (y.cross z) * x.weight)) * y.weight := by ring1
  rw [chordalSq_eq_cross, chordalSq_eq_cross, chordalSq_eq_cross]
  have xzPositive : 0 < x.weight * z.weight :=
    RFAP.ConstructiveFraction.mul_pos_direct hxWeight hzWeight
  apply (RFAP.ConstructiveFraction.div_le_iff_pos xzPositive).2
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := y.weight) _ hyWeight
  calc
    (normSq (x.cross z) * y.weight) =
        normSq (x.cross z) * y.weight := rfl
    _ ≤ 2 * (normSq (x.cross y) * z.weight +
        normSq (y.cross z) * x.weight) := cancelled
    _ = (2 *
        (normSq (x.cross y) / (x.weight * y.weight) +
          normSq (y.cross z) / (y.weight * z.weight)) *
        (x.weight * z.weight)) * y.weight := by
      have xyNonzero : x.weight * y.weight ≠ 0 :=
        (RFAP.ConstructiveFraction.mul_pos_direct hxWeight hyWeight).ne'
      have yzNonzero : y.weight * z.weight ≠ 0 :=
        (RFAP.ConstructiveFraction.mul_pos_direct hyWeight hzWeight).ne'
      have leftCancel :
          (normSq (x.cross y) / (x.weight * y.weight) *
              (x.weight * z.weight)) * y.weight =
            normSq (x.cross y) * z.weight := by
        calc
          (normSq (x.cross y) / (x.weight * y.weight) *
              (x.weight * z.weight)) * y.weight =
              (normSq (x.cross y) / (x.weight * y.weight) *
                (x.weight * y.weight)) * z.weight := by ring1
          _ = normSq (x.cross y) * z.weight :=
            congrArg (fun value => value * z.weight)
              (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ xyNonzero)
      have rightCancel :
          (normSq (y.cross z) / (y.weight * z.weight) *
              (x.weight * z.weight)) * y.weight =
            normSq (y.cross z) * x.weight := by
        calc
          (normSq (y.cross z) / (y.weight * z.weight) *
              (x.weight * z.weight)) * y.weight =
              (normSq (y.cross z) / (y.weight * z.weight) *
                (y.weight * z.weight)) * x.weight := by ring1
          _ = normSq (y.cross z) * x.weight :=
            congrArg (fun value => value * x.weight)
              (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ yzNonzero)
      rw [← leftCancel, ← rightCancel]
      ring1

namespace Mat2

/-- Determinant of a two-by-two constructive Gaussian matrix. -/
def det (M : Mat2) : Gaussian := M.a * M.d - M.b * M.c

/-- Proposition 7.8, the homographic truncation identity. -/
theorem chordalSq_truncation (M : Mat2) (t : Gaussian) :
    chordalSq (CCL.Mat2.act M (CCL.Proj.affine t))
        (CCL.Mat2.act M CCL.Proj.omega) =
      normSq M.det /
        ((normSq M.a + normSq M.c) *
          (normSq (M.a * t + M.b) + normSq (M.c * t + M.d))) := by
  have numerator :
      (M.a * t + M.b) * M.c - M.a * (M.c * t + M.d) = -M.det := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
        neg_re, neg_im, det] <;>
      ring1
  simp only [chordalSq, CCL.Mat2.act, CCL.Proj.affine, CCL.Proj.omega,
    mul_one, mul_zero, add_zero, numerator, normSq_neg]
  congr 1
  ring1

/-- Exact determinant scaling between two affine inputs under one matrix. -/
theorem chordalSq_act_affine (M : Mat2) (left right : Gaussian) :
    chordalSq (CCL.Mat2.act M (CCL.Proj.affine left))
        (CCL.Mat2.act M (CCL.Proj.affine right)) =
      normSq M.det * normSq (left - right) /
        (Proj.weight (CCL.Mat2.act M (CCL.Proj.affine left)) *
          Proj.weight (CCL.Mat2.act M (CCL.Proj.affine right))) := by
  have crossIdentity :
      (M.a * left + M.b) * (M.c * right + M.d) -
          (M.a * right + M.b) * (M.c * left + M.d) =
        M.det * (left - right) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [det, add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;>
      ring1
  rw [chordalSq_eq_cross]
  simp only [Proj.cross, CCL.Mat2.act, CCL.Proj.affine,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    Proj.weight, crossIdentity, normSq_mul]

/-- Exact determinant scaling of the homogeneous cross numerator. -/
theorem cross_act (M : Mat2) (left right : Proj) :
    Proj.cross (CCL.Mat2.act M left) (CCL.Mat2.act M right) =
      M.det * Proj.cross left right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [Proj.cross, CCL.Mat2.act, det, add_re, add_im, sub_re,
      sub_im, mul_re, mul_im] <;>
    ring1

/-- Exact projective two-point transport under an arbitrary displayed
matrix. -/
theorem chordalSq_act (M : Mat2) (left right : Proj) :
    chordalSq (CCL.Mat2.act M left) (CCL.Mat2.act M right) =
      normSq M.det * normSq (Proj.cross left right) /
        (Proj.weight (CCL.Mat2.act M left) *
          Proj.weight (CCL.Mat2.act M right)) := by
  rw [chordalSq_eq_cross, cross_act, normSq_mul]

end Mat2

/-- Affine specialization of squared chordal quadrance. -/
theorem chordalSq_affine (z w : Gaussian) :
    chordalSq (CCL.Proj.affine z) (CCL.Proj.affine w) =
      normSq (z - w) / ((1 + normSq z) * (1 + normSq w)) := by
  have numerator : z * 1 - w * 1 = z - w := by
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_one,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  simp only [chordalSq, CCL.Proj.affine, numerator, normSq_one]
  congr 1
  all_goals ring1

/-- Affine squared-chordal quadrance is bounded by the ordinary displayed
Gaussian squared distance. -/
theorem chordalSq_affine_le_normSq (z w : Gaussian) :
    chordalSq (CCL.Proj.affine z) (CCL.Proj.affine w) ≤ normSq (z - w) := by
  have leftOne : (1 : Coordinate) ≤ 1 + normSq z :=
    le_add_of_nonneg_right (normSq_nonneg z)
  have rightOne : (1 : Coordinate) ≤ 1 + normSq w :=
    le_add_of_nonneg_right (normSq_nonneg w)
  have denominatorOne : (1 : Coordinate) ≤
      (1 + normSq z) * (1 + normSq w) := by
    calc
      1 = 1 * 1 := by ring1
      _ ≤ (1 + normSq z) * (1 + normSq w) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct leftOne rightOne
          (by decide)
          (add_nonneg (by decide) (normSq_nonneg z))
  rw [chordalSq_affine]
  have quotientBound :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (normSq_nonneg (z - w)) (show (0 : Coordinate) < 1 by decide)
      denominatorOne
  have divideOne : normSq (z - w) / 1 = normSq (z - w) := by
    calc
      normSq (z - w) / 1 =
          (normSq (z - w) / 1) * 1 :=
        (RFAP.ConstructiveFraction.mul_one_direct _).symm
      _ = normSq (z - w) :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (normSq (z - w)) 1 (show (1 : Coordinate) ≠ 0 by decide)
  exact quotientBound.trans_eq divideOne

/-- Every two affine points in one rational box are projectively at most the
box's squared diagonal apart.  Thus winding-box refinement and projective
cylinder refinement can be compared in the same `chi^2` metric. -/
theorem chordalSq_affine_le_box_diagonal
    {box : RFAP.Boxes.Box} {z w : Gaussian}
    (zInside : box.Contains z) (wInside : box.Contains w) :
    chordalSq (CCL.Proj.affine z) (CCL.Proj.affine w) ≤ box.diagonalSq :=
  (chordalSq_affine_le_normSq z w).trans
    (box.normSq_sub_le_diagonalSq zInside wInside)

/-- Squared chordal quadrance from an affine point to `ω`. -/
theorem chordalSq_omega (z : Gaussian) :
    chordalSq (CCL.Proj.affine z) CCL.Proj.omega =
      1 / (1 + normSq z) := by
  simp only [chordalSq, CCL.Proj.affine, CCL.Proj.omega, mul_zero,
    mul_one, zero_sub, normSq_neg, normSq_one, normSq_zero]
  congr 1
  all_goals ring1

theorem chordalSq_comm (x y : Proj) : chordalSq x y = chordalSq y x := by
  have numerator : y.p * x.q - x.p * y.q =
      -(x.p * y.q - y.p * x.q) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;>
      ring1
  simp only [chordalSq, numerator, normSq_neg]
  congr 1
  all_goals ring1

theorem Proj.weight_scale (scalar : Gaussian) (x : Proj) :
    (x.scale scalar).weight = normSq scalar * x.weight := by
  simp only [Proj.scale, Proj.weight, normSq_mul]
  ring1

/-- `χ²` is unchanged by a nonzero rescaling of the left homogeneous
coordinate pair. -/
theorem chordalSq_scale_left (scalar : Gaussian) (scalarNonzero : scalar ≠ 0)
    (x y : Proj) : chordalSq (x.scale scalar) y = chordalSq x y := by
  have normNonzero : normSq scalar ≠ 0 :=
    fun normZero => scalarNonzero (normSq_eq_zero.mp normZero)
  have crossIdentity :
      (x.scale scalar).cross y = scalar * x.cross y := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [Proj.cross, Proj.scale, sub_re, sub_im, mul_re, mul_im] <;>
      ring1
  rw [chordalSq_eq_cross, chordalSq_eq_cross, crossIdentity, normSq_mul,
    Proj.weight_scale]
  rw [show (normSq scalar * x.weight) * y.weight =
    normSq scalar * (x.weight * y.weight) by ring1]
  exact RFAP.ConstructiveFraction.mul_div_mul_left_direct
    (normSq scalar) (normSq (x.cross y)) (x.weight * y.weight) normNonzero

/-- `χ²` is unchanged by a nonzero rescaling of the right homogeneous
coordinate pair. -/
theorem chordalSq_scale_right (scalar : Gaussian) (scalarNonzero : scalar ≠ 0)
    (x y : Proj) : chordalSq x (y.scale scalar) = chordalSq x y := by
  rw [chordalSq_comm, chordalSq_scale_left scalar scalarNonzero,
    chordalSq_comm]

/-- Two valid equivalent homogeneous pairs differ by one explicit nonzero
scalar.  The proof splits on a displayed coordinate; it performs no choice. -/
theorem Proj.exists_nonzero_scale_of_equivalent {x y : Proj}
    (xValid : x.HasNonzeroCoordinate) (yValid : y.HasNonzeroCoordinate)
    (equivalent : x.Equivalent y) :
    ∃ scalar : Gaussian, scalar ≠ 0 ∧ x = y.scale scalar := by
  by_cases yDenominatorZero : y.q = 0
  · have yNumeratorNonzero : y.p ≠ 0 := by
      rcases yValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero
      · exact (denominatorNonzero yDenominatorZero).elim
    have xDenominatorZero : x.q = 0 := by
      have crossIdentity := equivalent
      dsimp only [CCL.Proj.Equivalent] at crossIdentity
      have productZero : y.p * x.q = 0 := by
        rw [yDenominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.mul_zero] at crossIdentity
        exact crossIdentity.symm
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        yNumeratorNonzero
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm x.q y.p,
        productZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul]
    have xNumeratorNonzero : x.p ≠ 0 := by
      rcases xValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero
      · exact (denominatorNonzero xDenominatorZero).elim
    let scalar := x.p * y.p⁻¹
    have scalarNonzero : scalar ≠ 0 :=
      RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        xNumeratorNonzero
        (RFAP.ConstructiveGaussian.Gaussian.inv_ne_zero_direct
          yNumeratorNonzero)
    have numeratorIdentity : scalar * y.p = x.p := by
      dsimp only [scalar]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ yNumeratorNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    exact ⟨scalar, scalarNonzero, by
      apply CCL.Proj.ext
      · exact numeratorIdentity.symm
      · rw [Proj.scale, yDenominatorZero, xDenominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.mul_zero]⟩
  · have yDenominatorNonzero : y.q ≠ 0 := yDenominatorZero
    have xDenominatorNonzero : x.q ≠ 0 := by
      intro xDenominatorZero
      have crossIdentity := equivalent
      dsimp only [CCL.Proj.Equivalent] at crossIdentity
      have productZero : x.p * y.q = 0 := by
        rw [xDenominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.mul_zero] at crossIdentity
        exact crossIdentity
      have xNumeratorZero : x.p = 0 := by
        apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
          yDenominatorNonzero
        rw [productZero,
          RFAP.ConstructiveGaussian.Gaussian.zero_mul]
      rcases xValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero xNumeratorZero
      · exact denominatorNonzero xDenominatorZero
    let scalar := x.q * y.q⁻¹
    have scalarNonzero : scalar ≠ 0 :=
      RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        xDenominatorNonzero
        (RFAP.ConstructiveGaussian.Gaussian.inv_ne_zero_direct
          yDenominatorNonzero)
    have denominatorIdentity : scalar * y.q = x.q := by
      dsimp only [scalar]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _ yDenominatorNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    have numeratorIdentity : scalar * y.p = x.p := by
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        yDenominatorNonzero
      calc
        (scalar * y.p) * y.q = scalar * (y.p * y.q) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
        _ = scalar * (y.q * y.p) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm y.p y.q]
        _ = (scalar * y.q) * y.p :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = y.p * (scalar * y.q) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
        _ = y.p * x.q := by rw [denominatorIdentity]
        _ = x.p * y.q := equivalent.symm
    exact ⟨scalar, scalarNonzero, by
      apply CCL.Proj.ext
      · exact numeratorIdentity.symm
      · exact denominatorIdentity.symm⟩

theorem chordalSq_eq_of_equivalent_left {x y : Proj}
    (xValid : x.HasNonzeroCoordinate) (yValid : y.HasNonzeroCoordinate)
    (equivalent : x.Equivalent y) (z : Proj) :
    chordalSq x z = chordalSq y z := by
  rcases Proj.exists_nonzero_scale_of_equivalent xValid yValid equivalent with
    ⟨scalar, scalarNonzero, rfl⟩
  exact chordalSq_scale_left scalar scalarNonzero y z

theorem chordalSq_eq_of_equivalent_right {x y : Proj}
    (xValid : x.HasNonzeroCoordinate) (yValid : y.HasNonzeroCoordinate)
    (equivalent : x.Equivalent y) (z : Proj) :
    chordalSq z x = chordalSq z y := by
  rw [chordalSq_comm z x, chordalSq_comm z y]
  exact chordalSq_eq_of_equivalent_left xValid yValid equivalent z

/-- Transitivity of projective equivalence through a valid middle/right pair,
proved by exposing their finite nonzero scale. -/
theorem Proj.equivalent_trans {x y z : Proj}
    (xy : x.Equivalent y) (yz : y.Equivalent z)
    (yValid : y.HasNonzeroCoordinate) (zValid : z.HasNonzeroCoordinate) :
    x.Equivalent z := by
  rcases Proj.exists_nonzero_scale_of_equivalent yValid zValid yz with
    ⟨scalar, scalarNonzero, yIdentity⟩
  rw [yIdentity] at xy
  dsimp only [CCL.Proj.Equivalent, Proj.scale] at xy ⊢
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne scalarNonzero
  calc
    (x.p * z.q) * scalar = x.p * (scalar * z.q) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm scalar z.q,
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = (scalar * z.p) * x.q := xy
    _ = (z.p * scalar) * x.q := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm scalar z.p]
    _ = z.p * (scalar * x.q) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = z.p * (x.q * scalar) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm scalar x.q]
    _ = (z.p * x.q) * scalar :=
      (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm

/-- A strictly positive coarse coefficient controlling the homogeneous
weight under one displayed matrix action. -/
def Mat2.actionWeightCoefficient (matrix : Mat2) : Coordinate :=
  2 * (normSq matrix.a + normSq matrix.b + normSq matrix.c +
    normSq matrix.d + 1)

theorem Mat2.actionWeightCoefficient_pos (matrix : Mat2) :
    0 < matrix.actionWeightCoefficient := by
  apply RFAP.ConstructiveFraction.mul_pos_direct (by decide)
  exact add_pos_of_nonneg_of_pos
    (add_nonneg
      (add_nonneg
        (add_nonneg (normSq_nonneg matrix.a) (normSq_nonneg matrix.b))
        (normSq_nonneg matrix.c))
      (normSq_nonneg matrix.d))
    (by decide)

/-- Coefficient-only upper bound for homogeneous projective weight under a
matrix action. -/
theorem Mat2.act_weight_le (matrix : Mat2) (point : Proj) :
    Proj.weight (CCL.Mat2.act matrix point) ≤
      matrix.actionWeightCoefficient * point.weight := by
  let coefficientSum := normSq matrix.a + normSq matrix.b +
    normSq matrix.c + normSq matrix.d
  let productSum :=
    normSq matrix.a * normSq point.p +
      normSq matrix.b * normSq point.q +
      normSq matrix.c * normSq point.p +
      normSq matrix.d * normSq point.q
  have numeratorBound :
      normSq (matrix.a * point.p + matrix.b * point.q) ≤
        2 * (normSq matrix.a * normSq point.p +
          normSq matrix.b * normSq point.q) := by
    simpa only [normSq_mul] using
      normSq_add_le_two (matrix.a * point.p) (matrix.b * point.q)
  have denominatorBound :
      normSq (matrix.c * point.p + matrix.d * point.q) ≤
        2 * (normSq matrix.c * normSq point.p +
          normSq matrix.d * normSq point.q) := by
    simpa only [normSq_mul] using
      normSq_add_le_two (matrix.c * point.p) (matrix.d * point.q)
  have productBound : productSum ≤ coefficientSum * point.weight := by
    apply sub_nonneg.mp
    have missingNonnegative : 0 ≤
        normSq matrix.a * normSq point.q +
          normSq matrix.b * normSq point.p +
          normSq matrix.c * normSq point.q +
          normSq matrix.d * normSq point.p :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (normSq_nonneg matrix.a) (normSq_nonneg point.q))
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (normSq_nonneg matrix.b) (normSq_nonneg point.p)))
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (normSq_nonneg matrix.c) (normSq_nonneg point.q)))
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg matrix.d) (normSq_nonneg point.p))
    calc
      0 ≤ normSq matrix.a * normSq point.q +
          normSq matrix.b * normSq point.p +
          normSq matrix.c * normSq point.q +
          normSq matrix.d * normSq point.p := missingNonnegative
      _ = coefficientSum * point.weight - productSum := by
        simp only [coefficientSum, productSum, Proj.weight]
        ring1
  have coefficientSumNonnegative : 0 ≤ coefficientSum :=
    add_nonneg
      (add_nonneg
        (add_nonneg (normSq_nonneg matrix.a) (normSq_nonneg matrix.b))
        (normSq_nonneg matrix.c))
      (normSq_nonneg matrix.d)
  have weightNonnegative := point.weight_nonneg
  calc
    Proj.weight (CCL.Mat2.act matrix point) =
        normSq (matrix.a * point.p + matrix.b * point.q) +
          normSq (matrix.c * point.p + matrix.d * point.q) := rfl
    _ ≤ 2 * (normSq matrix.a * normSq point.p +
          normSq matrix.b * normSq point.q) +
        2 * (normSq matrix.c * normSq point.p +
          normSq matrix.d * normSq point.q) :=
      add_le_add numeratorBound denominatorBound
    _ = 2 * productSum := by
      simp only [productSum]
      ring1
    _ ≤ 2 * (coefficientSum * point.weight) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ ≤ 2 * ((coefficientSum + 1) * point.weight) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        · exact le_add_of_nonneg_right (show (0 : Coordinate) ≤ 1 by decide)
        · exact weightNonnegative
      · decide
    _ = matrix.actionWeightCoefficient * point.weight := by
      simp only [Mat2.actionWeightCoefficient, coefficientSum]
      ring1

/-- A nonzero-determinant matrix preserves finite projective validity. -/
theorem Mat2.act_hasNonzeroCoordinate {matrix : Mat2} {point : Proj}
    (determinantNonzero : matrix.det ≠ 0)
    (pointValid : point.HasNonzeroCoordinate) :
    Proj.HasNonzeroCoordinate (CCL.Mat2.act matrix point) := by
  by_cases numeratorZero : (CCL.Mat2.act matrix point).p = 0
  · apply Or.inr
    intro denominatorZero
    rcases pointValid with pointNumeratorNonzero | pointDenominatorNonzero
    · have determinantProduct : matrix.det * point.p = 0 := by
        calc
          matrix.det * point.p =
              matrix.d * (CCL.Mat2.act matrix point).p -
                matrix.b * (CCL.Mat2.act matrix point).q := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [Mat2.det, CCL.Mat2.act, add_re, add_im,
                sub_re, sub_im, mul_re, mul_im] <;>
              ring1
          _ = 0 := by
            rw [numeratorZero, denominatorZero]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, mul_re, mul_im, zero_re, zero_im] <;>
              ring1
      exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        determinantNonzero pointNumeratorNonzero determinantProduct
    · have determinantProduct : matrix.det * point.q = 0 := by
        calc
          matrix.det * point.q =
              matrix.a * (CCL.Mat2.act matrix point).q -
                matrix.c * (CCL.Mat2.act matrix point).p := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [Mat2.det, CCL.Mat2.act, add_re, add_im,
                sub_re, sub_im, mul_re, mul_im] <;>
              ring1
          _ = 0 := by
            rw [denominatorZero, numeratorZero]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, mul_re, mul_im, zero_re, zero_im] <;>
              ring1
      exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        determinantNonzero pointDenominatorNonzero determinantProduct
  · exact Or.inl numeratorZero

end CCL.Chordal
