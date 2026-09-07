import CCL.Gaussian
import CCL.Geometry.Projective
import Mathlib.Algebra.Order.Field.Basic

/-!
# Exact finite projective error

The squared chordal expression and Proposition 7.8, entirely over homogeneous
Gaussian-rational coordinates.  The algebraic identity is actually valid
without nonzero-coordinate hypotheses; those hypotheses are only needed when
interpreting a pair as a projective point.
-/

namespace CCL

open GaussianRat

namespace Proj

/-- Multiply both homogeneous coordinates by a Gaussian-rational scalar. -/
def scale (l : GaussianRat) (x : Proj GaussianRat) : Proj GaussianRat :=
  ⟨l * x.p, l * x.q⟩

/-- Squared Euclidean weight of a homogeneous coordinate pair. -/
def weight (x : Proj GaussianRat) : ℚ := normSq x.p + normSq x.q

/-- Constructive validity predicate for a homogeneous coordinate pair. -/
def HasNonzeroCoordinate (x : Proj GaussianRat) : Prop :=
  x.p ≠ 0 ∨ x.q ≠ 0

/-- The Hermitian scalar product used in the rational chordal estimates. -/
def hermitian (x y : Proj GaussianRat) : GaussianRat :=
  GaussianRat.conj x.p * y.p + GaussianRat.conj x.q * y.q

/-- The alternating product occurring in the numerator of `chordalSq`. -/
def cross (x y : Proj GaussianRat) : GaussianRat :=
  x.p * y.q - y.p * x.q

theorem weight_nonneg (x : Proj GaussianRat) : 0 ≤ x.weight := by
  exact add_nonneg (normSq_nonneg x.p) (normSq_nonneg x.q)

theorem weight_pos {x : Proj GaussianRat} (hx : x.HasNonzeroCoordinate) :
    0 < x.weight := by
  rcases hx with hp | hq
  · exact add_pos_of_pos_of_nonneg (normSq_pos hp) (normSq_nonneg x.q)
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg x.p) (normSq_pos hq)

theorem affine_hasNonzeroCoordinate (z : GaussianRat) :
    (affine z).HasNonzeroCoordinate := by
  exact Or.inr one_ne_zero

theorem omega_hasNonzeroCoordinate :
    (omega : Proj GaussianRat).HasNonzeroCoordinate := by
  exact Or.inl one_ne_zero

/-- The two-dimensional complex Lagrange identity, over rational coordinates. -/
theorem normSq_hermitian_add_normSq_cross (x y : Proj GaussianRat) :
    normSq (x.hermitian y) + normSq (x.cross y) = x.weight * y.weight := by
  simp only [hermitian, cross, weight, GaussianRat.normSq, GaussianRat.conj,
    GaussianRat.add_re, GaussianRat.add_im, GaussianRat.sub_re,
    GaussianRat.sub_im, GaussianRat.mul_re, GaussianRat.mul_im]
  ring

theorem normSq_hermitian_le_weight_mul (x y : Proj GaussianRat) :
    normSq (x.hermitian y) ≤ x.weight * y.weight := by
  rw [← normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_right (normSq_nonneg (x.cross y))

/-- Determinant expansion through a third homogeneous coordinate pair. -/
theorem cross_mul_weight (x y z : Proj GaussianRat) :
    x.cross z * ⟨y.weight, 0⟩ =
      x.cross y * y.hermitian z + y.cross z * y.hermitian x := by
  ext <;>
    simp only [cross, weight, hermitian, GaussianRat.normSq, GaussianRat.conj,
      GaussianRat.add_re, GaussianRat.add_im, GaussianRat.sub_re,
      GaussianRat.sub_im, GaussianRat.mul_re, GaussianRat.mul_im] <;>
    ring

end Proj

/-- The paper's exact squared chordal expression `χ²`. -/
def chordalSq (x y : Proj GaussianRat) : ℚ :=
  normSq (x.p * y.q - y.p * x.q) /
    ((normSq x.p + normSq x.q) * (normSq y.p + normSq y.q))

theorem chordalSq_eq_cross (x y : Proj GaussianRat) :
    chordalSq x y = normSq (x.cross y) / (x.weight * y.weight) := rfl

theorem chordalSq_nonneg (x y : Proj GaussianRat) : 0 ≤ chordalSq x y := by
  rw [chordalSq_eq_cross]
  exact div_nonneg (normSq_nonneg _) (mul_nonneg x.weight_nonneg y.weight_nonneg)

/-- Squared chordal error is at most one for valid homogeneous pairs. -/
theorem chordalSq_le_one {x y : Proj GaussianRat}
    (hx : x.HasNonzeroCoordinate) (hy : y.HasNonzeroCoordinate) :
    chordalSq x y ≤ 1 := by
  rw [chordalSq_eq_cross]
  apply (div_le_one (mul_pos (Proj.weight_pos hx) (Proj.weight_pos hy))).2
  rw [← Proj.normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_left (normSq_nonneg (x.hermitian y))

theorem chordalSq_eq_zero_of_equivalent {x y : Proj GaussianRat}
    (equivalent : x.Equivalent y) : chordalSq x y = 0 := by
  have crossZero : x.cross y = 0 := by
    dsimp [Proj.cross, Proj.Equivalent] at equivalent ⊢
    rw [equivalent]
    exact sub_self _
  simp [chordalSq_eq_cross, crossZero]

/-- Square-root-free triangle estimate for the squared chordal expression.
The factor two is the price of keeping the entire statement rational. -/
theorem chordalSq_triangle_two {x y z : Proj GaussianRat}
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
            simp only [normSq, GaussianRat.mul_re, GaussianRat.mul_im]
            ring
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
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (Proj.normSq_hermitian_le_weight_mul y z)
                (normSq_nonneg (x.cross y))
            · have bound := Proj.normSq_hermitian_le_weight_mul y x
              rw [_root_.mul_comm y.weight x.weight] at bound
              exact mul_le_mul_of_nonneg_left bound
                (normSq_nonneg (y.cross z))
  have cancelled :
      normSq (x.cross z) * y.weight ≤
        2 * (normSq (x.cross y) * z.weight +
          normSq (y.cross z) * x.weight) := by
    have scaled :
        y.weight * (normSq (x.cross z) * y.weight) ≤
          y.weight * (2 * (normSq (x.cross y) * z.weight +
            normSq (y.cross z) * x.weight)) := by
      calc
        y.weight * (normSq (x.cross z) * y.weight) =
            normSq (x.cross z) * y.weight ^ 2 := by ring
        _ ≤ 2 * (normSq (x.cross y) * (y.weight * z.weight) +
            normSq (y.cross z) * (x.weight * y.weight)) := crossBound
        _ = y.weight * (2 * (normSq (x.cross y) * z.weight +
            normSq (y.cross z) * x.weight)) := by ring
    exact le_of_mul_le_mul_left scaled hyWeight
  rw [chordalSq_eq_cross, chordalSq_eq_cross, chordalSq_eq_cross]
  apply (div_le_iff₀ (mul_pos hxWeight hzWeight)).2
  have rhsIdentity :
      2 *
          (normSq (x.cross y) / (x.weight * y.weight) +
            normSq (y.cross z) / (y.weight * z.weight)) *
          (x.weight * z.weight) =
        2 * (normSq (x.cross y) * z.weight +
          normSq (y.cross z) * x.weight) / y.weight := by
    field_simp [ne_of_gt hxWeight, ne_of_gt hyWeight, ne_of_gt hzWeight]
  rw [rhsIdentity]
  exact (le_div_iff₀ hyWeight).2 cancelled

namespace Mat2

/-- Determinant of a two-by-two Gaussian-rational matrix. -/
def det (M : Mat2 GaussianRat) : GaussianRat := M.a * M.d - M.b * M.c

/-- Proposition 7.8, the homographic truncation identity. -/
theorem chordalSq_truncation (M : Mat2 GaussianRat) (t : GaussianRat) :
    chordalSq (act M (Proj.affine t)) (act M Proj.omega) =
      normSq M.det /
        ((normSq M.a + normSq M.c) *
          (normSq (M.a * t + M.b) + normSq (M.c * t + M.d))) := by
  have hnum :
      (M.a * t + M.b) * M.c - M.a * (M.c * t + M.d) = -M.det := by
    ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im, neg_re, neg_im, det] <;>
      ring
  simp only [chordalSq, act, Proj.affine, Proj.omega, mul_one, mul_zero, add_zero,
    hnum, normSq_neg]
  ring

/-- Exact determinant scaling of squared chordal distance between two affine
inputs under one matrix action. -/
theorem chordalSq_act_affine (M : Mat2 GaussianRat)
    (left right : GaussianRat) :
    chordalSq (act M (Proj.affine left)) (act M (Proj.affine right)) =
      normSq M.det * normSq (left - right) /
        ((act M (Proj.affine left)).weight *
          (act M (Proj.affine right)).weight) := by
  have crossIdentity :
      (M.a * left + M.b) * (M.c * right + M.d) -
          (M.a * right + M.b) * (M.c * left + M.d) =
        M.det * (left - right) := by
    ext <;>
      simp only [det, GaussianRat.add_re, GaussianRat.add_im,
        GaussianRat.sub_re, GaussianRat.sub_im, GaussianRat.mul_re,
        GaussianRat.mul_im] <;>
      ring
  rw [chordalSq_eq_cross]
  simp only [Proj.cross, act, Proj.affine, mul_one, Proj.weight,
    crossIdentity, normSq_mul]

end Mat2

/-- Remark 7.9, affine specialization. -/
theorem chordalSq_affine (z w : GaussianRat) :
    chordalSq (Proj.affine z) (Proj.affine w) =
      normSq (z - w) / ((1 + normSq z) * (1 + normSq w)) := by
  have hnum : z * 1 - w * 1 = z - w := by simp
  simp only [chordalSq, Proj.affine, hnum, normSq_one]
  congr 1
  ring

/-- Remark 7.9, the formal point `ω`. -/
theorem chordalSq_omega (z : GaussianRat) :
    chordalSq (Proj.affine z) Proj.omega = 1 / (1 + normSq z) := by
  simp only [chordalSq, Proj.affine, Proj.omega, mul_zero, mul_one, zero_sub,
    normSq_neg, normSq_one, normSq_zero]
  ring

theorem chordalSq_comm (x y : Proj GaussianRat) : chordalSq x y = chordalSq y x := by
  have hnum : y.p * x.q - x.p * y.q = -(x.p * y.q - y.p * x.q) := by
    ext <;> simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;> ring
  simp only [chordalSq, hnum, normSq_neg]
  congr 1
  ring

/-- `χ²` is unchanged by a nonzero rescaling of the left coordinate pair. -/
theorem chordalSq_scale_left (l : GaussianRat) (hl : l ≠ 0)
    (x y : Proj GaussianRat) : chordalSq (x.scale l) y = chordalSq x y := by
  have hnorm : normSq l ≠ 0 := fun h => hl (normSq_eq_zero.mp h)
  have hnum :
      (l * x.p) * y.q - y.p * (l * x.q) = l * (x.p * y.q - y.p * x.q) := by
    ext <;> simp only [sub_re, sub_im, mul_re, mul_im] <;> ring
  simp only [chordalSq, Proj.scale, hnum, normSq_mul]
  field_simp [hnorm]

/-- `χ²` is unchanged by a nonzero rescaling of the right coordinate pair. -/
theorem chordalSq_scale_right (l : GaussianRat) (hl : l ≠ 0)
    (x y : Proj GaussianRat) : chordalSq x (y.scale l) = chordalSq x y := by
  rw [chordalSq_comm, chordalSq_scale_left l hl, chordalSq_comm]

end CCL
