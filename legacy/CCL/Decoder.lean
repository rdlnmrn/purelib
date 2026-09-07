import CCL.Encoding.Normalization
import CCL.Geometry.Chordal
import CCL.Prefix
import CCL.Geometry.Projective
import CCL.Encoding.Sectors

/-!
# Completed CCL blocks and denominator descent

This module formalizes Sections 6.3–6.5 at the block boundary: raw words,
decoder matrices, their finite matrix factorizations and determinants, and the
strict norm descent that drives the well-founded encoder.
-/

namespace CCL

open GaussianRat

namespace CCLDecoder

/-- Raw syntax `[k,s] = 1ᵏ 0 β(s)`. -/
def regularWord (k : ℕ) (s : Sector) : Prefix.Word :=
  List.replicate k true ++ false :: s.code

/-- Raw syntax `0[m,s]`, with the extra low-initial zero. -/
def lowWord (m : ℕ) (s : Sector) : Prefix.Word := false :: regularWord m s

@[simp] theorem regularWord_length (k : ℕ) (s : Sector) :
    (regularWord k s).length = k + 4 := by
  simp [regularWord]

@[simp] theorem lowWord_length (m : ℕ) (s : Sector) :
    (lowWord m s).length = m + 5 := by
  simp [lowWord]

/-- Formula (6.2), the completed regular block matrix. -/
def regularBlock (k : ℕ) (s : Sector) : Mat2 GaussianRat :=
  ⟨natPow gamma (k + 1) * s.rep, natPow gamma k, gamma, 0⟩

/-- The low-header diagonal factor `E⁻ₘ`. -/
def lowScale (m : ℕ) : Mat2 GaussianRat :=
  ⟨1, 0, 0, natPow gamma m⟩

/-- Formula (6.3), the completed low initial block matrix. -/
def lowBlock (m : ℕ) (s : Sector) : Mat2 GaussianRat :=
  ⟨gamma * s.rep, 1, natPow gamma (m + 1), 0⟩

private theorem matrix_ext_ring {M N : Mat2 GaussianRat}
    (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M
  cases N
  simp_all

/-- The finite factorization `B(k,s) = S_{γᵏ} T_s I_γ`. -/
theorem regularBlock_factorization (k : ℕ) (s : Sector) :
    Mat2.mul (Mat2.mul (Mat2.scale (natPow gamma k)) (Mat2.translate s.rep))
      (Mat2.invert gamma) = regularBlock k s := by
  apply matrix_ext_ring
  all_goals ext <;>
    simp only [Mat2.mul, Mat2.scale, Mat2.translate, Mat2.invert, regularBlock,
      natPow_succ, add_re, add_im, mul_re, mul_im, zero_re, zero_im, one_re, one_im,
      gamma] <;>
    ring

/-- The finite factorization `L(m,s) = E⁻ₘ T_s I_γ`. -/
theorem lowBlock_factorization (m : ℕ) (s : Sector) :
    Mat2.mul (Mat2.mul (lowScale m) (Mat2.translate s.rep))
      (Mat2.invert gamma) = lowBlock m s := by
  apply matrix_ext_ring
  all_goals ext <;>
    simp only [Mat2.mul, Mat2.translate, Mat2.invert, lowScale, lowBlock,
      natPow_succ, add_re, add_im, mul_re, mul_im, zero_re, zero_im, one_re, one_im,
      gamma] <;>
    ring

theorem regularBlock_det (k : ℕ) (s : Sector) :
    (regularBlock k s).det = -natPow gamma (k + 1) := by
  ext <;>
    simp only [Mat2.det, regularBlock, natPow_succ, sub_re, sub_im, mul_re, mul_im,
      neg_re, neg_im, zero_re, zero_im, gamma] <;>
    ring

theorem lowBlock_det (m : ℕ) (s : Sector) :
    (lowBlock m s).det = -natPow gamma (m + 1) := by
  ext <;>
    simp only [Mat2.det, lowBlock, sub_re, sub_im, mul_re, mul_im, neg_re, neg_im,
      zero_re, zero_im, one_re, one_im] <;>
    ring

/-- Lemma 6.4 over an uncancelled Gaussian-rational numerator/denominator pair. -/
theorem inversion_stage_descent {y P Q : GaussianRat} (hQ : Q ≠ 0)
    (hy : Sector.Band y) (s : Sector) (hs : s.Holds y) (hP : P = y * Q) :
    normSq (gamma * (P - s.rep * Q)) < normSq Q := by
  have hdiff : P - s.rep * Q = (y - s.rep) * Q := by
    subst P
    ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im] <;>
      ring
  rw [hdiff, normSq_mul, normSq_mul, normSq_gamma]
  have hc := Sector.contraction hy s hs
  have hQpos := normSq_pos hQ
  nlinarith

/-- The post-inversion state is automatically outside the unit norm. -/
theorem postInversion_norm_gt_one {y : GaussianRat} (hy : Sector.Band y)
    (s : Sector) (hs : s.Holds y) (hr : y - s.rep ≠ 0) :
    1 < normSq (inv (gamma * (y - s.rep))) := by
  have hgamma : gamma * (y - s.rep) ≠ 0 := by
    intro h
    have hn := congrArg normSq h
    rw [normSq_mul, normSq_gamma, normSq_zero] at hn
    exact hr (normSq_eq_zero.mp (by nlinarith [normSq_nonneg (y - s.rep)]))
  have hinv := mul_inv (gamma * (y - s.rep)) hgamma
  have hnormInv := congrArg normSq hinv
  rw [normSq_mul, normSq_one] at hnormInv
  have hc := Sector.contraction hy s hs
  rw [normSq_mul, normSq_gamma] at hnormInv
  have hrpos := normSq_pos hr
  nlinarith

/-- The second strict inequality in Theorem 6.5, after loop normalization. -/
theorem normalized_denominator_descent (k : ℕ) {Qplus Q : GaussianRat}
    (hscale : (2 : ℚ) ^ k * normSq Qplus < normSq Q) :
    normSq (natPow gamma k * Qplus) < normSq Q := by
  rwa [normSq_gamma_pow_mul]

/-- The complete denominator descent used by a nonterminal CCL macro-step. -/
theorem ccl_macro_descent {y P Q : GaussianRat} (_hQ : Q ≠ 0)
    (_hy : Sector.Band y) (s : Sector) (_hs : s.Holds y) (_hP : P = y * Q)
    (k : ℕ)
    (hscale : (2 : ℚ) ^ k * normSq (gamma * (P - s.rep * Q)) < normSq Q) :
    normSq (natPow gamma k * (gamma * (P - s.rep * Q))) < normSq Q :=
  normalized_denominator_descent k hscale

end CCLDecoder

end CCL
