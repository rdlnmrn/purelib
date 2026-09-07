import CCL.Encoding.CCF.CoordinateFloor
import Mathlib.Tactic.LinearCombination

/-!
# Finite three-step CCF contraction certificate

This module formalizes the explicit finite certificate in Table (5.1).  The
eight exceptional digits are an inductive finite type, so the certificate is
checked by ordinary Lean case splits and rational polynomial normalization.
-/

namespace CCL

open GaussianRat
open Integral

namespace CCFContraction

/-- The eight digits left by the cone and `λ(t) < 8`. -/
inductive SmallDigit where
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7
deriving DecidableEq, Repr

/-- The exceptional digit list `τ₀,…,τ₇` from Table (5.1). -/
def tau : SmallDigit → GI
  | .d0 => ⟨1, -2⟩
  | .d1 => ⟨1, -1⟩
  | .d2 => ⟨1, 0⟩
  | .d3 => ⟨1, 1⟩
  | .d4 => ⟨2, -2⟩
  | .d5 => ⟨2, -1⟩
  | .d6 => ⟨2, 0⟩
  | .d7 => ⟨2, 1⟩

/-- The piecewise integer lower bound used in the coarse estimate. -/
def lambda (t : GI) : ℤ :=
  if 0 ≤ t.im then t.re ^ 2 + t.im ^ 2
  else if t.im = -1 then t.re ^ 2
  else t.re ^ 2 + (t.im + 1) ^ 2

@[simp] theorem lambda_tau :
    lambda (tau .d0) = 2 ∧ lambda (tau .d1) = 1 ∧
    lambda (tau .d2) = 1 ∧ lambda (tau .d3) = 2 ∧
    lambda (tau .d4) = 5 ∧ lambda (tau .d5) = 4 ∧
    lambda (tau .d6) = 4 ∧ lambda (tau .d7) = 5 := by
  norm_num [lambda, tau]

/-- The piecewise `λ` is a uniform lower bound for translating any point of
the coordinate square by a cone digit. -/
theorem lambda_le_norm_translate (t : GI) (ha : 0 ≤ t.re)
    (q : GaussianRat) (hq : CoordinateFloor.Sq q) :
    (lambda t : ℚ) ≤ normSq (toRat t + q) := by
  rcases hq with ⟨hx₀, hx₁, hy₀, hy₁⟩
  have haQ : (0 : ℚ) ≤ t.re := by exact_mod_cast ha
  have hxgrow : (t.re : ℚ) ^ 2 ≤ ((t.re : ℚ) + q.re) ^ 2 := by
    nlinarith [mul_nonneg haQ hx₀]
  by_cases hb : 0 ≤ t.im
  · have hbQ : (0 : ℚ) ≤ t.im := by exact_mod_cast hb
    have hygrow : (t.im : ℚ) ^ 2 ≤ ((t.im : ℚ) + q.im) ^ 2 := by
      nlinarith [mul_nonneg hbQ hy₀]
    simp only [lambda, if_pos hb, normSq, add_re, add_im, toRat]
    push_cast
    exact add_le_add hxgrow hygrow
  · have hbneg : t.im < 0 := lt_of_not_ge hb
    by_cases hbm1 : t.im = -1
    · simp only [lambda, if_neg hb, if_pos hbm1, normSq, add_re, add_im, toRat]
      rw [hbm1]
      norm_num
      nlinarith [sq_nonneg (-1 + q.im)]
    · have hble : t.im ≤ -2 := by omega
      have hleft : (t.im : ℚ) + q.im ≤ (t.im : ℚ) + 1 := by
        linarith
      have hright : (t.im : ℚ) + 1 ≤ 0 := by exact_mod_cast (show t.im + 1 ≤ 0 by omega)
      have hsqgrow : ((t.im : ℚ) + 1) ^ 2 ≤
          ((t.im : ℚ) + q.im) ^ 2 := by
        have hp : 0 ≤ (((t.im : ℚ) + 1) - ((t.im : ℚ) + q.im)) *
            (-(((t.im : ℚ) + 1) + ((t.im : ℚ) + q.im))) :=
          mul_nonneg (sub_nonneg.mpr hleft) (by linarith)
        nlinarith
      simp only [lambda, if_neg hb, if_neg hbm1, normSq, add_re, add_im, toRat]
      push_cast
      exact add_le_add hxgrow hsqgrow

/-- The digit cone plus `λ(t) < 8` leaves exactly the eight displayed
exceptional digits. -/
theorem exists_small_of_cone (t : GI)
    (hcone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re)
    (hlambda : lambda t < 8) : ∃ r : SmallDigit, t = tau r := by
  rcases hcone with ⟨ha, hb₀, hb₁⟩
  have hareSq : t.re ^ 2 < 8 := by
    dsimp [lambda] at hlambda
    split at hlambda
    · nlinarith [sq_nonneg t.im]
    · split at hlambda
      · exact hlambda
      · nlinarith [sq_nonneg (t.im + 1)]
  have ha₂ : t.re ≤ 2 := by
    by_contra h
    have : 3 ≤ t.re := by omega
    nlinarith
  rcases (show t.re = 1 ∨ t.re = 2 by omega) with haEq | haEq
  · have hbCases : t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨ t.im = 1 := by
      omega
    rcases hbCases with hbEq | hbEq | hbEq | hbEq
    · refine ⟨.d0, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d1, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d2, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d3, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
  · have hbCases : t.im = -3 ∨ t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨
        t.im = 1 ∨ t.im = 2 := by
      omega
    rcases hbCases with hbEq | hbEq | hbEq | hbEq | hbEq | hbEq
    · norm_num [lambda, haEq, hbEq] at hlambda
    · refine ⟨.d4, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d5, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d6, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · refine ⟨.d7, ?_⟩
      apply Zsqrtd.ext <;> simp [tau, haEq, hbEq]
    · norm_num [lambda, haEq, hbEq] at hlambda

theorem lambda_nonneg (t : GI) : 0 ≤ lambda t := by
  dsimp [lambda]
  split
  · positivity
  · split <;> positivity

theorem one_le_lambda_of_cone (t : GI)
    (hcone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re) :
    1 ≤ lambda t := by
  have ha := hcone.1
  have haSq : 1 ≤ t.re ^ 2 := by nlinarith
  dsimp [lambda]
  split
  · nlinarith [sq_nonneg t.im]
  · split
    · exact haSq
    · nlinarith [sq_nonneg (t.im + 1)]

/-- The exact polynomial `Δᵣ,ᶜ(x,y)` from the proof of Lemma 5.2. -/
def delta (t t' : GI) (w : GaussianRat) : ℚ :=
  normSq (toRat t * (toRat t' + w) + gamma) - 4 * normSq w

/-- Every entry of Table (5.1) is strictly positive on the half-open square,
apart from the marked impossible pair `(1-i,1-2i)`. -/
theorem delta_pos_of_small (r c : SmallDigit) (w : GaussianRat)
    (hw : CoordinateFloor.Sq w) (hcross : ¬ (r = .d1 ∧ c = .d0)) :
    0 < delta (tau r) (tau c) w := by
  rcases hw with ⟨hx₀, hx₁, hy₀, hy₁⟩
  have hxprod : 0 ≤ w.re * (1 - w.re) :=
    mul_nonneg hx₀ (by linarith)
  have hyprod : 0 ≤ w.im * (1 - w.im) :=
    mul_nonneg hy₀ (by linarith)
  cases r <;> cases c
  all_goals norm_num [delta, tau, normSq, toRat, gamma] at hcross
  all_goals norm_num [delta, tau, normSq, toRat, gamma]
  all_goals ring_nf at ⊢
  all_goals nlinarith [sq_nonneg w.re, sq_nonneg w.im]

private theorem mul_quotient_eq_gamma (z : GaussianRat) (hz : z ≠ 0) :
    z * (gamma * inv z) = gamma := by
  rw [← GaussianRat.mul_assoc, GaussianRat.mul_comm z gamma,
    GaussianRat.mul_assoc, mul_inv z hz, mul_one]

/-- The crossed-out entry `(t,t') = (1-i,1-2i)` in Table (5.1) cannot occur
for three successive square states. -/
theorem cross_pair_impossible (u v w : GaussianRat)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hsu : CoordinateFloor.Sq u) (hsv : CoordinateFloor.Sq v)
    (hsw : CoordinateFloor.Sq w)
    (huBranch : gamma * inv u = toRat (tau .d1) + v)
    (hvBranch : gamma * inv v = toRat (tau .d0) + w) : False := by
  rcases hsu with ⟨hux₀, hux₁, huy₀, huy₁⟩
  rcases hsv with ⟨hvx₀, hvx₁, hvy₀, hvy₁⟩
  rcases hsw with ⟨hwx₀, hwx₁, hwy₀, hwy₁⟩
  have hvMul : v * (toRat (tau .d0) + w) = gamma := by
    rw [← hvBranch]
    exact mul_quotient_eq_gamma v hv
  have hvRe := congrArg GaussianRat.re hvMul
  have hvIm := congrArg GaussianRat.im hvMul
  norm_num [tau, toRat, gamma, mul_re, mul_im, add_re, add_im] at hvRe hvIm
  let A : ℚ := 1 + w.re
  let B : ℚ := 2 - w.im
  let R : ℚ := A ^ 2 + B ^ 2
  have hB : 1 < B := by dsimp [B]; linarith
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [sq_nonneg A, sq_nonneg B]
  have hpR : v.re * R = A - B := by
    dsimp [R, A, B]
    linear_combination (1 + w.re) * hvRe - (2 - w.im) * hvIm
  have hqR : v.im * R = A + B := by
    dsimp [R, A, B]
    linear_combination (2 - w.im) * hvRe + (1 + w.re) * hvIm
  have hnormR : (v.re ^ 2 + v.im ^ 2) * R = 2 := by
    calc
      (v.re ^ 2 + v.im ^ 2) * R =
          v.re * (v.re * R) + v.im * (v.im * R) := by ring
      _ = v.re * (A - B) + v.im * (A + B) := by rw [hpR, hqR]
      _ = 2 := by
        dsimp [A, B]
        linarith [hvRe, hvIm]
  let numerator : ℚ := v.im * (1 - v.im) - v.re * (1 + v.re)
  have hnumR : numerator * R = 2 * (B - 1) := by
    calc
      numerator * R =
          v.im * R - v.re * R - (v.re ^ 2 + v.im ^ 2) * R := by
        dsimp [numerator]
        ring
      _ = (A + B) - (A - B) - 2 := by rw [hqR, hpR, hnormR]
      _ = 2 * (B - 1) := by ring
  have hnumMulPos : 0 < numerator * R := by
    rw [hnumR]
    positivity
  have hnumPos : 0 < numerator := by
    rcases (mul_pos_iff.mp hnumMulPos) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge hR.le) h.2)
  have huMul : u * (toRat (tau .d1) + v) = gamma := by
    rw [← huBranch]
    exact mul_quotient_eq_gamma u hu
  have huRe := congrArg GaussianRat.re huMul
  have huIm := congrArg GaussianRat.im huMul
  norm_num [tau, toRat, gamma, mul_re, mul_im, add_re, add_im] at huRe huIm
  let D : ℚ := (1 + v.re) ^ 2 + (v.im - 1) ^ 2
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg (v.im - 1)]
  have huyD : u.im * D = 2 + v.re - v.im := by
    dsimp [D]
    linear_combination -(v.im - 1) * huRe + (1 + v.re) * huIm
  have hshift : (u.im - 1) * D = numerator := by
    dsimp [D, numerator]
    linear_combination huyD
  have hshiftPos : 0 < (u.im - 1) * D := by rwa [hshift]
  rcases (mul_pos_iff.mp hshiftPos) with h | h
  · linarith
  · exact False.elim ((not_lt_of_ge hD.le) h.2)

/-- Lemma 5.2: three successive nonterminal coordinate-floor remainders
contract their norm product strictly below one. -/
theorem three_step_contraction (u : GaussianRat) (hu : u ≠ 0)
    (hsu : CoordinateFloor.Sq u) (hv : CoordinateFloor.step u ≠ 0) :
    normSq (u * CoordinateFloor.step u *
      CoordinateFloor.step (CoordinateFloor.step u)) < 1 := by
  let v := CoordinateFloor.step u
  let w := CoordinateFloor.step v
  let t := CoordinateFloor.floor (gamma * inv u)
  let t' := CoordinateFloor.floor (gamma * inv v)
  have hsv : CoordinateFloor.Sq v := by
    dsimp [v]
    exact CoordinateFloor.step_sq u
  have hsw : CoordinateFloor.Sq w := by
    dsimp [w]
    exact CoordinateFloor.step_sq v
  have huBranch : gamma * inv u = toRat t + v := by
    symm
    simpa [t, v] using CoordinateFloor.floor_add_step u
  have hvBranch : gamma * inv v = toRat t' + w := by
    symm
    simpa [t', w] using CoordinateFloor.floor_add_step v
  have htCone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
    simpa [t] using CoordinateFloor.digit_cone u hu hsu
  have ht'Cone : 1 ≤ t'.re ∧ -t'.re - 1 ≤ t'.im ∧ t'.im ≤ t'.re := by
    simpa [t'] using CoordinateFloor.digit_cone v hv hsv
  have huMul : u * (toRat t + v) = gamma := by
    rw [← huBranch]
    exact mul_quotient_eq_gamma u hu
  have hvMul : v * (toRat t' + w) = gamma := by
    rw [← hvBranch]
    exact mul_quotient_eq_gamma v hv
  have huNorm := congrArg normSq huMul
  have hvNorm := congrArg normSq hvMul
  rw [normSq_mul, normSq_gamma] at huNorm hvNorm
  have hden : 4 * normSq w <
      normSq (toRat t + v) * normSq (toRat t' + w) := by
    by_cases hcoarse : 8 ≤ lambda t * lambda t'
    · have htLower := lambda_le_norm_translate t (by omega) v hsv
      have ht'Lower := lambda_le_norm_translate t' (by omega) w hsw
      have hmulLower : ((lambda t * lambda t' : ℤ) : ℚ) ≤
          normSq (toRat t + v) * normSq (toRat t' + w) := by
        rw [Int.cast_mul]
        exact mul_le_mul htLower ht'Lower (by exact_mod_cast lambda_nonneg t')
          (normSq_nonneg (toRat t + v))
      have hcoarseQ : (8 : ℚ) ≤ (lambda t * lambda t' : ℤ) := by
        exact_mod_cast hcoarse
      have hwlt := CoordinateFloor.normSq_lt_two_of_sq hsw
      nlinarith
    · have hprodlt : lambda t * lambda t' < 8 := lt_of_not_ge hcoarse
      have htOne := one_le_lambda_of_cone t htCone
      have ht'One := one_le_lambda_of_cone t' ht'Cone
      have htSmall : lambda t < 8 := by nlinarith
      have ht'Small : lambda t' < 8 := by nlinarith
      obtain ⟨r, ht⟩ := exists_small_of_cone t htCone htSmall
      obtain ⟨c, ht'⟩ := exists_small_of_cone t' ht'Cone ht'Small
      have hcross : ¬ (r = .d1 ∧ c = .d0) := by
        rintro ⟨rfl, rfl⟩
        apply cross_pair_impossible u v w hu hv hsu hsv hsw
        · simpa [ht] using huBranch
        · simpa [ht'] using hvBranch
      have hdelta := delta_pos_of_small r c w hsw hcross
      have hvMul' : v * (toRat (tau c) + w) = gamma := by
        simpa [ht'] using hvMul
      have hfactor :
          toRat (tau r) * (toRat (tau c) + w) + gamma =
            (toRat (tau r) + v) * (toRat (tau c) + w) := by
        rw [right_distrib, hvMul']
      rw [delta, hfactor, normSq_mul] at hdelta
      simpa [ht, ht'] using hdelta
  have hproduct :
      normSq (u * v * w) *
          (normSq (toRat t + v) * normSq (toRat t' + w)) =
        4 * normSq w := by
    rw [normSq_mul, normSq_mul]
    calc
      (normSq u * normSq v * normSq w) *
          (normSq (toRat t + v) * normSq (toRat t' + w)) =
          (normSq u * normSq (toRat t + v)) *
            (normSq v * normSq (toRat t' + w)) * normSq w := by ring
      _ = 2 * 2 * normSq w := by rw [huNorm, hvNorm]
      _ = 4 * normSq w := by ring
  have hdenPos : 0 < normSq (toRat t + v) * normSq (toRat t' + w) := by
    nlinarith [normSq_nonneg w]
  have hresult : normSq (u * v * w) < 1 := by
    nlinarith
  simpa [v, w] using hresult

end CCFContraction

end CCL
