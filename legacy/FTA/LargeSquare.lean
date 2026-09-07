import FTA.PolynomialBounds

/-!
# Computable leading-term dominance on a large rational square

This module isolates the finite coefficient estimate used in the large-square
step of the constructive FTA.  From a nonzero Gaussian-rational polynomial it
computes a rational radius.  On the boundary of the corresponding symmetric
square, every lower-degree term is strictly smaller in squared norm than the
leading monomial.

The coefficient weight includes the factor `2^k` forced by the corner bound
`N(z) <= 2 R^2`.  This gives a deliberately strong, directly checkable version
of the paper's large-radius condition without a search or a recursion-depth
override.
-/

namespace FTA

open CCL CCL.GaussianRat Polynomial
open scoped BigOperators

/-- The exact sum of all terms below the leading degree, evaluated at `z`. -/
def lowerTermsValue (p : Polynomial QI) (z : QI) : QI :=
  ∑ k ∈ Finset.range p.natDegree, p.coeff k * z ^ k

/-- A finite rational coefficient weight dominating the lower terms on a
symmetric square. -/
def lowerCoefficientWeight (p : Polynomial QI) : ℚ :=
  (p.natDegree : ℚ) *
    ∑ k ∈ Finset.range p.natDegree,
      normSq (p.coeff k) * (2 : ℚ) ^ k

/-- An explicit rational radius at least one.  For nonzero `p`, its square is
large enough for the leading monomial to dominate the lower terms. -/
def largeSquareRadius (p : Polynomial QI) : ℚ :=
  max 1 (lowerCoefficientWeight p / normSq p.leadingCoeff + 1)

/-- Exact membership in the four edges of the symmetric square of radius
`R`, including its corners. -/
def OnSymmetricSquareBoundary (R : ℚ) (z : QI) : Prop :=
  -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R ∧
    (z.re = -R ∨ z.re = R ∨ z.im = -R ∨ z.im = R)

/-- Splitting the finite evaluation sum at the leading degree. -/
theorem eval_eq_lowerTermsValue_add_leading (p : Polynomial QI) (z : QI) :
    p.eval z = lowerTermsValue p z + p.leadingCoeff * z ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
  simp only [lowerTermsValue, Polynomial.coeff_natDegree]

/-- The coefficient weight is nonnegative. -/
theorem lowerCoefficientWeight_nonneg (p : Polynomial QI) :
    0 ≤ lowerCoefficientWeight p := by
  dsimp only [lowerCoefficientWeight]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (normSq_nonneg _) (pow_nonneg (by norm_num) _)

/-- The computed radius is at least one. -/
theorem one_le_largeSquareRadius (p : Polynomial QI) :
    1 ≤ largeSquareRadius p := by
  exact le_max_left _ _

/-- In particular, the computed radius is strictly positive. -/
theorem largeSquareRadius_pos (p : Polynomial QI) :
    0 < largeSquareRadius p :=
  zero_lt_one.trans_le (one_le_largeSquareRadius p)

/-- A point on the symmetric boundary has squared norm at least `R^2`. -/
theorem sq_le_normSq_of_onSymmetricSquareBoundary {R : ℚ} {z : QI}
    (hz : OnSymmetricSquareBoundary R z) : R ^ 2 ≤ normSq z := by
  rcases hz with ⟨_hxLower, _hxUpper, _hyLower, _hyUpper,
    hreLower | hreUpper | himLower | himUpper⟩
  · rw [normSq, hreLower]
    nlinarith [sq_nonneg z.im]
  · rw [normSq, hreUpper]
    nlinarith [sq_nonneg z.im]
  · rw [normSq, himLower]
    nlinarith [sq_nonneg z.re]
  · rw [normSq, himUpper]
    nlinarith [sq_nonneg z.re]

/-- A point on the symmetric boundary has squared norm at most `2 R^2`. -/
theorem normSq_le_two_mul_sq_of_onSymmetricSquareBoundary {R : ℚ} {z : QI}
    (hR : 0 ≤ R) (hz : OnSymmetricSquareBoundary R z) :
    normSq z ≤ 2 * R ^ 2 := by
  rcases hz with ⟨hxLower, hxUpper, hyLower, hyUpper, _hside⟩
  have hxAbs : |z.re| ≤ R := abs_le.mpr ⟨by linarith, hxUpper⟩
  have hyAbs : |z.im| ≤ R := abs_le.mpr ⟨by linarith, hyUpper⟩
  have hxSq : z.re ^ 2 ≤ R ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg hR] using hxAbs
  have hySq : z.im ^ 2 ≤ R ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg hR] using hyAbs
  rw [normSq]
  linarith

/-- The chosen radius satisfies the strict coefficient inequality required by
leading-term dominance. -/
theorem lowerCoefficientWeight_lt_leading_mul_radius_sq
    {p : Polynomial QI} (hp : p ≠ 0) :
    lowerCoefficientWeight p <
      normSq p.leadingCoeff * largeSquareRadius p ^ 2 := by
  have hleading : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  have hnormPos : 0 < normSq p.leadingCoeff := normSq_pos hleading
  have hweightNonneg := lowerCoefficientWeight_nonneg p
  have hradiusLower :
      lowerCoefficientWeight p / normSq p.leadingCoeff + 1 ≤
        largeSquareRadius p :=
    le_max_right _ _
  have hquotient :
      lowerCoefficientWeight p / normSq p.leadingCoeff <
        largeSquareRadius p := by
    linarith
  have hlinear :
      lowerCoefficientWeight p <
        normSq p.leadingCoeff * largeSquareRadius p := by
    have h := (div_lt_iff₀ hnormPos).mp hquotient
    calc
      lowerCoefficientWeight p <
          largeSquareRadius p * normSq p.leadingCoeff := h
      _ = normSq p.leadingCoeff * largeSquareRadius p := mul_comm _ _
  have hradiusSq : largeSquareRadius p ≤ largeSquareRadius p ^ 2 := by
    have hradiusNonneg : 0 ≤ largeSquareRadius p :=
      (largeSquareRadius_pos p).le
    have hfactor := mul_nonneg hradiusNonneg
      (sub_nonneg.mpr (one_le_largeSquareRadius p))
    nlinarith
  exact hlinear.trans_le
    (mul_le_mul_of_nonneg_left hradiusSq hnormPos.le)

/-- Cauchy--Schwarz plus the corner bound controls all terms below the leading
degree by the finite coefficient weight. -/
theorem normSq_lowerTermsValue_le
    (p : Polynomial QI) {R : ℚ} {z : QI}
    (hR : 1 ≤ R) (hz : normSq z ≤ 2 * R ^ 2) :
    normSq (lowerTermsValue p z) ≤
      lowerCoefficientWeight p * (R ^ 2) ^ (p.natDegree - 1) := by
  have hRsq : 1 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - 1)]
  calc
    normSq (lowerTermsValue p z) ≤
        (p.natDegree : ℚ) *
          ∑ k ∈ Finset.range p.natDegree,
            normSq (p.coeff k * z ^ k) := by
      simpa only [lowerTermsValue, Finset.card_range] using
        normSq_finset_sum_le (Finset.range p.natDegree)
          (fun k => p.coeff k * z ^ k)
    _ = (p.natDegree : ℚ) *
          ∑ k ∈ Finset.range p.natDegree,
            normSq (p.coeff k) * normSq z ^ k := by
      simp only [normSq_mul, normSq_pow]
    _ ≤ (p.natDegree : ℚ) *
          ∑ k ∈ Finset.range p.natDegree,
            (normSq (p.coeff k) * (2 : ℚ) ^ k) *
              (R ^ 2) ^ (p.natDegree - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      have hkDegree : k ≤ p.natDegree - 1 := by
        have := Finset.mem_range.mp hk
        omega
      have hRpow : (R ^ 2) ^ k ≤ (R ^ 2) ^ (p.natDegree - 1) :=
        pow_le_pow_right₀ hRsq hkDegree
      calc
        normSq (p.coeff k) * normSq z ^ k ≤
            normSq (p.coeff k) * (2 * R ^ 2) ^ k := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (normSq_nonneg z) hz k)
            (normSq_nonneg _)
        _ = (normSq (p.coeff k) * (2 : ℚ) ^ k) *
              (R ^ 2) ^ k := by
          rw [mul_pow]
          ring
        _ ≤ (normSq (p.coeff k) * (2 : ℚ) ^ k) *
              (R ^ 2) ^ (p.natDegree - 1) := by
          exact mul_le_mul_of_nonneg_left hRpow
            (mul_nonneg (normSq_nonneg _) (pow_nonneg (by norm_num) _))
    _ = lowerCoefficientWeight p * (R ^ 2) ^ (p.natDegree - 1) := by
      rw [lowerCoefficientWeight, ← Finset.sum_mul]
      ring

/-- On the computed square for a nonconstant polynomial, the lower terms are
strictly dominated in squared norm by the leading monomial. -/
theorem lowerTermsValue_strictly_dominated
    {p : Polynomial QI} (hdegree : 0 < p.natDegree) {z : QI}
    (hz : OnSymmetricSquareBoundary (largeSquareRadius p) z) :
    normSq (lowerTermsValue p z) <
      normSq (p.leadingCoeff * z ^ p.natDegree) := by
  have hp : p ≠ 0 := by
    intro hp
    subst p
    simp at hdegree
  have hradiusOne := one_le_largeSquareRadius p
  have hradiusNonneg : 0 ≤ largeSquareRadius p := by linarith
  have hzUpper :=
    normSq_le_two_mul_sq_of_onSymmetricSquareBoundary hradiusNonneg hz
  have hzLower := sq_le_normSq_of_onSymmetricSquareBoundary hz
  have hlower := normSq_lowerTermsValue_le p hradiusOne hzUpper
  have hcoefficient :=
    lowerCoefficientWeight_lt_leading_mul_radius_sq hp
  have hfactorPos :
      0 < (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) := by
    exact pow_pos (sq_pos_of_pos (largeSquareRadius_pos p)) _
  have hweighted :
      lowerCoefficientWeight p *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) <
        (normSq p.leadingCoeff * largeSquareRadius p ^ 2) *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) :=
    mul_lt_mul_of_pos_right hcoefficient hfactorPos
  have hdegreeOne : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hdegree)
  have hradiusPowers :
      largeSquareRadius p ^ 2 *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) =
        (largeSquareRadius p ^ 2) ^ p.natDegree := by
    calc
      _ = (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) *
          largeSquareRadius p ^ 2 := mul_comm _ _
      _ = (largeSquareRadius p ^ 2) ^ ((p.natDegree - 1) + 1) :=
        (pow_succ _ _).symm
      _ = _ := by rw [Nat.sub_add_cancel hdegreeOne]
  have hpowerIdentity :
      (normSq p.leadingCoeff * largeSquareRadius p ^ 2) *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) =
        normSq p.leadingCoeff *
          (largeSquareRadius p ^ 2) ^ p.natDegree := by
    calc
      _ = normSq p.leadingCoeff *
          (largeSquareRadius p ^ 2 *
            (largeSquareRadius p ^ 2) ^ (p.natDegree - 1)) := by ring
      _ = _ := by rw [hradiusPowers]
  calc
    normSq (lowerTermsValue p z) ≤
        lowerCoefficientWeight p *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) := hlower
    _ < normSq p.leadingCoeff *
          (largeSquareRadius p ^ 2) ^ p.natDegree := by
      simpa only [hpowerIdentity] using hweighted
    _ ≤ normSq p.leadingCoeff * normSq z ^ p.natDegree := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sq_nonneg _) hzLower p.natDegree)
        (normSq_nonneg _)
    _ = normSq (p.leadingCoeff * z ^ p.natDegree) := by
      rw [normSq_mul, normSq_pow]

/-- Explicit uniform rational gap between the leading monomial and all lower
terms on the computed square. -/
def largeSquareDominanceMargin (p : Polynomial QI) : ℚ :=
  (normSq p.leadingCoeff * largeSquareRadius p ^ 2 -
      lowerCoefficientWeight p) *
    (largeSquareRadius p ^ 2) ^ (p.natDegree - 1)

theorem largeSquareDominanceMargin_pos
    {p : Polynomial QI} (hp : p ≠ 0) :
    0 < largeSquareDominanceMargin p := by
  have hgap := lowerCoefficientWeight_lt_leading_mul_radius_sq hp
  have hfactor :
      0 < (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) :=
    pow_pos (sq_pos_of_pos (largeSquareRadius_pos p)) _
  exact mul_pos (sub_pos.mpr hgap) hfactor

/-- The explicit gap lower-bounds the pointwise difference of squared norms
on every edge and corner of the computed square. -/
theorem largeSquareDominanceMargin_le
    {p : Polynomial QI} (hdegree : 0 < p.natDegree) {z : QI}
    (hz : OnSymmetricSquareBoundary (largeSquareRadius p) z) :
    largeSquareDominanceMargin p ≤
      normSq (p.leadingCoeff * z ^ p.natDegree) -
        normSq (lowerTermsValue p z) := by
  have hradiusOne := one_le_largeSquareRadius p
  have hradiusNonneg : 0 ≤ largeSquareRadius p := hradiusOne.trans' (by norm_num)
  have hzUpper :=
    normSq_le_two_mul_sq_of_onSymmetricSquareBoundary hradiusNonneg hz
  have hzLower := sq_le_normSq_of_onSymmetricSquareBoundary hz
  have hlower := normSq_lowerTermsValue_le p hradiusOne hzUpper
  have hdegreeOne : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hdegree)
  have hradiusPowers :
      largeSquareRadius p ^ 2 *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) =
        (largeSquareRadius p ^ 2) ^ p.natDegree := by
    calc
      _ = (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) *
          largeSquareRadius p ^ 2 := mul_comm _ _
      _ = (largeSquareRadius p ^ 2) ^ ((p.natDegree - 1) + 1) :=
        (pow_succ _ _).symm
      _ = _ := by rw [Nat.sub_add_cancel hdegreeOne]
  have hleading :
      normSq p.leadingCoeff *
          (largeSquareRadius p ^ 2) ^ p.natDegree ≤
        normSq (p.leadingCoeff * z ^ p.natDegree) := by
    rw [normSq_mul, normSq_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sq_nonneg _) hzLower p.natDegree)
      (normSq_nonneg _)
  dsimp only [largeSquareDominanceMargin]
  calc
    (normSq p.leadingCoeff * largeSquareRadius p ^ 2 -
          lowerCoefficientWeight p) *
        (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) =
      normSq p.leadingCoeff *
          (largeSquareRadius p ^ 2) ^ p.natDegree -
        lowerCoefficientWeight p *
          (largeSquareRadius p ^ 2) ^ (p.natDegree - 1) := by
            rw [← hradiusPowers]
            ring
    _ ≤ normSq (p.leadingCoeff * z ^ p.natDegree) -
        normSq (lowerTermsValue p z) := sub_le_sub hleading hlower

/-- Hence the polynomial has no zero on its computed large-square boundary. -/
theorem eval_ne_zero_on_largeSquareBoundary
    {p : Polynomial QI} (hdegree : 0 < p.natDegree) {z : QI}
    (hz : OnSymmetricSquareBoundary (largeSquareRadius p) z) :
    p.eval z ≠ 0 := by
  have hdominated := lowerTermsValue_strictly_dominated hdegree hz
  rw [eval_eq_lowerTermsValue_add_leading]
  intro hzero
  have hlower :
      lowerTermsValue p z = -(p.leadingCoeff * z ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hzero
  rw [hlower, normSq_neg] at hdominated
  exact lt_irrefl _ hdominated

end FTA
