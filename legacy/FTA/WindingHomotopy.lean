import FTA.CauchyNoPole
import FTA.WindingProduct

/-!
# Finite winding homotopy foundations

The first result converts a strict-sign certificate for the real coordinate
of one polynomial edge into an endpoint-only formula for its doubled winding.
On a closed box the four endpoint terms cancel cyclically.  This is the
finite half-plane winding lemma used by the dominance homotopy and Rouché
transfer in Section 4 of the accompanying paper.
-/

namespace FTA.WindingHomotopy

open CCL
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.RationalPolynomialBounds
open FTA.PathPolynomial
open FTA.Sturm
open FTA.SturmTransducer
open FTA.CauchyProduct
open FTA.CauchyNoPole
open FTA.Winding

abbrev RatPolynomial := DensePolynomial ℚ

/-- If the first coordinate has a certified positive absolute lower bound,
inversion turns the edge Cauchy index into a difference of its two raw
endpoint quadrant jumps.  The inverted index is the constructive no-pole
case. -/
theorem cauchyIndex2_eq_endpointJumps_of_first_absLower
    (R S : RatPolynomial) {root : RationalInterval}
    (proper : root.Proper)
    (lower : IntervalAbsLowerCertificate R root) :
    cauchyIndex2 R S root.lower root.upper =
      (signJump 1 (R.eval root.lower * S.eval root.lower) : ℤ) -
        signJump 1 (R.eval root.upper * S.eval root.upper) := by
  have hlower : R.eval root.lower ≠ 0 := by
    intro hzero
    have hbound := lower.lower root.lower le_rfl proper.le
    rw [hzero, abs_zero] at hbound
    exact (not_lt_of_ge hbound) lower.positive
  have hupper : R.eval root.upper ≠ 0 := by
    intro hzero
    have hbound := lower.lower root.upper proper.le le_rfl
    rw [hzero, abs_zero] at hbound
    exact (not_lt_of_ge hbound) lower.positive
  have hR : R.isZero = false := isZero_false_of_eval_ne_zero hlower
  by_cases hS : S.isZero = false
  · have hinversion := cauchyIndex2_inversion R S
      root.lower root.upper hR hS
    have hnopole := cauchyIndex2_eq_zero_of_intervalAbsLower S R proper lower
    have hraw := pairVariationDifference2_eq_raw_product_jumps
      hR hS (Or.inl hlower) (Or.inl hupper)
    omega
  · have hSzero : S.isZero = true := by simpa using hS
    have hlowerZero := eval_eq_zero_of_isZero hSzero root.lower
    have hupperZero := eval_eq_zero_of_isZero hSzero root.upper
    simp [cauchyIndex2, hSzero, hlowerZero, hupperZero, signJump]

/-- Whole-cell strict-sign specialization of the absolute-lower-bound edge
formula. -/
theorem cauchyIndex2_eq_endpointJumps_of_first_intervalSign
    (R S : RatPolynomial) {root : RationalInterval}
    (proper : root.Proper)
    (sign : IntervalSignCertificate R root.lower root.upper) :
    cauchyIndex2 R S root.lower root.upper =
      (signJump 1 (R.eval root.lower * S.eval root.lower) : ℤ) -
        signJump 1 (R.eval root.upper * S.eval root.upper) :=
  cauchyIndex2_eq_endpointJumps_of_first_absLower R S proper
    (IntervalAbsLowerCertificate.ofIntervalSign sign)

/-- Real coordinate polynomial on a horizontal line, independent of the
oriented parameter endpoints used to package an edge. -/
def horizontalRealCoordinate (p : GaussianPolynomial) (y : ℚ) : RatPolynomial :=
  (pathReal p (horizontalBase y) horizontalDirection).normalize

/-- Imaginary coordinate polynomial on a horizontal line. -/
def horizontalImagCoordinate (p : GaussianPolynomial) (y : ℚ) : RatPolynomial :=
  (pathImag p (horizontalBase y) horizontalDirection).normalize

/-- Real coordinate polynomial on a vertical line. -/
def verticalRealCoordinate (p : GaussianPolynomial) (x : ℚ) : RatPolynomial :=
  (pathReal p (verticalBase x) verticalDirection).normalize

/-- Imaginary coordinate polynomial on a vertical line. -/
def verticalImagCoordinate (p : GaussianPolynomial) (x : ℚ) : RatPolynomial :=
  (pathImag p (verticalBase x) verticalDirection).normalize

@[simp] theorem horizontalRealCoordinate_eval
    (p : GaussianPolynomial) (y t : ℚ) :
    (horizontalRealCoordinate p y).eval t =
      (p.eval (CCL.GaussianRat.mk t y)).re := by
  simpa [horizontalRealCoordinate, horizontalEdge,
    PolynomialEdge.ofLine] using horizontalEdge_real_eval p y 0 0 t

@[simp] theorem horizontalImagCoordinate_eval
    (p : GaussianPolynomial) (y t : ℚ) :
    (horizontalImagCoordinate p y).eval t =
      (p.eval (CCL.GaussianRat.mk t y)).im := by
  simpa [horizontalImagCoordinate, horizontalEdge,
    PolynomialEdge.ofLine] using horizontalEdge_imag_eval p y 0 0 t

@[simp] theorem verticalRealCoordinate_eval
    (p : GaussianPolynomial) (x t : ℚ) :
    (verticalRealCoordinate p x).eval t =
      (p.eval (CCL.GaussianRat.mk x t)).re := by
  simpa [verticalRealCoordinate, verticalEdge,
    PolynomialEdge.ofLine] using verticalEdge_real_eval p x 0 0 t

@[simp] theorem verticalImagCoordinate_eval
    (p : GaussianPolynomial) (x t : ℚ) :
    (verticalImagCoordinate p x).eval t =
      (p.eval (CCL.GaussianRat.mk x t)).im := by
  simpa [verticalImagCoordinate, verticalEdge,
    PolynomialEdge.ofLine] using verticalEdge_imag_eval p x 0 0 t

/-! ## Quantitative dominance certificates -/

/-- A positive rational margin certifying `N(G) < N(F)` throughout one
closed rational parameter interval. -/
structure NormDominanceCertificate
    (A B C D : RatPolynomial) (root : RationalInterval) where
  margin : ℚ
  positive : 0 < margin
  lower : ∀ t : ℚ, root.lower ≤ t → t ≤ root.upper →
    margin ≤ A.eval t ^ 2 + B.eval t ^ 2 -
      (C.eval t ^ 2 + D.eval t ^ 2)

/-- Real coordinate of `conj(F) * (F + G)` for coordinate pairs
`F=A+iB` and `G=C+iD`. -/
def roucheReal (A B C D : RatPolynomial) : RatPolynomial :=
  productNumerator A (-B) (A + C) (B + D)

/-- Imaginary coordinate of `conj(F) * (F + G)`. -/
def roucheImag (A B C D : RatPolynomial) : RatPolynomial :=
  productDenominator A (-B) (A + C) (B + D)

@[simp] theorem eval_roucheReal
    (A B C D : RatPolynomial) (t : ℚ) :
    (roucheReal A B C D).eval t =
      A.eval t * (A.eval t + C.eval t) +
        B.eval t * (B.eval t + D.eval t) := by
  simp [roucheReal, productNumerator]

@[simp] theorem eval_roucheImag
    (A B C D : RatPolynomial) (t : ℚ) :
    (roucheImag A B C D).eval t =
      A.eval t * (B.eval t + D.eval t) -
        B.eval t * (A.eval t + C.eval t) := by
  simp [roucheImag, productDenominator]
  ring

/-- The dominance margin gives half that margin as a positive absolute lower
bound for the real coordinate of `conj(F) * (F + G)`.  Algebraically,
`2 Re(conj(F)(F+G)) = N(F)-N(G)+N(F+G)`. -/
def NormDominanceCertificate.roucheRealAbsLower
    {A B C D : RatPolynomial} {root : RationalInterval}
    (certificate : NormDominanceCertificate A B C D root) :
    IntervalAbsLowerCertificate (roucheReal A B C D) root where
  bound := certificate.margin / 2
  positive := div_pos certificate.positive (by norm_num)
  lower := by
    intro t hLower hUpper
    have hdominance := certificate.lower t hLower hUpper
    have hsumNonneg :
        0 ≤ (A.eval t + C.eval t) ^ 2 +
          (B.eval t + D.eval t) ^ 2 := by positivity
    have hreal : certificate.margin / 2 ≤
        (roucheReal A B C D).eval t := by
      rw [eval_roucheReal]
      nlinarith
    have hrealPos : 0 < (roucheReal A B C D).eval t :=
      (div_pos certificate.positive (by norm_num)).trans_le hreal
    rw [abs_of_pos hrealPos]
    exact hreal

/-- Dominance makes the first coordinate pair nonzero at every point of the
certified interval. -/
theorem NormDominanceCertificate.leftPair_ne_zero
    {A B C D : RatPolynomial} {root : RationalInterval}
    (certificate : NormDominanceCertificate A B C D root)
    {t : ℚ} (hLower : root.lower ≤ t) (hUpper : t ≤ root.upper) :
    A.eval t ≠ 0 ∨ B.eval t ≠ 0 := by
  by_contra hzero
  rw [not_or, not_ne_iff, not_ne_iff] at hzero
  have hdominance := certificate.lower t hLower hUpper
  rw [hzero.1, hzero.2] at hdominance
  nlinarith [sq_nonneg (C.eval t), sq_nonneg (D.eval t), certificate.positive]

/-- Dominance also makes `F+G` nonzero throughout the interval. -/
theorem NormDominanceCertificate.sumPair_ne_zero
    {A B C D : RatPolynomial} {root : RationalInterval}
    (certificate : NormDominanceCertificate A B C D root)
    {t : ℚ} (hLower : root.lower ≤ t) (hUpper : t ≤ root.upper) :
    A.eval t + C.eval t ≠ 0 ∨ B.eval t + D.eval t ≠ 0 := by
  by_contra hzero
  rw [not_or, not_ne_iff, not_ne_iff] at hzero
  have hdominance := certificate.lower t hLower hUpper
  have hC : C.eval t = -A.eval t := by linarith [hzero.1]
  have hD : D.eval t = -B.eval t := by linarith [hzero.2]
  rw [hC, hD] at hdominance
  nlinarith [certificate.positive]

/-- The complete finite auxiliary product formula applies to
`conj(F) * (F+G)` on either orientation between two points of a dominance
interval. -/
theorem NormDominanceCertificate.roucheAuxiliaryProductFormula
    {A B C D : RatPolynomial} {root : RationalInterval}
    (certificate : NormDominanceCertificate A B C D root)
    {a b : ℚ}
    (haLower : root.lower ≤ a) (haUpper : a ≤ root.upper)
    (hbLower : root.lower ≤ b) (hbUpper : b ≤ root.upper)
    (hab : a ≠ b) :
    AuxiliaryProductFormula A (-B) (A + C) (B + D) a b := by
  have hleftA : A.eval a ≠ 0 ∨ (-B).eval a ≠ 0 := by
    simpa using certificate.leftPair_ne_zero haLower haUpper
  have hrightA : A.eval b ≠ 0 ∨ (-B).eval b ≠ 0 := by
    simpa using certificate.leftPair_ne_zero hbLower hbUpper
  have hleftSum : (A + C).eval a ≠ 0 ∨ (B + D).eval a ≠ 0 := by
    simpa using certificate.sumPair_ne_zero haLower haUpper
  have hrightSum : (A + C).eval b ≠ 0 ∨ (B + D).eval b ≠ 0 := by
    simpa using certificate.sumPair_ne_zero hbLower hbUpper
  exact auxiliaryProductFormula_of_endpoint_nonzero_of_ne
    hleftA hleftSum hrightA hrightSum hab

/-- Conjugating one rational polynomial coordinate pair negates its complete
Cauchy index, including the identically-zero coordinate rows. -/
theorem cauchyIndex2_conjugate
    (A B : RatPolynomial) (a b : ℚ) :
    cauchyIndex2 A (-B) a b = -cauchyIndex2 A B a b := by
  by_cases hA : A.isZero = false
  · by_cases hB : B.isZero = false
    · exact cauchyIndex2_neg_denominator A B a b hA hB
    · have hBzero : B.isZero = true := by simpa using hB
      have hnegBzero : (-B).isZero = true := by simpa using hBzero
      simp [cauchyIndex2, hBzero, hnegBzero]
  · have hAzero : A.isZero = true := by simpa using hA
    simp [cauchyIndex2, hAzero]

/-- Horizontal real-coordinate extraction commutes exactly with dense
polynomial addition. -/
theorem horizontalRealCoordinate_add
    (p q : GaussianPolynomial) (y : ℚ) :
    horizontalRealCoordinate (p + q) y =
      horizontalRealCoordinate p y + horizontalRealCoordinate q y := by
  have hpoly : (horizontalRealCoordinate (p + q) y).toPolynomial =
      (horizontalRealCoordinate p y +
        horizontalRealCoordinate q y).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, horizontalRealCoordinate_eval, eval_add,
      CCL.GaussianRat.add_re]
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show (horizontalRealCoordinate (p + q) y).normalize =
      horizontalRealCoordinate (p + q) y by
    simp [horizontalRealCoordinate]] at h
  simpa only [normalize_add] using h

/-- Horizontal imaginary-coordinate extraction commutes with addition. -/
theorem horizontalImagCoordinate_add
    (p q : GaussianPolynomial) (y : ℚ) :
    horizontalImagCoordinate (p + q) y =
      horizontalImagCoordinate p y + horizontalImagCoordinate q y := by
  have hpoly : (horizontalImagCoordinate (p + q) y).toPolynomial =
      (horizontalImagCoordinate p y +
        horizontalImagCoordinate q y).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, horizontalImagCoordinate_eval, eval_add,
      CCL.GaussianRat.add_im]
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show (horizontalImagCoordinate (p + q) y).normalize =
      horizontalImagCoordinate (p + q) y by
    simp [horizontalImagCoordinate]] at h
  simpa only [normalize_add] using h

/-- Vertical real-coordinate extraction commutes with addition. -/
theorem verticalRealCoordinate_add
    (p q : GaussianPolynomial) (x : ℚ) :
    verticalRealCoordinate (p + q) x =
      verticalRealCoordinate p x + verticalRealCoordinate q x := by
  have hpoly : (verticalRealCoordinate (p + q) x).toPolynomial =
      (verticalRealCoordinate p x +
        verticalRealCoordinate q x).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, verticalRealCoordinate_eval, eval_add,
      CCL.GaussianRat.add_re]
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show (verticalRealCoordinate (p + q) x).normalize =
      verticalRealCoordinate (p + q) x by
    simp [verticalRealCoordinate]] at h
  simpa only [normalize_add] using h

/-- Vertical imaginary-coordinate extraction commutes with addition. -/
theorem verticalImagCoordinate_add
    (p q : GaussianPolynomial) (x : ℚ) :
    verticalImagCoordinate (p + q) x =
      verticalImagCoordinate p x + verticalImagCoordinate q x := by
  have hpoly : (verticalImagCoordinate (p + q) x).toPolynomial =
      (verticalImagCoordinate p x +
        verticalImagCoordinate q x).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, verticalImagCoordinate_eval, eval_add,
      CCL.GaussianRat.add_im]
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show (verticalImagCoordinate (p + q) x).normalize =
      verticalImagCoordinate (p + q) x by
    simp [verticalImagCoordinate]] at h
  simpa only [normalize_add] using h

/-- Horizontal real coordinate polynomials respect exact sparse polynomial
identity. -/
theorem horizontalRealCoordinate_congr
    {p q : GaussianPolynomial} (h : p.toPolynomial = q.toPolynomial) (y : ℚ) :
    horizontalRealCoordinate p y = horizontalRealCoordinate q y := by
  have eval_identity (z : QI) : p.eval z = q.eval z := by
    rw [← eval_toPolynomial, ← eval_toPolynomial, h]
  have hpoly : (horizontalRealCoordinate p y).toPolynomial =
      (horizontalRealCoordinate q y).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, horizontalRealCoordinate_eval, eval_identity]
  have heq := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [horizontalRealCoordinate] using heq

/-- Horizontal imaginary coordinate extensionality. -/
theorem horizontalImagCoordinate_congr
    {p q : GaussianPolynomial} (h : p.toPolynomial = q.toPolynomial) (y : ℚ) :
    horizontalImagCoordinate p y = horizontalImagCoordinate q y := by
  have eval_identity (z : QI) : p.eval z = q.eval z := by
    rw [← eval_toPolynomial, ← eval_toPolynomial, h]
  have hpoly : (horizontalImagCoordinate p y).toPolynomial =
      (horizontalImagCoordinate q y).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, horizontalImagCoordinate_eval, eval_identity]
  have heq := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [horizontalImagCoordinate] using heq

/-- Vertical real coordinate extensionality. -/
theorem verticalRealCoordinate_congr
    {p q : GaussianPolynomial} (h : p.toPolynomial = q.toPolynomial) (x : ℚ) :
    verticalRealCoordinate p x = verticalRealCoordinate q x := by
  have eval_identity (z : QI) : p.eval z = q.eval z := by
    rw [← eval_toPolynomial, ← eval_toPolynomial, h]
  have hpoly : (verticalRealCoordinate p x).toPolynomial =
      (verticalRealCoordinate q x).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, verticalRealCoordinate_eval, eval_identity]
  have heq := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [verticalRealCoordinate] using heq

/-- Vertical imaginary coordinate extensionality. -/
theorem verticalImagCoordinate_congr
    {p q : GaussianPolynomial} (h : p.toPolynomial = q.toPolynomial) (x : ℚ) :
    verticalImagCoordinate p x = verticalImagCoordinate q x := by
  have eval_identity (z : QI) : p.eval z = q.eval z := by
    rw [← eval_toPolynomial, ← eval_toPolynomial, h]
  have hpoly : (verticalImagCoordinate p x).toPolynomial =
      (verticalImagCoordinate q x).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    simp only [eval_toPolynomial, verticalImagCoordinate_eval, eval_identity]
  have heq := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [verticalImagCoordinate] using heq

/-- The raw closed-box winding depends only on the exact sparse polynomial,
not on the dense coefficient-list representative. -/
theorem quadrupledBoxWinding_congr
    {p q : GaussianPolynomial} (B : CCL.RatBox)
    (h : p.toPolynomial = q.toPolynomial) :
    quadrupledBoxWinding p B = quadrupledBoxWinding q B := by
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq]
  change cauchyIndex2 (horizontalRealCoordinate p B.yLower)
        (horizontalImagCoordinate p B.yLower) B.xLower B.xUpper +
      cauchyIndex2 (verticalRealCoordinate p B.xUpper)
        (verticalImagCoordinate p B.xUpper) B.yLower B.yUpper +
      cauchyIndex2 (horizontalRealCoordinate p B.yUpper)
        (horizontalImagCoordinate p B.yUpper) B.xUpper B.xLower +
      cauchyIndex2 (verticalRealCoordinate p B.xLower)
        (verticalImagCoordinate p B.xLower) B.yUpper B.yLower =
    cauchyIndex2 (horizontalRealCoordinate q B.yLower)
        (horizontalImagCoordinate q B.yLower) B.xLower B.xUpper +
      cauchyIndex2 (verticalRealCoordinate q B.xUpper)
        (verticalImagCoordinate q B.xUpper) B.yLower B.yUpper +
      cauchyIndex2 (horizontalRealCoordinate q B.yUpper)
        (horizontalImagCoordinate q B.yUpper) B.xUpper B.xLower +
      cauchyIndex2 (verticalRealCoordinate q B.xLower)
        (verticalImagCoordinate q B.xLower) B.yUpper B.yLower
  rw [horizontalRealCoordinate_congr h,
    horizontalImagCoordinate_congr h,
    verticalRealCoordinate_congr h, verticalImagCoordinate_congr h,
    horizontalRealCoordinate_congr h,
    horizontalImagCoordinate_congr h,
    verticalRealCoordinate_congr h, verticalImagCoordinate_congr h]

/-! ## Finite dominance transfer -/

/-- Lemma 4.6 / finite Rouché transfer at the raw closed-box normalization.
Four positive rational norm margins certify `N(q) < N(p)` on the boundary.
The path `conj(p) * (p+q)` then has a coefficient-explicit positive real
lower bound.  Its endpoint-only half-plane winding is zero, while the complete
auxiliary product formulas and conjugation identify that zero with
`-Wind(p)+Wind(p+q)`. -/
theorem quadrupledBoxWinding_add_of_normDominance
    (p q : GaussianPolynomial) (B : CCL.RatBox)
    (bottom : NormDominanceCertificate
      (horizontalRealCoordinate p B.yLower)
      (horizontalImagCoordinate p B.yLower)
      (horizontalRealCoordinate q B.yLower)
      (horizontalImagCoordinate q B.yLower)
      ⟨B.xLower, B.xUpper⟩)
    (right : NormDominanceCertificate
      (verticalRealCoordinate p B.xUpper)
      (verticalImagCoordinate p B.xUpper)
      (verticalRealCoordinate q B.xUpper)
      (verticalImagCoordinate q B.xUpper)
      ⟨B.yLower, B.yUpper⟩)
    (top : NormDominanceCertificate
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      (horizontalRealCoordinate q B.yUpper)
      (horizontalImagCoordinate q B.yUpper)
      ⟨B.xLower, B.xUpper⟩)
    (left : NormDominanceCertificate
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      (verticalRealCoordinate q B.xLower)
      (verticalImagCoordinate q B.xLower)
      ⟨B.yLower, B.yUpper⟩)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding (p + q) B = quadrupledBoxWinding p B := by
  have hbottomHalf := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (roucheReal
      (horizontalRealCoordinate p B.yLower)
      (horizontalImagCoordinate p B.yLower)
      (horizontalRealCoordinate q B.yLower)
      (horizontalImagCoordinate q B.yLower))
    (roucheImag
      (horizontalRealCoordinate p B.yLower)
      (horizontalImagCoordinate p B.yLower)
      (horizontalRealCoordinate q B.yLower)
      (horizontalImagCoordinate q B.yLower))
    (root := ⟨B.xLower, B.xUpper⟩)
    hx bottom.roucheRealAbsLower
  have hrightHalf := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (roucheReal
      (verticalRealCoordinate p B.xUpper)
      (verticalImagCoordinate p B.xUpper)
      (verticalRealCoordinate q B.xUpper)
      (verticalImagCoordinate q B.xUpper))
    (roucheImag
      (verticalRealCoordinate p B.xUpper)
      (verticalImagCoordinate p B.xUpper)
      (verticalRealCoordinate q B.xUpper)
      (verticalImagCoordinate q B.xUpper))
    (root := ⟨B.yLower, B.yUpper⟩)
    hy right.roucheRealAbsLower
  have htopHalfForward := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (roucheReal
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      (horizontalRealCoordinate q B.yUpper)
      (horizontalImagCoordinate q B.yUpper))
    (roucheImag
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      (horizontalRealCoordinate q B.yUpper)
      (horizontalImagCoordinate q B.yUpper))
    (root := ⟨B.xLower, B.xUpper⟩)
    hx top.roucheRealAbsLower
  have hleftHalfForward := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (roucheReal
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      (verticalRealCoordinate q B.xLower)
      (verticalImagCoordinate q B.xLower))
    (roucheImag
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      (verticalRealCoordinate q B.xLower)
      (verticalImagCoordinate q B.xLower))
    (root := ⟨B.yLower, B.yUpper⟩)
    hy left.roucheRealAbsLower
  have htopHalfReverse := cauchyIndex2_reverse
    (roucheReal
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      (horizontalRealCoordinate q B.yUpper)
      (horizontalImagCoordinate q B.yUpper))
    (roucheImag
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      (horizontalRealCoordinate q B.yUpper)
      (horizontalImagCoordinate q B.yUpper))
    B.xLower B.xUpper
  have hleftHalfReverse := cauchyIndex2_reverse
    (roucheReal
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      (verticalRealCoordinate q B.xLower)
      (verticalImagCoordinate q B.xLower))
    (roucheImag
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      (verticalRealCoordinate q B.xLower)
      (verticalImagCoordinate q B.xLower))
    B.yLower B.yUpper
  have hroucheSum :
      cauchyIndex2
          (roucheReal
            (horizontalRealCoordinate p B.yLower)
            (horizontalImagCoordinate p B.yLower)
            (horizontalRealCoordinate q B.yLower)
            (horizontalImagCoordinate q B.yLower))
          (roucheImag
            (horizontalRealCoordinate p B.yLower)
            (horizontalImagCoordinate p B.yLower)
            (horizontalRealCoordinate q B.yLower)
            (horizontalImagCoordinate q B.yLower))
          B.xLower B.xUpper +
        cauchyIndex2
          (roucheReal
            (verticalRealCoordinate p B.xUpper)
            (verticalImagCoordinate p B.xUpper)
            (verticalRealCoordinate q B.xUpper)
            (verticalImagCoordinate q B.xUpper))
          (roucheImag
            (verticalRealCoordinate p B.xUpper)
            (verticalImagCoordinate p B.xUpper)
            (verticalRealCoordinate q B.xUpper)
            (verticalImagCoordinate q B.xUpper))
          B.yLower B.yUpper +
        cauchyIndex2
          (roucheReal
            (horizontalRealCoordinate p B.yUpper)
            (horizontalImagCoordinate p B.yUpper)
            (horizontalRealCoordinate q B.yUpper)
            (horizontalImagCoordinate q B.yUpper))
          (roucheImag
            (horizontalRealCoordinate p B.yUpper)
            (horizontalImagCoordinate p B.yUpper)
            (horizontalRealCoordinate q B.yUpper)
            (horizontalImagCoordinate q B.yUpper))
          B.xUpper B.xLower +
        cauchyIndex2
          (roucheReal
            (verticalRealCoordinate p B.xLower)
            (verticalImagCoordinate p B.xLower)
            (verticalRealCoordinate q B.xLower)
            (verticalImagCoordinate q B.xLower))
          (roucheImag
            (verticalRealCoordinate p B.xLower)
            (verticalImagCoordinate p B.xLower)
            (verticalRealCoordinate q B.xLower)
            (verticalImagCoordinate q B.xLower))
          B.yUpper B.yLower = 0 := by
    have htopForward' := htopHalfForward
    have hleftForward' := hleftHalfForward
    rw [hbottomHalf, hrightHalf]
    rw [htopHalfReverse, hleftHalfReverse]
    rw [htopForward', hleftForward']
    simp only [eval_roucheReal, eval_roucheImag,
      horizontalRealCoordinate_eval, horizontalImagCoordinate_eval,
      verticalRealCoordinate_eval, verticalImagCoordinate_eval]
    ring
  have hbottomProduct := bottom.roucheAuxiliaryProductFormula
    le_rfl hx.le hx.le le_rfl hx.ne
  have hrightProduct := right.roucheAuxiliaryProductFormula
    le_rfl hy.le hy.le le_rfl hy.ne
  have htopProduct := top.roucheAuxiliaryProductFormula
    hx.le le_rfl le_rfl hx.le hx.ne'
  have hleftProduct := left.roucheAuxiliaryProductFormula
    hy.le le_rfl le_rfl hy.le hy.ne'
  rw [AuxiliaryProductFormula] at hbottomProduct hrightProduct htopProduct hleftProduct
  simp only [roucheReal, roucheImag] at hroucheSum
  have hproductSum :
      (cauchyIndex2
          (horizontalRealCoordinate p B.yLower)
          (-(horizontalImagCoordinate p B.yLower)) B.xLower B.xUpper +
        cauchyIndex2
          (verticalRealCoordinate p B.xUpper)
          (-(verticalImagCoordinate p B.xUpper)) B.yLower B.yUpper +
        cauchyIndex2
          (horizontalRealCoordinate p B.yUpper)
          (-(horizontalImagCoordinate p B.yUpper)) B.xUpper B.xLower +
        cauchyIndex2
          (verticalRealCoordinate p B.xLower)
          (-(verticalImagCoordinate p B.xLower)) B.yUpper B.yLower) +
      (cauchyIndex2
          (horizontalRealCoordinate p B.yLower +
            horizontalRealCoordinate q B.yLower)
          (horizontalImagCoordinate p B.yLower +
            horizontalImagCoordinate q B.yLower) B.xLower B.xUpper +
        cauchyIndex2
          (verticalRealCoordinate p B.xUpper +
            verticalRealCoordinate q B.xUpper)
          (verticalImagCoordinate p B.xUpper +
            verticalImagCoordinate q B.xUpper) B.yLower B.yUpper +
        cauchyIndex2
          (horizontalRealCoordinate p B.yUpper +
            horizontalRealCoordinate q B.yUpper)
          (horizontalImagCoordinate p B.yUpper +
            horizontalImagCoordinate q B.yUpper) B.xUpper B.xLower +
        cauchyIndex2
          (verticalRealCoordinate p B.xLower +
            verticalRealCoordinate q B.xLower)
          (verticalImagCoordinate p B.xLower +
            verticalImagCoordinate q B.xLower) B.yUpper B.yLower) = 0 := by
    simp only [auxiliaryEndpointCorrection2_eq_signJump, eval_neg, eval_add,
      horizontalRealCoordinate_eval, horizontalImagCoordinate_eval,
      verticalRealCoordinate_eval, verticalImagCoordinate_eval] at hbottomProduct hrightProduct htopProduct hleftProduct
    omega
  have hconjugateSum :
      cauchyIndex2
          (horizontalRealCoordinate p B.yLower)
          (-(horizontalImagCoordinate p B.yLower)) B.xLower B.xUpper +
        cauchyIndex2
          (verticalRealCoordinate p B.xUpper)
          (-(verticalImagCoordinate p B.xUpper)) B.yLower B.yUpper +
        cauchyIndex2
          (horizontalRealCoordinate p B.yUpper)
          (-(horizontalImagCoordinate p B.yUpper)) B.xUpper B.xLower +
        cauchyIndex2
          (verticalRealCoordinate p B.xLower)
          (-(verticalImagCoordinate p B.xLower)) B.yUpper B.yLower =
      -quadrupledBoxWinding p B := by
    rw [quadrupledBoxWinding_eq]
    change _ = -(cauchyIndex2
        (horizontalRealCoordinate p B.yLower)
          (horizontalImagCoordinate p B.yLower) B.xLower B.xUpper +
      cauchyIndex2
        (verticalRealCoordinate p B.xUpper)
          (verticalImagCoordinate p B.xUpper) B.yLower B.yUpper +
      cauchyIndex2
        (horizontalRealCoordinate p B.yUpper)
          (horizontalImagCoordinate p B.yUpper) B.xUpper B.xLower +
      cauchyIndex2
        (verticalRealCoordinate p B.xLower)
          (verticalImagCoordinate p B.xLower) B.yUpper B.yLower)
    rw [cauchyIndex2_conjugate, cauchyIndex2_conjugate,
      cauchyIndex2_conjugate, cauchyIndex2_conjugate]
    ring
  have haddCoordinateSum :
      cauchyIndex2
          (horizontalRealCoordinate p B.yLower +
            horizontalRealCoordinate q B.yLower)
          (horizontalImagCoordinate p B.yLower +
            horizontalImagCoordinate q B.yLower) B.xLower B.xUpper +
        cauchyIndex2
          (verticalRealCoordinate p B.xUpper +
            verticalRealCoordinate q B.xUpper)
          (verticalImagCoordinate p B.xUpper +
            verticalImagCoordinate q B.xUpper) B.yLower B.yUpper +
        cauchyIndex2
          (horizontalRealCoordinate p B.yUpper +
            horizontalRealCoordinate q B.yUpper)
          (horizontalImagCoordinate p B.yUpper +
            horizontalImagCoordinate q B.yUpper) B.xUpper B.xLower +
        cauchyIndex2
          (verticalRealCoordinate p B.xLower +
            verticalRealCoordinate q B.xLower)
          (verticalImagCoordinate p B.xLower +
            verticalImagCoordinate q B.xLower) B.yUpper B.yLower =
      quadrupledBoxWinding (p + q) B := by
    rw [quadrupledBoxWinding_eq]
    change _ = cauchyIndex2
        (horizontalRealCoordinate (p + q) B.yLower)
          (horizontalImagCoordinate (p + q) B.yLower) B.xLower B.xUpper +
      cauchyIndex2
        (verticalRealCoordinate (p + q) B.xUpper)
          (verticalImagCoordinate (p + q) B.xUpper) B.yLower B.yUpper +
      cauchyIndex2
        (horizontalRealCoordinate (p + q) B.yUpper)
          (horizontalImagCoordinate (p + q) B.yUpper) B.xUpper B.xLower +
      cauchyIndex2
        (verticalRealCoordinate (p + q) B.xLower)
          (verticalImagCoordinate (p + q) B.xLower) B.yUpper B.yLower
    rw [horizontalRealCoordinate_add, horizontalImagCoordinate_add,
      verticalRealCoordinate_add, verticalImagCoordinate_add,
      horizontalRealCoordinate_add, horizontalImagCoordinate_add,
      verticalRealCoordinate_add, verticalImagCoordinate_add]
  rw [hconjugateSum, haddCoordinateSum] at hproductSum
  omega

/-- A polynomial image whose real coordinate has a certified positive
absolute lower bound along all four box edges has zero raw closed winding.
Each edge reduces to two endpoint jumps; the four shared-vertex terms cancel
exactly. -/
theorem quadrupledBoxWinding_eq_zero_of_real_absLower
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (bottomLower : IntervalAbsLowerCertificate
      (horizontalRealCoordinate p B.yLower) ⟨B.xLower, B.xUpper⟩)
    (rightLower : IntervalAbsLowerCertificate
      (verticalRealCoordinate p B.xUpper) ⟨B.yLower, B.yUpper⟩)
    (topLower : IntervalAbsLowerCertificate
      (horizontalRealCoordinate p B.yUpper) ⟨B.xLower, B.xUpper⟩)
    (leftLower : IntervalAbsLowerCertificate
      (verticalRealCoordinate p B.xLower) ⟨B.yLower, B.yUpper⟩)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding p B = 0 := by
  have hbottom := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (horizontalRealCoordinate p B.yLower)
    (horizontalImagCoordinate p B.yLower)
    (root := ⟨B.xLower, B.xUpper⟩) hx bottomLower
  have hright := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (verticalRealCoordinate p B.xUpper)
    (verticalImagCoordinate p B.xUpper)
    (root := ⟨B.yLower, B.yUpper⟩) hy rightLower
  have htopForward := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (horizontalRealCoordinate p B.yUpper)
    (horizontalImagCoordinate p B.yUpper)
    (root := ⟨B.xLower, B.xUpper⟩) hx topLower
  have hleftForward := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (verticalRealCoordinate p B.xLower)
    (verticalImagCoordinate p B.xLower)
    (root := ⟨B.yLower, B.yUpper⟩) hy leftLower
  have htopReverse := cauchyIndex2_reverse
    (horizontalRealCoordinate p B.yUpper)
    (horizontalImagCoordinate p B.yUpper)
    B.xLower B.xUpper
  have hleftReverse := cauchyIndex2_reverse
    (verticalRealCoordinate p B.xLower)
    (verticalImagCoordinate p B.xLower)
    B.yLower B.yUpper
  have htopForward' : cauchyIndex2
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper) B.xLower B.xUpper =
      (signJump 1 ((horizontalRealCoordinate p B.yUpper).eval B.xLower *
          (horizontalImagCoordinate p B.yUpper).eval B.xLower) : ℤ) -
        signJump 1 ((horizontalRealCoordinate p B.yUpper).eval B.xUpper *
          (horizontalImagCoordinate p B.yUpper).eval B.xUpper) := by
    simpa using htopForward
  have hleftForward' : cauchyIndex2
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower) B.yLower B.yUpper =
      (signJump 1 ((verticalRealCoordinate p B.xLower).eval B.yLower *
          (verticalImagCoordinate p B.xLower).eval B.yLower) : ℤ) -
        signJump 1 ((verticalRealCoordinate p B.xLower).eval B.yUpper *
          (verticalImagCoordinate p B.xLower).eval B.yUpper) := by
    simpa using hleftForward
  have htop : cauchyIndex2
      (horizontalRealCoordinate p B.yUpper)
      (horizontalImagCoordinate p B.yUpper)
      B.xUpper B.xLower =
      (signJump 1 ((horizontalRealCoordinate p B.yUpper).eval B.xUpper *
          (horizontalImagCoordinate p B.yUpper).eval B.xUpper) : ℤ) -
        signJump 1 ((horizontalRealCoordinate p B.yUpper).eval B.xLower *
          (horizontalImagCoordinate p B.yUpper).eval B.xLower) := by
    omega
  have hleft : cauchyIndex2
      (verticalRealCoordinate p B.xLower)
      (verticalImagCoordinate p B.xLower)
      B.yUpper B.yLower =
      (signJump 1 ((verticalRealCoordinate p B.xLower).eval B.yUpper *
          (verticalImagCoordinate p B.xLower).eval B.yUpper) : ℤ) -
        signJump 1 ((verticalRealCoordinate p B.xLower).eval B.yLower *
          (verticalImagCoordinate p B.xLower).eval B.yLower) := by
    omega
  rw [quadrupledBoxWinding_eq]
  change cauchyIndex2 (horizontalRealCoordinate p B.yLower)
        (horizontalImagCoordinate p B.yLower) B.xLower B.xUpper +
      cauchyIndex2 (verticalRealCoordinate p B.xUpper)
        (verticalImagCoordinate p B.xUpper) B.yLower B.yUpper +
      cauchyIndex2 (horizontalRealCoordinate p B.yUpper)
        (horizontalImagCoordinate p B.yUpper) B.xUpper B.xLower +
      cauchyIndex2 (verticalRealCoordinate p B.xLower)
        (verticalImagCoordinate p B.xLower) B.yUpper B.yLower = 0
  rw [hbottom, hright, htop, hleft]
  simp only [horizontalRealCoordinate_eval, horizontalImagCoordinate_eval,
    verticalRealCoordinate_eval, verticalImagCoordinate_eval]
  ring

/-- A polynomial image whose imaginary coordinate has a certified positive
absolute lower bound along all four box edges has zero raw closed winding.
Here every forward edge is the constructive no-pole case, and reversing the
top and left zero indices preserves zero. -/
theorem quadrupledBoxWinding_eq_zero_of_imag_absLower
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (bottomLower : IntervalAbsLowerCertificate
      (horizontalImagCoordinate p B.yLower) ⟨B.xLower, B.xUpper⟩)
    (rightLower : IntervalAbsLowerCertificate
      (verticalImagCoordinate p B.xUpper) ⟨B.yLower, B.yUpper⟩)
    (topLower : IntervalAbsLowerCertificate
      (horizontalImagCoordinate p B.yUpper) ⟨B.xLower, B.xUpper⟩)
    (leftLower : IntervalAbsLowerCertificate
      (verticalImagCoordinate p B.xLower) ⟨B.yLower, B.yUpper⟩)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding p B = 0 := by
  have hbottom := cauchyIndex2_eq_zero_of_intervalAbsLower
    (horizontalRealCoordinate p B.yLower)
    (horizontalImagCoordinate p B.yLower)
    (root := ⟨B.xLower, B.xUpper⟩) hx bottomLower
  have hright := cauchyIndex2_eq_zero_of_intervalAbsLower
    (verticalRealCoordinate p B.xUpper)
    (verticalImagCoordinate p B.xUpper)
    (root := ⟨B.yLower, B.yUpper⟩) hy rightLower
  have htopForward := cauchyIndex2_eq_zero_of_intervalAbsLower
    (horizontalRealCoordinate p B.yUpper)
    (horizontalImagCoordinate p B.yUpper)
    (root := ⟨B.xLower, B.xUpper⟩) hx topLower
  have hleftForward := cauchyIndex2_eq_zero_of_intervalAbsLower
    (verticalRealCoordinate p B.xLower)
    (verticalImagCoordinate p B.xLower)
    (root := ⟨B.yLower, B.yUpper⟩) hy leftLower
  have htopReverse := cauchyIndex2_reverse
    (horizontalRealCoordinate p B.yUpper)
    (horizontalImagCoordinate p B.yUpper)
    B.xLower B.xUpper
  have hleftReverse := cauchyIndex2_reverse
    (verticalRealCoordinate p B.xLower)
    (verticalImagCoordinate p B.xLower)
    B.yLower B.yUpper
  rw [htopForward] at htopReverse
  rw [hleftForward] at hleftReverse
  rw [quadrupledBoxWinding_eq]
  change cauchyIndex2 (horizontalRealCoordinate p B.yLower)
        (horizontalImagCoordinate p B.yLower) B.xLower B.xUpper +
      cauchyIndex2 (verticalRealCoordinate p B.xUpper)
        (verticalImagCoordinate p B.xUpper) B.yLower B.yUpper +
      cauchyIndex2 (horizontalRealCoordinate p B.yUpper)
        (horizontalImagCoordinate p B.yUpper) B.xUpper B.xLower +
      cauchyIndex2 (verticalRealCoordinate p B.xLower)
        (verticalImagCoordinate p B.xLower) B.yUpper B.yLower = 0
  rw [hbottom, hright, htopReverse, hleftReverse]
  omega

/-- Lemma 4.5 in raw normalization: a polynomial image whose real coordinate
has certified strict sign along all four box edges has zero closed winding. -/
theorem quadrupledBoxWinding_eq_zero_of_real_sign
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (bottomSign : IntervalSignCertificate
      (horizontalRealCoordinate p B.yLower) B.xLower B.xUpper)
    (rightSign : IntervalSignCertificate
      (verticalRealCoordinate p B.xUpper) B.yLower B.yUpper)
    (topSign : IntervalSignCertificate
      (horizontalRealCoordinate p B.yUpper) B.xLower B.xUpper)
    (leftSign : IntervalSignCertificate
      (verticalRealCoordinate p B.xLower) B.yLower B.yUpper)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    quadrupledBoxWinding p B = 0 :=
  quadrupledBoxWinding_eq_zero_of_real_absLower p B
    (IntervalAbsLowerCertificate.ofIntervalSign bottomSign)
    (IntervalAbsLowerCertificate.ofIntervalSign rightSign)
    (IntervalAbsLowerCertificate.ofIntervalSign topSign)
    (IntervalAbsLowerCertificate.ofIntervalSign leftSign) hx hy

/-- Both normalized winding conventions inherit the half-plane zero. -/
theorem normalizedBoxWinding_eq_zero_of_real_sign
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (bottomSign : IntervalSignCertificate
      (horizontalRealCoordinate p B.yLower) B.xLower B.xUpper)
    (rightSign : IntervalSignCertificate
      (verticalRealCoordinate p B.xUpper) B.yLower B.yUpper)
    (topSign : IntervalSignCertificate
      (horizontalRealCoordinate p B.yUpper) B.xLower B.xUpper)
    (leftSign : IntervalSignCertificate
      (verticalRealCoordinate p B.xLower) B.yLower B.yUpper)
    (hx : B.xLower < B.xUpper) (hy : B.yLower < B.yUpper) :
    doubledBoxWinding p B = 0 ∧ boxWinding p B = 0 := by
  have hraw := quadrupledBoxWinding_eq_zero_of_real_sign
    p B bottomSign rightSign topSign leftSign hx hy
  simp [doubledBoxWinding, boxWinding, hraw]

end FTA.WindingHomotopy
