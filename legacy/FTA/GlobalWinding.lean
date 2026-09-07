import FTA.LargeSquare
import FTA.WindingHomotopy

/-!
# Global winding on the coefficient-computed large square

This module bridges the sparse coefficient estimate from `FTA.LargeSquare`
to the executable dense-polynomial winding API.  It constructs the exact
rational box used in Section 6 of the finite constructive FTA paper and
packages its strict geometry and four boundary-vertex nonvanishing proofs.
-/

namespace FTA.GlobalWinding

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Sturm
open FTA.Winding
open FTA.CauchyProduct
open FTA.CauchyNoPole
open FTA.WindingProduct
open FTA.WindingHomotopy

/-- Executable dense coefficient weight corresponding exactly to
`lowerCoefficientWeight` on the sparse specification. -/
def denseLowerCoefficientWeight (p : GaussianPolynomial) : ℚ :=
  (p.natDegree : ℚ) *
    ∑ k ∈ Finset.range p.natDegree,
      normSq (p.coeffs.reverse.getD k 0) * (2 : ℚ) ^ k

/-- Executable coefficient-derived large-square radius.  Unlike the sparse
specification bridge, this definition runs directly on the finite dense
coefficient list. -/
def denseLargeSquareRadius (p : GaussianPolynomial) : ℚ :=
  max 1 (denseLowerCoefficientWeight p / normSq p.leadingCoeff + 1)

/-- The dense computed radius is at least one. -/
theorem one_le_denseLargeSquareRadius (p : GaussianPolynomial) :
    1 ≤ denseLargeSquareRadius p :=
  le_max_left _ _

/-- Hence the executable dense radius is strictly positive. -/
theorem denseLargeSquareRadius_pos (p : GaussianPolynomial) :
    0 < denseLargeSquareRadius p :=
  zero_lt_one.trans_le (one_le_denseLargeSquareRadius p)

/-- The executable dense weight agrees exactly with the sparse specification
for every nonzero polynomial. -/
theorem denseLowerCoefficientWeight_eq
    {p : GaussianPolynomial} (hp : p.isZero = false) :
    denseLowerCoefficientWeight p = lowerCoefficientWeight p.toPolynomial := by
  simp only [denseLowerCoefficientWeight, lowerCoefficientWeight,
    natDegree_toPolynomial hp, coeff_toPolynomial]

/-- The executable radius is extensionally the radius used by the proved
large-square coefficient estimate. -/
theorem denseLargeSquareRadius_eq
    {p : GaussianPolynomial} (hp : p.isZero = false) :
    denseLargeSquareRadius p = largeSquareRadius p.toPolynomial := by
  rw [denseLargeSquareRadius, largeSquareRadius,
    denseLowerCoefficientWeight_eq hp, leadingCoeff_toPolynomial hp]

/-- The symmetric rational box at the coefficient-computed dominance
radius. -/
def largeSquareBox (p : GaussianPolynomial) : CCL.RatBox :=
  CCL.RatBox.symmetric (denseLargeSquareRadius p)
    (denseLargeSquareRadius_pos p).le

/-- Positive dense natural degree rules out the executable zero
representation. -/
theorem isZero_false_of_natDegree_pos {p : GaussianPolynomial}
    (hdegree : 0 < p.natDegree) : p.isZero = false := by
  cases hzero : p.isZero with
  | false => rfl
  | true =>
      have hcount := degreeCount_eq_zero_of_isZero hzero
      rw [natDegree, hcount] at hdegree
      omega

/-- The computed large square has two strict positive side lengths. -/
theorem largeSquareBox_strict (p : GaussianPolynomial) :
    (largeSquareBox p).xLower < (largeSquareBox p).xUpper ∧
      (largeSquareBox p).yLower < (largeSquareBox p).yUpper := by
  have hR := denseLargeSquareRadius_pos p
  simp only [largeSquareBox, CCL.RatBox.symmetric]
  constructor <;> linarith

private theorem lowerLeft_on_boundary (p : GaussianPolynomial) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xLower
        (largeSquareBox p).yLower) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simp [largeSquareBox, CCL.RatBox.symmetric,
    hR,
    OnSymmetricSquareBoundary]

private theorem lowerRight_on_boundary (p : GaussianPolynomial) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xUpper
        (largeSquareBox p).yLower) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simp [largeSquareBox, CCL.RatBox.symmetric,
    hR,
    OnSymmetricSquareBoundary]

private theorem upperRight_on_boundary (p : GaussianPolynomial) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xUpper
        (largeSquareBox p).yUpper) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simp [largeSquareBox, CCL.RatBox.symmetric,
    hR,
    OnSymmetricSquareBoundary]

private theorem upperLeft_on_boundary (p : GaussianPolynomial) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xLower
        (largeSquareBox p).yUpper) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simp [largeSquareBox, CCL.RatBox.symmetric,
    hR,
    OnSymmetricSquareBoundary]

/-- Every point on the bottom edge of the executable large square satisfies
the sparse boundary predicate. -/
theorem bottom_on_denseLargeSquareBoundary
    (p : GaussianPolynomial) {t : ℚ}
    (hLower : (largeSquareBox p).xLower ≤ t)
    (hUpper : t ≤ (largeSquareBox p).xUpper) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk t (largeSquareBox p).yLower) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simpa [largeSquareBox, CCL.RatBox.symmetric, hR,
    OnSymmetricSquareBoundary] using And.intro hLower hUpper

/-- Every point on the top edge satisfies the same boundary predicate. -/
theorem top_on_denseLargeSquareBoundary
    (p : GaussianPolynomial) {t : ℚ}
    (hLower : (largeSquareBox p).xLower ≤ t)
    (hUpper : t ≤ (largeSquareBox p).xUpper) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk t (largeSquareBox p).yUpper) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simpa [largeSquareBox, CCL.RatBox.symmetric, hR,
    OnSymmetricSquareBoundary] using And.intro hLower hUpper

/-- Every point on the right edge satisfies the large-square boundary
predicate. -/
theorem right_on_denseLargeSquareBoundary
    (p : GaussianPolynomial) {t : ℚ}
    (hLower : (largeSquareBox p).yLower ≤ t)
    (hUpper : t ≤ (largeSquareBox p).yUpper) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xUpper t) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simpa [largeSquareBox, CCL.RatBox.symmetric, hR,
    OnSymmetricSquareBoundary] using And.intro hLower hUpper

/-- Every point on the left edge satisfies the large-square boundary
predicate. -/
theorem left_on_denseLargeSquareBoundary
    (p : GaussianPolynomial) {t : ℚ}
    (hLower : (largeSquareBox p).yLower ≤ t)
    (hUpper : t ≤ (largeSquareBox p).yUpper) :
    OnSymmetricSquareBoundary (denseLargeSquareRadius p)
      (CCL.GaussianRat.mk (largeSquareBox p).xLower t) := by
  have hR := (denseLargeSquareRadius_pos p).le
  simpa [largeSquareBox, CCL.RatBox.symmetric, hR,
    OnSymmetricSquareBoundary] using And.intro hLower hUpper

/-- Dense executable form of the full large-square boundary clearance
certificate, not only its four vertices. -/
theorem eval_ne_zero_on_denseLargeSquareBoundary
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) {z : QI}
    (hz : OnSymmetricSquareBoundary (denseLargeSquareRadius p) z) :
    p.eval z ≠ 0 := by
  have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
  have hsparseDegree : 0 < p.toPolynomial.natDegree := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  have hR := denseLargeSquareRadius_eq hp
  rw [hR] at hz
  have h := eval_ne_zero_on_largeSquareBoundary hsparseDegree hz
  simpa only [eval_toPolynomial] using h

/-- Every vertex of the coefficient-computed large square is nonzero for a
nonconstant dense Gaussian-rational polynomial. -/
theorem largeSquareBox_vertex_nonzero
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    BoxVertexNonzero p (largeSquareBox p) := by
  constructor
  · exact eval_ne_zero_on_denseLargeSquareBoundary hdegree
      (lowerLeft_on_boundary p)
  · exact eval_ne_zero_on_denseLargeSquareBoundary hdegree
      (lowerRight_on_boundary p)
  · exact eval_ne_zero_on_denseLargeSquareBoundary hdegree
      (upperRight_on_boundary p)
  · exact eval_ne_zero_on_denseLargeSquareBoundary hdegree
      (upperLeft_on_boundary p)

/-! ## Symbolic normalization for the coordinate polynomial -/

/-- Executable dense coordinate polynomial `Z`. -/
def coordinatePolynomial : GaussianPolynomial := ⟨[1, 0]⟩

private def rationalOne : FTA.Sturm.RatPolynomial := constant 1
private def rationalVariable : FTA.Sturm.RatPolynomial := ⟨[1, 0]⟩

private theorem rationalOne_nonzero : rationalOne.isZero = false := by
  decide

private theorem rationalVariable_nonzero :
    rationalVariable.isZero = false := by
  decide

private theorem rationalVariable_eval (x : ℚ) :
    rationalVariable.eval x = x := by
  simp [rationalVariable, DensePolynomial.eval, DensePolynomial.evalCoeffs]

private theorem rationalOne_eval (x : ℚ) : rationalOne.eval x = 1 := by
  simp [rationalOne]

private def rationalOneAbsLower (a b : ℚ) :
    IntervalAbsLowerCertificate rationalOne ⟨a, b⟩ where
  bound := 1
  positive := by norm_num
  lower := by
    intro t _ _
    simp [rationalOne_eval]

/-- A polynomial rational function `T/1` has no finite Cauchy pole. -/
theorem cauchyIndex2_variable_over_one (a b : ℚ) :
    cauchyIndex2 rationalVariable rationalOne a b = 0 := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact cauchyIndex2_eq_zero_of_intervalAbsLower
      (root := ⟨a, b⟩) rationalVariable rationalOne
      (by exact hab) (rationalOneAbsLower a b)
  · subst b
    exact cauchyIndex2_refl rationalVariable rationalOne a
  · have hforward := cauchyIndex2_eq_zero_of_intervalAbsLower
      (root := ⟨b, a⟩) rationalVariable rationalOne
      (by exact hba) (rationalOneAbsLower b a)
    have hreverse := cauchyIndex2_reverse rationalVariable rationalOne b a
    rw [hforward] at hreverse
    omega

/-- The doubled Cauchy index of `1/T` across a positive symmetric interval
is two.  Cauchy--Sturm inversion reduces it to the constant-denominator case
and the two explicit endpoint jumps. -/
theorem cauchyIndex2_one_over_variable {R : ℚ} (hR : 0 < R) :
    cauchyIndex2 rationalOne rationalVariable (-R) R = 2 := by
  have hinversion := cauchyIndex2_inversion
    rationalOne rationalVariable (-R) R
    rationalOne_nonzero rationalVariable_nonzero
  have hpair := pairVariationDifference2_eq_raw_product_jumps
    (R := rationalOne) (S := rationalVariable) (a := -R) (b := R)
    rationalOne_nonzero rationalVariable_nonzero
    (Or.inl (by simp [rationalOne_eval]))
    (Or.inl (by simp [rationalOne_eval]))
  rw [hpair, cauchyIndex2_variable_over_one] at hinversion
  simp only [rationalOne_eval, rationalVariable_eval] at hinversion
  rw [signJump_eq_two_of_mul_neg (by nlinarith),
    signJump_eq_zero_of_mul_pos (by nlinarith)] at hinversion
  omega

private theorem scale_one_variable :
    scale (1 : ℚ) rationalVariable = rationalVariable := by
  apply DensePolynomial.ext
  norm_num [scale, DensePolynomial.normalize, rationalVariable]

private theorem scale_neg_one_variable :
    scale (-1 : ℚ) rationalVariable = -rationalVariable := by
  apply DensePolynomial.ext
  norm_num [scale, DensePolynomial.normalize, rationalVariable]

/-- The real coordinate of `Z` on a horizontal edge is exactly `T`. -/
theorem coordinate_horizontal_real
    (y a b : ℚ) :
    (horizontalEdge coordinatePolynomial y a b).realPart =
      rationalVariable := by
  have eval_identity (t : ℚ) :
      (horizontalEdge coordinatePolynomial y a b).realPart.eval t =
        rationalVariable.eval t := by
    rw [horizontalEdge_real_eval]
    simp [coordinatePolynomial, rationalVariable, DensePolynomial.eval,
      DensePolynomial.evalCoeffs]
  have hpoly :
      (horizontalEdge coordinatePolynomial y a b).realPart.toPolynomial =
        rationalVariable.toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show rationalVariable.normalize = rationalVariable by decide] at h
  simpa [horizontalEdge, PolynomialEdge.ofLine] using h

/-- The imaginary coordinate of `Z` on a horizontal edge is its constant
height, represented as a scalar multiple of `1`. -/
theorem coordinate_horizontal_imag
    (y a b : ℚ) :
    (horizontalEdge coordinatePolynomial y a b).imagPart =
      scale y rationalOne := by
  have eval_identity (t : ℚ) :
      (horizontalEdge coordinatePolynomial y a b).imagPart.eval t =
        (scale y rationalOne).eval t := by
    rw [horizontalEdge_imag_eval, eval_scale, rationalOne_eval]
    simp [coordinatePolynomial, DensePolynomial.eval, DensePolynomial.evalCoeffs]
  have hpoly :
      (horizontalEdge coordinatePolynomial y a b).imagPart.toPolynomial =
        (scale y rationalOne).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [horizontalEdge, PolynomialEdge.ofLine] using h

/-- The real coordinate of `Z` on a vertical edge is its constant horizontal
position. -/
theorem coordinate_vertical_real
    (x a b : ℚ) :
    (verticalEdge coordinatePolynomial x a b).realPart =
      scale x rationalOne := by
  have eval_identity (t : ℚ) :
      (verticalEdge coordinatePolynomial x a b).realPart.eval t =
        (scale x rationalOne).eval t := by
    rw [verticalEdge_real_eval, eval_scale, rationalOne_eval]
    simp [coordinatePolynomial, DensePolynomial.eval, DensePolynomial.evalCoeffs]
  have hpoly :
      (verticalEdge coordinatePolynomial x a b).realPart.toPolynomial =
        (scale x rationalOne).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [verticalEdge, PolynomialEdge.ofLine] using h

/-- The imaginary coordinate of `Z` on a vertical edge is exactly `T`. -/
theorem coordinate_vertical_imag
    (x a b : ℚ) :
    (verticalEdge coordinatePolynomial x a b).imagPart =
      rationalVariable := by
  have eval_identity (t : ℚ) :
      (verticalEdge coordinatePolynomial x a b).imagPart.eval t =
        rationalVariable.eval t := by
    rw [verticalEdge_imag_eval]
    simp [coordinatePolynomial, rationalVariable, DensePolynomial.eval,
      DensePolynomial.evalCoeffs]
  have hpoly :
      (verticalEdge coordinatePolynomial x a b).imagPart.toPolynomial =
        rationalVariable.toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [show rationalVariable.normalize = rationalVariable by decide] at h
  simpa [verticalEdge, PolynomialEdge.ofLine] using h

private theorem coordinate_bottom_winding {R : ℚ} (hR : 0 < R) :
    (horizontalEdge coordinatePolynomial (-R) (-R) R).doubledWinding = 0 := by
  change cauchyIndex2
    (horizontalEdge coordinatePolynomial (-R) (-R) R).realPart
    (horizontalEdge coordinatePolynomial (-R) (-R) R).imagPart (-R) R = 0
  rw [coordinate_horizontal_real, coordinate_horizontal_imag]
  have hscaled := cauchyIndex2_scale_of_mul_pos
    rationalVariable_nonzero rationalOne_nonzero
    (c := (-1 : ℚ)) (d := -R) (by nlinarith)
    (-R) R
  rw [scale_neg_one_variable,
    cauchyIndex2_variable_over_one] at hscaled
  have hdenominator : (scale (-R) rationalOne).isZero = false :=
    scale_isZero_false (by linarith) rationalOne_nonzero
  have hnegative := cauchyIndex2_neg_numerator rationalVariable
    (scale (-R) rationalOne) (-R) R
    rationalVariable_nonzero hdenominator
  omega

private theorem coordinate_right_winding {R : ℚ} (hR : 0 < R) :
    (verticalEdge coordinatePolynomial R (-R) R).doubledWinding = 2 := by
  change cauchyIndex2
    (verticalEdge coordinatePolynomial R (-R) R).realPart
    (verticalEdge coordinatePolynomial R (-R) R).imagPart (-R) R = 2
  rw [coordinate_vertical_real, coordinate_vertical_imag]
  have hscaled := cauchyIndex2_scale_of_mul_pos
    rationalOne_nonzero rationalVariable_nonzero
    (c := R) (d := (1 : ℚ)) (by simpa using hR)
    (-R) R
  rw [scale_one_variable, cauchyIndex2_one_over_variable hR] at hscaled
  exact hscaled

private theorem coordinate_top_winding {R : ℚ} (hR : 0 < R) :
    (horizontalEdge coordinatePolynomial R R (-R)).doubledWinding = 0 := by
  change cauchyIndex2
    (horizontalEdge coordinatePolynomial R R (-R)).realPart
    (horizontalEdge coordinatePolynomial R R (-R)).imagPart R (-R) = 0
  rw [coordinate_horizontal_real, coordinate_horizontal_imag]
  have hscaled := cauchyIndex2_scale_of_mul_pos
    rationalVariable_nonzero rationalOne_nonzero
    (c := (1 : ℚ)) (d := R) (by simpa using hR)
    R (-R)
  rw [scale_one_variable,
    cauchyIndex2_variable_over_one] at hscaled
  exact hscaled

private theorem coordinate_left_winding {R : ℚ} (hR : 0 < R) :
    (verticalEdge coordinatePolynomial (-R) R (-R)).doubledWinding = 2 := by
  change cauchyIndex2
    (verticalEdge coordinatePolynomial (-R) R (-R)).realPart
    (verticalEdge coordinatePolynomial (-R) R (-R)).imagPart R (-R) = 2
  rw [coordinate_vertical_real, coordinate_vertical_imag]
  have hscaled := cauchyIndex2_scale_of_mul_pos
    rationalOne_nonzero rationalVariable_nonzero
    (c := -R) (d := (-1 : ℚ)) (by nlinarith)
    R (-R)
  rw [scale_neg_one_variable] at hscaled
  have hbaseForward := cauchyIndex2_one_over_variable hR
  have hbaseReverse := cauchyIndex2_reverse
    rationalOne rationalVariable (-R) R
  rw [hbaseForward] at hbaseReverse
  have hscaledNumerator : (scale (-R) rationalOne).isZero = false :=
    scale_isZero_false (by linarith) rationalOne_nonzero
  have hdenominator := cauchyIndex2_neg_denominator
    (scale (-R) rationalOne) rationalVariable R (-R)
    hscaledNumerator rationalVariable_nonzero
  omega

/-- Proposition 4.3 for `Z` on every positive rational symmetric square,
proved symbolically rather than by a fixed native regression. -/
theorem coordinate_symmetric_normalization {R : ℚ} (hR : 0 < R) :
    let B := CCL.RatBox.symmetric R hR.le
    quadrupledBoxWinding coordinatePolynomial B = 4 ∧
      doubledBoxWinding coordinatePolynomial B = 2 ∧
      boxWinding coordinatePolynomial B = 1 := by
  dsimp only
  have hraw :
      quadrupledBoxWinding coordinatePolynomial
          (CCL.RatBox.symmetric R hR.le) = 4 := by
    rw [quadrupledBoxWinding_eq]
    dsimp only [CCL.RatBox.symmetric]
    rw [coordinate_bottom_winding hR, coordinate_right_winding hR,
      coordinate_top_winding hR, coordinate_left_winding hR]
    norm_num
  refine ⟨hraw, ?_, ?_⟩
  · rw [doubledBoxWinding, hraw]
    norm_num
  · rw [boxWinding, hraw]
    norm_num

/-! ## Positive powers of the coordinate polynomial -/

/-- Finite multiplication program for `Z^(n+1)`, avoiding a zero-exponent
special case in the positive-degree global theorem. -/
def coordinatePositivePower : ℕ → GaussianPolynomial
  | 0 => coordinatePolynomial
  | n + 1 => coordinatePositivePower n * coordinatePolynomial

private theorem coordinate_eval (z : QI) : coordinatePolynomial.eval z = z := by
  simp [coordinatePolynomial, DensePolynomial.eval, DensePolynomial.evalCoeffs]

/-- The executable positive-power program evaluates exactly to `z^(n+1)`. -/
theorem coordinatePositivePower_eval (n : ℕ) (z : QI) :
    (coordinatePositivePower n).eval z = z ^ (n + 1) := by
  induction n with
  | zero =>
      rw [show coordinatePositivePower 0 = coordinatePolynomial by rfl,
        coordinate_eval]
      simp
  | succ n ih =>
      rw [coordinatePositivePower, eval_mul, ih, coordinate_eval]
      exact (pow_succ z (n + 1)).symm

/-- `Z` is nonzero at all four vertices of every positive symmetric square. -/
theorem coordinate_symmetric_vertex_nonzero {R : ℚ} (hR : 0 < R) :
    BoxVertexNonzero coordinatePolynomial
      (CCL.RatBox.symmetric R hR.le) := by
  constructor <;> rw [coordinate_eval] <;> intro hzero
  all_goals have hre := congrArg CCL.GaussianRat.re hzero
  all_goals simp only [CCL.RatBox.symmetric,
    CCL.GaussianRat.zero_re] at hre
  all_goals linarith

/-- Every positive coordinate power inherits the same four nonzero vertex
certificates. -/
theorem coordinatePositivePower_symmetric_vertex_nonzero
    {R : ℚ} (hR : 0 < R) (n : ℕ) :
    BoxVertexNonzero (coordinatePositivePower n)
      (CCL.RatBox.symmetric R hR.le) := by
  induction n with
  | zero => exact coordinate_symmetric_vertex_nonzero hR
  | succ n ih =>
      exact ih.mul (coordinate_symmetric_vertex_nonzero hR)

/-- Repeated use of the vertex-only product theorem gives the raw winding of
`Z^(n+1)` on every positive symmetric square. -/
theorem quadrupledBoxWinding_coordinatePositivePower
    {R : ℚ} (hR : 0 < R) (n : ℕ) :
    quadrupledBoxWinding (coordinatePositivePower n)
        (CCL.RatBox.symmetric R hR.le) =
      (4 : ℤ) * (n + 1) := by
  let B := CCL.RatBox.symmetric R hR.le
  have hstrict : B.xLower < B.xUpper ∧ B.yLower < B.yUpper := by
    dsimp only [B, CCL.RatBox.symmetric]
    constructor <;> linarith
  have hcoordinate := (coordinate_symmetric_normalization hR).1
  induction n with
  | zero =>
      rw [show coordinatePositivePower 0 = coordinatePolynomial by rfl,
        hcoordinate]
      norm_num
  | succ n ih =>
      rw [coordinatePositivePower,
        quadrupledBoxWinding_mul
          (coordinatePositivePower n) coordinatePolynomial B
          (coordinatePositivePower_symmetric_vertex_nonzero hR n)
          (coordinate_symmetric_vertex_nonzero hR)
          hstrict.1 hstrict.2,
        ih, hcoordinate]
      push_cast
      ring

/-- Symbolic normalization for every positive coordinate power. -/
theorem coordinatePositivePower_symmetric_normalization
    {R : ℚ} (hR : 0 < R) (n : ℕ) :
    let B := CCL.RatBox.symmetric R hR.le
    quadrupledBoxWinding (coordinatePositivePower n) B =
        (4 : ℤ) * (n + 1) ∧
      doubledBoxWinding (coordinatePositivePower n) B =
        (2 : ℤ) * (n + 1) ∧
      boxWinding (coordinatePositivePower n) B = n + 1 := by
  dsimp only
  have hraw := quadrupledBoxWinding_coordinatePositivePower hR n
  refine ⟨hraw, ?_, ?_⟩
  · rw [doubledBoxWinding, hraw]
    omega
  · rw [boxWinding, hraw]
    omega

/-! ## Nonzero constants and leading monomials -/

/-- Executable dense constant Gaussian polynomial. -/
def gaussianConstant (c : QI) : GaussianPolynomial := constant c

private theorem gaussianConstant_ofLine_real
    (c u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (gaussianConstant c) u d a b).realPart =
      scale c.re rationalOne := by
  have eval_identity (t : ℚ) :
      (PolynomialEdge.ofLine (gaussianConstant c) u d a b).realPart.eval t =
        (scale c.re rationalOne).eval t := by
    rw [PolynomialEdge.ofLine_real_eval, eval_scale, rationalOne_eval]
    simp [gaussianConstant]
  have hpoly :
      (PolynomialEdge.ofLine (gaussianConstant c) u d a b).realPart.toPolynomial =
        (scale c.re rationalOne).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [PolynomialEdge.ofLine] using h

private theorem gaussianConstant_ofLine_imag
    (c u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (gaussianConstant c) u d a b).imagPart =
      scale c.im rationalOne := by
  have eval_identity (t : ℚ) :
      (PolynomialEdge.ofLine (gaussianConstant c) u d a b).imagPart.eval t =
        (scale c.im rationalOne).eval t := by
    rw [PolynomialEdge.ofLine_imag_eval, eval_scale, rationalOne_eval]
    simp [gaussianConstant]
  have hpoly :
      (PolynomialEdge.ofLine (gaussianConstant c) u d a b).imagPart.toPolynomial =
        (scale c.im rationalOne).toPolynomial := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial]
    exact eval_identity ((i : ℕ) : ℚ)
  have h := normalize_eq_normalize_of_toPolynomial_eq hpoly
  simpa [PolynomialEdge.ofLine] using h

private theorem gaussianConstant_ofLine_winding
    (c u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (gaussianConstant c) u d a b).doubledWinding =
      cauchyIndex2 (scale c.re rationalOne)
        (scale c.im rationalOne) a b := by
  change cauchyIndex2
    (PolynomialEdge.ofLine (gaussianConstant c) u d a b).realPart
    (PolynomialEdge.ofLine (gaussianConstant c) u d a b).imagPart a b = _
  rw [gaussianConstant_ofLine_real, gaussianConstant_ofLine_imag]

/-- Every Gaussian constant has raw closed-box winding zero.  No sign case is
needed: opposite box edges carry the identical constant coordinate pair with
reversed parameter intervals. -/
theorem quadrupledBoxWinding_gaussianConstant
    (c : QI) (B : CCL.RatBox) :
    quadrupledBoxWinding (gaussianConstant c) B = 0 := by
  have hhorizontal := cauchyIndex2_reverse
    (scale c.re rationalOne) (scale c.im rationalOne)
    B.xLower B.xUpper
  have hvertical := cauchyIndex2_reverse
    (scale c.re rationalOne) (scale c.im rationalOne)
    B.yLower B.yUpper
  rw [quadrupledBoxWinding_eq]
  simp only [horizontalEdge, verticalEdge]
  rw [gaussianConstant_ofLine_winding,
    gaussianConstant_ofLine_winding,
    gaussianConstant_ofLine_winding,
    gaussianConstant_ofLine_winding]
  omega

/-- A nonzero Gaussian constant is nonzero at every box vertex. -/
theorem gaussianConstant_vertex_nonzero
    {c : QI} (hc : c ≠ 0) (B : CCL.RatBox) :
    BoxVertexNonzero (gaussianConstant c) B := by
  constructor <;> simpa [gaussianConstant] using hc

/-- Executable leading monomial `a_d Z^d` for a positive-degree dense
polynomial. -/
def leadingMonomial (p : GaussianPolynomial) : GaussianPolynomial :=
  gaussianConstant p.leadingCoeff *
    coordinatePositivePower (p.natDegree - 1)

/-- At positive degree, the executable leading monomial evaluates to the
usual `a_d z^d`. -/
theorem leadingMonomial_eval
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) (z : QI) :
    (leadingMonomial p).eval z = p.leadingCoeff * z ^ p.natDegree := by
  have hdegreeOne : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hdegree)
  rw [leadingMonomial, eval_mul, coordinatePositivePower_eval]
  simp only [gaussianConstant, eval_constant]
  rw [Nat.sub_add_cancel hdegreeOne]

/-- Executable dense polynomial containing exactly the terms below the
leading monomial, extensionally. -/
def lowerTermsPolynomial (p : GaussianPolynomial) : GaussianPolynomial :=
  p - leadingMonomial p

/-- The dense lower-term polynomial agrees pointwise with the sparse finite
sum used by the large-square estimate. -/
theorem lowerTermsPolynomial_eval
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) (z : QI) :
    (lowerTermsPolynomial p).eval z = lowerTermsValue p.toPolynomial z := by
  have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
  have hsplit := eval_eq_lowerTermsValue_add_leading p.toPolynomial z
  rw [eval_toPolynomial, leadingCoeff_toPolynomial hp,
    natDegree_toPolynomial hp] at hsplit
  rw [lowerTermsPolynomial, eval_sub, leadingMonomial_eval hdegree, hsplit]
  ring

/-- Dense form of the explicit uniform leading-term dominance margin. -/
def denseLargeSquareDominanceMargin (p : GaussianPolynomial) : ℚ :=
  (normSq p.leadingCoeff * denseLargeSquareRadius p ^ 2 -
      denseLowerCoefficientWeight p) *
    (denseLargeSquareRadius p ^ 2) ^ (p.natDegree - 1)

theorem denseLargeSquareDominanceMargin_eq
    {p : GaussianPolynomial} (hp : p.isZero = false) :
    denseLargeSquareDominanceMargin p =
      largeSquareDominanceMargin p.toPolynomial := by
  simp only [denseLargeSquareDominanceMargin,
    largeSquareDominanceMargin, leadingCoeff_toPolynomial hp,
    denseLargeSquareRadius_eq hp, denseLowerCoefficientWeight_eq hp,
    natDegree_toPolynomial hp]

theorem denseLargeSquareDominanceMargin_pos
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    0 < denseLargeSquareDominanceMargin p := by
  have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
  have hpoly : p.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hp
  rw [denseLargeSquareDominanceMargin_eq hp]
  exact largeSquareDominanceMargin_pos hpoly

/-- Dense bridge for the explicit pointwise dominance-gap theorem. -/
theorem denseLargeSquareDominanceMargin_le
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) {z : QI}
    (hz : OnSymmetricSquareBoundary (denseLargeSquareRadius p) z) :
    denseLargeSquareDominanceMargin p ≤
      normSq ((leadingMonomial p).eval z) -
        normSq ((lowerTermsPolynomial p).eval z) := by
  have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
  have hsparseDegree : 0 < p.toPolynomial.natDegree := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  have hR := denseLargeSquareRadius_eq hp
  rw [hR] at hz
  have hmargin := largeSquareDominanceMargin_le hsparseDegree hz
  rw [denseLargeSquareDominanceMargin_eq hp]
  simpa only [
    leadingMonomial_eval hdegree, lowerTermsPolynomial_eval hdegree,
    leadingCoeff_toPolynomial hp, natDegree_toPolynomial hp] using hmargin

/-! ## Computed dominance certificates on the four square edges -/

/-- The coefficient-computed margin certifies leading-term dominance on the
bottom edge of the large square. -/
def largeSquareBottomDominanceCertificate
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    NormDominanceCertificate
      (horizontalRealCoordinate (leadingMonomial p)
        (largeSquareBox p).yLower)
      (horizontalImagCoordinate (leadingMonomial p)
        (largeSquareBox p).yLower)
      (horizontalRealCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).yLower)
      (horizontalImagCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).yLower)
      ⟨(largeSquareBox p).xLower, (largeSquareBox p).xUpper⟩ where
  margin := denseLargeSquareDominanceMargin p
  positive := denseLargeSquareDominanceMargin_pos hdegree
  lower := by
    intro t hLower hUpper
    have hmargin := denseLargeSquareDominanceMargin_le hdegree
      (bottom_on_denseLargeSquareBoundary p hLower hUpper)
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, normSq] using hmargin

/-- The same computed margin certifies dominance on the right edge. -/
def largeSquareRightDominanceCertificate
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    NormDominanceCertificate
      (verticalRealCoordinate (leadingMonomial p)
        (largeSquareBox p).xUpper)
      (verticalImagCoordinate (leadingMonomial p)
        (largeSquareBox p).xUpper)
      (verticalRealCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).xUpper)
      (verticalImagCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).xUpper)
      ⟨(largeSquareBox p).yLower, (largeSquareBox p).yUpper⟩ where
  margin := denseLargeSquareDominanceMargin p
  positive := denseLargeSquareDominanceMargin_pos hdegree
  lower := by
    intro t hLower hUpper
    have hmargin := denseLargeSquareDominanceMargin_le hdegree
      (right_on_denseLargeSquareBoundary p hLower hUpper)
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, normSq] using hmargin

/-- The same computed margin certifies dominance on the top edge. -/
def largeSquareTopDominanceCertificate
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    NormDominanceCertificate
      (horizontalRealCoordinate (leadingMonomial p)
        (largeSquareBox p).yUpper)
      (horizontalImagCoordinate (leadingMonomial p)
        (largeSquareBox p).yUpper)
      (horizontalRealCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).yUpper)
      (horizontalImagCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).yUpper)
      ⟨(largeSquareBox p).xLower, (largeSquareBox p).xUpper⟩ where
  margin := denseLargeSquareDominanceMargin p
  positive := denseLargeSquareDominanceMargin_pos hdegree
  lower := by
    intro t hLower hUpper
    have hmargin := denseLargeSquareDominanceMargin_le hdegree
      (top_on_denseLargeSquareBoundary p hLower hUpper)
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, normSq] using hmargin

/-- The same computed margin certifies dominance on the left edge. -/
def largeSquareLeftDominanceCertificate
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    NormDominanceCertificate
      (verticalRealCoordinate (leadingMonomial p)
        (largeSquareBox p).xLower)
      (verticalImagCoordinate (leadingMonomial p)
        (largeSquareBox p).xLower)
      (verticalRealCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).xLower)
      (verticalImagCoordinate (lowerTermsPolynomial p)
        (largeSquareBox p).xLower)
      ⟨(largeSquareBox p).yLower, (largeSquareBox p).yUpper⟩ where
  margin := denseLargeSquareDominanceMargin p
  positive := denseLargeSquareDominanceMargin_pos hdegree
  lower := by
    intro t hLower hUpper
    have hmargin := denseLargeSquareDominanceMargin_le hdegree
      (left_on_denseLargeSquareBoundary p hLower hUpper)
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, normSq] using hmargin

/-- The leading monomial of a positive-degree polynomial has raw winding
`4d` on that polynomial's coefficient-computed large square. -/
theorem quadrupledBoxWinding_leadingMonomial
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    quadrupledBoxWinding (leadingMonomial p) (largeSquareBox p) =
      (4 : ℤ) * p.natDegree := by
  have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
  have hleading : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hp
  let R := denseLargeSquareRadius p
  let B := largeSquareBox p
  have hR : 0 < R := denseLargeSquareRadius_pos p
  have hstrict := largeSquareBox_strict p
  have hconstantVertices :
      BoxVertexNonzero (gaussianConstant p.leadingCoeff) B :=
    gaussianConstant_vertex_nonzero hleading B
  have hpowerVertices :
      BoxVertexNonzero (coordinatePositivePower (p.natDegree - 1)) B := by
    simpa only [B, largeSquareBox, R] using
      coordinatePositivePower_symmetric_vertex_nonzero
        hR (p.natDegree - 1)
  have hpower := quadrupledBoxWinding_coordinatePositivePower
    hR (p.natDegree - 1)
  have hdegreeOne : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hdegree)
  have hpowerValue :
      quadrupledBoxWinding
          (coordinatePositivePower (p.natDegree - 1))
          (CCL.RatBox.symmetric R hR.le) =
        (4 : ℤ) * p.natDegree := by
    rw [hpower]
    have hdegreeIdentity := Nat.sub_add_cancel hdegreeOne
    omega
  have hproduct := quadrupledBoxWinding_mul
    (gaussianConstant p.leadingCoeff)
    (coordinatePositivePower (p.natDegree - 1)) B
    hconstantVertices hpowerVertices hstrict.1 hstrict.2
  have hpowerB :
      quadrupledBoxWinding
          (coordinatePositivePower (p.natDegree - 1)) B =
        (4 : ℤ) * p.natDegree := by
    simpa only [B, largeSquareBox, R] using hpowerValue
  rw [quadrupledBoxWinding_gaussianConstant] at hproduct
  rw [leadingMonomial, hproduct]
  omega

/-- Doubled and ordinary winding normalization for the leading monomial on
the computed large square. -/
theorem leadingMonomial_largeSquare_normalization
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    doubledBoxWinding (leadingMonomial p) (largeSquareBox p) =
        (2 : ℤ) * p.natDegree ∧
      boxWinding (leadingMonomial p) (largeSquareBox p) = p.natDegree := by
  have hraw := quadrupledBoxWinding_leadingMonomial hdegree
  constructor
  · rw [doubledBoxWinding, hraw]
    omega
  · rw [boxWinding, hraw]
    omega

/-! ## Global degree winding -/

/-- Splitting off the leading monomial is an exact sparse-polynomial identity,
independently of the normalized dense coefficient-list representatives. -/
theorem leadingMonomial_add_lowerTermsPolynomial_toPolynomial
    (p : GaussianPolynomial) :
    (leadingMonomial p + lowerTermsPolynomial p).toPolynomial =
      p.toPolynomial := by
  rw [toPolynomial_add, lowerTermsPolynomial, toPolynomial_sub]
  ring

/-- Evaluation form of the exact leading/lower-term split. -/
theorem leadingMonomial_add_lowerTermsPolynomial_eval
    (p : GaussianPolynomial) (z : QI) :
    (leadingMonomial p + lowerTermsPolynomial p).eval z = p.eval z := by
  rw [← eval_toPolynomial, ← eval_toPolynomial,
    leadingMonomial_add_lowerTermsPolynomial_toPolynomial]

/-- The raw winding of every positive-degree Gaussian-rational polynomial on
its coefficient-computed large square is four times its natural degree. -/
theorem quadrupledBoxWinding_largeSquare_eq_degree
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    quadrupledBoxWinding p (largeSquareBox p) =
      (4 : ℤ) * p.natDegree := by
  have hstrict := largeSquareBox_strict p
  have htransfer := quadrupledBoxWinding_add_of_normDominance
    (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
    (largeSquareBottomDominanceCertificate hdegree)
    (largeSquareRightDominanceCertificate hdegree)
    (largeSquareTopDominanceCertificate hdegree)
    (largeSquareLeftDominanceCertificate hdegree)
    hstrict.1 hstrict.2
  have hcongr := quadrupledBoxWinding_congr (largeSquareBox p)
    (leadingMonomial_add_lowerTermsPolynomial_toPolynomial p)
  calc
    quadrupledBoxWinding p (largeSquareBox p) =
        quadrupledBoxWinding
          (leadingMonomial p + lowerTermsPolynomial p)
          (largeSquareBox p) := hcongr.symm
    _ = quadrupledBoxWinding (leadingMonomial p) (largeSquareBox p) :=
      htransfer
    _ = (4 : ℤ) * p.natDegree :=
      quadrupledBoxWinding_leadingMonomial hdegree

/-- Section 6 global theorem: all three winding normalizations on the
coefficient-computed large square recover the positive polynomial degree. -/
theorem largeSquare_winding_eq_degree
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    quadrupledBoxWinding p (largeSquareBox p) =
        (4 : ℤ) * p.natDegree ∧
      doubledBoxWinding p (largeSquareBox p) =
        (2 : ℤ) * p.natDegree ∧
      boxWinding p (largeSquareBox p) = p.natDegree := by
  have hraw := quadrupledBoxWinding_largeSquare_eq_degree hdegree
  refine ⟨hraw, ?_, ?_⟩
  · rw [doubledBoxWinding, hraw]
    omega
  · rw [boxWinding, hraw]
    omega

end FTA.GlobalWinding
