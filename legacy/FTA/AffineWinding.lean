import FTA.GlobalWinding

/-!
# Winding of rational affine linear polynomials

The local extractor compares a polynomial with its affine linearization
`f'(a)(Z-c)`.  This module proves directly from finite Cauchy indices that
`Z-c` has winding one on every proper rational rectangle whose strict interior
contains `c`, and that multiplication by a nonzero rational Gaussian constant
preserves this normalization.
-/

namespace FTA.AffineWinding

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Sturm
open FTA.SturmTransducer
open FTA.CauchyNoPole
open FTA.Winding
open FTA.WindingProduct
open FTA.WindingHomotopy
open FTA.GlobalWinding

/-- Executable dense polynomial `Z-c`. -/
def translatedCoordinate (c : QI) : GaussianPolynomial :=
  coordinatePolynomial - gaussianConstant c

@[simp] theorem translatedCoordinate_eval (c z : QI) :
    (translatedCoordinate c).eval z = z - c := by
  rw [translatedCoordinate, eval_sub]
  rw [show coordinatePolynomial.eval z = z by
    simp [coordinatePolynomial, DensePolynomial.eval,
      DensePolynomial.evalCoeffs]]
  rw [show (gaussianConstant c).eval z = c by
    simp [gaussianConstant]]
  change z + -c = z - c
  exact (GaussianRat.sub_eq_add_neg z c).symm

/-- On a horizontal line not passing through `c`, the imaginary coordinate
has a constant positive absolute lower bound. -/
def horizontalImagAbsLowerCertificate
    (c : QI) (y : ℚ) {root : RationalInterval}
    (hy : y ≠ c.im) :
    IntervalAbsLowerCertificate
      (horizontalImagCoordinate (translatedCoordinate c) y) root where
  bound := |y - c.im|
  positive := abs_pos.mpr (sub_ne_zero.mpr hy)
  lower := by
    intro t _hLower _hUpper
    simp only [horizontalImagCoordinate_eval, translatedCoordinate_eval,
      sub_im]
    exact le_rfl

/-- On a vertical line not passing through `c`, the real coordinate has the
analogous constant absolute lower bound. -/
def verticalRealAbsLowerCertificate
    (c : QI) (x : ℚ) {root : RationalInterval}
    (hx : x ≠ c.re) :
    IntervalAbsLowerCertificate
      (verticalRealCoordinate (translatedCoordinate c) x) root where
  bound := |x - c.re|
  positive := abs_pos.mpr (sub_ne_zero.mpr hx)
  lower := by
    intro t _hLower _hUpper
    simp only [verticalRealCoordinate_eval, translatedCoordinate_eval,
      sub_re]
    exact le_rfl

/-- If the center lies strictly left of a horizontal parameter interval,
the real coordinate `t-c.re` has an explicit positive lower bound. -/
def horizontalRealAbsLowerCertificate_of_center_left
    (c : QI) (y : ℚ) {root : RationalInterval}
    (outside : c.re < root.lower) :
    IntervalAbsLowerCertificate
      (horizontalRealCoordinate (translatedCoordinate c) y) root where
  bound := root.lower - c.re
  positive := sub_pos.mpr outside
  lower := by
    intro t hLower _hUpper
    simp only [horizontalRealCoordinate_eval, translatedCoordinate_eval,
      sub_re]
    rw [abs_of_pos (sub_pos.mpr (outside.trans_le hLower))]
    linarith

/-- If the center lies strictly right of a horizontal parameter interval,
the real coordinate `t-c.re` has an explicit positive absolute lower bound. -/
def horizontalRealAbsLowerCertificate_of_center_right
    (c : QI) (y : ℚ) {root : RationalInterval}
    (outside : root.upper < c.re) :
    IntervalAbsLowerCertificate
      (horizontalRealCoordinate (translatedCoordinate c) y) root where
  bound := c.re - root.upper
  positive := sub_pos.mpr outside
  lower := by
    intro t _hLower hUpper
    simp only [horizontalRealCoordinate_eval, translatedCoordinate_eval,
      sub_re]
    rw [abs_of_neg (sub_neg.mpr (hUpper.trans_lt outside))]
    linarith

/-- If the center lies strictly below a vertical parameter interval, the
imaginary coordinate `t-c.im` has an explicit positive lower bound. -/
def verticalImagAbsLowerCertificate_of_center_below
    (c : QI) (x : ℚ) {root : RationalInterval}
    (outside : c.im < root.lower) :
    IntervalAbsLowerCertificate
      (verticalImagCoordinate (translatedCoordinate c) x) root where
  bound := root.lower - c.im
  positive := sub_pos.mpr outside
  lower := by
    intro t hLower _hUpper
    simp only [verticalImagCoordinate_eval, translatedCoordinate_eval,
      sub_im]
    rw [abs_of_pos (sub_pos.mpr (outside.trans_le hLower))]
    linarith

/-- If the center lies strictly above a vertical parameter interval, the
imaginary coordinate `t-c.im` has an explicit positive absolute lower bound. -/
def verticalImagAbsLowerCertificate_of_center_above
    (c : QI) (x : ℚ) {root : RationalInterval}
    (outside : root.upper < c.im) :
    IntervalAbsLowerCertificate
      (verticalImagCoordinate (translatedCoordinate c) x) root where
  bound := c.im - root.upper
  positive := sub_pos.mpr outside
  lower := by
    intro t _hLower hUpper
    simp only [verticalImagCoordinate_eval, translatedCoordinate_eval,
      sub_im]
    rw [abs_of_neg (sub_neg.mpr (hUpper.trans_lt outside))]
    linarith

/-- A horizontal edge away from the center's height has no Cauchy pole and
hence doubled edge winding zero. -/
theorem translated_horizontal_index_zero
    (c : QI) {y a b : ℚ} (hab : a < b) (hy : y ≠ c.im) :
    cauchyIndex2
      (horizontalRealCoordinate (translatedCoordinate c) y)
      (horizontalImagCoordinate (translatedCoordinate c) y) a b = 0 := by
  exact cauchyIndex2_eq_zero_of_intervalAbsLower
    (root := ⟨a, b⟩) _ _ hab
    (horizontalImagAbsLowerCertificate c y hy)

/-- A forward vertical edge to the right of `c` contributes two raw units. -/
theorem translated_vertical_index_right
    (c : QI) {x a b : ℚ}
    (hab : a < b) (ha : a < c.im) (hb : c.im < b)
    (hx : c.re < x) :
    cauchyIndex2
      (verticalRealCoordinate (translatedCoordinate c) x)
      (verticalImagCoordinate (translatedCoordinate c) x) a b = 2 := by
  have hformula := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (root := ⟨a, b⟩)
    (verticalRealCoordinate (translatedCoordinate c) x)
    (verticalImagCoordinate (translatedCoordinate c) x) hab
    (verticalRealAbsLowerCertificate c x (ne_of_gt hx))
  simp only [verticalRealCoordinate_eval, verticalImagCoordinate_eval,
    translatedCoordinate_eval, sub_re, sub_im] at hformula
  have hlower : signJump 1 ((x - c.re) * (a - c.im)) = 2 :=
    signJump_eq_two_of_mul_neg (by nlinarith)
  have hupper : signJump 1 ((x - c.re) * (b - c.im)) = 0 :=
    signJump_eq_zero_of_mul_pos (by nlinarith)
  rw [hlower, hupper] at hformula
  exact hformula

/-- A forward vertical edge to the left of `c` contributes minus two; its
reversed box orientation therefore contributes plus two. -/
theorem translated_vertical_index_left_forward
    (c : QI) {x a b : ℚ}
    (hab : a < b) (ha : a < c.im) (hb : c.im < b)
    (hx : x < c.re) :
    cauchyIndex2
      (verticalRealCoordinate (translatedCoordinate c) x)
      (verticalImagCoordinate (translatedCoordinate c) x) a b = -2 := by
  have hformula := cauchyIndex2_eq_endpointJumps_of_first_absLower
    (root := ⟨a, b⟩)
    (verticalRealCoordinate (translatedCoordinate c) x)
    (verticalImagCoordinate (translatedCoordinate c) x) hab
    (verticalRealAbsLowerCertificate c x (ne_of_lt hx))
  simp only [verticalRealCoordinate_eval, verticalImagCoordinate_eval,
    translatedCoordinate_eval, sub_re, sub_im] at hformula
  have hlower : signJump 1 ((x - c.re) * (a - c.im)) = 0 :=
    signJump_eq_zero_of_mul_pos (by nlinarith)
  have hupper : signJump 1 ((x - c.re) * (b - c.im)) = 2 :=
    signJump_eq_two_of_mul_neg (by nlinarith)
  rw [hlower, hupper] at hformula
  exact hformula

/-- Raw winding normalization for `Z-c` on every rational rectangle strictly
containing `c`. -/
theorem quadrupledBoxWinding_translatedCoordinate
    (c : QI) {B : CCL.RatBox}
    (hcxLower : B.xLower < c.re) (hcxUpper : c.re < B.xUpper)
    (hcyLower : B.yLower < c.im) (hcyUpper : c.im < B.yUpper) :
    quadrupledBoxWinding (translatedCoordinate c) B = 4 := by
  have hx : B.xLower < B.xUpper := hcxLower.trans hcxUpper
  have hy : B.yLower < B.yUpper := hcyLower.trans hcyUpper
  have hbottom := translated_horizontal_index_zero c hx
    (ne_of_lt hcyLower)
  have htopForward := translated_horizontal_index_zero c hx
    (ne_of_gt hcyUpper)
  have htopReverse := cauchyIndex2_reverse
    (horizontalRealCoordinate (translatedCoordinate c) B.yUpper)
    (horizontalImagCoordinate (translatedCoordinate c) B.yUpper)
    B.xLower B.xUpper
  rw [htopForward] at htopReverse
  have hright := translated_vertical_index_right c hy
    hcyLower hcyUpper hcxUpper
  have hleftForward := translated_vertical_index_left_forward c hy
    hcyLower hcyUpper hcxLower
  have hleftReverse := cauchyIndex2_reverse
    (verticalRealCoordinate (translatedCoordinate c) B.xLower)
    (verticalImagCoordinate (translatedCoordinate c) B.xLower)
    B.yLower B.yUpper
  rw [hleftForward] at hleftReverse
  rw [quadrupledBoxWinding_eq]
  change cauchyIndex2
        (horizontalRealCoordinate (translatedCoordinate c) B.yLower)
        (horizontalImagCoordinate (translatedCoordinate c) B.yLower)
        B.xLower B.xUpper +
      cauchyIndex2
        (verticalRealCoordinate (translatedCoordinate c) B.xUpper)
        (verticalImagCoordinate (translatedCoordinate c) B.xUpper)
        B.yLower B.yUpper +
      cauchyIndex2
        (horizontalRealCoordinate (translatedCoordinate c) B.yUpper)
        (horizontalImagCoordinate (translatedCoordinate c) B.yUpper)
        B.xUpper B.xLower +
      cauchyIndex2
        (verticalRealCoordinate (translatedCoordinate c) B.xLower)
        (verticalImagCoordinate (translatedCoordinate c) B.xLower)
        B.yUpper B.yLower = 4
  omega

/-- All winding normalizations for a translated coordinate. -/
theorem translatedCoordinate_box_normalization
    (c : QI) {B : CCL.RatBox}
    (hcxLower : B.xLower < c.re) (hcxUpper : c.re < B.xUpper)
    (hcyLower : B.yLower < c.im) (hcyUpper : c.im < B.yUpper) :
    doubledBoxWinding (translatedCoordinate c) B = 2 ∧
      boxWinding (translatedCoordinate c) B = 1 := by
  have hraw := quadrupledBoxWinding_translatedCoordinate c
    hcxLower hcxUpper hcyLower hcyUpper
  constructor
  · rw [doubledBoxWinding, hraw]
    norm_num
  · rw [boxWinding, hraw]
    norm_num

/-- A translated coordinate has zero raw winding on every proper rational
box that does not contain its unique zero.  The finite proof splits on the
four exact rational inequalities witnessing exclusion and applies either
real-coordinate endpoint cancellation or imaginary-coordinate no-pole
cancellation. -/
theorem quadrupledBoxWinding_translatedCoordinate_eq_zero_of_not_contains
    (c : QI) {B : CCL.RatBox} (proper : B.Proper)
    (outside : ¬B.Contains c) :
    quadrupledBoxWinding (translatedCoordinate c) B = 0 := by
  simp only [RatBox.Contains, not_and_or, not_le] at outside
  rcases outside with left | right | below | above
  · exact quadrupledBoxWinding_eq_zero_of_real_absLower
      (translatedCoordinate c) B
      (horizontalRealAbsLowerCertificate_of_center_left c B.yLower left)
      (verticalRealAbsLowerCertificate c B.xUpper
        (ne_of_gt (left.trans_le B.x_valid)))
      (horizontalRealAbsLowerCertificate_of_center_left c B.yUpper left)
      (verticalRealAbsLowerCertificate c B.xLower (ne_of_gt left))
      proper.1 proper.2
  · exact quadrupledBoxWinding_eq_zero_of_real_absLower
      (translatedCoordinate c) B
      (horizontalRealAbsLowerCertificate_of_center_right c B.yLower right)
      (verticalRealAbsLowerCertificate c B.xUpper (ne_of_lt right))
      (horizontalRealAbsLowerCertificate_of_center_right c B.yUpper right)
      (verticalRealAbsLowerCertificate c B.xLower
        (ne_of_lt (B.x_valid.trans_lt right)))
      proper.1 proper.2
  · exact quadrupledBoxWinding_eq_zero_of_imag_absLower
      (translatedCoordinate c) B
      (horizontalImagAbsLowerCertificate c B.yLower (ne_of_gt below))
      (verticalImagAbsLowerCertificate_of_center_below c B.xUpper below)
      (horizontalImagAbsLowerCertificate c B.yUpper
        (ne_of_gt (below.trans_le B.y_valid)))
      (verticalImagAbsLowerCertificate_of_center_below c B.xLower below)
      proper.1 proper.2
  · exact quadrupledBoxWinding_eq_zero_of_imag_absLower
      (translatedCoordinate c) B
      (horizontalImagAbsLowerCertificate c B.yLower
        (ne_of_lt (B.y_valid.trans_lt above)))
      (verticalImagAbsLowerCertificate_of_center_above c B.xUpper above)
      (horizontalImagAbsLowerCertificate c B.yUpper (ne_of_lt above))
      (verticalImagAbsLowerCertificate_of_center_above c B.xLower above)
      proper.1 proper.2

/-- Both normalized winding conventions inherit the outside-box zero. -/
theorem translatedCoordinate_box_normalization_of_not_contains
    (c : QI) {B : CCL.RatBox} (proper : B.Proper)
    (outside : ¬B.Contains c) :
    doubledBoxWinding (translatedCoordinate c) B = 0 ∧
      boxWinding (translatedCoordinate c) B = 0 := by
  have hraw :=
    quadrupledBoxWinding_translatedCoordinate_eq_zero_of_not_contains
      c proper outside
  simp [doubledBoxWinding, boxWinding, hraw]

/-- `Z-c` is nonzero at every vertex of a box that strictly contains `c`. -/
theorem translatedCoordinate_vertex_nonzero
    (c : QI) {B : CCL.RatBox}
    (hcxLower : B.xLower < c.re) (hcxUpper : c.re < B.xUpper) :
    BoxVertexNonzero (translatedCoordinate c) B := by
  constructor <;> rw [translatedCoordinate_eval] <;> intro hzero
  all_goals have hre := congrArg CCL.GaussianRat.re hzero
  all_goals simp only [sub_re, zero_re] at hre
  all_goals linarith

/-- Excluding the unique zero from the whole box makes every translated
coordinate vertex value nonzero. -/
theorem translatedCoordinate_vertex_nonzero_of_not_contains
    (c : QI) {B : CCL.RatBox} (outside : ¬B.Contains c) :
    BoxVertexNonzero (translatedCoordinate c) B := by
  have point_eq (z : QI) (zero : z - c = 0) : z = c := by
    ext
    · have real := congrArg CCL.GaussianRat.re zero
      simp only [sub_re, zero_re] at real
      linarith
    · have imag := congrArg CCL.GaussianRat.im zero
      simp only [sub_im, zero_im] at imag
      linarith
  constructor
  · rw [translatedCoordinate_eval]
    intro zero
    apply outside
    have point : CCL.GaussianRat.mk B.xLower B.yLower = c :=
      point_eq _ zero
    rw [← point]
    exact ⟨le_rfl, B.x_valid, le_rfl, B.y_valid⟩
  · rw [translatedCoordinate_eval]
    intro zero
    apply outside
    have point : CCL.GaussianRat.mk B.xUpper B.yLower = c :=
      point_eq _ zero
    rw [← point]
    exact ⟨B.x_valid, le_rfl, le_rfl, B.y_valid⟩
  · rw [translatedCoordinate_eval]
    intro zero
    apply outside
    have point : CCL.GaussianRat.mk B.xUpper B.yUpper = c :=
      point_eq _ zero
    rw [← point]
    exact ⟨B.x_valid, le_rfl, B.y_valid, le_rfl⟩
  · rw [translatedCoordinate_eval]
    intro zero
    apply outside
    have point : CCL.GaussianRat.mk B.xLower B.yUpper = c :=
      point_eq _ zero
    rw [← point]
    exact ⟨le_rfl, B.x_valid, B.y_valid, le_rfl⟩

/-- Executable affine linear polynomial `s(Z-c)`. -/
def affineCoordinate (s c : QI) : GaussianPolynomial :=
  gaussianConstant s * translatedCoordinate c

@[simp] theorem affineCoordinate_eval (s c z : QI) :
    (affineCoordinate s c).eval z = s * (z - c) := by
  rw [affineCoordinate, eval_mul, gaussianConstant, eval_constant,
    translatedCoordinate_eval]

/-- A nonzero rational slope does not change the winding-one normalization
of `Z-c`. -/
theorem affineCoordinate_box_normalization
    {s : QI} (hs : s ≠ 0) (c : QI) {B : CCL.RatBox}
    (hcxLower : B.xLower < c.re) (hcxUpper : c.re < B.xUpper)
    (hcyLower : B.yLower < c.im) (hcyUpper : c.im < B.yUpper) :
    quadrupledBoxWinding (affineCoordinate s c) B = 4 ∧
      doubledBoxWinding (affineCoordinate s c) B = 2 ∧
      boxWinding (affineCoordinate s c) B = 1 := by
  have hstrict : B.xLower < B.xUpper ∧ B.yLower < B.yUpper :=
    ⟨hcxLower.trans hcxUpper, hcyLower.trans hcyUpper⟩
  have hconstant := gaussianConstant_vertex_nonzero hs B
  have htranslated := translatedCoordinate_vertex_nonzero c
    hcxLower hcxUpper
  have hproduct := quadrupledBoxWinding_mul
    (gaussianConstant s) (translatedCoordinate c) B
    hconstant htranslated hstrict.1 hstrict.2
  have htranslatedRaw := quadrupledBoxWinding_translatedCoordinate c
    hcxLower hcxUpper hcyLower hcyUpper
  rw [quadrupledBoxWinding_gaussianConstant, htranslatedRaw] at hproduct
  have hraw : quadrupledBoxWinding (affineCoordinate s c) B = 4 := by
    dsimp only [affineCoordinate]
    omega
  refine ⟨hraw, ?_, ?_⟩
  · rw [doubledBoxWinding, hraw]
    norm_num
  · rw [boxWinding, hraw]
    norm_num

end FTA.AffineWinding
