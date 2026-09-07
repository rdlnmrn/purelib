import FTA.BoxGeometry
import FTA.CCLFormulaPullback
import FTA.CCLFormulaStability

/-!
# Exact Hermitian-form signs on rational boxes

The clear-curve branch of Theorem 10.2 eventually leaves a winding-one box
which meets no relevant generalized circle or line.  This module supplies the
finite interval calculation used at that point.  A coefficient-computed
rational variation bound encloses a Hermitian form on the whole box around
its rational center.  Exact comparison of the enclosure with zero either
certifies one strict sign everywhere or requests further refinement.

Applying the atom calculation recursively gives an executable decision that
a complete finite parser formula has constant truth value throughout the box.
-/

namespace FTA
namespace CCLHermitianBox

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLFormulaStability

abbrev QI := CCL.GaussianRat

/-- A positive coefficient majorizing the variation of a Hermitian form on
an ambient rational box. -/
def variationMajorant (form : HermitianForm) (box : RatBox) : ℚ :=
  max 1 (2 * |form.radial| * box.coordinateRadius +
    |form.realLinear| + |form.imagLinear|)

theorem variationMajorant_pos (form : HermitianForm) (box : RatBox) :
    0 < variationMajorant form box :=
  zero_lt_one.trans_le (le_max_left _ _)

private theorem abs_add_add_le (a b c : ℚ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| :=
      add_le_add (abs_add_le a b) le_rfl

private theorem abs_coordinate_sub_le_width
    {box : RatBox} {z w : QI} (hz : box.Contains z) (hw : box.Contains w) :
    |z.re - w.re| ≤ box.widthX ∧ |z.im - w.im| ≤ box.widthY := by
  rcases hz with ⟨hzLower, hzUpper, hzBottom, hzTop⟩
  rcases hw with ⟨hwLower, hwUpper, hwBottom, hwTop⟩
  constructor
  · rw [abs_le]
    dsimp only [RatBox.widthX]
    constructor <;> linarith
  · rw [abs_le]
    dsimp only [RatBox.widthY]
    constructor <;> linarith

private theorem abs_normSq_sub_le
    {box : RatBox} {z w : QI} (hz : box.Contains z) (hw : box.Contains w) :
    |normSq z - normSq w| ≤
      2 * box.coordinateRadius *
        (|z.re - w.re| + |z.im - w.im|) := by
  rcases box.abs_coordinates_le_radius hz with ⟨hzRe, hzIm⟩
  rcases box.abs_coordinates_le_radius hw with ⟨hwRe, hwIm⟩
  have hsumRe : |z.re + w.re| ≤ 2 * box.coordinateRadius := by
    calc
      |z.re + w.re| ≤ |z.re| + |w.re| := abs_add_le _ _
      _ ≤ box.coordinateRadius + box.coordinateRadius :=
        add_le_add hzRe hwRe
      _ = 2 * box.coordinateRadius := by ring
  have hsumIm : |z.im + w.im| ≤ 2 * box.coordinateRadius := by
    calc
      |z.im + w.im| ≤ |z.im| + |w.im| := abs_add_le _ _
      _ ≤ box.coordinateRadius + box.coordinateRadius :=
        add_le_add hzIm hwIm
      _ = 2 * box.coordinateRadius := by ring
  calc
    |normSq z - normSq w| =
        |(z.re - w.re) * (z.re + w.re) +
          (z.im - w.im) * (z.im + w.im)| := by
      congr 1
      simp only [normSq]
      ring
    _ ≤ |(z.re - w.re) * (z.re + w.re)| +
        |(z.im - w.im) * (z.im + w.im)| := abs_add_le _ _
    _ = |z.re - w.re| * |z.re + w.re| +
        |z.im - w.im| * |z.im + w.im| := by rw [abs_mul, abs_mul]
    _ ≤ |z.re - w.re| * (2 * box.coordinateRadius) +
        |z.im - w.im| * (2 * box.coordinateRadius) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsumRe (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hsumIm (abs_nonneg _))
    _ = 2 * box.coordinateRadius *
        (|z.re - w.re| + |z.im - w.im|) := by ring

/-- Rational Lipschitz enclosure for a Hermitian form on one rational box. -/
theorem abs_eval_sub_eval_le
    (form : HermitianForm) {box : RatBox} {z w : QI}
    (hz : box.Contains z) (hw : box.Contains w) :
    |form.eval z - form.eval w| ≤ variationMajorant form box *
      (|z.re - w.re| + |z.im - w.im|) := by
  let distance := |z.re - w.re| + |z.im - w.im|
  have distanceNonnegative : 0 ≤ distance :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have normVariation := abs_normSq_sub_le hz hw
  have rawLeMajorant :
      2 * |form.radial| * box.coordinateRadius +
          |form.realLinear| + |form.imagLinear| ≤
        variationMajorant form box :=
    le_max_right _ _
  have evaluationIdentity : form.eval z - form.eval w =
      form.radial * (normSq z - normSq w) +
        form.realLinear * (z.re - w.re) +
        form.imagLinear * (z.im - w.im) := by
    simp only [HermitianForm.eval]
    ring
  rw [evaluationIdentity]
  have triangle := abs_add_add_le
    (form.radial * (normSq z - normSq w))
    (form.realLinear * (z.re - w.re))
    (form.imagLinear * (z.im - w.im))
  rw [abs_mul, abs_mul, abs_mul] at triangle
  apply triangle.trans
  have radialBound :
      |form.radial| * |normSq z - normSq w| ≤
        |form.radial| * (2 * box.coordinateRadius * distance) :=
    mul_le_mul_of_nonneg_left normVariation (abs_nonneg _)
  have normStep :
      |form.radial| * |normSq z - normSq w| +
          |form.realLinear| * |z.re - w.re| +
          |form.imagLinear| * |z.im - w.im| ≤
        |form.radial| * (2 * box.coordinateRadius * distance) +
          |form.realLinear| * |z.re - w.re| +
          |form.imagLinear| * |z.im - w.im| :=
    add_le_add (add_le_add radialBound le_rfl) le_rfl
  apply normStep.trans
  have realLe : |z.re - w.re| ≤ distance :=
    le_add_of_nonneg_right (abs_nonneg _)
  have imagLe : |z.im - w.im| ≤ distance :=
    le_add_of_nonneg_left (abs_nonneg _)
  have realScaled := mul_le_mul_of_nonneg_left realLe
    (abs_nonneg form.realLinear)
  have imagScaled := mul_le_mul_of_nonneg_left imagLe
    (abs_nonneg form.imagLinear)
  have coordinateStep :
      (2 * |form.radial| * box.coordinateRadius) * distance +
          |form.realLinear| * |z.re - w.re| +
          |form.imagLinear| * |z.im - w.im| ≤
        (2 * |form.radial| * box.coordinateRadius) * distance +
          |form.realLinear| * distance +
          |form.imagLinear| * distance :=
    add_le_add (add_le_add le_rfl realScaled) imagScaled
  have leftIdentity :
      |form.radial| * (2 * box.coordinateRadius * distance) +
          |form.realLinear| * |z.re - w.re| +
          |form.imagLinear| * |z.im - w.im| =
        (2 * |form.radial| * box.coordinateRadius) * distance +
          |form.realLinear| * |z.re - w.re| +
          |form.imagLinear| * |z.im - w.im| := by ring
  rw [leftIdentity]
  apply coordinateStep.trans
  have combineIdentity :
      (2 * |form.radial| * box.coordinateRadius) * distance +
          |form.realLinear| * distance +
          |form.imagLinear| * distance =
        (2 * |form.radial| * box.coordinateRadius +
          |form.realLinear| + |form.imagLinear|) * distance := by ring
  rw [combineIdentity]
  exact mul_le_mul_of_nonneg_right rawLeMajorant distanceNonnegative

/-- Whole-box variation radius around the rational center. -/
def boxVariation (form : HermitianForm) (box : RatBox) : ℚ :=
  variationMajorant form box * (box.widthX + box.widthY)

theorem boxVariation_nonneg (form : HermitianForm) (box : RatBox) :
    0 ≤ boxVariation form box := by
  exact mul_nonneg (variationMajorant_pos form box).le
    (add_nonneg box.widthX_nonneg box.widthY_nonneg)

theorem abs_eval_sub_center_le
    (form : HermitianForm) {box : RatBox} {z : QI}
    (hz : box.Contains z) :
    |form.eval z - form.eval box.center| ≤ boxVariation form box := by
  have coordinateBounds := abs_coordinate_sub_le_width hz box.contains_center
  apply (abs_eval_sub_eval_le form hz box.contains_center).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add coordinateBounds.1 coordinateBounds.2)
    (variationMajorant_pos form box).le

/-- Lower endpoint of the certified center-radius enclosure. -/
def lowerBound (form : HermitianForm) (box : RatBox) : ℚ :=
  form.eval box.center - boxVariation form box

/-- Upper endpoint of the certified center-radius enclosure. -/
def upperBound (form : HermitianForm) (box : RatBox) : ℚ :=
  form.eval box.center + boxVariation form box

theorem lowerBound_le_eval
    (form : HermitianForm) {box : RatBox} {z : QI}
    (hz : box.Contains z) : lowerBound form box ≤ form.eval z := by
  have bound := (abs_le.mp (abs_eval_sub_center_le form hz)).1
  dsimp only [lowerBound]
  linarith

theorem eval_le_upperBound
    (form : HermitianForm) {box : RatBox} {z : QI}
    (hz : box.Contains z) : form.eval z ≤ upperBound form box := by
  have bound := (abs_le.mp (abs_eval_sub_center_le form hz)).2
  dsimp only [upperBound]
  linarith

/-- Exact Boolean test that the center-radius enclosure avoids zero. -/
def strictSignCheck (form : HermitianForm) (box : RatBox) : Bool :=
  decide (0 < lowerBound form box) || decide (upperBound form box < 0)

theorem strictSignCheck_eq_true_iff
    (form : HermitianForm) (box : RatBox) :
    strictSignCheck form box = true ↔
      0 < lowerBound form box ∨ upperBound form box < 0 := by
  simp [strictSignCheck]

/-- A successful finite interval check proves that every box point has the
same strict sign as the rational center. -/
theorem eval_center_mul_pos_of_strictSignCheck
    (form : HermitianForm) {box : RatBox}
    (check : strictSignCheck form box = true) {z : QI}
    (hz : box.Contains z) :
    0 < form.eval box.center * form.eval z := by
  rcases (strictSignCheck_eq_true_iff form box).mp check with
      lowerPositive | upperNegative
  · exact mul_pos
      (lowerPositive.trans_le (lowerBound_le_eval form box.contains_center))
      (lowerPositive.trans_le (lowerBound_le_eval form hz))
  · exact mul_pos_of_neg_of_neg
      ((eval_le_upperBound form box.contains_center).trans_lt upperNegative)
      ((eval_le_upperBound form hz).trans_lt upperNegative)

namespace Formula

/-- Every atom enclosure must avoid zero; conjunctions and disjunctions use
the same finite recursive traversal as formula evaluation. -/
def strictOnBox : Formula → RatBox → Bool
  | .truth, _ | .falsity, _ => true
  | .atom atom, box => strictSignCheck atom.form box
  | .and left right, box | .or left right, box =>
      strictOnBox left box && strictOnBox right box

/-- If all atom enclosures avoid zero, the complete Boolean formula has its
center truth value at every point of the rational box. -/
theorem holds_iff_center_of_strictOnBox
    (formula : Formula) {box : RatBox}
    (check : strictOnBox formula box = true) {z : QI}
    (hz : box.Contains z) :
    formula.Holds z ↔ formula.Holds box.center := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom =>
      apply (SignTest.holds_iff_of_mul_pos atom.sign
        (eval_center_mul_pos_of_strictSignCheck atom.form check hz)).symm
  | and left right leftIH rightIH =>
      simp only [strictOnBox, Bool.and_eq_true] at check
      simp only [Formula.Holds]
      exact and_congr (leftIH check.1) (rightIH check.2)
  | or left right leftIH rightIH =>
      simp only [strictOnBox, Bool.and_eq_true] at check
      simp only [Formula.Holds]
      exact or_congr (leftIH check.1) (rightIH check.2)

/-- Finite outcome of whole-box formula evaluation.  A stable result carries
the exact truth bit and its proof for every point; `unresolved` asks the track
controller for another finite refinement. -/
inductive CellDecision (formula : Formula) (box : RatBox) where
  | unresolved
  | stable (value : Bool)
      (strict : strictOnBox formula box = true)
      (characterization : ∀ {z : QI}, box.Contains z →
        (formula.Holds z ↔ value = true))

/-- Direct exact interval decision for a complete Hermitian formula. -/
def decideCell (formula : Formula) (box : RatBox) :
    CellDecision formula box := by
  if check : strictOnBox formula box = true then
    let value := formula.evalBool box.center
    have characterization : ∀ {z : QI}, box.Contains z →
        (formula.Holds z ↔ value = true) :=
      fun {z : QI} (hz : box.Contains z) => by
        change formula.Holds z ↔ formula.evalBool box.center = true
        exact (holds_iff_center_of_strictOnBox formula check hz).trans
          (Formula.evalBool_eq_true formula box.center).symm
    exact .stable value check characterization
  else
    exact .unresolved

end Formula

end CCLHermitianBox
end FTA
