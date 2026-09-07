import FTA.PolynomialBounds

/-!
# Finite rational box geometry

Coordinate lemmas for Definitions 1.3--1.4 and the error bounds in Theorem
1.5(c).  No point completion or topological compactness is used.
-/

namespace CCL

open GaussianRat

namespace RatBox

/-- Rational center of a box. -/
def center (B : RatBox) : GaussianRat where
  re := (B.xLower + B.xUpper) / 2
  im := (B.yLower + B.yUpper) / 2

@[simp] theorem center_re (B : RatBox) : B.center.re =
    (B.xLower + B.xUpper) / 2 := rfl

@[simp] theorem center_im (B : RatBox) : B.center.im =
    (B.yLower + B.yUpper) / 2 := rfl

theorem contains_center (B : RatBox) : B.Contains B.center := by
  dsimp [Contains, center]
  constructor
  · linarith [B.x_valid]
  constructor
  · linarith [B.x_valid]
  constructor <;> linarith [B.y_valid]

def widthX (B : RatBox) : ℚ := B.xUpper - B.xLower
def widthY (B : RatBox) : ℚ := B.yUpper - B.yLower

theorem widthX_nonneg (B : RatBox) : 0 ≤ B.widthX := by
  dsimp [widthX]
  linarith [B.x_valid]

theorem widthY_nonneg (B : RatBox) : 0 ≤ B.widthY := by
  dsimp [widthY]
  linarith [B.y_valid]

theorem diagonalSq_eq (B : RatBox) :
    B.diagonalSq = B.widthX ^ 2 + B.widthY ^ 2 := rfl

theorem diagonalSq_pos {B : RatBox} (hB : B.Proper) :
    0 < B.diagonalSq := by
  rcases hB with ⟨hx, hy⟩
  dsimp [diagonalSq]
  positivity

theorem normSq_center_sub_le_diagonalSq {B : RatBox} {z : GaussianRat}
    (hz : B.Contains z) : normSq (B.center - z) ≤ B.diagonalSq :=
  normSq_sub_le_diagonalSq B.contains_center hz

/-- Coordinatewise positive-gap separation used for finite distinctness. -/
def Separated (B C : RatBox) : Prop :=
  ∃ g : ℚ, 0 < g ∧
    (B.xUpper + g ≤ C.xLower ∨ C.xUpper + g ≤ B.xLower ∨
      B.yUpper + g ≤ C.yLower ∨ C.yUpper + g ≤ B.yLower)

theorem separated_symm {B C : RatBox} (h : B.Separated C) : C.Separated B := by
  rcases h with ⟨g, hg, hgap⟩
  refine ⟨g, hg, ?_⟩
  rcases hgap with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Positive coordinate-gap separation is preserved by box refinement. -/
theorem Separated.of_refines
    {B C B' C' : RatBox} (h : B.Separated C)
    (hB : B'.Refines B) (hC : C'.Refines C) : B'.Separated C' := by
  rcases h with ⟨g, hg, hgap⟩
  rcases hB with ⟨hBLower, hBUpper, hBYLower, hBYUpper⟩
  rcases hC with ⟨hCLower, hCUpper, hCYLower, hCYUpper⟩
  refine ⟨g, hg, ?_⟩
  rcases hgap with hgap | hgap | hgap | hgap
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

theorem separated_no_common_member {B C : RatBox} (h : B.Separated C) :
    ¬∃ z : GaussianRat, B.Contains z ∧ C.Contains z := by
  rintro ⟨z, hzB, hzC⟩
  rcases h with ⟨g, hg, hgap⟩
  rcases hzB with ⟨hBxl, hBxU, hByl, hByU⟩
  rcases hzC with ⟨hCxl, hCxU, hCyl, hCyU⟩
  rcases hgap with h | h | h | h <;> linarith

/-- Failure of positive-gap separation is exactly the four coordinate
overlap inequalities needed by later quantitative clamp arguments. -/
theorem not_separated_coordinate_overlaps {B C : RatBox}
    (h : ¬B.Separated C) :
    C.xLower ≤ B.xUpper ∧ B.xLower ≤ C.xUpper ∧
      C.yLower ≤ B.yUpper ∧ B.yLower ≤ C.yUpper := by
  constructor
  · by_contra notOverlap
    have gapPositive : 0 < C.xLower - B.xUpper := sub_pos.mpr (lt_of_not_ge notOverlap)
    apply h
    exact ⟨C.xLower - B.xUpper, gapPositive, Or.inl (by linarith)⟩
  constructor
  · by_contra notOverlap
    have gapPositive : 0 < B.xLower - C.xUpper := sub_pos.mpr (lt_of_not_ge notOverlap)
    apply h
    exact ⟨B.xLower - C.xUpper, gapPositive,
      Or.inr (Or.inl (by linarith))⟩
  constructor
  · by_contra notOverlap
    have gapPositive : 0 < C.yLower - B.yUpper := sub_pos.mpr (lt_of_not_ge notOverlap)
    apply h
    exact ⟨C.yLower - B.yUpper, gapPositive,
      Or.inr (Or.inr (Or.inl (by linarith)))⟩
  · by_contra notOverlap
    have gapPositive : 0 < B.yLower - C.yUpper := sub_pos.mpr (lt_of_not_ge notOverlap)
    apply h
    exact ⟨B.yLower - C.yUpper, gapPositive,
      Or.inr (Or.inr (Or.inr (by linarith)))⟩

/-- A displayed positive coordinate gap gives a squared-norm lower bound for
every pair of points in the two boxes. -/
theorem sq_le_normSq_sub_of_coordinate_gap
    {B C : RatBox} {g : ℚ} (hg : 0 < g)
    (hgap : B.xUpper + g ≤ C.xLower ∨
      C.xUpper + g ≤ B.xLower ∨
      B.yUpper + g ≤ C.yLower ∨
      C.yUpper + g ≤ B.yLower)
    {u v : GaussianRat} (hu : B.Contains u) (hv : C.Contains v) :
    g ^ 2 ≤ normSq (v - u) := by
  rcases hu with ⟨huXLower, huXUpper, huYLower, huYUpper⟩
  rcases hv with ⟨hvXLower, hvXUpper, hvYLower, hvYUpper⟩
  rcases hgap with hgap | hgap | hgap | hgap
  · have hdifference : g ≤ v.re - u.re := by linarith
    have hproduct : 0 ≤ (v.re - u.re - g) * (v.re - u.re + g) :=
      mul_nonneg (sub_nonneg.mpr hdifference) (by linarith)
    dsimp [normSq]
    nlinarith [hproduct, sq_nonneg (v.im - u.im)]
  · have hdifference : g ≤ u.re - v.re := by linarith
    have hproduct : 0 ≤ (u.re - v.re - g) * (u.re - v.re + g) :=
      mul_nonneg (sub_nonneg.mpr hdifference) (by linarith)
    dsimp [normSq]
    nlinarith [hproduct, sq_nonneg (v.im - u.im)]
  · have hdifference : g ≤ v.im - u.im := by linarith
    have hproduct : 0 ≤ (v.im - u.im - g) * (v.im - u.im + g) :=
      mul_nonneg (sub_nonneg.mpr hdifference) (by linarith)
    dsimp [normSq]
    nlinarith [hproduct, sq_nonneg (v.re - u.re)]
  · have hdifference : g ≤ u.im - v.im := by linarith
    have hproduct : 0 ≤ (u.im - v.im - g) * (u.im - v.im + g) :=
      mul_nonneg (sub_nonneg.mpr hdifference) (by linarith)
    dsimp [normSq]
    nlinarith [hproduct, sq_nonneg (v.re - u.re)]

/-- Existential separation therefore supplies an explicit positive rational
squared-norm gap. -/
theorem Separated.exists_normSq_gap
    {B C : RatBox} (hseparated : B.Separated C)
    {u v : GaussianRat} (hu : B.Contains u) (hv : C.Contains v) :
    ∃ gapSq : ℚ, 0 < gapSq ∧ gapSq ≤ normSq (v - u) := by
  rcases hseparated with ⟨g, hg, hgap⟩
  exact ⟨g ^ 2, sq_pos_of_pos hg,
    sq_le_normSq_sub_of_coordinate_gap hg hgap hu hv⟩

/-- Closed left child made by a certified vertical rational cut. -/
def verticalLeft (B : RatBox) (c : ℚ) (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) : RatBox where
  xLower := B.xLower
  xUpper := c
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := hc.1
  y_valid := B.y_valid

/-- Closed right child made by a certified vertical rational cut. -/
def verticalRight (B : RatBox) (c : ℚ) (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) : RatBox where
  xLower := c
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := hc.2
  y_valid := B.y_valid

/-- Closed lower child made by a certified horizontal rational cut. -/
def horizontalLower (B : RatBox) (c : ℚ) (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) : RatBox where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := c
  x_valid := B.x_valid
  y_valid := hc.1

/-- Closed upper child made by a certified horizontal rational cut. -/
def horizontalUpper (B : RatBox) (c : ℚ) (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) : RatBox where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := c
  yUpper := B.yUpper
  x_valid := B.x_valid
  y_valid := hc.2

theorem verticalLeft_refines (B : RatBox) (c : ℚ)
    (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) : (B.verticalLeft c hc).Refines B := by
  exact ⟨le_rfl, hc.2, le_rfl, le_rfl⟩

theorem verticalRight_refines (B : RatBox) (c : ℚ)
    (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) : (B.verticalRight c hc).Refines B := by
  exact ⟨hc.1, le_rfl, le_rfl, le_rfl⟩

theorem horizontalLower_refines (B : RatBox) (c : ℚ)
    (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) : (B.horizontalLower c hc).Refines B := by
  exact ⟨le_rfl, le_rfl, le_rfl, hc.2⟩

theorem horizontalUpper_refines (B : RatBox) (c : ℚ)
    (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) : (B.horizontalUpper c hc).Refines B := by
  exact ⟨le_rfl, le_rfl, hc.1, le_rfl⟩

/-- A point of the parent belongs to at least one closed vertical child. -/
theorem contains_verticalLeft_or_right {B : RatBox} {c : ℚ}
    (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) {z : GaussianRat}
    (hz : B.Contains z) :
    (B.verticalLeft c hc).Contains z ∨ (B.verticalRight c hc).Contains z := by
  rcases hz with ⟨hxl, hxu, hyl, hyu⟩
  by_cases hzc : z.re ≤ c
  · exact Or.inl ⟨hxl, hzc, hyl, hyu⟩
  · exact Or.inr ⟨le_of_not_ge hzc, hxu, hyl, hyu⟩

/-- A point of the parent belongs to at least one closed horizontal child. -/
theorem contains_horizontalLower_or_upper {B : RatBox} {c : ℚ}
    (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) {z : GaussianRat}
    (hz : B.Contains z) :
    (B.horizontalLower c hc).Contains z ∨ (B.horizontalUpper c hc).Contains z := by
  rcases hz with ⟨hxl, hxu, hyl, hyu⟩
  by_cases hzc : z.im ≤ c
  · exact Or.inl ⟨hxl, hxu, hyl, hzc⟩
  · exact Or.inr ⟨hxl, hxu, le_of_not_ge hzc, hyu⟩

end RatBox

end CCL
