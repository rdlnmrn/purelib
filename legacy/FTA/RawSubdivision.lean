import FTA.AxisSafeCuts

/-!
# Raw-winding safe subdivision

Before global nonnegativity has been proved, normalized winding additivity
would require divisibility hypotheses.  The raw winding is unconditionally
additive.  This module therefore performs the shrinking phase of Theorem 7.3
at the raw normalization: every central safe-cut round chooses the first of
four children with nonzero raw winding and contracts its squared diagonal by
`4/9`.
-/

namespace FTA.RawSubdivision

open CCL
open FTA.AxisSafeCuts
open FTA.PathPolynomial
open FTA.SafeCuts
open FTA.SturmTransducer
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- A proper subbox carrying nonzero raw winding. -/
structure RawWindingState
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  box : CCL.RatBox
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  rawWinding_ne : quadrupledBoxWinding p box ≠ 0

/-- One four-child grid together with exactly the refinement facts used by
the deterministic nonzero-child selector. -/
structure RawFourGrid
    (p : GaussianPolynomial) (parent : CCL.RatBox) where
  lowerLeft : CCL.RatBox
  upperLeft : CCL.RatBox
  lowerRight : CCL.RatBox
  upperRight : CCL.RatBox
  lowerLeft_refines : lowerLeft.Refines parent
  upperLeft_refines : upperLeft.Refines parent
  lowerRight_refines : lowerRight.Refines parent
  upperRight_refines : upperRight.Refines parent
  lowerLeft_proper : lowerLeft.Proper
  upperLeft_proper : upperLeft.Proper
  lowerRight_proper : lowerRight.Proper
  upperRight_proper : upperRight.Proper
  additive : quadrupledBoxWinding p parent =
    quadrupledBoxWinding p lowerLeft +
      quadrupledBoxWinding p upperLeft +
      quadrupledBoxWinding p lowerRight +
      quadrupledBoxWinding p upperRight
  lowerLeft_contract : lowerLeft.diagonalSq ≤
    (4 / 9 : ℚ) * parent.diagonalSq
  upperLeft_contract : upperLeft.diagonalSq ≤
    (4 / 9 : ℚ) * parent.diagonalSq
  lowerRight_contract : lowerRight.diagonalSq ≤
    (4 / 9 : ℚ) * parent.diagonalSq
  upperRight_contract : upperRight.diagonalSq ≤
    (4 / 9 : ℚ) * parent.diagonalSq

/-- One executable central safe-cut grid. -/
def safeRawFourGrid
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) : RawFourGrid p state.box := by
  let cx := verticalSafeCoordinate elimination state.proper.1
  let cy := horizontalSafeCoordinate elimination state.proper.2
  have hcxSpec := verticalSafeCoordinate_spec elimination state.proper.1
  have hcySpec := horizontalSafeCoordinate_spec elimination state.proper.2
  have hcx : state.box.xLower ≤ cx ∧ cx ≤ state.box.xUpper :=
    ⟨hcxSpec.2.1.le, hcxSpec.2.2.le⟩
  have hcy : state.box.yLower ≤ cy ∧ cy ≤ state.box.yUpper :=
    ⟨hcySpec.2.1.le, hcySpec.2.2.le⟩
  have hcxContract :=
    verticalSafeCoordinate_contraction elimination state.proper.1
  have hcyContract :=
    horizontalSafeCoordinate_contraction elimination state.proper.2
  let left := state.box.verticalLeft cx hcx
  let right := state.box.verticalRight cx hcx
  let lowerLeft := left.horizontalLower cy hcy
  let upperLeft := left.horizontalUpper cy hcy
  let lowerRight := right.horizontalLower cy hcy
  let upperRight := right.horizontalUpper cy hcy
  have hcontraction := four_child_diagonal_contraction hcx hcy
    hcxContract.1.le hcxContract.2.le hcyContract.1.le hcyContract.2.le
  exact
    { lowerLeft := lowerLeft
      upperLeft := upperLeft
      lowerRight := lowerRight
      upperRight := upperRight
      lowerLeft_refines :=
        (CCL.RatBox.horizontalLower_refines left cy hcy).trans
          (CCL.RatBox.verticalLeft_refines state.box cx hcx)
      upperLeft_refines :=
        (CCL.RatBox.horizontalUpper_refines left cy hcy).trans
          (CCL.RatBox.verticalLeft_refines state.box cx hcx)
      lowerRight_refines :=
        (CCL.RatBox.horizontalLower_refines right cy hcy).trans
          (CCL.RatBox.verticalRight_refines state.box cx hcx)
      upperRight_refines :=
        (CCL.RatBox.horizontalUpper_refines right cy hcy).trans
          (CCL.RatBox.verticalRight_refines state.box cx hcx)
      lowerLeft_proper := by
        constructor <;> dsimp [lowerLeft, left, CCL.RatBox.horizontalLower,
          CCL.RatBox.verticalLeft] <;> linarith
      upperLeft_proper := by
        constructor <;> dsimp [upperLeft, left, CCL.RatBox.horizontalUpper,
          CCL.RatBox.verticalLeft] <;> linarith
      lowerRight_proper := by
        constructor <;> dsimp [lowerRight, right, CCL.RatBox.horizontalLower,
          CCL.RatBox.verticalRight] <;> linarith
      upperRight_proper := by
        constructor <;> dsimp [upperRight, right, CCL.RatBox.horizontalUpper,
          CCL.RatBox.verticalRight] <;> linarith
      additive := by
        simpa only [lowerLeft, upperLeft, lowerRight, upperRight, left, right]
          using quadrupledBoxWinding_four_split p state.box cx cy hcx hcy
      lowerLeft_contract := hcontraction.1
      upperLeft_contract := hcontraction.2.1
      lowerRight_contract := hcontraction.2.2.1
      upperRight_contract := hcontraction.2.2.2 }

/-- Fixed finite order on the four children: lower-left, upper-left,
lower-right, upper-right. -/
def firstNonzeroChild
    {p : GaussianPolynomial} {parent : CCL.RatBox}
    (grid : RawFourGrid p parent) : CCL.RatBox :=
  if quadrupledBoxWinding p grid.lowerLeft ≠ 0 then grid.lowerLeft
  else if quadrupledBoxWinding p grid.upperLeft ≠ 0 then grid.upperLeft
  else if quadrupledBoxWinding p grid.lowerRight ≠ 0 then grid.lowerRight
  else grid.upperRight

theorem firstNonzeroChild_rawWinding_ne
    {p : GaussianPolynomial} {parent : CCL.RatBox}
    (grid : RawFourGrid p parent)
    (hparent : quadrupledBoxWinding p parent ≠ 0) :
    quadrupledBoxWinding p (firstNonzeroChild grid) ≠ 0 := by
  by_cases h₀ : quadrupledBoxWinding p grid.lowerLeft ≠ 0
  · unfold firstNonzeroChild
    rw [if_pos h₀]
    exact h₀
  by_cases h₁ : quadrupledBoxWinding p grid.upperLeft ≠ 0
  · unfold firstNonzeroChild
    rw [if_neg h₀, if_pos h₁]
    exact h₁
  by_cases h₂ : quadrupledBoxWinding p grid.lowerRight ≠ 0
  · unfold firstNonzeroChild
    rw [if_neg h₀, if_neg h₁, if_pos h₂]
    exact h₂
  have h₃ : quadrupledBoxWinding p grid.upperRight ≠ 0 := by
    intro hzero
    apply hparent
    rw [grid.additive]
    simp only [not_ne_iff.mp h₀, not_ne_iff.mp h₁,
      not_ne_iff.mp h₂, hzero]
    norm_num
  simpa [firstNonzeroChild, h₀, h₁, h₂] using h₃

theorem firstNonzeroChild_refines
    {p : GaussianPolynomial} {parent : CCL.RatBox}
    (grid : RawFourGrid p parent) :
    (firstNonzeroChild grid).Refines parent := by
  by_cases h₀ : quadrupledBoxWinding p grid.lowerLeft ≠ 0
  · simpa [firstNonzeroChild, h₀] using grid.lowerLeft_refines
  by_cases h₁ : quadrupledBoxWinding p grid.upperLeft ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁] using grid.upperLeft_refines
  by_cases h₂ : quadrupledBoxWinding p grid.lowerRight ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.lowerRight_refines
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.upperRight_refines

theorem firstNonzeroChild_proper
    {p : GaussianPolynomial} {parent : CCL.RatBox}
    (grid : RawFourGrid p parent) :
    (firstNonzeroChild grid).Proper := by
  by_cases h₀ : quadrupledBoxWinding p grid.lowerLeft ≠ 0
  · simpa [firstNonzeroChild, h₀] using grid.lowerLeft_proper
  by_cases h₁ : quadrupledBoxWinding p grid.upperLeft ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁] using grid.upperLeft_proper
  by_cases h₂ : quadrupledBoxWinding p grid.lowerRight ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.lowerRight_proper
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.upperRight_proper

theorem firstNonzeroChild_contracts
    {p : GaussianPolynomial} {parent : CCL.RatBox}
    (grid : RawFourGrid p parent) :
    (firstNonzeroChild grid).diagonalSq ≤
      (4 / 9 : ℚ) * parent.diagonalSq := by
  by_cases h₀ : quadrupledBoxWinding p grid.lowerLeft ≠ 0
  · simpa [firstNonzeroChild, h₀] using grid.lowerLeft_contract
  by_cases h₁ : quadrupledBoxWinding p grid.upperLeft ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁] using grid.upperLeft_contract
  by_cases h₂ : quadrupledBoxWinding p grid.lowerRight ≠ 0
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.lowerRight_contract
  · simpa [firstNonzeroChild, h₀, h₁, h₂] using grid.upperRight_contract

/-- One deterministic raw-winding-preserving safe refinement. -/
def refineOnce
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) : RawWindingState p ambient :=
  let grid := safeRawFourGrid elimination state
  { box := firstNonzeroChild grid
    refinesAmbient := (firstNonzeroChild_refines grid).trans
      state.refinesAmbient
    proper := firstNonzeroChild_proper grid
    rawWinding_ne := firstNonzeroChild_rawWinding_ne grid state.rawWinding_ne }

theorem refineOnce_refines
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.Refines state.box := by
  exact firstNonzeroChild_refines (safeRawFourGrid elimination state)

theorem refineOnce_contracts
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.diagonalSq ≤
      (4 / 9 : ℚ) * state.box.diagonalSq := by
  exact firstNonzeroChild_contracts (safeRawFourGrid elimination state)

/-- Fixed-depth iteration of the safe raw refinement. -/
def refineN
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D) :
    ℕ → RawWindingState p ambient → RawWindingState p ambient
  | 0, state => state
  | n + 1, state => refineOnce elimination (refineN elimination n state)

theorem refineN_refines
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (n : ℕ) (state : RawWindingState p ambient) :
    (refineN elimination n state).box.Refines state.box := by
  induction n with
  | zero => exact CCL.RatBox.refines_refl _
  | succ n ih =>
      exact (refineOnce_refines elimination (refineN elimination n state)).trans ih

theorem refineN_diagonalSq_le
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (n : ℕ) (state : RawWindingState p ambient) :
    (refineN elimination n state).box.diagonalSq ≤
      (4 / 9 : ℚ) ^ n * state.box.diagonalSq := by
  induction n with
  | zero => simp [refineN]
  | succ n ih =>
      calc
        (refineN elimination (n + 1) state).box.diagonalSq ≤
            (4 / 9 : ℚ) *
              (refineN elimination n state).box.diagonalSq :=
          refineOnce_contracts elimination (refineN elimination n state)
        _ ≤ (4 / 9 : ℚ) *
              ((4 / 9 : ℚ) ^ n * state.box.diagonalSq) := by
          gcongr
        _ = (4 / 9 : ℚ) ^ (n + 1) * state.box.diagonalSq := by
          rw [pow_succ]
          ring

/-- Explicit natural depth sufficient for a requested positive squared
diagonal. -/
def refinementDepth
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (state : RawWindingState p ambient) (threshold : ℚ) : ℕ :=
  geometricDepth state.box.diagonalSq threshold

/-- Total finite refinement to the requested positive squared diagonal. -/
def refineTo
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) (threshold : ℚ) :
    RawWindingState p ambient :=
  refineN elimination (refinementDepth state threshold) state

theorem refineTo_diagonalSq_le
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) {threshold : ℚ}
    (hthreshold : 0 < threshold) :
    (refineTo elimination state threshold).box.diagonalSq ≤ threshold := by
  let n := refinementDepth state threshold
  have hraw := refineN_diagonalSq_le elimination n state
  have hpow : (4 / 9 : ℚ) ^ n ≤ (2 / 3 : ℚ) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hscaled : (4 / 9 : ℚ) ^ n * state.box.diagonalSq ≤
      (2 / 3 : ℚ) ^ n * state.box.diagonalSq :=
    mul_le_mul_of_nonneg_right hpow state.box.diagonalSq_nonneg
  exact hraw.trans (hscaled.trans (by
    simpa only [n, refinementDepth] using
      geometricDepth_sufficient state.box.diagonalSq_nonneg hthreshold))

theorem refineTo_refines
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (state : RawWindingState p ambient) (threshold : ℚ) :
    (refineTo elimination state threshold).box.Refines state.box :=
  refineN_refines elimination (refinementDepth state threshold) state

end FTA.RawSubdivision
