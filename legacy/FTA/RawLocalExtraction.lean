import FTA.RawSubdivision

/-!
# Complete local extraction from nonzero raw winding

This module assembles Lemmas 7.1--7.2, finite raw-winding subdivision, the
Newton scale inequalities, and the four resultant-certified band searches
into Theorem 7.3.  Starting from a proper rational box with nonzero raw
winding, one total finite computation returns a strictly interior rational
box whose raw winding is exactly four.
-/

namespace FTA.RawLocalExtraction

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.PathPolynomial
open FTA.RawSubdivision
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- Positive Newton-band scale chosen below both the protected-strip radius
and the Taylor-dominance scale. -/
def baseExtractionRadius
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) : ℚ :=
  min (protectedBoundaryRadius p B clearance)
    (min 1 (LocalExtraction.derivativeMargin squarefree B /
      (600 * denseTaylorRemainderBound p B)))

theorem baseExtractionRadius_pos
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) :
    0 < baseExtractionRadius squarefree clearance := by
  have hrho := protectedBoundaryRadius_pos p clearance hB
  have heta := LocalExtraction.derivativeMargin_pos squarefree B
  have hL₂ := denseTaylorRemainderBound_pos p B
  exact lt_min hrho (lt_min zero_lt_one
    (div_pos heta (mul_pos (by norm_num) hL₂)))

theorem baseExtractionRadius_le_protectedBoundaryRadius
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) :
    baseExtractionRadius squarefree clearance ≤
      protectedBoundaryRadius p B clearance := min_le_left _ _

theorem baseExtractionRadius_taylor
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) :
    300 * denseTaylorRemainderBound p B *
        baseExtractionRadius squarefree clearance ^ 2 <
      LocalExtraction.derivativeMargin squarefree B := by
  let r := baseExtractionRadius squarefree clearance
  let eta := LocalExtraction.derivativeMargin squarefree B
  let L₂ := denseTaylorRemainderBound p B
  have hr : 0 < r := baseExtractionRadius_pos squarefree clearance hB
  have hrOne : r ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrRatio : r ≤ eta / (600 * L₂) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hL₂ : 0 < L₂ := denseTaylorRemainderBound_pos p B
  have hscaled : 600 * L₂ * r ≤ eta := by
    have := (le_div_iff₀ (mul_pos (by norm_num) hL₂)).1 hrRatio
    calc
      600 * L₂ * r = r * (600 * L₂) := by ring
      _ ≤ eta := this
  have hsqLe : r ^ 2 ≤ r := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hrOne)]
  dsimp only [r, eta, L₂] at hscaled hsqLe ⊢
  nlinarith

/-- Requested Newton-band radius.  The extra `ε / 8` cap makes the final
band's squared diagonal at most `ε²`. -/
def extractionRadius
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) : ℚ :=
  min (baseExtractionRadius squarefree clearance) (ε / 8)

theorem extractionRadius_pos
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) {ε : ℚ} (hε : 0 < ε) :
    0 < extractionRadius squarefree clearance ε :=
  lt_min (baseExtractionRadius_pos squarefree clearance hB)
    (div_pos hε (by norm_num))

theorem extractionRadius_le_protectedBoundaryRadius
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) :
    extractionRadius squarefree clearance ε ≤
      protectedBoundaryRadius p B clearance :=
  (min_le_left _ _).trans
    (baseExtractionRadius_le_protectedBoundaryRadius squarefree clearance)

theorem extractionRadius_le_eighth
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) :
    extractionRadius squarefree clearance ε ≤ ε / 8 := min_le_right _ _

theorem extractionRadius_taylor
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) {ε : ℚ} (hε : 0 < ε) :
    300 * denseTaylorRemainderBound p B *
        extractionRadius squarefree clearance ε ^ 2 <
      LocalExtraction.derivativeMargin squarefree B := by
  let r := extractionRadius squarefree clearance ε
  let r₀ := baseExtractionRadius squarefree clearance
  have hr : 0 < r := extractionRadius_pos squarefree clearance hB hε
  have hr₀ : 0 < r₀ := baseExtractionRadius_pos squarefree clearance hB
  have hrLe : r ≤ r₀ := min_le_left _ _
  have hsq : r ^ 2 ≤ r₀ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrLe) (by linarith : 0 ≤ r + r₀)]
  calc
    300 * denseTaylorRemainderBound p B * r ^ 2 ≤
        300 * denseTaylorRemainderBound p B * r₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (by norm_num) (denseTaylorRemainderBound_pos p B).le)
    _ < LocalExtraction.derivativeMargin squarefree B :=
      baseExtractionRadius_taylor squarefree clearance hB

/-- Positive squared-diagonal target sufficient for the protected strip,
the derivative threshold, and the Newton displacement inequality. -/
def sourceDiagonalThreshold
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) : ℚ :=
  let rho := protectedBoundaryRadius p B clearance
  let r := extractionRadius squarefree clearance ε
  let L₁ := denseLipschitzBound p B
  min (rho ^ 2)
      (min (LocalExtraction.derivativeThreshold squarefree B / L₁)
      (LocalExtraction.derivativeMargin squarefree B * r ^ 2 / (32 * L₁)))

theorem sourceDiagonalThreshold_pos
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) {ε : ℚ} (hε : 0 < ε) :
    0 < sourceDiagonalThreshold squarefree clearance ε := by
  have hrho := protectedBoundaryRadius_pos p clearance hB
  have hr := extractionRadius_pos squarefree clearance hB hε
  have hL₁ := denseLipschitzBound_pos p B
  have htau := LocalExtraction.derivativeThreshold_pos squarefree B
  have heta := LocalExtraction.derivativeMargin_pos squarefree B
  exact lt_min (sq_pos_of_pos hrho)
    (lt_min (div_pos htau hL₁)
      (div_pos (mul_pos heta (sq_pos_of_pos hr))
        (mul_pos (by norm_num) hL₁)))

theorem sourceDiagonalThreshold_le_protected_sq
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) :
    sourceDiagonalThreshold squarefree clearance ε ≤
      protectedBoundaryRadius p B clearance ^ 2 := min_le_left _ _

/-- A squared Euclidean displacement below `(r / 4)²` puts both rational
coordinates strictly between `-r / 4` and `r / 4`. -/
theorem coordinate_bounds_of_sq_add_sq_lt
    {x y r : ℚ} (hr : 0 < r)
    (hnear : x ^ 2 + y ^ 2 < r ^ 2 / 16) :
    -r / 4 < x ∧ x < r / 4 ∧ -r / 4 < y ∧ y < r / 4 := by
  have hxUpper : x < r / 4 := by
    by_contra hnot
    have hx : r / 4 ≤ x := le_of_not_gt hnot
    have hproduct : 0 ≤ (x - r / 4) * (x + r / 4) :=
      mul_nonneg (sub_nonneg.mpr hx) (by linarith)
    nlinarith [sq_nonneg y]
  have hxLower : -r / 4 < x := by
    by_contra hnot
    have hx : x ≤ -r / 4 := le_of_not_gt hnot
    have hproduct : 0 ≤ (x + r / 4) * (x - r / 4) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [sq_nonneg y]
  have hyUpper : y < r / 4 := by
    by_contra hnot
    have hy : r / 4 ≤ y := le_of_not_gt hnot
    have hproduct : 0 ≤ (y - r / 4) * (y + r / 4) :=
      mul_nonneg (sub_nonneg.mpr hy) (by linarith)
    nlinarith [sq_nonneg x]
  have hyLower : -r / 4 < y := by
    by_contra hnot
    have hy : y ≤ -r / 4 := le_of_not_gt hnot
    have hproduct : 0 ≤ (y + r / 4) * (y - r / 4) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [sq_nonneg x]
  exact ⟨hxLower, hxUpper, hyLower, hyUpper⟩

/-- A nonzero-raw-winding source below the protected diagonal scale cannot
touch any of the four protected strips of its ambient box. -/
theorem strictly_inside_protectedBoundary
    {p : GaussianPolynomial} {B source : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) (hsourceProper : source.Proper)
    (hsourceRefines : source.Refines B)
    (hsourceRaw : quadrupledBoxWinding p source ≠ 0)
    (hsourceDiagonal : source.diagonalSq ≤
      protectedBoundaryRadius p B clearance ^ 2) :
    let rho := protectedBoundaryRadius p B clearance
    B.xLower + 4 * rho < source.xLower ∧
      source.xUpper < B.xUpper - 4 * rho ∧
      B.yLower + 4 * rho < source.yLower ∧
      source.yUpper < B.yUpper - 4 * rho := by
  let rho := protectedBoundaryRadius p B clearance
  have hleft : B.xLower + 4 * rho < source.xLower := by
    by_contra hnot
    have hside : source.xLower ≤ B.xLower + 4 * rho := le_of_not_gt hnot
    let point := CCL.GaussianRat.mk source.xLower source.yLower
    let witness : BoundaryStripWitness B source (4 * rho) :=
      { point := point
        point_mem := ⟨le_rfl, source.x_valid, le_rfl, source.y_valid⟩
        side := CoordinateBoundaryStripSide.left hside }
    apply hsourceRaw
    exact quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
      p clearance hB hsourceProper hsourceRefines hsourceDiagonal witness
  have hright : source.xUpper < B.xUpper - 4 * rho := by
    by_contra hnot
    have hside : B.xUpper - 4 * rho ≤ source.xUpper := le_of_not_gt hnot
    let point := CCL.GaussianRat.mk source.xUpper source.yLower
    let witness : BoundaryStripWitness B source (4 * rho) :=
      { point := point
        point_mem := ⟨source.x_valid, le_rfl, le_rfl, source.y_valid⟩
        side := CoordinateBoundaryStripSide.right hside }
    apply hsourceRaw
    exact quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
      p clearance hB hsourceProper hsourceRefines hsourceDiagonal witness
  have hbottom : B.yLower + 4 * rho < source.yLower := by
    by_contra hnot
    have hside : source.yLower ≤ B.yLower + 4 * rho := le_of_not_gt hnot
    let point := CCL.GaussianRat.mk source.xLower source.yLower
    let witness : BoundaryStripWitness B source (4 * rho) :=
      { point := point
        point_mem := ⟨le_rfl, source.x_valid, le_rfl, source.y_valid⟩
        side := CoordinateBoundaryStripSide.bottom hside }
    apply hsourceRaw
    exact quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
      p clearance hB hsourceProper hsourceRefines hsourceDiagonal witness
  have htop : source.yUpper < B.yUpper - 4 * rho := by
    by_contra hnot
    have hside : B.yUpper - 4 * rho ≤ source.yUpper := le_of_not_gt hnot
    let point := CCL.GaussianRat.mk source.xLower source.yUpper
    let witness : BoundaryStripWitness B source (4 * rho) :=
      { point := point
        point_mem := ⟨le_rfl, source.x_valid, source.y_valid, le_rfl⟩
        side := CoordinateBoundaryStripSide.top hside }
    apply hsourceRaw
    exact quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
      p clearance hB hsourceProper hsourceRefines hsourceDiagonal witness
  exact ⟨hleft, hright, hbottom, htop⟩

/-- The outer Newton-band square is contained in the ambient box once its
source lies beyond the protected strips and the Newton displacement is below
one quarter of the band radius. -/
theorem bandSquareInside_of_normSq_sub_center_lt
    {B source : CCL.RatBox} {center : QI} {r rho : ℚ}
    (hr : 0 < r) (hrLeRho : r ≤ rho)
    (hleft : B.xLower + 4 * rho < source.xLower)
    (hright : source.xUpper < B.xUpper - 4 * rho)
    (hbottom : B.yLower + 4 * rho < source.yLower)
    (htop : source.yUpper < B.yUpper - 4 * rho)
    (hnear : normSq (center - source.center) < r ^ 2 / 16) :
    BandSquareInside B center r := by
  have hcoordinateNear :
      (center.re - source.center.re) ^ 2 +
          (center.im - source.center.im) ^ 2 < r ^ 2 / 16 := by
    simpa only [normSq, sub_re, sub_im] using hnear
  rcases coordinate_bounds_of_sq_add_sq_lt hr hcoordinateNear with
    ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  have hsourceCenter := source.contains_center
  constructor
  · linarith [hsourceCenter.1]
  · linarith [hsourceCenter.2.1]
  · linarith [hsourceCenter.2.2.1]
  · linarith [hsourceCenter.2.2.2]

/-- Every rectangle selected in the Newton bands is strictly inside the
ambient box under the same protected-strip hypotheses. -/
theorem newtonBand_strictly_inside
    {B source : CCL.RatBox} {center : QI} {r rho : ℚ}
    (hr : 0 < r) (hrLeRho : r ≤ rho)
    (hleft : B.xLower + 4 * rho < source.xLower)
    (hright : source.xUpper < B.xUpper - 4 * rho)
    (hbottom : B.yLower + 4 * rho < source.yLower)
    (htop : source.yUpper < B.yUpper - 4 * rho)
    (hnear : normSq (center - source.center) < r ^ 2 / 16)
    (band : NewtonBandBox center r) :
    B.xLower < band.box.xLower ∧ band.box.xUpper < B.xUpper ∧
      B.yLower < band.box.yLower ∧ band.box.yUpper < B.yUpper := by
  have hcoordinateNear :
      (center.re - source.center.re) ^ 2 +
          (center.im - source.center.im) ^ 2 < r ^ 2 / 16 := by
    simpa only [normSq, sub_re, sub_im] using hnear
  rcases coordinate_bounds_of_sq_add_sq_lt hr hcoordinateNear with
    ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  have hsourceCenter := source.contains_center
  constructor
  · linarith [hsourceCenter.1, band.left_lower]
  constructor
  · linarith [hsourceCenter.2.1, band.right_upper]
  constructor
  · linarith [hsourceCenter.2.2.1, band.bottom_lower]
  · linarith [hsourceCenter.2.2.2, band.top_upper]

/-- The finite raw-subdivision phase, packaged separately from the Newton
phase so neither proof needs enlarged elaboration limits. -/
structure SourceOutput
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B) (ε : ℚ) where
  source : CCL.RatBox
  refines : source.Refines B
  proper : source.Proper
  rawWinding_ne : quadrupledBoxWinding p source ≠ 0
  diagonalSq_le : source.diagonalSq ≤
    sourceDiagonalThreshold squarefree clearance ε

/-- Shrink a nonzero-raw-winding box to the coefficient-computed source
scale used by the Newton phase. -/
def selectSource
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) (hraw : quadrupledBoxWinding p B ≠ 0)
    {ε : ℚ} (hε : 0 < ε)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    SourceOutput p B squarefree clearance ε := by
  let initial : RawWindingState p B :=
    { box := B
      refinesAmbient := CCL.RatBox.refines_refl B
      proper := hB
      rawWinding_ne := hraw }
  let threshold := sourceDiagonalThreshold squarefree clearance ε
  have hthreshold : 0 < threshold :=
    sourceDiagonalThreshold_pos squarefree clearance hB hε
  let state := refineTo elimination initial threshold
  exact
    { source := state.box
      refines := state.refinesAmbient
      proper := state.proper
      rawWinding_ne := state.rawWinding_ne
      diagonalSq_le :=
        refineTo_diagonalSq_le elimination initial hthreshold }

/-- Proof-bearing output of the complete local extraction. -/
structure Output
    (p : GaussianPolynomial) (B : CCL.RatBox) (D : ℕ) (ε : ℚ) where
  source : CCL.RatBox
  source_refines : source.Refines B
  source_proper : source.Proper
  source_rawWinding_ne : quadrupledBoxWinding p source ≠ 0
  radius : ℚ
  band : SafeNewtonBandOutput p B source D radius
  band_diagonalSq_le : band.band.box.diagonalSq ≤ ε ^ 2
  band_strictly_inside :
    B.xLower < band.band.box.xLower ∧
      band.band.box.xUpper < B.xUpper ∧
      B.yLower < band.band.box.yLower ∧
      band.band.box.yUpper < B.yUpper

/-- Complete the Newton and safe-band phases from a sufficiently small raw
source box. -/
def extractFromSource
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) {ε : ℚ} (hε : 0 < ε) {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (sourceData : SourceOutput p B squarefree clearance ε) :
    Output p B D ε := by
  let threshold := sourceDiagonalThreshold squarefree clearance ε
  let source := sourceData.source
  have hsourceRefines : source.Refines B := sourceData.refines
  have hsourceProper : source.Proper := sourceData.proper
  have hsourceRaw : quadrupledBoxWinding p source ≠ 0 :=
    sourceData.rawWinding_ne
  have hsourceDiagonal : source.diagonalSq ≤ threshold :=
    sourceData.diagonalSq_le
  let rho := protectedBoundaryRadius p B clearance
  let r := extractionRadius squarefree clearance ε
  let L₁ := denseLipschitzBound p B
  let eta := LocalExtraction.derivativeMargin squarefree B
  have hrho : 0 < rho := protectedBoundaryRadius_pos p clearance hB
  have hr : 0 < r := extractionRadius_pos squarefree clearance hB hε
  have hL₁ : 0 < L₁ := denseLipschitzBound_pos p B
  have heta : 0 < eta := LocalExtraction.derivativeMargin_pos squarefree B
  have hrLeRho : r ≤ rho :=
    extractionRadius_le_protectedBoundaryRadius squarefree clearance ε
  have hsourceRho : source.diagonalSq ≤ rho ^ 2 :=
    hsourceDiagonal.trans
      (sourceDiagonalThreshold_le_protected_sq squarefree clearance ε)
  have hsourceDerivative : centerResidualBound p B source ≤
      LocalExtraction.derivativeThreshold squarefree B := by
    have hthresholdDerivative : threshold ≤
        LocalExtraction.derivativeThreshold squarefree B / L₁ :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hscaled : L₁ * threshold ≤
        LocalExtraction.derivativeThreshold squarefree B := by
      have := (le_div_iff₀ hL₁).1 hthresholdDerivative
      calc
        L₁ * threshold = threshold * L₁ := by ring
        _ ≤ LocalExtraction.derivativeThreshold squarefree B := this
    calc
      centerResidualBound p B source = L₁ * source.diagonalSq := rfl
      _ ≤ L₁ * threshold :=
        mul_le_mul_of_nonneg_left hsourceDiagonal hL₁.le
      _ ≤ LocalExtraction.derivativeThreshold squarefree B := hscaled
  have hnear : centerResidualBound p B source / eta < r ^ 2 / 16 := by
    have hthresholdNear : threshold ≤ eta * r ^ 2 / (32 * L₁) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hresidualBound : centerResidualBound p B source ≤
        eta * r ^ 2 / 32 := by
      calc
        centerResidualBound p B source = L₁ * source.diagonalSq := rfl
        _ ≤ L₁ * threshold :=
          mul_le_mul_of_nonneg_left hsourceDiagonal hL₁.le
        _ ≤ L₁ * (eta * r ^ 2 / (32 * L₁)) :=
          mul_le_mul_of_nonneg_left hthresholdNear hL₁.le
        _ = eta * r ^ 2 / 32 := by field_simp [ne_of_gt hL₁]
    have hdiv : centerResidualBound p B source / eta ≤ r ^ 2 / 32 := by
      apply (div_le_iff₀ heta).2
      calc
        centerResidualBound p B source ≤ eta * r ^ 2 / 32 := hresidualBound
        _ = r ^ 2 / 32 * eta := by ring
    nlinarith [sq_pos_of_pos hr]
  have hinterior := strictly_inside_protectedBoundary clearance hB
    hsourceProper hsourceRefines hsourceRaw hsourceRho
  let newton := computeNewtonCenterOfRawWinding p squarefree hsourceRefines
    hsourceProper hsourceRaw hsourceDerivative
  have hnewtonNear : normSq
      (rationalNewtonCenter p source - source.center) < r ^ 2 / 16 :=
    newton.displacement.trans_lt hnear
  have inside : BandSquareInside B (rationalNewtonCenter p source) r :=
    bandSquareInside_of_normSq_sub_center_lt hr hrLeRho
      hinterior.1 hinterior.2.1 hinterior.2.2.1 hinterior.2.2.2
      hnewtonNear
  let band := selectSafeNewtonBand squarefree newton hsourceRefines
    elimination hr inside hnear
      (extractionRadius_taylor squarefree clearance hB hε)
  have hbandDiagonal : band.band.box.diagonalSq ≤ ε ^ 2 := by
    have hrawBound := band.band.diagonalSq_le hr
    have hrEighth : r ≤ ε / 8 :=
      extractionRadius_le_eighth squarefree clearance ε
    have hrNonneg : 0 ≤ r := hr.le
    have hεNonneg : 0 ≤ ε := hε.le
    have hsq : r ^ 2 ≤ (ε / 8) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrEighth)
        (by linarith : 0 ≤ r + ε / 8)]
    nlinarith
  have hbandStrict := newtonBand_strictly_inside hr hrLeRho
    hinterior.1 hinterior.2.1 hinterior.2.2.1 hinterior.2.2.2
    hnewtonNear band.band
  exact
    { source := source
      source_refines := hsourceRefines
      source_proper := hsourceProper
      source_rawWinding_ne := hsourceRaw
      radius := r
      band := band
      band_diagonalSq_le := hbandDiagonal
      band_strictly_inside := hbandStrict }

/-- Theorem 7.3: the complete finite local winding-one extraction. -/
def extract
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hB : B.Proper) (hraw : quadrupledBoxWinding p B ≠ 0)
    {ε : ℚ} (hε : 0 < ε)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Output p B D ε :=
  extractFromSource squarefree clearance hB hε elimination
    (selectSource squarefree clearance hB hraw hε elimination)

end FTA.RawLocalExtraction
