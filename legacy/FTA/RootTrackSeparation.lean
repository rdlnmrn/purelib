import FTA.BoxClearance
import FTA.CentralBandGrid
import FTA.GaussianDifferenceResultant
import FTA.LocalExtraction

/-!
# Separation of nonterminal winding-one tracks

This module connects the Gaussian difference-resultant inequalities to the
finite winding-box refinement interface.  It formalizes Theorem 8.2 for the
nonterminal part of a root-approximation transducer: two tracks with a
displayed positive coordinate gap cannot both be supported in a common box
whose squared diagonal is below the coefficient-computed separation radius.
-/

namespace FTA.RootTrackSeparation

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Winding
open FTA.GaussianDerivative
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.GaussianDifferenceResultant

/-- One finite nonterminal state of the numerical, winding-one part of a
root-approximation transducer. -/
structure WindingOneState
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  box : CCL.RatBox
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  rawWindingFour : quadrupledBoxWinding p box = 4
  clearance : BoxBoundaryClearanceCertificate p box
  ambientLeftClearance : FTA.BoxClearance.VerticalLineClearance p ambient box.xLower
  ambientRightClearance : FTA.BoxClearance.VerticalLineClearance p ambient box.xUpper
  ambientBottomClearance :
    FTA.BoxClearance.HorizontalLineClearance p ambient box.yLower
  ambientTopClearance :
    FTA.BoxClearance.HorizontalLineClearance p ambient box.yUpper

namespace WindingOneState

theorem windingOne
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (state : WindingOneState p ambient) :
    boxWinding p state.box = 1 := by
  rw [boxWinding, state.rawWindingFour]
  norm_num

theorem rawWinding_ne
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (state : WindingOneState p ambient) :
    quadrupledBoxWinding p state.box ≠ 0 := by
  rw [state.rawWindingFour]
  norm_num

theorem winding_ne_zero
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (state : WindingOneState p ambient) :
    boxWinding p state.box ≠ 0 := by
  rw [state.windingOne]
  norm_num

end WindingOneState

/-- Total finite-precision interface for a nonterminal winding-one track.
Every call is an ordinary function call on finite state and rational input. -/
structure WindingOneTrack
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  initial : WindingOneState p ambient
  refine : (current : WindingOneState p ambient) →
    (ε : ℚ) → 0 < ε → WindingOneState p ambient
  nested : ∀ current ε hε,
    (refine current ε hε).box.Refines current.box
  strict : ∀ current ε hε,
    FTA.CentralBandGrid.StrictInterior
      (refine current ε hε).box current.box
  accurate : ∀ current ε hε,
    (refine current ε hε).box.diagonalSq ≤ ε ^ 2

/-- The pointwise dense Gaussian Bézout certificate gives the exact sparse
polynomial identity required by the resultant construction. -/
def sparseSquarefreeCertificate
    {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p) :
    SquarefreeCert p.toPolynomial where
  U := certificate.left.toPolynomial
  V := certificate.right.toPolynomial
  bezout := by
    rw [← FTA.GaussianDerivative.toPolynomial_derivative]
    exact certificate.identity

/-- Rational refinement radius which forces the center residual below a
prescribed positive threshold. -/
def residualRefinementRadius
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (threshold : ℚ) : ℚ :=
  min 1 (threshold / denseLipschitzBound p ambient)

theorem residualRefinementRadius_pos
    (p : GaussianPolynomial) (ambient : CCL.RatBox) {threshold : ℚ}
    (hthreshold : 0 < threshold) :
    0 < residualRefinementRadius p ambient threshold := by
  apply lt_min
  · norm_num
  · exact div_pos hthreshold (denseLipschitzBound_pos p ambient)

theorem denseLipschitzBound_mul_refinementRadius_sq_le
    (p : GaussianPolynomial) (ambient : CCL.RatBox) {threshold : ℚ}
    (hthreshold : 0 < threshold) :
    denseLipschitzBound p ambient *
        residualRefinementRadius p ambient threshold ^ 2 ≤ threshold := by
  let radius := residualRefinementRadius p ambient threshold
  let L := denseLipschitzBound p ambient
  have hradiusPos : 0 < radius :=
    residualRefinementRadius_pos p ambient hthreshold
  have hradiusOne : radius ≤ 1 := min_le_left _ _
  have hradiusRatio : radius ≤ threshold / L := min_le_right _ _
  have hLPos : 0 < L := denseLipschitzBound_pos p ambient
  have hradiusSq : radius ^ 2 ≤ radius := by
    nlinarith [mul_nonneg hradiusPos.le (sub_nonneg.mpr hradiusOne)]
  calc
    L * radius ^ 2 ≤ L * radius :=
      mul_le_mul_of_nonneg_left hradiusSq hLPos.le
    _ ≤ L * (threshold / L) :=
      mul_le_mul_of_nonneg_left hradiusRatio hLPos.le
    _ = threshold := by field_simp [ne_of_gt hLPos]

/-- Refining a winding-one state at the displayed radius makes its rational
center a certified approximate root below the requested threshold. -/
theorem refined_center_residual_le
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) {threshold : ℚ}
    (hthreshold : 0 < threshold) :
    let radius := residualRefinementRadius p ambient threshold
    let refined := track.refine current radius
      (residualRefinementRadius_pos p ambient hthreshold)
    normSq (p.eval refined.box.center) ≤ threshold := by
  dsimp only
  let radius := residualRefinementRadius p ambient threshold
  let hRadius := residualRefinementRadius_pos p ambient hthreshold
  let refined := track.refine current radius hRadius
  have hresidual := center_residual_le_of_boxWinding_ne_zero
    p refined.refinesAmbient refined.proper refined.winding_ne_zero
  have hdiagonal := track.accurate current radius hRadius
  calc
    normSq (p.eval refined.box.center) ≤
        centerResidualBound p ambient refined.box := hresidual
    _ = denseLipschitzBound p ambient * refined.box.diagonalSq := rfl
    _ ≤ denseLipschitzBound p ambient * radius ^ 2 :=
      mul_le_mul_of_nonneg_left hdiagonal
        (denseLipschitzBound_pos p ambient).le
    _ ≤ threshold :=
      denseLipschitzBound_mul_refinementRadius_sq_le
        p ambient hthreshold

/-- Theorem 8.2 for two displayed nonterminal winding-one tracks.  All
refinements used in the proof are finite calls at an explicit positive
rational accuracy. -/
theorem separated_tracks_not_supported_in_small_common_box
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    (leftTrack rightTrack : WindingOneTrack p ambient)
    (leftState rightState : WindingOneState p ambient)
    (hseparated : leftState.box.Separated rightState.box)
    (common : CCL.RatBox)
    (hleftCommon : leftState.box.Refines common)
    (hrightCommon : rightState.box.Refines common)
    (hsmall : common.diagonalSq <
      squarefreeSeparationRadius
        (sparseSquarefreeCertificate squarefree) ^ 2) : False := by
  let sparseCertificate := sparseSquarefreeCertificate squarefree
  obtain ⟨A, B, hbezout⟩ :=
    exists_resultant_bezout p.toPolynomial hdegree
  rcases hseparated with ⟨gap, hgapPos, hgap⟩
  let threshold := rootPairResidualThreshold sparseCertificate
    A B ambient (gap ^ 2)
  have hgapSqPos : 0 < gap ^ 2 := sq_pos_of_pos hgapPos
  have hthresholdPos : 0 < threshold :=
    rootPairResidualThreshold_pos sparseCertificate A B ambient hgapSqPos
  let radius := residualRefinementRadius p ambient threshold
  let hRadius := residualRefinementRadius_pos p ambient hthresholdPos
  let leftRefined := leftTrack.refine leftState radius hRadius
  let rightRefined := rightTrack.refine rightState radius hRadius
  let u := leftRefined.box.center
  let v := rightRefined.box.center
  have huResidualDense : normSq (p.eval u) ≤ threshold := by
    simpa only [radius, hRadius, leftRefined, u] using
      refined_center_residual_le leftTrack leftState hthresholdPos
  have hvResidualDense : normSq (p.eval v) ≤ threshold := by
    simpa only [radius, hRadius, rightRefined, v] using
      refined_center_residual_le rightTrack rightState hthresholdPos
  have huResidual :
      normSq (p.toPolynomial.eval u) ≤
        rootPairResidualThreshold sparseCertificate
          A B ambient (gap ^ 2) := by
    rw [eval_toPolynomial]
    exact huResidualDense
  have hvResidual :
      normSq (p.toPolynomial.eval v) ≤
        rootPairResidualThreshold sparseCertificate
          A B ambient (gap ^ 2) := by
    rw [eval_toPolynomial]
    exact hvResidualDense
  have huAmbient : ambient.Contains u :=
    leftRefined.refinesAmbient.contains leftRefined.box.contains_center
  have huLeft : leftState.box.Contains u :=
    (leftTrack.nested leftState radius hRadius).contains
      leftRefined.box.contains_center
  have hvRight : rightState.box.Contains v :=
    (rightTrack.nested rightState radius hRadius).contains
      rightRefined.box.contains_center
  have huCommon : common.Contains u :=
    hleftCommon.contains huLeft
  have hvCommon : common.Contains v :=
    hrightCommon.contains hvRight
  exact residual_pair_contradiction_of_coordinate_gap
    sparseCertificate ambient common leftState.box rightState.box
    hbezout huAmbient huLeft hvRight huCommon hvCommon hgapPos hgap
    hsmall huResidual hvResidual

end FTA.RootTrackSeparation
