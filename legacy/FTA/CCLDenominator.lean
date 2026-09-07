import FTA.CCLGeometry
import FTA.RootTrackSeparation

/-!
# Finite exclusion of a CCL decoder pole

This module formalizes the first branch of Theorem 10.2.  Exact evaluation
first decides whether the unique rational pole of a decoder homography is a
polynomial zero supported by the current box.  An outside pole is separated
immediately, even when it is another polynomial root; a nonroot pole still
uses one explicit track refinement.  A decidable side witness then gives a
positive rational lower bound for the decoder denominator norm everywhere in
the resulting box.
-/

namespace FTA
namespace CCLDenominator

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.GaussianPolynomialBounds
open FTA.RootTrackSeparation
open FTA.CCLGeometry

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

/-- One explicit side by which a rational point lies outside a rational box. -/
inductive OutsideSide (B : CCL.RatBox) (point : QI) where
  | left (h : point.re < B.xLower)
  | right (h : B.xUpper < point.re)
  | bottom (h : point.im < B.yLower)
  | top (h : B.yUpper < point.im)

/-- A failed box-membership test computes one of four strict side witnesses. -/
def outsideSide {B : CCL.RatBox} {point : QI}
    (houtside : ¬B.Contains point) : OutsideSide B point := by
  by_cases hleft : point.re < B.xLower
  · exact .left hleft
  by_cases hright : B.xUpper < point.re
  · exact .right hright
  by_cases hbottom : point.im < B.yLower
  · exact .bottom hbottom
  by_cases htop : B.yUpper < point.im
  · exact .top htop
  exfalso
  apply houtside
  exact ⟨not_lt.mp hleft, not_lt.mp hright,
    not_lt.mp hbottom, not_lt.mp htop⟩

namespace OutsideSide

/-- Squared coordinate distance certified by the selected outside side. -/
def margin {B : CCL.RatBox} {point : QI} : OutsideSide B point → ℚ
  | .left _ => (B.xLower - point.re) ^ 2
  | .right _ => (point.re - B.xUpper) ^ 2
  | .bottom _ => (B.yLower - point.im) ^ 2
  | .top _ => (point.im - B.yUpper) ^ 2

theorem margin_pos {B : CCL.RatBox} {point : QI}
    (side : OutsideSide B point) : 0 < side.margin := by
  cases side with
  | left h => exact sq_pos_of_pos (sub_pos.mpr h)
  | right h => exact sq_pos_of_pos (sub_pos.mpr h)
  | bottom h => exact sq_pos_of_pos (sub_pos.mpr h)
  | top h => exact sq_pos_of_pos (sub_pos.mpr h)

/-- Every point in the box stays at least the displayed squared coordinate
distance from the excluded point. -/
theorem margin_le_normSq_sub {B : CCL.RatBox} {point z : QI}
    (side : OutsideSide B point) (hz : B.Contains z) :
    side.margin ≤ normSq (z - point) := by
  rcases hz with ⟨hzLeft, hzRight, hzBottom, hzTop⟩
  cases side with
  | left h =>
      have hgap : 0 ≤ B.xLower - point.re := (sub_pos.mpr h).le
      have hcoordinate : 0 ≤ z.re - point.re := by linarith
      have hsquare : (B.xLower - point.re) ^ 2 ≤ (z.re - point.re) ^ 2 :=
        (sq_le_sq₀ hgap hcoordinate).2 (by linarith)
      dsimp [margin, normSq]
      nlinarith [sq_nonneg (z.im - point.im)]
  | right h =>
      have hgap : 0 ≤ point.re - B.xUpper := (sub_pos.mpr h).le
      have hcoordinate : 0 ≤ point.re - z.re := by linarith
      have hsquare : (point.re - B.xUpper) ^ 2 ≤ (point.re - z.re) ^ 2 :=
        (sq_le_sq₀ hgap hcoordinate).2 (by linarith)
      dsimp [margin, normSq]
      nlinarith [sq_nonneg (z.im - point.im)]
  | bottom h =>
      have hgap : 0 ≤ B.yLower - point.im := (sub_pos.mpr h).le
      have hcoordinate : 0 ≤ z.im - point.im := by linarith
      have hsquare : (B.yLower - point.im) ^ 2 ≤ (z.im - point.im) ^ 2 :=
        (sq_le_sq₀ hgap hcoordinate).2 (by linarith)
      dsimp [margin, normSq]
      nlinarith [sq_nonneg (z.re - point.re)]
  | top h =>
      have hgap : 0 ≤ point.im - B.yUpper := (sub_pos.mpr h).le
      have hcoordinate : 0 ≤ point.im - z.im := by linarith
      have hsquare : (point.im - B.yUpper) ^ 2 ≤ (point.im - z.im) ^ 2 :=
        (sq_le_sq₀ hgap hcoordinate).2 (by linarith)
      dsimp [margin, normSq]
      nlinarith [sq_nonneg (z.re - point.re)]

end OutsideSide

/-- The residual threshold used to exclude one exact nonroot point. -/
def nonrootThreshold (p : GaussianPolynomial) (point : QI) : ℚ :=
  normSq (p.eval point) / 8

theorem nonrootThreshold_pos {p : GaussianPolynomial} {point : QI}
    (hnonroot : p.eval point ≠ 0) : 0 < nonrootThreshold p point := by
  exact div_pos (normSq_pos hnonroot) (by norm_num)

/-- One explicit finite track call at the residual radius for a nonroot point. -/
def refineAwayFromNonroot
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (point : QI)
    (hnonroot : p.eval point ≠ 0) : WindingOneState p ambient :=
  let threshold := nonrootThreshold p point
  let radius := residualRefinementRadius p ambient threshold
  track.refine current radius
    (residualRefinementRadius_pos p ambient (nonrootThreshold_pos hnonroot))

theorem refineAwayFromNonroot_refines
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (point : QI)
    (hnonroot : p.eval point ≠ 0) :
    (refineAwayFromNonroot track current point hnonroot).box.Refines current.box := by
  exact track.nested current
    (residualRefinementRadius p ambient (nonrootThreshold p point))
    (residualRefinementRadius_pos p ambient (nonrootThreshold_pos hnonroot))

/-- The explicit residual refinement cannot still contain the exact nonroot
point.  Otherwise two finite polynomial bounds would force
`N(f(point)) ≤ N(f(point))/2`. -/
theorem refineAwayFromNonroot_excludes
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (point : QI)
    (hnonroot : p.eval point ≠ 0) :
    ¬(refineAwayFromNonroot track current point hnonroot).box.Contains point := by
  let threshold := nonrootThreshold p point
  let radius := residualRefinementRadius p ambient threshold
  let hthreshold : 0 < threshold := nonrootThreshold_pos hnonroot
  let hRadius : 0 < radius := residualRefinementRadius_pos p ambient hthreshold
  let refined := track.refine current radius hRadius
  have hrefined : refined = refineAwayFromNonroot track current point hnonroot := rfl
  rw [← hrefined]
  intro hpointBox
  have hcenterBox : refined.box.Contains refined.box.center :=
    refined.box.contains_center
  have hcenterAmbient : ambient.Contains refined.box.center :=
    refined.refinesAmbient.contains hcenterBox
  have hpointAmbient : ambient.Contains point :=
    refined.refinesAmbient.contains hpointBox
  have hcenterResidual : normSq (p.eval refined.box.center) ≤ threshold := by
    simpa only [radius, hRadius, refined] using
      refined_center_residual_le track current hthreshold
  have hpointDistance : normSq (refined.box.center - point) ≤
      refined.box.diagonalSq :=
    CCL.RatBox.normSq_sub_le_diagonalSq hcenterBox hpointBox
  have hevalDifference :
      normSq (p.eval refined.box.center - p.eval point) ≤ threshold := by
    have hlipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound
      p hcenterAmbient hpointAmbient
    have hdiagonal := track.accurate current radius hRadius
    calc
      normSq (p.eval refined.box.center - p.eval point) ≤
          denseLipschitzBound p ambient *
            normSq (refined.box.center - point) := by
        simpa only [GaussianRat.sub_eq_add_neg] using hlipschitz
      _ ≤ denseLipschitzBound p ambient * refined.box.diagonalSq :=
        mul_le_mul_of_nonneg_left hpointDistance
          (denseLipschitzBound_pos p ambient).le
      _ ≤ denseLipschitzBound p ambient * radius ^ 2 :=
        mul_le_mul_of_nonneg_left hdiagonal
          (denseLipschitzBound_pos p ambient).le
      _ ≤ threshold :=
        denseLipschitzBound_mul_refinementRadius_sq_le p ambient hthreshold
  have hdecompose :
      p.eval refined.box.center -
          (p.eval refined.box.center - p.eval point) = p.eval point := by
    ext <;> simp only [sub_re, sub_im] <;> ring
  have hsum := normSq_sub_le_two (p.eval refined.box.center)
    (p.eval refined.box.center - p.eval point)
  rw [hdecompose] at hsum
  have hpointNorm : 0 < normSq (p.eval point) := normSq_pos hnonroot
  dsimp [threshold, nonrootThreshold] at hcenterResidual hevalDifference
  nlinarith

/-- A refined winding-one state with a uniform positive decoder-denominator
certificate. -/
structure SeparationOutput
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (current : WindingOneState p ambient) (M : Mat2 QI) where
  state : WindingOneState p ambient
  refines : state.box.Refines current.box
  margin : ℚ
  margin_pos : 0 < margin
  lower : ∀ {z : QI}, state.box.Contains z →
    margin ≤ normSq (M.c * z + M.d)

namespace SeparationOutput

/-- Regard a denominator certificate constructed below a nested winding state
as a certificate below any displayed ancestor.  The separated box and its
positive margin are unchanged. -/
def rebase
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {outer inner : WindingOneState p ambient} {M : Mat2 QI}
    (output : SeparationOutput p ambient inner M)
    (innerRefines : inner.box.Refines outer.box) :
    SeparationOutput p ambient outer M where
  state := output.state
  refines := output.refines.trans innerRefines
  margin := output.margin
  margin_pos := output.margin_pos
  lower := output.lower

@[simp] theorem rebase_state
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {outer inner : WindingOneState p ambient} {M : Mat2 QI}
    (output : SeparationOutput p ambient inner M)
    (innerRefines : inner.box.Refines outer.box) :
    (output.rebase innerRefines).state = output.state := rfl

/-- Restrict a denominator-separation certificate to any displayed nested
winding-one state.  The original positive margin remains valid, while the
result is again in the exact shape consumed by downstream branch resolution. -/
def restrict
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {current : WindingOneState p ambient} {M : Mat2 QI}
    (output : SeparationOutput p ambient current M)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines output.state.box) :
    SeparationOutput p ambient current M where
  state := next
  refines := nextRefines.trans output.refines
  margin := output.margin
  margin_pos := output.margin_pos
  lower := fun contains => output.lower (nextRefines.contains contains)

@[simp] theorem restrict_state
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {current : WindingOneState p ambient} {M : Mat2 QI}
    (output : SeparationOutput p ambient current M)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines output.state.box) :
    (output.restrict next nextRefines).state = next := rfl

end SeparationOutput

/-- Constant-denominator branch (`c=0`). -/
def separateConstantDenominator
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (current : WindingOneState p ambient) (M : Mat2 QI)
    (hc : M.c = 0) (hd : M.d ≠ 0) : SeparationOutput p ambient current M where
  state := current
  refines := CCL.RatBox.refines_refl current.box
  margin := normSq M.d
  margin_pos := normSq_pos hd
  lower := by
    intro z _hz
    simp [hc]

private theorem denominator_eq_mul_sub_pole
    (M : Mat2 QI) (hc : M.c ≠ 0) (z : QI) :
    M.c * z + M.d = M.c * (z - decoderPole M) := by
  have hpole := denominator_at_decoderPole M hc
  calc
    M.c * z + M.d = (M.c * z + M.d) -
        (M.c * decoderPole M + M.d) := by rw [hpole, sub_zero]
    _ = M.c * (z - decoderPole M) := by
      ext <;> simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im] <;> ring

/-- A pole already outside the current root box yields an immediate uniform
denominator margin, independently of whether it is another polynomial root. -/
def separateOutsidePole
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (current : WindingOneState p ambient) (M : Mat2 QI)
    (hc : M.c ≠ 0) (outside : ¬current.box.Contains (decoderPole M)) :
    SeparationOutput p ambient current M := by
  let side := outsideSide outside
  let margin := normSq M.c * side.margin
  refine
    { state := current
      refines := CCL.RatBox.refines_refl current.box
      margin := margin
      margin_pos := mul_pos (normSq_pos hc) side.margin_pos
      lower := ?_ }
  intro z contains
  have distance : side.margin ≤ normSq (z - decoderPole M) :=
    side.margin_le_normSq_sub contains
  rw [denominator_eq_mul_sub_pole M hc z, normSq_mul]
  exact mul_le_mul_of_nonneg_left distance (normSq_nonneg M.c)

/-- Nonconstant-denominator branch.  The track refinement excludes the exact
nonroot pole; its outside-side margin is then multiplied by `N(c)`. -/
def separateNonrootPole
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (M : Mat2 QI)
    (hc : M.c ≠ 0) (hnonroot : p.eval (decoderPole M) ≠ 0) :
    SeparationOutput p ambient current M := by
  let state := refineAwayFromNonroot track current (decoderPole M) hnonroot
  let side := outsideSide
    (refineAwayFromNonroot_excludes track current (decoderPole M) hnonroot)
  let margin := normSq M.c * side.margin
  refine
    { state := state
      refines := refineAwayFromNonroot_refines track current (decoderPole M) hnonroot
      margin := margin
      margin_pos := mul_pos (normSq_pos hc) side.margin_pos
      lower := ?_ }
  intro z hz
  have hdistance : side.margin ≤ normSq (z - decoderPole M) :=
    side.margin_le_normSq_sub hz
  rw [denominator_eq_mul_sub_pole M hc z, normSq_mul]
  exact mul_le_mul_of_nonneg_left hdistance (normSq_nonneg M.c)

/-- The exact finite denominator decision in the opening paragraph of
Theorem 10.2. -/
inductive Decision
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (current : WindingOneState p ambient) (M : Mat2 QI) where
  | terminal (point : QI) (root : p.eval point = 0)
      (contains : current.box.Contains point)
      (strict : current.box.StrictContains point)
      (denominator_zero : M.c * point + M.d = 0)
  | separated (output : SeparationOutput p ambient current M)

/-- Decide the rational terminal-pole case, or return a proof-bearing positive
denominator separation after one explicit finite track call. -/
def decide
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (M : Mat2 QI)
    (hrow : M.c ≠ 0 ∨ M.d ≠ 0) : Decision p ambient current M := by
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := hrow.resolve_left (fun hne => hne hc)
    exact .separated (separateConstantDenominator current M hc hd)
  · by_cases hroot : p.eval (decoderPole M) = 0
    · by_cases contains : current.box.Contains (decoderPole M)
      · exact .terminal (decoderPole M) hroot contains
          (FTA.BoxClearance.BoxBoundaryClearanceCertificate.root_strictContains
            current.clearance contains hroot)
          (denominator_at_decoderPole M hc)
      · exact .separated (separateOutsidePole current M hc contains)
    · exact .separated (separateNonrootPole track current M hc hroot)

end CCLDenominator
end FTA
