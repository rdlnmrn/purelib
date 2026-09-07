import FTA.GaussianPolynomialBounds
import FTA.GaussianDerivative
import FTA.AffineWinding

/-!
# Local extraction from a nonzero-winding rational box

This module begins Section 7 of the finite constructive FTA paper.  It turns
nonzero algebraic winding into a coefficient-explicit residual bound at the
rational box center, then combines that bound with the finite Bezout
certificate for `gcd(f,f') = 1` to certify a rational Newton center.  Every
argument uses rational inequalities and the finite Rouché transfer.
-/

namespace FTA.LocalExtraction

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Winding
open FTA.WindingHomotopy
open FTA.GlobalWinding
open FTA.GaussianPolynomialBounds
open FTA.GaussianDerivative
open FTA.AffineWinding

/-- Coefficient-computed upper bound for the squared residual variation from
the center of a rational subbox. -/
def centerResidualBound (p : GaussianPolynomial)
    (ambient small : CCL.RatBox) : ℚ :=
  denseLipschitzBound p ambient * small.diagonalSq

/-- Every point of the small box differs from its rational center by at most
the displayed coefficient-computed residual bound. -/
theorem normSq_eval_sub_center_le
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) {z : QI} (hz : small.Contains z) :
    normSq ((p - gaussianConstant (p.eval small.center)).eval z) ≤
      centerResidualBound p ambient small := by
  have hzAmbient : ambient.Contains z := hrefines.contains hz
  have hcenterSmall : small.Contains small.center := small.contains_center
  have hcenterAmbient : ambient.Contains small.center :=
    hrefines.contains hcenterSmall
  have heval := normSq_dense_eval_sub_eval_le_denseLipschitzBound
    p hzAmbient hcenterAmbient
  have hdistance : normSq (z + -small.center) ≤ small.diagonalSq := by
    simpa only [GaussianRat.sub_eq_add_neg] using
      CCL.RatBox.normSq_sub_le_diagonalSq hz hcenterSmall
  have hpolynomialDifference :
      (p - gaussianConstant (p.eval small.center)).eval z =
        p.eval z + -(p.eval small.center) := by
    rw [eval_sub, gaussianConstant, eval_constant]
    rfl
  calc
    normSq ((p - gaussianConstant (p.eval small.center)).eval z) =
        normSq (p.eval z + -(p.eval small.center)) := by
      rw [hpolynomialDifference]
    _ ≤ denseLipschitzBound p ambient *
          normSq (z + -small.center) := by
      exact heval
    _ ≤ denseLipschitzBound p ambient *
        small.diagonalSq :=
      mul_le_mul_of_nonneg_left hdistance
        (denseLipschitzBound_pos p ambient).le
    _ = centerResidualBound p ambient small := rfl

/-- Positive rational gap available when the center residual strictly exceeds
the uniform oscillation bound. -/
def centerConstantDominanceMargin (p : GaussianPolynomial)
    (ambient small : CCL.RatBox) : ℚ :=
  normSq (p.eval small.center) - centerResidualBound p ambient small

theorem centerConstantDominanceMargin_pos
    (p : GaussianPolynomial) (ambient small : CCL.RatBox)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    0 < centerConstantDominanceMargin p ambient small := by
  exact sub_pos.mpr hlarge

/-- Under a large-center-residual hypothesis, the constant center value
dominates the polynomial oscillation on the bottom edge. -/
def bottomCenterDominanceCertificate
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    NormDominanceCertificate
      (horizontalRealCoordinate (gaussianConstant (p.eval small.center))
        small.yLower)
      (horizontalImagCoordinate (gaussianConstant (p.eval small.center))
        small.yLower)
      (horizontalRealCoordinate
        (p - gaussianConstant (p.eval small.center)) small.yLower)
      (horizontalImagCoordinate
        (p - gaussianConstant (p.eval small.center)) small.yLower)
      ⟨small.xLower, small.xUpper⟩ where
  margin := centerConstantDominanceMargin p ambient small
  positive := centerConstantDominanceMargin_pos p ambient small hlarge
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk t small.yLower
    have hz : small.Contains z := ⟨hLower, hUpper, le_rfl, small.y_valid⟩
    have hosc := normSq_eval_sub_center_le p hrefines hz
    have hdominance :
        centerConstantDominanceMargin p ambient small ≤
          normSq (p.eval small.center) -
            normSq ((p - gaussianConstant (p.eval small.center)).eval z) := by
      dsimp only [centerConstantDominanceMargin]
      linarith
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, gaussianConstant, eval_constant,
      normSq, z] using hdominance

/-- The same center-value margin dominates on the right edge. -/
def rightCenterDominanceCertificate
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    NormDominanceCertificate
      (verticalRealCoordinate (gaussianConstant (p.eval small.center))
        small.xUpper)
      (verticalImagCoordinate (gaussianConstant (p.eval small.center))
        small.xUpper)
      (verticalRealCoordinate
        (p - gaussianConstant (p.eval small.center)) small.xUpper)
      (verticalImagCoordinate
        (p - gaussianConstant (p.eval small.center)) small.xUpper)
      ⟨small.yLower, small.yUpper⟩ where
  margin := centerConstantDominanceMargin p ambient small
  positive := centerConstantDominanceMargin_pos p ambient small hlarge
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk small.xUpper t
    have hz : small.Contains z :=
      ⟨small.x_valid, le_rfl, hLower, hUpper⟩
    have hosc := normSq_eval_sub_center_le p hrefines hz
    have hdominance :
        centerConstantDominanceMargin p ambient small ≤
          normSq (p.eval small.center) -
            normSq ((p - gaussianConstant (p.eval small.center)).eval z) := by
      dsimp only [centerConstantDominanceMargin]
      linarith
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, gaussianConstant, eval_constant,
      normSq, z] using hdominance

/-- The same center-value margin dominates on the top edge. -/
def topCenterDominanceCertificate
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    NormDominanceCertificate
      (horizontalRealCoordinate (gaussianConstant (p.eval small.center))
        small.yUpper)
      (horizontalImagCoordinate (gaussianConstant (p.eval small.center))
        small.yUpper)
      (horizontalRealCoordinate
        (p - gaussianConstant (p.eval small.center)) small.yUpper)
      (horizontalImagCoordinate
        (p - gaussianConstant (p.eval small.center)) small.yUpper)
      ⟨small.xLower, small.xUpper⟩ where
  margin := centerConstantDominanceMargin p ambient small
  positive := centerConstantDominanceMargin_pos p ambient small hlarge
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk t small.yUpper
    have hz : small.Contains z :=
      ⟨hLower, hUpper, small.y_valid, le_rfl⟩
    have hosc := normSq_eval_sub_center_le p hrefines hz
    have hdominance :
        centerConstantDominanceMargin p ambient small ≤
          normSq (p.eval small.center) -
            normSq ((p - gaussianConstant (p.eval small.center)).eval z) := by
      dsimp only [centerConstantDominanceMargin]
      linarith
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, gaussianConstant, eval_constant,
      normSq, z] using hdominance

/-- The same center-value margin dominates on the left edge. -/
def leftCenterDominanceCertificate
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    NormDominanceCertificate
      (verticalRealCoordinate (gaussianConstant (p.eval small.center))
        small.xLower)
      (verticalImagCoordinate (gaussianConstant (p.eval small.center))
        small.xLower)
      (verticalRealCoordinate
        (p - gaussianConstant (p.eval small.center)) small.xLower)
      (verticalImagCoordinate
        (p - gaussianConstant (p.eval small.center)) small.xLower)
      ⟨small.yLower, small.yUpper⟩ where
  margin := centerConstantDominanceMargin p ambient small
  positive := centerConstantDominanceMargin_pos p ambient small hlarge
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk small.xLower t
    have hz : small.Contains z :=
      ⟨le_rfl, small.x_valid, hLower, hUpper⟩
    have hosc := normSq_eval_sub_center_le p hrefines hz
    have hdominance :
        centerConstantDominanceMargin p ambient small ≤
          normSq (p.eval small.center) -
            normSq ((p - gaussianConstant (p.eval small.center)).eval z) := by
      dsimp only [centerConstantDominanceMargin]
      linarith
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, gaussianConstant, eval_constant,
      normSq, z] using hdominance

/-- The constant center value plus the exact dense oscillation polynomial is
the original sparse polynomial. -/
theorem centerConstant_add_difference_toPolynomial
    (p : GaussianPolynomial) (small : CCL.RatBox) :
    (gaussianConstant (p.eval small.center) +
        (p - gaussianConstant (p.eval small.center))).toPolynomial =
      p.toPolynomial := by
  rw [toPolynomial_add, toPolynomial_sub]
  ring

/-- If the center value strictly exceeds the uniform oscillation bound, the
finite Rouché theorem contracts the polynomial to that constant and its raw
box winding is zero. -/
theorem quadrupledBoxWinding_eq_zero_of_centerResidualBound_lt
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center)) :
    quadrupledBoxWinding p small = 0 := by
  have htransfer := quadrupledBoxWinding_add_of_normDominance
    (gaussianConstant (p.eval small.center))
    (p - gaussianConstant (p.eval small.center)) small
    (bottomCenterDominanceCertificate p hrefines hlarge)
    (rightCenterDominanceCertificate p hrefines hlarge)
    (topCenterDominanceCertificate p hrefines hlarge)
    (leftCenterDominanceCertificate p hrefines hlarge)
    hproper.1 hproper.2
  have hcongr := quadrupledBoxWinding_congr small
    (centerConstant_add_difference_toPolynomial p small)
  calc
    quadrupledBoxWinding p small =
        quadrupledBoxWinding
          (gaussianConstant (p.eval small.center) +
            (p - gaussianConstant (p.eval small.center))) small := hcongr.symm
    _ = quadrupledBoxWinding
        (gaussianConstant (p.eval small.center)) small := htransfer
    _ = 0 := quadrupledBoxWinding_gaussianConstant _ _

/-- Lemma 7.2's first conclusion: nonzero raw winding forces the rational
center residual below the coefficient-computed Lipschitz variation bound. -/
theorem center_residual_le_of_quadrupledBoxWinding_ne_zero
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hwinding : quadrupledBoxWinding p small ≠ 0) :
    normSq (p.eval small.center) ≤ centerResidualBound p ambient small := by
  by_contra hnot
  have hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center) := lt_of_not_ge hnot
  exact hwinding
    (quadrupledBoxWinding_eq_zero_of_centerResidualBound_lt
      p hrefines hproper hlarge)

/-- Ordinary nonzero winding has the same center-residual consequence. -/
theorem center_residual_le_of_boxWinding_ne_zero
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hwinding : boxWinding p small ≠ 0) :
    normSq (p.eval small.center) ≤ centerResidualBound p ambient small := by
  have hraw : quadrupledBoxWinding p small ≠ 0 := by
    intro hzero
    apply hwinding
    rw [boxWinding, hzero]
    norm_num
  exact center_residual_le_of_quadrupledBoxWinding_ne_zero
    p hrefines hproper hraw

/-! ## Protected boundary core -/

/-- Finite rational data saying that the center of a small subbox is close to
a quantitatively clear point in the ambient box, with enough remaining margin
to dominate the small-box oscillation.  The later boundary-strip geometry
constructs this record from a projection to one of the four parent edges. -/
structure NearbyClearPointCertificate
    (p : GaussianPolynomial) (ambient small : CCL.RatBox) where
  point : QI
  point_mem : ambient.Contains point
  clearance : ℚ
  radiusSq : ℚ
  clearance_lower : clearance ≤ normSq (p.eval point)
  center_distance : normSq (point + -small.center) ≤ radiusSq
  dominates : centerResidualBound p ambient small +
      denseLipschitzBound p ambient * radiusSq < clearance / 2

/-- A nearby clear point supplies an explicit lower bound at the small-box
center.  This is the finite norm inequality used in the protected-strip
argument. -/
theorem center_eval_lower_of_nearby_clear_point
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient)
    (certificate : NearbyClearPointCertificate p ambient small) :
    certificate.clearance / 2 -
        denseLipschitzBound p ambient * certificate.radiusSq ≤
      normSq (p.eval small.center) := by
  have hcenterAmbient : ambient.Contains small.center :=
    hrefines.contains small.contains_center
  have hvariation := normSq_dense_eval_sub_eval_le_denseLipschitzBound
    p certificate.point_mem hcenterAmbient
  have hvariationRadius :
      normSq (p.eval certificate.point + -(p.eval small.center)) ≤
        denseLipschitzBound p ambient * certificate.radiusSq :=
    hvariation.trans (mul_le_mul_of_nonneg_left
      certificate.center_distance (denseLipschitzBound_pos p ambient).le)
  have hdecomposition :
      p.eval small.center +
          (p.eval certificate.point + -(p.eval small.center)) =
        p.eval certificate.point := by
    ext <;> simp only [add_re, add_im, neg_re, neg_im] <;> ring
  have htwo := normSq_add_le_two (p.eval small.center)
    (p.eval certificate.point + -(p.eval small.center))
  rw [hdecomposition] at htwo
  have hclear := certificate.clearance_lower
  linarith

/-- A protected nearby-clear-point record contracts the small-box boundary to
the constant center value, hence forces raw winding zero. -/
theorem quadrupledBoxWinding_eq_zero_of_nearby_clear_point
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (certificate : NearbyClearPointCertificate p ambient small) :
    quadrupledBoxWinding p small = 0 := by
  have hlower := center_eval_lower_of_nearby_clear_point
    p hrefines certificate
  have hlarge : centerResidualBound p ambient small <
      normSq (p.eval small.center) := by
    linarith [certificate.dominates]
  exact quadrupledBoxWinding_eq_zero_of_centerResidualBound_lt
    p hrefines hproper hlarge

/-- Ordinary winding also vanishes under the protected-point certificate. -/
theorem boxWinding_eq_zero_of_nearby_clear_point
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (certificate : NearbyClearPointCertificate p ambient small) :
    boxWinding p small = 0 := by
  rw [boxWinding,
    quadrupledBoxWinding_eq_zero_of_nearby_clear_point
      p hrefines hproper certificate]
  norm_num

/-- Exact coordinate predicate for the boundary of a rational box. -/
def OnBoxBoundary (B : CCL.RatBox) (z : QI) : Prop :=
  B.Contains z ∧
    (z.re = B.xLower ∨ z.re = B.xUpper ∨
      z.im = B.yLower ∨ z.im = B.yUpper)

/-- A single positive rational lower bound valid on all four box edges. -/
structure BoxBoundaryClearanceCertificate
    (p : GaussianPolynomial) (B : CCL.RatBox) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ z : QI, OnBoxBoundary B z → bound ≤ normSq (p.eval z)

/-- Explicit positive rational protected-strip scale.  Taking minima avoids a
square-root operation while remaining strong enough for the paper's
`1024 L ρ² < μ` estimate. -/
def protectedBoundaryRadius
    (p : GaussianPolynomial) (B : CCL.RatBox)
    (clearance : BoxBoundaryClearanceCertificate p B) : ℚ :=
  min 1
    (min (clearance.bound / (2048 * denseLipschitzBound p B))
      (min (B.widthX / 32) (B.widthY / 32)))

theorem protectedBoundaryRadius_pos
    (p : GaussianPolynomial) {B : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hproper : B.Proper) :
    0 < protectedBoundaryRadius p B clearance := by
  have hx : 0 < B.widthX := by
    dsimp only [CCL.RatBox.widthX]
    linarith [hproper.1]
  have hy : 0 < B.widthY := by
    dsimp only [CCL.RatBox.widthY]
    linarith [hproper.2]
  have hL := denseLipschitzBound_pos p B
  exact lt_min zero_lt_one
    (lt_min
      (div_pos clearance.positive (mul_pos (by norm_num) hL))
      (lt_min (div_pos hx (by norm_num)) (div_pos hy (by norm_num))))

/-- The explicit scale satisfies the protected-strip clearance inequality. -/
theorem protectedBoundaryRadius_clearance
    (p : GaussianPolynomial) {B : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hproper : B.Proper) :
    1024 * denseLipschitzBound p B *
        protectedBoundaryRadius p B clearance ^ 2 <
      clearance.bound := by
  let rho := protectedBoundaryRadius p B clearance
  let L := denseLipschitzBound p B
  have hrho : 0 < rho := protectedBoundaryRadius_pos p clearance hproper
  have hL : 0 < L := denseLipschitzBound_pos p B
  have hrhoOne : rho ≤ 1 := by
    exact min_le_left _ _
  have hrhoRatio : rho ≤ clearance.bound / (2048 * L) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hscaled : rho * (2048 * L) ≤ clearance.bound := by
    rwa [le_div_iff₀ (mul_pos (by norm_num) hL)] at hrhoRatio
  have hscaledRho := mul_le_mul_of_nonneg_left hscaled hrho.le
  have hrhoBound := mul_le_mul_of_nonneg_right hrhoOne clearance.positive.le
  dsimp only [rho, L] at hscaledRho hrhoBound ⊢
  nlinarith

/-- The strip scale is strictly smaller than one sixteenth of both side
lengths, as required to keep the later Newton square in the parent interior. -/
theorem protectedBoundaryRadius_side_lengths
    (p : GaussianPolynomial) {B : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p B)
    (hproper : B.Proper) :
    16 * protectedBoundaryRadius p B clearance < B.widthX ∧
      16 * protectedBoundaryRadius p B clearance < B.widthY := by
  let rho := protectedBoundaryRadius p B clearance
  have hrho : 0 < rho := protectedBoundaryRadius_pos p clearance hproper
  have hrhoInner : rho ≤
      min (clearance.bound / (2048 * denseLipschitzBound p B))
        (min (B.widthX / 32) (B.widthY / 32)) := min_le_right _ _
  have hrhoWidths : rho ≤ min (B.widthX / 32) (B.widthY / 32) :=
    hrhoInner.trans (min_le_right _ _)
  have hrhoX : rho ≤ B.widthX / 32 :=
    hrhoWidths.trans (min_le_left _ _)
  have hrhoY : rho ≤ B.widthY / 32 :=
    hrhoWidths.trans (min_le_right _ _)
  constructor <;> dsimp only [rho] at * <;> linarith

/-- The paper's stronger `1024` inequality automatically supplies the exact
constant-dominance inequality needed by the protected-point theorem. -/
theorem protectedBoundaryRadius_dominates
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p ambient)
    (hproper : ambient.Proper)
    (hdiagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2) :
    centerResidualBound p ambient small +
        denseLipschitzBound p ambient *
          (25 * protectedBoundaryRadius p ambient clearance ^ 2) <
      clearance.bound / 2 := by
  have hL := denseLipschitzBound_pos p ambient
  have hfirst := mul_le_mul_of_nonneg_left hdiagonal hL.le
  have hclearance := protectedBoundaryRadius_clearance
    p clearance hproper
  dsimp only [centerResidualBound]
  nlinarith [sq_nonneg (protectedBoundaryRadius p ambient clearance)]

/-- Closed coordinate strip of the displayed width along any parent edge. -/
def InCoordinateBoundaryStrip
    (B : CCL.RatBox) (width : ℚ) (z : QI) : Prop :=
  B.Contains z ∧
    (z.re ≤ B.xLower + width ∨ B.xUpper - width ≤ z.re ∨
      z.im ≤ B.yLower + width ∨ B.yUpper - width ≤ z.im)

/-- Proof-relevant choice of the parent edge whose strip contains the point. -/
inductive CoordinateBoundaryStripSide
    (B : CCL.RatBox) (width : ℚ) (z : QI) : Type
  | left (h : z.re ≤ B.xLower + width)
  | right (h : B.xUpper - width ≤ z.re)
  | bottom (h : z.im ≤ B.yLower + width)
  | top (h : B.yUpper - width ≤ z.im)

/-- Proof-relevant finite witness that a small box meets a parent boundary
strip.  Keeping the rational point as data avoids choosing from an existential
proposition. -/
structure BoundaryStripWitness
    (ambient small : CCL.RatBox) (width : ℚ) where
  point : QI
  point_mem : small.Contains point
  side : CoordinateBoundaryStripSide ambient width point

theorem BoundaryStripWitness.in_strip
    {ambient small : CCL.RatBox} {width : ℚ}
    (witness : BoundaryStripWitness ambient small width)
    (hrefines : small.Refines ambient) :
    InCoordinateBoundaryStrip ambient width witness.point := by
  refine ⟨hrefines.contains witness.point_mem, ?_⟩
  cases witness.side with
  | left h => exact Or.inl h
  | right h => exact Or.inr (Or.inl h)
  | bottom h => exact Or.inr (Or.inr (Or.inl h))
  | top h => exact Or.inr (Or.inr (Or.inr h))

/-- If a small subbox meets the width-`4ρ` coordinate strip, its center is
within squared distance `25ρ²` of an explicit parent-boundary projection.
Together with the parent clearance and the displayed rational dominance
inequality, this constructs the protected-point record. -/
def nearbyClearPointCertificate_of_meets_boundaryStrip
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p ambient)
    {rho : ℚ} (hrho : 0 < rho)
    (hrefines : small.Refines ambient)
    (hdiagonal : small.diagonalSq ≤ rho ^ 2)
    (hmeet : BoundaryStripWitness ambient small (4 * rho))
    (hdominates : centerResidualBound p ambient small +
        denseLipschitzBound p ambient * (25 * rho ^ 2) <
      clearance.bound / 2) :
    NearbyClearPointCertificate p ambient small := by
  rcases hmeet with ⟨z, hzSmall, hside⟩
  have hzAmbient : ambient.Contains z := hrefines.contains hzSmall
  have hcenterSmall : small.Contains small.center := small.contains_center
  have hcenterAmbient : ambient.Contains small.center :=
    hrefines.contains hcenterSmall
  have hcenterDistance :
      normSq (small.center + -z) ≤ rho ^ 2 := by
    have hbox := CCL.RatBox.normSq_sub_le_diagonalSq hcenterSmall hzSmall
    have hbox' : normSq (small.center + -z) ≤ small.diagonalSq := by
      simpa only [GaussianRat.sub_eq_add_neg] using hbox
    exact hbox'.trans hdiagonal
  have hreSq : (small.center.re - z.re) ^ 2 ≤ rho ^ 2 := by
    simp only [normSq, add_re, add_im, neg_re, neg_im] at hcenterDistance
    nlinarith [sq_nonneg (small.center.im - z.im)]
  have himSq : (small.center.im - z.im) ^ 2 ≤ rho ^ 2 := by
    simp only [normSq, add_re, add_im, neg_re, neg_im] at hcenterDistance
    nlinarith [sq_nonneg (small.center.re - z.re)]
  have hreUpper : small.center.re - z.re ≤ rho := by
    nlinarith [sq_nonneg (small.center.re - z.re + rho)]
  have hreLower : -rho ≤ small.center.re - z.re := by
    nlinarith [sq_nonneg (small.center.re - z.re - rho)]
  have himUpper : small.center.im - z.im ≤ rho := by
    nlinarith [sq_nonneg (small.center.im - z.im + rho)]
  have himLower : -rho ≤ small.center.im - z.im := by
    nlinarith [sq_nonneg (small.center.im - z.im - rho)]
  rcases hcenterAmbient with ⟨hcxLower, hcxUpper, hcyLower, hcyUpper⟩
  cases hside with
  | left hleft =>
    let point := CCL.GaussianRat.mk ambient.xLower small.center.im
    have hdistanceLinear :
        small.center.re - ambient.xLower ≤ 5 * rho := by
      linarith
    have hdistance : normSq (point + -small.center) ≤ 25 * rho ^ 2 := by
      dsimp only [point, normSq, add_re, add_im, neg_re, neg_im]
      have hnonneg : 0 ≤ small.center.re - ambient.xLower := by linarith
      nlinarith
    refine
      { point := point
        point_mem := ⟨le_rfl, ambient.x_valid, hcyLower, hcyUpper⟩
        clearance := clearance.bound
        radiusSq := 25 * rho ^ 2
        clearance_lower := clearance.lower point ?_
        center_distance := hdistance
        dominates := hdominates }
    exact ⟨⟨le_rfl, ambient.x_valid, hcyLower, hcyUpper⟩, Or.inl rfl⟩
  | right hright =>
    let point := CCL.GaussianRat.mk ambient.xUpper small.center.im
    have hdistanceLinear :
        ambient.xUpper - small.center.re ≤ 5 * rho := by
      linarith
    have hdistance : normSq (point + -small.center) ≤ 25 * rho ^ 2 := by
      dsimp only [point, normSq, add_re, add_im, neg_re, neg_im]
      have hnonneg : 0 ≤ ambient.xUpper - small.center.re := by linarith
      nlinarith
    refine
      { point := point
        point_mem := ⟨ambient.x_valid, le_rfl, hcyLower, hcyUpper⟩
        clearance := clearance.bound
        radiusSq := 25 * rho ^ 2
        clearance_lower := clearance.lower point ?_
        center_distance := hdistance
        dominates := hdominates }
    exact ⟨⟨ambient.x_valid, le_rfl, hcyLower, hcyUpper⟩,
      Or.inr (Or.inl rfl)⟩
  | bottom hbottom =>
    let point := CCL.GaussianRat.mk small.center.re ambient.yLower
    have hdistanceLinear :
        small.center.im - ambient.yLower ≤ 5 * rho := by
      linarith
    have hdistance : normSq (point + -small.center) ≤ 25 * rho ^ 2 := by
      dsimp only [point, normSq, add_re, add_im, neg_re, neg_im]
      have hnonneg : 0 ≤ small.center.im - ambient.yLower := by linarith
      nlinarith
    refine
      { point := point
        point_mem := ⟨hcxLower, hcxUpper, le_rfl, ambient.y_valid⟩
        clearance := clearance.bound
        radiusSq := 25 * rho ^ 2
        clearance_lower := clearance.lower point ?_
        center_distance := hdistance
        dominates := hdominates }
    exact ⟨⟨hcxLower, hcxUpper, le_rfl, ambient.y_valid⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩
  | top htop =>
    let point := CCL.GaussianRat.mk small.center.re ambient.yUpper
    have hdistanceLinear :
        ambient.yUpper - small.center.im ≤ 5 * rho := by
      linarith
    have hdistance : normSq (point + -small.center) ≤ 25 * rho ^ 2 := by
      dsimp only [point, normSq, add_re, add_im, neg_re, neg_im]
      have hnonneg : 0 ≤ ambient.yUpper - small.center.im := by linarith
      nlinarith
    refine
      { point := point
        point_mem := ⟨hcxLower, hcxUpper, ambient.y_valid, le_rfl⟩
        clearance := clearance.bound
        radiusSq := 25 * rho ^ 2
        clearance_lower := clearance.lower point ?_
        center_distance := hdistance
        dominates := hdominates }
    exact ⟨⟨hcxLower, hcxUpper, ambient.y_valid, le_rfl⟩,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Protected boundary strip, in the exact form used by Lemma 7.1: every
proper small subbox meeting the strip has winding zero. -/
theorem boxWinding_eq_zero_of_meets_boundaryStrip
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p ambient)
    {rho : ℚ} (hrho : 0 < rho)
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hdiagonal : small.diagonalSq ≤ rho ^ 2)
    (hmeet : BoundaryStripWitness ambient small (4 * rho))
    (hdominates : centerResidualBound p ambient small +
        denseLipschitzBound p ambient * (25 * rho ^ 2) <
      clearance.bound / 2) :
    boxWinding p small = 0 := by
  exact boxWinding_eq_zero_of_nearby_clear_point p hrefines hproper
    (nearbyClearPointCertificate_of_meets_boundaryStrip p clearance hrho
      hrefines hdiagonal hmeet hdominates)

/-- Fully coefficient-computed protected boundary strip at the exact raw
winding normalization. -/
theorem quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p ambient)
    (hambient : ambient.Proper) (hsmall : small.Proper)
    (hrefines : small.Refines ambient)
    (hdiagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2)
    (hmeet : BoundaryStripWitness ambient small
      (4 * protectedBoundaryRadius p ambient clearance)) :
    quadrupledBoxWinding p small = 0 := by
  exact quadrupledBoxWinding_eq_zero_of_nearby_clear_point p hrefines hsmall
    (nearbyClearPointCertificate_of_meets_boundaryStrip p clearance
      (protectedBoundaryRadius_pos p clearance hambient) hrefines hdiagonal
      hmeet
      (protectedBoundaryRadius_dominates p clearance hambient hdiagonal))

/-- Fully coefficient-computed protected boundary strip (Lemma 7.1).  No
radius or dominance premise remains for the caller: both are the explicit
rational values above. -/
theorem boxWinding_eq_zero_of_meets_protectedBoundaryStrip
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (clearance : BoxBoundaryClearanceCertificate p ambient)
    (hambient : ambient.Proper) (hsmall : small.Proper)
    (hrefines : small.Refines ambient)
    (hdiagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2)
    (hmeet : BoundaryStripWitness ambient small
      (4 * protectedBoundaryRadius p ambient clearance)) :
    boxWinding p small = 0 := by
  rw [boxWinding,
    quadrupledBoxWinding_eq_zero_of_meets_protectedBoundaryStrip
      p clearance hambient hsmall hrefines hdiagonal hmeet]
  norm_num

/-! ## Dense squarefree margins and the rational Newton center -/

/-- Finite dense Bézout data witnessing `gcd(p,p') = 1` by an exact
coefficient identity.  All three polynomials are executable coefficient
lists. -/
structure GaussianSquarefreeCertificate (p : GaussianPolynomial) where
  left : GaussianPolynomial
  right : GaussianPolynomial
  identity : left.toPolynomial * p.toPolynomial +
    right.toPolynomial * (derivative p).toPolynomial = 1

/-- Evaluation of the finite coefficient identity at one supplied point. -/
theorem GaussianSquarefreeCertificate.bezout
    {p : GaussianPolynomial} (certificate : GaussianSquarefreeCertificate p)
    (z : QI) :
    certificate.left.eval z * p.eval z +
      certificate.right.eval z * (derivative p).eval z = 1 := by
  have h := congrArg (Polynomial.eval z) certificate.identity
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    eval_toPolynomial] using h

/-- Residual threshold computed from the left Bézout coefficient. -/
def derivativeThreshold {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p)
    (B : CCL.RatBox) : ℚ :=
  1 / (8 * denseEvalNormMajorant certificate.left B)

/-- Positive derivative margin computed from the right Bézout coefficient. -/
def derivativeMargin {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p)
    (B : CCL.RatBox) : ℚ :=
  1 / (4 * denseEvalNormMajorant certificate.right B)

theorem derivativeThreshold_pos {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p)
    (B : CCL.RatBox) :
    0 < derivativeThreshold certificate B := by
  dsimp only [derivativeThreshold]
  exact div_pos zero_lt_one
    (mul_pos (by norm_num)
      (zero_lt_one.trans_le
        (one_le_denseEvalNormMajorant certificate.left B)))

theorem derivativeMargin_pos {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p)
    (B : CCL.RatBox) :
    0 < derivativeMargin certificate B := by
  dsimp only [derivativeMargin]
  exact div_pos zero_lt_one
    (mul_pos (by norm_num)
      (zero_lt_one.trans_le
        (one_le_denseEvalNormMajorant certificate.right B)))

/-- The dense Bézout identity turns a small center residual into an explicit
positive lower bound for the executable derivative. -/
theorem derivative_margin_of_small_residual
    {p : GaussianPolynomial}
    (certificate : GaussianSquarefreeCertificate p)
    (B : CCL.RatBox) {z : QI} (hz : B.Contains z)
    (hsmall : normSq (p.eval z) ≤ derivativeThreshold certificate B) :
    derivativeMargin certificate B ≤ normSq ((derivative p).eval z) := by
  let MU := denseEvalNormMajorant certificate.left B
  let MV := denseEvalNormMajorant certificate.right B
  let fu := certificate.left.eval z
  let fv := certificate.right.eval z
  let fz := p.eval z
  let dfz := (derivative p).eval z
  have hMU : 1 ≤ MU := one_le_denseEvalNormMajorant certificate.left B
  have hMV : 1 ≤ MV := one_le_denseEvalNormMajorant certificate.right B
  have hU : normSq fu ≤ MU :=
    normSq_dense_eval_le_denseEvalNormMajorant certificate.left hz
  have hV : normSq fv ≤ MV :=
    normSq_dense_eval_le_denseEvalNormMajorant certificate.right hz
  have hbez : fu * fz + fv * dfz = 1 := certificate.bezout z
  have hone : 1 ≤ 2 *
      (normSq fu * normSq fz + normSq fv * normSq dfz) := by
    calc
      1 = normSq (fu * fz + fv * dfz) := by rw [hbez, normSq_one]
      _ ≤ 2 * (normSq (fu * fz) + normSq (fv * dfz)) :=
        normSq_add_le_two _ _
      _ = 2 * (normSq fu * normSq fz + normSq fv * normSq dfz) := by
        rw [normSq_mul, normSq_mul]
  have hmain : 1 ≤ 2 * (MU * normSq fz + MV * normSq dfz) := by
    refine hone.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add
      (mul_le_mul_of_nonneg_right hU (normSq_nonneg fz))
      (mul_le_mul_of_nonneg_right hV (normSq_nonneg dfz))
  have hMUpos : 0 < MU := zero_lt_one.trans_le hMU
  have hMVpos : 0 < MV := zero_lt_one.trans_le hMV
  have hfirst : 2 * MU * normSq fz ≤ 1 / 4 := by
    calc
      2 * MU * normSq fz ≤
          2 * MU * derivativeThreshold certificate B := by gcongr
      _ = 1 / 4 := by
        change 2 * MU * (1 / (8 * MU)) = 1 / 4
        field_simp [ne_of_gt hMUpos]
        norm_num
  have hsecond : (3 : ℚ) / 4 ≤ 2 * MV * normSq dfz := by
    nlinarith
  have heta : 2 * MV * derivativeMargin certificate B = 1 / 2 := by
    change 2 * MV * (1 / (4 * MV)) = 1 / 2
    field_simp [ne_of_gt hMVpos]
    norm_num
  have hscaled : (2 * MV) * derivativeMargin certificate B ≤
      (2 * MV) * normSq dfz := by
    rw [heta]
    linarith
  exact le_of_mul_le_mul_left hscaled
    (mul_pos (by norm_num : (0 : ℚ) < 2) hMVpos)

/-- The rational Newton center computed at the rational center of a box. -/
def rationalNewtonCenter (p : GaussianPolynomial) (B : CCL.RatBox) : QI :=
  B.center - p.eval B.center / (derivative p).eval B.center

/-- Exact squared norm of the executable Newton displacement. -/
theorem normSq_rationalNewtonCenter_sub_center
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (hderivative : (derivative p).eval B.center ≠ 0) :
    normSq (rationalNewtonCenter p B - B.center) =
      normSq (p.eval B.center) /
        normSq ((derivative p).eval B.center) := by
  have hdisplacement :
      rationalNewtonCenter p B - B.center =
        -(p.eval B.center / (derivative p).eval B.center) := by
    dsimp only [rationalNewtonCenter]
    simp only [GaussianRat.sub_eq_add_neg]
    ring
  rw [hdisplacement, normSq_neg,
    GaussianRat.normSq_div _ _ hderivative]

/-- Proof-bearing finite output of the small nonzero-winding Newton-center
construction in Lemma 7.2. -/
structure NewtonCenterCertificate
    (p : GaussianPolynomial) (ambient small : CCL.RatBox)
    (squarefree : GaussianSquarefreeCertificate p) where
  point : QI
  point_eq : point = rationalNewtonCenter p small
  residual : normSq (p.eval small.center) ≤
    centerResidualBound p ambient small
  derivative : derivativeMargin squarefree ambient ≤
    normSq ((FTA.GaussianDerivative.derivative p).eval small.center)
  displacement : normSq (point - small.center) ≤
    centerResidualBound p ambient small / derivativeMargin squarefree ambient

/-- Build the Newton-center certificate directly from an explicit residual
bound.  This is the non-circular core: winding is one way to obtain the
residual premise, but a separately certified rational approximation can
supply it as well. -/
def computeNewtonCenterOfResidual
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (hrefines : small.Refines ambient)
    (hresidual : normSq (p.eval small.center) ≤
      centerResidualBound p ambient small)
    (hthreshold : centerResidualBound p ambient small ≤
      derivativeThreshold squarefree ambient) :
    NewtonCenterCertificate p ambient small squarefree := by
  have hsmall : normSq (p.eval small.center) ≤
      derivativeThreshold squarefree ambient := hresidual.trans hthreshold
  have hcenterAmbient : ambient.Contains small.center :=
    hrefines.contains small.contains_center
  have hderivative := derivative_margin_of_small_residual
    squarefree ambient hcenterAmbient hsmall
  have hmarginPos := derivativeMargin_pos squarefree ambient
  have hderivativeNorm : 0 < normSq ((derivative p).eval small.center) :=
    hmarginPos.trans_le hderivative
  have hderivativeNe : (derivative p).eval small.center ≠ 0 := by
    intro hzero
    rw [hzero, normSq_zero] at hderivativeNorm
    exact lt_irrefl 0 hderivativeNorm
  refine
    { point := rationalNewtonCenter p small
      point_eq := rfl
      residual := hresidual
      derivative := hderivative
      displacement := ?_ }
  rw [normSq_rationalNewtonCenter_sub_center hderivativeNe]
  calc
    normSq (p.eval small.center) /
        normSq ((derivative p).eval small.center) ≤
      normSq (p.eval small.center) / derivativeMargin squarefree ambient :=
        div_le_div_of_nonneg_left (normSq_nonneg _)
          hmarginPos hderivative
    _ ≤ centerResidualBound p ambient small /
        derivativeMargin squarefree ambient :=
      div_le_div_of_nonneg_right hresidual hmarginPos.le

/-- Complete executable form of Lemma 7.2.  Once the small-box variation is
below the Bézout threshold, nonzero winding returns a rational Newton center
with residual, derivative, and displacement certificates. -/
def computeNewtonCenter
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hwinding : boxWinding p small ≠ 0)
    (hthreshold : centerResidualBound p ambient small ≤
      derivativeThreshold squarefree ambient) :
    NewtonCenterCertificate p ambient small squarefree := by
  have hresidual := center_residual_le_of_boxWinding_ne_zero
    p hrefines hproper hwinding
  exact computeNewtonCenterOfResidual p squarefree hrefines hresidual hthreshold

/-- Raw-winding form of Lemma 7.2.  This is the form used during the
pre-nonnegativity extraction loop, where raw subdivision additivity is
available without a divisibility premise. -/
def computeNewtonCenterOfRawWinding
    (p : GaussianPolynomial) {ambient small : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (hrefines : small.Refines ambient) (hproper : small.Proper)
    (hwinding : quadrupledBoxWinding p small ≠ 0)
    (hthreshold : centerResidualBound p ambient small ≤
      derivativeThreshold squarefree ambient) :
    NewtonCenterCertificate p ambient small squarefree := by
  have hresidual := center_residual_le_of_quadrupledBoxWinding_ne_zero
    p hrefines hproper hwinding
  exact computeNewtonCenterOfResidual p squarefree hrefines hresidual hthreshold

/-! ## Taylor dominance around the rational Newton center -/

/-- Executable affine linearization, written in its Newton-centered form
`f'(a)(Z-c)`. -/
def newtonLinearization
    (p : GaussianPolynomial) (source : CCL.RatBox) : GaussianPolynomial :=
  affineCoordinate ((derivative p).eval source.center)
    (rationalNewtonCenter p source)

/-- The Newton-centered affine program is exactly the usual first-order
Taylor polynomial at the rational source center. -/
theorem newtonLinearization_eval
    (p : GaussianPolynomial) (source : CCL.RatBox) (z : QI)
    (hderivative : (derivative p).eval source.center ≠ 0) :
    (newtonLinearization p source).eval z =
      p.eval source.center +
        (derivative p).eval source.center * (z + -source.center) := by
  rw [newtonLinearization, affineCoordinate_eval]
  dsimp only [rationalNewtonCenter]
  simp only [GaussianRat.sub_eq_add_neg]
  field_simp [hderivative]
  ring

/-- The executable Taylor scan bounds the difference between the polynomial
and its Newton-centered affine linearization. -/
theorem normSq_newtonLinearization_error_le
    (p : GaussianPolynomial) {ambient source : CCL.RatBox}
    (hrefines : source.Refines ambient) {z : QI}
    (hz : ambient.Contains z)
    (hderivative : (derivative p).eval source.center ≠ 0) :
    normSq ((p - newtonLinearization p source).eval z) ≤
      denseTaylorRemainderBound p ambient *
        normSq (z + -source.center) ^ 2 := by
  have hcenter : ambient.Contains source.center :=
    hrefines.contains source.contains_center
  have htaylor :=
    normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      p hz hcenter
  have herror :
      (p - newtonLinearization p source).eval z =
        p.eval z + -(p.eval source.center) +
          -((derivative p).eval source.center *
            (z + -source.center)) := by
    rw [eval_sub, newtonLinearization_eval p source z hderivative]
    change p.eval z +
        -(p.eval source.center +
          (derivative p).eval source.center * (z + -source.center)) = _
    ring
  rw [herror]
  exact htaylor

/-- Exact norm of the affine linearization at an arbitrary rational point. -/
theorem normSq_newtonLinearization_eval
    (p : GaussianPolynomial) (source : CCL.RatBox) (z : QI) :
    normSq ((newtonLinearization p source).eval z) =
      normSq ((derivative p).eval source.center) *
        normSq (z - rationalNewtonCenter p source) := by
  rw [newtonLinearization, affineCoordinate_eval, normSq_mul]

/-- Explicit rational margin comparing the Newton affine term with the
quadratic Taylor remainder. -/
def newtonLinearizationDominanceMargin
    {p : GaussianPolynomial}
    (squarefree : GaussianSquarefreeCertificate p)
    (ambient : CCL.RatBox) (radialLower centerRadiusSq : ℚ) : ℚ :=
  derivativeMargin squarefree ambient * radialLower -
    denseTaylorRemainderBound p ambient * centerRadiusSq ^ 2

/-- Quantitative pointwise dominance of the Newton affine term. -/
theorem newtonLinearizationDominanceMargin_le
    {p : GaussianPolynomial} {ambient source : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (hrefines : source.Refines ambient)
    {z : QI} (hz : ambient.Contains z)
    (hderivative : derivativeMargin squarefree ambient ≤
      normSq ((derivative p).eval source.center))
    {radialLower centerRadiusSq : ℚ}
    (hradialLowerNonneg : 0 ≤ radialLower)
    (hradialLower : radialLower ≤
      normSq (z - rationalNewtonCenter p source))
    (hcenterRadius : normSq (z + -source.center) ≤ centerRadiusSq) :
    newtonLinearizationDominanceMargin squarefree ambient
        radialLower centerRadiusSq ≤
      normSq ((newtonLinearization p source).eval z) -
        normSq ((p - newtonLinearization p source).eval z) := by
  have hmarginPos := derivativeMargin_pos squarefree ambient
  have hlinearLower :
      derivativeMargin squarefree ambient * radialLower ≤
        normSq ((newtonLinearization p source).eval z) := by
    rw [normSq_newtonLinearization_eval]
    exact mul_le_mul hderivative hradialLower
      hradialLowerNonneg (normSq_nonneg _)
  have herror := normSq_newtonLinearization_error_le
    p hrefines hz (by
      intro hzero
      rw [hzero, normSq_zero] at hderivative
      exact (not_lt_of_ge hderivative) hmarginPos)
  have hcenterRadiusNonneg := normSq_nonneg (z + -source.center)
  have hcenterRadiusSq : normSq (z + -source.center) ^ 2 ≤
      centerRadiusSq ^ 2 :=
    pow_le_pow_left₀ hcenterRadiusNonneg hcenterRadius 2
  have herrorUpper :
      normSq ((p - newtonLinearization p source).eval z) ≤
        denseTaylorRemainderBound p ambient * centerRadiusSq ^ 2 :=
    herror.trans (mul_le_mul_of_nonneg_left hcenterRadiusSq
      (denseTaylorRemainderBound_pos p ambient).le)
  dsimp only [newtonLinearizationDominanceMargin]
  linarith

/-- Proof-relevant rational geometry sufficient for Taylor dominance on every
edge of a proposed Newton box. -/
structure NewtonBoundaryGeometry
    {p : GaussianPolynomial}
    (squarefree : GaussianSquarefreeCertificate p)
    (ambient source target : CCL.RatBox) where
  radialLower : ℚ
  centerRadiusSq : ℚ
  radialLower_nonneg : 0 ≤ radialLower
  margin_positive : 0 < newtonLinearizationDominanceMargin
    squarefree ambient radialLower centerRadiusSq
  radial_lower : ∀ z : QI, OnBoxBoundary target z →
    radialLower ≤ normSq (z - rationalNewtonCenter p source)
  center_upper : ∀ z : QI, OnBoxBoundary target z →
    normSq (z + -source.center) ≤ centerRadiusSq

/-- Automatic bottom-edge dominance certificate from the shared Newton
boundary geometry. -/
def newtonBottomDominanceCertificate
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target) :
    NormDominanceCertificate
      (horizontalRealCoordinate (newtonLinearization p source) target.yLower)
      (horizontalImagCoordinate (newtonLinearization p source) target.yLower)
      (horizontalRealCoordinate
        (p - newtonLinearization p source) target.yLower)
      (horizontalImagCoordinate
        (p - newtonLinearization p source) target.yLower)
      ⟨target.xLower, target.xUpper⟩ where
  margin := newtonLinearizationDominanceMargin squarefree ambient
    geometry.radialLower geometry.centerRadiusSq
  positive := geometry.margin_positive
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk t target.yLower
    have hzTarget : target.Contains z :=
      ⟨hLower, hUpper, le_rfl, target.y_valid⟩
    have hzBoundary : OnBoxBoundary target z :=
      ⟨hzTarget, Or.inr (Or.inr (Or.inl rfl))⟩
    have hdom := newtonLinearizationDominanceMargin_le squarefree
      hsource (htarget.contains hzTarget) newton.derivative
      geometry.radialLower_nonneg (geometry.radial_lower z hzBoundary)
      (geometry.center_upper z hzBoundary)
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, normSq, z] using hdom

/-- Automatic right-edge dominance certificate. -/
def newtonRightDominanceCertificate
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target) :
    NormDominanceCertificate
      (verticalRealCoordinate (newtonLinearization p source) target.xUpper)
      (verticalImagCoordinate (newtonLinearization p source) target.xUpper)
      (verticalRealCoordinate
        (p - newtonLinearization p source) target.xUpper)
      (verticalImagCoordinate
        (p - newtonLinearization p source) target.xUpper)
      ⟨target.yLower, target.yUpper⟩ where
  margin := newtonLinearizationDominanceMargin squarefree ambient
    geometry.radialLower geometry.centerRadiusSq
  positive := geometry.margin_positive
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk target.xUpper t
    have hzTarget : target.Contains z :=
      ⟨target.x_valid, le_rfl, hLower, hUpper⟩
    have hzBoundary : OnBoxBoundary target z :=
      ⟨hzTarget, Or.inr (Or.inl rfl)⟩
    have hdom := newtonLinearizationDominanceMargin_le squarefree
      hsource (htarget.contains hzTarget) newton.derivative
      geometry.radialLower_nonneg (geometry.radial_lower z hzBoundary)
      (geometry.center_upper z hzBoundary)
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, normSq, z] using hdom

/-- Automatic top-edge dominance certificate. -/
def newtonTopDominanceCertificate
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target) :
    NormDominanceCertificate
      (horizontalRealCoordinate (newtonLinearization p source) target.yUpper)
      (horizontalImagCoordinate (newtonLinearization p source) target.yUpper)
      (horizontalRealCoordinate
        (p - newtonLinearization p source) target.yUpper)
      (horizontalImagCoordinate
        (p - newtonLinearization p source) target.yUpper)
      ⟨target.xLower, target.xUpper⟩ where
  margin := newtonLinearizationDominanceMargin squarefree ambient
    geometry.radialLower geometry.centerRadiusSq
  positive := geometry.margin_positive
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk t target.yUpper
    have hzTarget : target.Contains z :=
      ⟨hLower, hUpper, target.y_valid, le_rfl⟩
    have hzBoundary : OnBoxBoundary target z :=
      ⟨hzTarget, Or.inr (Or.inr (Or.inr rfl))⟩
    have hdom := newtonLinearizationDominanceMargin_le squarefree
      hsource (htarget.contains hzTarget) newton.derivative
      geometry.radialLower_nonneg (geometry.radial_lower z hzBoundary)
      (geometry.center_upper z hzBoundary)
    simpa only [horizontalRealCoordinate_eval,
      horizontalImagCoordinate_eval, normSq, z] using hdom

/-- Automatic left-edge dominance certificate. -/
def newtonLeftDominanceCertificate
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target) :
    NormDominanceCertificate
      (verticalRealCoordinate (newtonLinearization p source) target.xLower)
      (verticalImagCoordinate (newtonLinearization p source) target.xLower)
      (verticalRealCoordinate
        (p - newtonLinearization p source) target.xLower)
      (verticalImagCoordinate
        (p - newtonLinearization p source) target.xLower)
      ⟨target.yLower, target.yUpper⟩ where
  margin := newtonLinearizationDominanceMargin squarefree ambient
    geometry.radialLower geometry.centerRadiusSq
  positive := geometry.margin_positive
  lower := by
    intro t hLower hUpper
    let z := CCL.GaussianRat.mk target.xLower t
    have hzTarget : target.Contains z :=
      ⟨le_rfl, target.x_valid, hLower, hUpper⟩
    have hzBoundary : OnBoxBoundary target z :=
      ⟨hzTarget, Or.inl rfl⟩
    have hdom := newtonLinearizationDominanceMargin_le squarefree
      hsource (htarget.contains hzTarget) newton.derivative
      geometry.radialLower_nonneg (geometry.radial_lower z hzBoundary)
      (geometry.center_upper z hzBoundary)
    simpa only [verticalRealCoordinate_eval,
      verticalImagCoordinate_eval, normSq, z] using hdom

/-- Splitting the polynomial into its Newton linearization and exact error is
an exact sparse-polynomial identity. -/
theorem newtonLinearization_add_error_toPolynomial
    (p : GaussianPolynomial) (source : CCL.RatBox) :
    (newtonLinearization p source +
        (p - newtonLinearization p source)).toPolynomial = p.toPolynomial := by
  rw [toPolynomial_add, toPolynomial_sub]
  ring

/-- Finite Taylor-Rouché transfer from the polynomial to its Newton affine
linearization on a target box carrying the rational geometry record. -/
theorem quadrupledBoxWinding_eq_newtonLinearization
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (htargetProper : target.Proper)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target) :
    quadrupledBoxWinding p target =
      quadrupledBoxWinding (newtonLinearization p source) target := by
  have htransfer := quadrupledBoxWinding_add_of_normDominance
    (newtonLinearization p source)
    (p - newtonLinearization p source) target
    (newtonBottomDominanceCertificate squarefree newton hsource htarget geometry)
    (newtonRightDominanceCertificate squarefree newton hsource htarget geometry)
    (newtonTopDominanceCertificate squarefree newton hsource htarget geometry)
    (newtonLeftDominanceCertificate squarefree newton hsource htarget geometry)
    htargetProper.1 htargetProper.2
  have hcongr := quadrupledBoxWinding_congr target
    (newtonLinearization_add_error_toPolynomial p source)
  exact hcongr.symm.trans htransfer

/-- A target box with the finite Newton geometry and strict containment of the
Newton center has raw winding four. -/
theorem quadrupledBoxWinding_eq_four_of_newtonBoundaryGeometry
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (htargetProper : target.Proper)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target)
    (hcxLower : target.xLower < (rationalNewtonCenter p source).re)
    (hcxUpper : (rationalNewtonCenter p source).re < target.xUpper)
    (hcyLower : target.yLower < (rationalNewtonCenter p source).im)
    (hcyUpper : (rationalNewtonCenter p source).im < target.yUpper) :
    quadrupledBoxWinding p target = 4 := by
  have hmarginPos := derivativeMargin_pos squarefree ambient
  have hderivativeNe : (derivative p).eval source.center ≠ 0 := by
    intro hzero
    have hderivative := newton.derivative
    rw [hzero, normSq_zero] at hderivative
    exact (not_lt_of_ge hderivative) hmarginPos
  have haffine := affineCoordinate_box_normalization hderivativeNe
    (rationalNewtonCenter p source) hcxLower hcxUpper hcyLower hcyUpper
  have hlinearRaw :
      quadrupledBoxWinding (newtonLinearization p source) target = 4 := by
    simpa only [newtonLinearization] using haffine.1
  have htransfer := quadrupledBoxWinding_eq_newtonLinearization
    squarefree newton hsource htarget htargetProper geometry
  rw [htransfer, hlinearRaw]

/-- Ordinary winding one is the normalized form of the exact raw winding
certificate above. -/
theorem boxWinding_eq_one_of_newtonBoundaryGeometry
    {p : GaussianPolynomial} {ambient source target : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) (htarget : target.Refines ambient)
    (htargetProper : target.Proper)
    (geometry : NewtonBoundaryGeometry squarefree ambient source target)
    (hcxLower : target.xLower < (rationalNewtonCenter p source).re)
    (hcxUpper : (rationalNewtonCenter p source).re < target.xUpper)
    (hcyLower : target.yLower < (rationalNewtonCenter p source).im)
    (hcyUpper : (rationalNewtonCenter p source).im < target.yUpper) :
    boxWinding p target = 1 := by
  rw [boxWinding,
    quadrupledBoxWinding_eq_four_of_newtonBoundaryGeometry
      squarefree newton hsource htarget htargetProper geometry
      hcxLower hcxUpper hcyLower hcyUpper]
  norm_num

/-! ## Specialization to the four Newton bands -/

/-- A rational rectangle whose four sides have been chosen in the paper's
bands at coordinate distance between `r` and `2r` from the Newton center. -/
structure NewtonBandBox (center : QI) (r : ℚ) where
  box : CCL.RatBox
  left_lower : center.re - 2 * r ≤ box.xLower
  left_upper : box.xLower ≤ center.re - r
  right_lower : center.re + r ≤ box.xUpper
  right_upper : box.xUpper ≤ center.re + 2 * r
  bottom_lower : center.im - 2 * r ≤ box.yLower
  bottom_upper : box.yLower ≤ center.im - r
  top_lower : center.im + r ≤ box.yUpper
  top_upper : box.yUpper ≤ center.im + 2 * r

theorem NewtonBandBox.proper
    {center : QI} {r : ℚ} (band : NewtonBandBox center r)
    (hr : 0 < r) : band.box.Proper := by
  constructor
  · linarith [band.left_upper, band.right_lower]
  · linarith [band.bottom_upper, band.top_lower]

/-- Both side lengths are at most `4r`, so the selected band's squared
diagonal is at most `32r²`. -/
theorem NewtonBandBox.diagonalSq_le
    {center : QI} {r : ℚ} (band : NewtonBandBox center r)
    (hr : 0 < r) : band.box.diagonalSq ≤ 32 * r ^ 2 := by
  let widthX := band.box.xUpper - band.box.xLower
  let widthY := band.box.yUpper - band.box.yLower
  have hxNonneg : 0 ≤ widthX := sub_nonneg.mpr band.box.x_valid
  have hyNonneg : 0 ≤ widthY := sub_nonneg.mpr band.box.y_valid
  have hxBound : widthX ≤ 4 * r := by
    dsimp only [widthX]
    linarith [band.left_lower, band.right_upper]
  have hyBound : widthY ≤ 4 * r := by
    dsimp only [widthY]
    linarith [band.bottom_lower, band.top_upper]
  have hxProduct : 0 ≤ (4 * r - widthX) * (4 * r + widthX) :=
    mul_nonneg (sub_nonneg.mpr hxBound) (by nlinarith)
  have hyProduct : 0 ≤ (4 * r - widthY) * (4 * r + widthY) :=
    mul_nonneg (sub_nonneg.mpr hyBound) (by nlinarith)
  dsimp only [CCL.RatBox.diagonalSq, widthX, widthY] at *
  nlinarith

theorem NewtonBandBox.center_strictly_inside
    {center : QI} {r : ℚ} (band : NewtonBandBox center r)
    (hr : 0 < r) :
    band.box.xLower < center.re ∧ center.re < band.box.xUpper ∧
      band.box.yLower < center.im ∧ center.im < band.box.yUpper := by
  constructor
  · linarith [band.left_upper]
  constructor
  · linarith [band.right_lower]
  constructor
  · linarith [band.bottom_upper]
  · linarith [band.top_lower]

/-- Every boundary point is at squared distance at least `r²` from the
Newton center. -/
theorem NewtonBandBox.radial_lower
    {center : QI} {r : ℚ} (band : NewtonBandBox center r)
    (hr : 0 < r) {z : QI} (hz : OnBoxBoundary band.box z) :
    r ^ 2 ≤ normSq (z - center) := by
  rcases hz with ⟨_hzMem, hside⟩
  simp only [normSq, sub_re, sub_im]
  rcases hside with hleft | hright | hbottom | htop
  · have hd : z.re - center.re ≤ -r := by
      rw [hleft]
      linarith [band.left_upper]
    have hproduct : 0 ≤
        (z.re - center.re + r) * (z.re - center.re - r) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [sq_nonneg (z.im - center.im)]
  · have hd : r ≤ z.re - center.re := by
      rw [hright]
      linarith [band.right_lower]
    have hproduct : 0 ≤
        (z.re - center.re - r) * (z.re - center.re + r) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (z.im - center.im)]
  · have hd : z.im - center.im ≤ -r := by
      rw [hbottom]
      linarith [band.bottom_upper]
    have hproduct : 0 ≤
        (z.im - center.im + r) * (z.im - center.im - r) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [sq_nonneg (z.re - center.re)]
  · have hd : r ≤ z.im - center.im := by
      rw [htop]
      linarith [band.top_lower]
    have hproduct : 0 ≤
        (z.im - center.im - r) * (z.im - center.im + r) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (z.re - center.re)]

/-- Every point of the band rectangle is within squared distance `8r²` of
the Newton center. -/
theorem NewtonBandBox.radial_upper
    {center : QI} {r : ℚ} (band : NewtonBandBox center r)
    {z : QI} (hz : band.box.Contains z) :
    normSq (z - center) ≤ 8 * r ^ 2 := by
  rcases hz with ⟨hzxLower, hzxUpper, hzyLower, hzyUpper⟩
  have hxLower : -(2 * r) ≤ z.re - center.re := by
    linarith [band.left_lower]
  have hxUpper : z.re - center.re ≤ 2 * r := by
    linarith [band.right_upper]
  have hyLower : -(2 * r) ≤ z.im - center.im := by
    linarith [band.bottom_lower]
  have hyUpper : z.im - center.im ≤ 2 * r := by
    linarith [band.top_upper]
  have hxProduct : 0 ≤
      (2 * r - (z.re - center.re)) * (2 * r + (z.re - center.re)) :=
    mul_nonneg (by linarith) (by linarith)
  have hyProduct : 0 ≤
      (2 * r - (z.im - center.im)) * (2 * r + (z.im - center.im)) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [normSq, sub_re, sub_im]
  nlinarith

/-- The paper's rational scale inequalities construct the complete Newton
boundary geometry for any rectangle selected from the four bands. -/
def newtonBoundaryGeometryOfBand
    {p : GaussianPolynomial} {ambient source : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    {r : ℚ} (band : NewtonBandBox (rationalNewtonCenter p source) r)
    (hr : 0 < r)
    (hnear : centerResidualBound p ambient source /
        derivativeMargin squarefree ambient < r ^ 2 / 16)
    (htaylor : 300 * denseTaylorRemainderBound p ambient * r ^ 2 <
      derivativeMargin squarefree ambient) :
    NewtonBoundaryGeometry squarefree ambient source band.box where
  radialLower := r ^ 2
  centerRadiusSq := 17 * r ^ 2
  radialLower_nonneg := sq_nonneg r
  margin_positive := by
    have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr
    have hscaled := mul_lt_mul_of_pos_right htaylor hrSq
    dsimp only [newtonLinearizationDominanceMargin]
    have hL := denseTaylorRemainderBound_pos p ambient
    nlinarith [mul_nonneg hL.le (sq_nonneg (r ^ 2))]
  radial_lower := by
    intro z hz
    exact band.radial_lower hr hz
  center_upper := by
    intro z hz
    have hzNewton : normSq
        (z - rationalNewtonCenter p source) ≤ 8 * r ^ 2 :=
      band.radial_upper hz.1
    have hnewton := newton.displacement
    rw [newton.point_eq] at hnewton
    have hnewtonNear : normSq
        (rationalNewtonCenter p source - source.center) < r ^ 2 / 16 :=
      hnewton.trans_lt hnear
    have hdecomposition :
        z + -source.center =
          (z + -(rationalNewtonCenter p source)) +
            (rationalNewtonCenter p source + -source.center) := by
      ext <;> simp only [add_re, add_im, neg_re, neg_im] <;> ring
    rw [hdecomposition]
    have htwo := normSq_add_le_two
      (z + -(rationalNewtonCenter p source))
      (rationalNewtonCenter p source + -source.center)
    have hzNewton' : normSq
        (z + -(rationalNewtonCenter p source)) ≤ 8 * r ^ 2 := by
      simpa only [GaussianRat.sub_eq_add_neg] using hzNewton
    have hnewtonNear' : normSq
        (rationalNewtonCenter p source + -source.center) < r ^ 2 / 16 := by
      simpa only [GaussianRat.sub_eq_add_neg] using hnewtonNear
    nlinarith [sq_nonneg r]

/-- Every safe-band rectangle satisfying the two explicit scale inequalities
has raw winding four. -/
theorem quadrupledBoxWinding_eq_four_of_newtonBandBox
    {p : GaussianPolynomial} {ambient source : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient)
    {r : ℚ} (hr : 0 < r)
    (band : NewtonBandBox (rationalNewtonCenter p source) r)
    (htarget : band.box.Refines ambient)
    (hnear : centerResidualBound p ambient source /
        derivativeMargin squarefree ambient < r ^ 2 / 16)
    (htaylor : 300 * denseTaylorRemainderBound p ambient * r ^ 2 <
      derivativeMargin squarefree ambient) :
    quadrupledBoxWinding p band.box = 4 := by
  have hinside := band.center_strictly_inside hr
  exact quadrupledBoxWinding_eq_four_of_newtonBoundaryGeometry squarefree newton
    hsource htarget (band.proper hr)
    (newtonBoundaryGeometryOfBand squarefree newton band hr hnear htaylor)
    hinside.1 hinside.2.1 hinside.2.2.1 hinside.2.2.2

/-- Normalized winding-one form of the exact raw certificate. -/
theorem boxWinding_eq_one_of_newtonBandBox
    {p : GaussianPolynomial} {ambient source : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient)
    {r : ℚ} (hr : 0 < r)
    (band : NewtonBandBox (rationalNewtonCenter p source) r)
    (htarget : band.box.Refines ambient)
    (hnear : centerResidualBound p ambient source /
        derivativeMargin squarefree ambient < r ^ 2 / 16)
    (htaylor : 300 * denseTaylorRemainderBound p ambient * r ^ 2 <
      derivativeMargin squarefree ambient) :
    boxWinding p band.box = 1 := by
  rw [boxWinding,
    quadrupledBoxWinding_eq_four_of_newtonBandBox squarefree newton
      hsource hr band htarget hnear htaylor]
  norm_num

end FTA.LocalExtraction
