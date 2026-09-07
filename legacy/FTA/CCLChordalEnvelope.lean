import CCL.Geometry.Chordal
import CCL.Encoding.RawParser
import FTA.BoxGeometry

/-!
# Tagged chordal envelopes for CCL root tracks

This module separates the two finite approximations used by the revised FTA
controller.  A raw word determines a tagged homogeneous truncation, while a
winding box contracts independently.  The square-root-free triangle estimate
couples a certified truncation error to the whole box.  A second rational
inequality turns precomputed coordinate separation into projective separation.
-/

namespace FTA
namespace CCLChordalEnvelope

open CCL
open CCL.GaussianRat

abbrev QI := CCL.GaussianRat

/-- A raw word retained alongside its canonical projective truncation.  The
tag remains informative when several partial-block words have the same pair. -/
structure TaggedTruncation where
  word : Prefix.Word
deriving DecidableEq, Repr

namespace TaggedTruncation

/-- Canonical homogeneous pair attached to the tagged raw word. -/
def point (tag : TaggedTruncation) : Proj QI :=
  (RawParser.parse tag.word).truncation

/-- Parser invertibility guarantees that every tagged truncation is a valid
homogeneous pair, including during an unfinished raw block. -/
theorem point_hasNonzeroCoordinate (tag : TaggedTruncation) :
    tag.point.HasNonzeroCoordinate := by
  rw [point, RawParser.State.truncation, Mat2.act_omega]
  by_cases ha : (RawParser.parse tag.word).matrix.a = 0
  · right
    intro hc
    change (RawParser.parse tag.word).matrix.c = 0 at hc
    exact (RawParser.parse_det_ne tag.word) (by
      rw [Mat2.det, ha, hc]
      simp)
  · exact Or.inl ha

end TaggedTruncation

/-- A rational upper bound for the error between one affine reference point
and the tagged truncation supplied by a raw CCL word. -/
structure ReferenceError where
  truncation : TaggedTruncation
  reference : QI
  radiusSq : ℚ
  radiusSq_nonneg : 0 ≤ radiusSq
  certified :
    chordalSq (Proj.affine reference) truncation.point ≤ radiusSq

/-- Square-root-free error after coupling a reference certificate to an
independently contracting winding box containing that reference. -/
def coupledRadiusSq (B : RatBox) (certificate : ReferenceError) : ℚ :=
  2 * (B.diagonalSq + certificate.radiusSq)

theorem coupledRadiusSq_nonneg (B : RatBox) (certificate : ReferenceError) :
    0 ≤ coupledRadiusSq B certificate := by
  exact mul_nonneg (by norm_num)
    (add_nonneg B.diagonalSq_nonneg certificate.radiusSq_nonneg)

/-- Dropping the affine normalization denominators only enlarges `χ²`. -/
theorem chordalSq_affine_le_normSq (z w : QI) :
    chordalSq (Proj.affine z) (Proj.affine w) ≤ normSq (z - w) := by
  rw [chordalSq_affine]
  have leftPositive : 0 < 1 + normSq z := by
    linarith [normSq_nonneg z]
  have rightPositive : 0 < 1 + normSq w := by
    linarith [normSq_nonneg w]
  have denominatorOne :
      1 ≤ (1 + normSq z) * (1 + normSq w) := by
    nlinarith [normSq_nonneg z, normSq_nonneg w,
      mul_nonneg (normSq_nonneg z) (normSq_nonneg w)]
  apply (div_le_iff₀ (mul_pos leftPositive rightPositive)).2
  calc
    normSq (z - w) = normSq (z - w) * 1 := by ring
    _ ≤ normSq (z - w) * ((1 + normSq z) * (1 + normSq w)) :=
      mul_le_mul_of_nonneg_left denominatorOne (normSq_nonneg (z - w))

/-- The rational coupling inequality: every point in the winding box lies in
the chordal envelope obtained by adding box error and truncation error. -/
theorem box_point_le_coupledRadiusSq
    {B : RatBox} {certificate : ReferenceError}
    (referenceInside : B.Contains certificate.reference)
    {z : QI} (inside : B.Contains z) :
    chordalSq (Proj.affine z) certificate.truncation.point ≤
      coupledRadiusSq B certificate := by
  have triangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate z)
    (Proj.affine_hasNonzeroCoordinate certificate.reference)
    certificate.truncation.point_hasNonzeroCoordinate
  have boxError :
      chordalSq (Proj.affine z) (Proj.affine certificate.reference) ≤
        B.diagonalSq :=
    (chordalSq_affine_le_normSq z certificate.reference).trans
      (RatBox.normSq_sub_le_diagonalSq inside referenceInside)
  dsimp [coupledRadiusSq]
  linarith [triangle, certificate.certified]

/-- Finite projective envelope produced by a box/reference coupling. -/
structure CoupledEnvelope where
  box : RatBox
  certificate : ReferenceError
  referenceInside : box.Contains certificate.reference

namespace CoupledEnvelope

/-- The envelope's exact rational squared radius. -/
def radiusSq (envelope : CoupledEnvelope) : ℚ :=
  coupledRadiusSq envelope.box envelope.certificate

/-- Membership in the closed projective ball around the tagged truncation. -/
def Contains (envelope : CoupledEnvelope) (z : QI) : Prop :=
  chordalSq (Proj.affine z) envelope.certificate.truncation.point ≤
    envelope.radiusSq

theorem radiusSq_nonneg (envelope : CoupledEnvelope) :
    0 ≤ envelope.radiusSq :=
  coupledRadiusSq_nonneg envelope.box envelope.certificate

theorem contains_of_box_contains (envelope : CoupledEnvelope) {z : QI}
    (inside : envelope.box.Contains z) : envelope.Contains z :=
  box_point_le_coupledRadiusSq envelope.referenceInside inside

/-- An explicit pair of component bounds certifies contraction of the coupled
envelope without requiring the displayed truncation pair itself to move. -/
theorem radiusSq_le {envelope : CoupledEnvelope} {boxError cylinderError : ℚ}
    (boxBound : envelope.box.diagonalSq ≤ boxError)
    (cylinderBound : envelope.certificate.radiusSq ≤ cylinderError) :
    envelope.radiusSq ≤ 2 * (boxError + cylinderError) := by
  dsimp [radiusSq, coupledRadiusSq]
  linarith

end CoupledEnvelope

/-- Uniform rational upper bound for `1 + N(z)` throughout a rational box. -/
def affineWeightBound (B : RatBox) : ℚ :=
  1 + 2 * B.coordinateRadius ^ 2

theorem normSq_le_two_coordinateRadius_sq {B : RatBox} {z : QI}
    (inside : B.Contains z) :
    normSq z ≤ 2 * B.coordinateRadius ^ 2 := by
  rcases B.abs_coordinates_le_radius inside with ⟨realBound, imagBound⟩
  have realSquare : z.re ^ 2 ≤ B.coordinateRadius ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg z.re) B.coordinateRadius_nonneg).2 realBound
  have imagSquare : z.im ^ 2 ≤ B.coordinateRadius ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg z.im) B.coordinateRadius_nonneg).2 imagBound
  dsimp [normSq]
  linarith

theorem affineWeightBound_pos (B : RatBox) : 0 < affineWeightBound B := by
  dsimp [affineWeightBound]
  positivity

theorem affine_weight_le_bound {B : RatBox} {z : QI}
    (inside : B.Contains z) : 1 + normSq z ≤ affineWeightBound B := by
  dsimp [affineWeightBound]
  linarith [normSq_le_two_coordinateRadius_sq inside]

/-- Projective squared separation obtained from a displayed rational
coordinate gap and uniform affine normalization bounds. -/
def chordalGapSq (B C : RatBox) (coordinateGap : ℚ) : ℚ :=
  coordinateGap ^ 2 / (affineWeightBound B * affineWeightBound C)

theorem chordalGapSq_pos (B C : RatBox) {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap) :
    0 < chordalGapSq B C coordinateGap := by
  exact div_pos (sq_pos_of_pos gapPositive)
    (mul_pos (affineWeightBound_pos B) (affineWeightBound_pos C))

/-- Every affine point pair in coordinate-separated boxes has at least the
precomputed rational squared chordal gap. -/
theorem chordalGapSq_le
    {B C : RatBox} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      B.xUpper + coordinateGap ≤ C.xLower ∨
      C.xUpper + coordinateGap ≤ B.xLower ∨
      B.yUpper + coordinateGap ≤ C.yLower ∨
      C.yUpper + coordinateGap ≤ B.yLower)
    {u v : QI} (insideB : B.Contains u) (insideC : C.Contains v) :
    chordalGapSq B C coordinateGap ≤
      chordalSq (Proj.affine u) (Proj.affine v) := by
  have numeratorBound := RatBox.sq_le_normSq_sub_of_coordinate_gap
    gapPositive coordinateSeparated insideB insideC
  have actualDenominatorPositive :
      0 < (1 + normSq u) * (1 + normSq v) :=
    mul_pos (by linarith [normSq_nonneg u])
      (by linarith [normSq_nonneg v])
  have boundDenominatorPositive :
      0 < affineWeightBound B * affineWeightBound C :=
    mul_pos (affineWeightBound_pos B) (affineWeightBound_pos C)
  have denominatorBound :
      (1 + normSq u) * (1 + normSq v) ≤
        affineWeightBound B * affineWeightBound C :=
    mul_le_mul (affine_weight_le_bound insideB)
      (affine_weight_le_bound insideC)
      (by linarith [normSq_nonneg v])
      (by linarith [affineWeightBound_pos B])
  have normSymm : normSq (u - v) = normSq (v - u) := by
    have difference : u - v = -(v - u) := by
      ext <;> simp
    rw [difference, normSq_neg]
  rw [chordalSq_affine]
  apply (le_div_iff₀ actualDenominatorPositive).2
  rw [chordalGapSq, div_mul_eq_mul_div]
  apply (div_le_iff₀ boundDenominatorPositive).2
  rw [normSymm]
  calc
    coordinateGap ^ 2 * ((1 + normSq u) * (1 + normSq v)) ≤
        coordinateGap ^ 2 *
          (affineWeightBound B * affineWeightBound C) :=
      mul_le_mul_of_nonneg_left denominatorBound (sq_nonneg coordinateGap)
    _ ≤ normSq (v - u) *
          (affineWeightBound B * affineWeightBound C) :=
      mul_le_mul_of_nonneg_right numeratorBound
        (le_of_lt boundDenominatorPositive)

/-- If two tagged envelopes are thinner than the precomputed separation gap,
their canonical truncations cannot represent the same projective point.  The
factor four comes from two applications of the rational squared triangle
estimate; no square roots or real-number completion are introduced. -/
theorem truncations_not_equivalent_of_error_sum_lt_gap
    {B C : RatBox} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      B.xUpper + coordinateGap ≤ C.xLower ∨
      C.xUpper + coordinateGap ≤ B.xLower ∨
      B.yUpper + coordinateGap ≤ C.yLower ∨
      C.yUpper + coordinateGap ≤ B.yLower)
    {left right : CoupledEnvelope}
    (leftBox : left.box = B) (rightBox : right.box = C)
    (thin : 4 * (left.radiusSq + right.radiusSq) <
      chordalGapSq B C coordinateGap) :
    ¬left.certificate.truncation.point.Equivalent
      right.certificate.truncation.point := by
  intro equivalent
  let u := left.certificate.reference
  let v := right.certificate.reference
  have insideB : B.Contains u := by
    simpa only [u, ← leftBox] using left.referenceInside
  have insideC : C.Contains v := by
    simpa only [v, ← rightBox] using right.referenceInside
  have lower := chordalGapSq_le gapPositive coordinateSeparated insideB insideC
  have middleZero :
      chordalSq left.certificate.truncation.point
        right.certificate.truncation.point = 0 :=
    chordalSq_eq_zero_of_equivalent equivalent
  have rightTriangle := chordalSq_triangle_two
    left.certificate.truncation.point_hasNonzeroCoordinate
    right.certificate.truncation.point_hasNonzeroCoordinate
    (Proj.affine_hasNonzeroCoordinate v)
  have leftToV :
      chordalSq left.certificate.truncation.point (Proj.affine v) ≤
        2 * right.radiusSq := by
    have rightContains := right.contains_of_box_contains right.referenceInside
    change chordalSq (Proj.affine v) right.certificate.truncation.point ≤
      right.radiusSq at rightContains
    rw [chordalSq_comm] at rightContains
    linarith [rightTriangle, middleZero]
  have leftTriangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate u)
    left.certificate.truncation.point_hasNonzeroCoordinate
    (Proj.affine_hasNonzeroCoordinate v)
  have leftContains := left.contains_of_box_contains left.referenceInside
  change chordalSq (Proj.affine u) left.certificate.truncation.point ≤
    left.radiusSq at leftContains
  have upper :
      chordalSq (Proj.affine u) (Proj.affine v) ≤
        4 * (left.radiusSq + right.radiusSq) := by
    linarith [leftTriangle, leftContains, leftToV,
      left.radiusSq_nonneg, right.radiusSq_nonneg]
  linarith

end CCLChordalEnvelope
end FTA
