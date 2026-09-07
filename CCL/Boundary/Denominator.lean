import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.WindingPointExclusion
import CCL.Boundary.Geometry

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

namespace CCL.CCLDenominator

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian

/-- A nonzero determinant constructively forces a nonzero affine lower row. -/
theorem lowerRow_ne_of_determinant_ne (matrix : Mat2)
    (determinantNonzero : CCL.Chordal.Mat2.det matrix ≠ 0) :
    matrix.c ≠ 0 ∨ matrix.d ≠ 0 := by
  by_cases lowerLeftZero : matrix.c = 0
  · by_cases lowerRightZero : matrix.d = 0
    · have determinantZero :
          CCL.Chordal.Mat2.det matrix = 0 := by
        rw [CCL.Chordal.Mat2.det, lowerLeftZero, lowerRightZero]
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_zero,
          RFAP.ConstructiveGaussian.Gaussian.sub_zero]
      exact (determinantNonzero determinantZero).elim
    · exact Or.inr lowerRightZero
  · exact Or.inl lowerLeftZero

/-- The unique affine pole when the lower-left matrix entry is nonzero. -/
def decoderPole (matrix : Mat2) : Gaussian :=
  (-matrix.d) * matrix.c⁻¹

theorem denominator_at_decoderPole (matrix : Mat2)
    (lowerLeftNonzero : matrix.c ≠ 0) :
    CCL.RawParser.denominator matrix (decoderPole matrix) = 0 := by
  unfold CCL.RawParser.denominator decoderPole
  calc
    matrix.c * ((-matrix.d) * matrix.c⁻¹) + matrix.d =
        (-matrix.d) * (matrix.c * matrix.c⁻¹) + matrix.d := by
      apply congrArg (fun value : Gaussian => value + matrix.d)
      calc
        matrix.c * ((-matrix.d) * matrix.c⁻¹) =
            (matrix.c * (-matrix.d)) * matrix.c⁻¹ :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = ((-matrix.d) * matrix.c) * matrix.c⁻¹ := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm matrix.c (-matrix.d)]
        _ = (-matrix.d) * (matrix.c * matrix.c⁻¹) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = (-matrix.d) * 1 + matrix.d := by
      rw [show matrix.c * matrix.c⁻¹ = 1 by
        exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel matrix.c
          lowerLeftNonzero]
    _ = -matrix.d + matrix.d := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = 0 := neg_add_cancel matrix.d

/-- The denominator factors as `c` times displacement from its pole. -/
theorem denominator_eq_mul_sub_pole (matrix : Mat2)
    (lowerLeftNonzero : matrix.c ≠ 0) (value : Gaussian) :
    CCL.RawParser.denominator matrix value =
      matrix.c * (value - decoderPole matrix) := by
  have poleZero := denominator_at_decoderPole matrix lowerLeftNonzero
  unfold CCL.RawParser.denominator at poleZero ⊢
  calc
    matrix.c * value + matrix.d =
        (matrix.c * value + matrix.d) -
          (matrix.c * decoderPole matrix + matrix.d) := by
      rw [poleZero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, zero_re, zero_im] <;>
        ring1
    _ = matrix.c * (value - decoderPole matrix) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im] <;>
        ring1

/-- One explicit coordinate side by which a rational point is outside a
rational box. -/
inductive OutsideSide (box : Box) (point : Gaussian) where
  | left (less : point.re < box.xLower)
  | right (less : box.xUpper < point.re)
  | bottom (less : point.im < box.yLower)
  | top (less : box.yUpper < point.im)

/-- A failed finite membership test computes a strict outside side. -/
def outsideSide {box : Box} {point : Gaussian}
    (outside : ¬box.Contains point) : OutsideSide box point := by
  by_cases left : point.re < box.xLower
  · exact .left left
  by_cases right : box.xUpper < point.re
  · exact .right right
  by_cases bottom : point.im < box.yLower
  · exact .bottom bottom
  by_cases top : box.yUpper < point.im
  · exact .top top
  exact (outside ⟨le_of_not_gt left, le_of_not_gt right,
    le_of_not_gt bottom, le_of_not_gt top⟩).elim

namespace OutsideSide

/-- Squared coordinate distance certified by an outside side. -/
def margin {box : Box} {point : Gaussian} :
    OutsideSide box point → Coordinate
  | .left _ => (box.xLower - point.re) ^ 2
  | .right _ => (point.re - box.xUpper) ^ 2
  | .bottom _ => (box.yLower - point.im) ^ 2
  | .top _ => (point.im - box.yUpper) ^ 2

theorem margin_pos {box : Box} {point : Gaussian}
    (side : OutsideSide box point) : 0 < side.margin := by
  cases side with
  | left less =>
      rw [margin, pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct less)
        (RFAP.ConstructiveFraction.sub_pos_direct less)
  | right less =>
      rw [margin, pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct less)
        (RFAP.ConstructiveFraction.sub_pos_direct less)
  | bottom less =>
      rw [margin, pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct less)
        (RFAP.ConstructiveFraction.sub_pos_direct less)
  | top less =>
      rw [margin, pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct less)
        (RFAP.ConstructiveFraction.sub_pos_direct less)

private theorem sq_le_sq_of_nonneg
    {left right : Coordinate} (order : left ≤ right)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    left ^ 2 ≤ right ^ 2 := by
  rw [pow_two, pow_two]
  exact RFAP.ConstructiveFraction.mul_le_mul_direct order order
    leftNonnegative rightNonnegative

/-- Every point of the box stays at least the displayed squared coordinate
distance from the excluded point. -/
theorem margin_le_normSq_sub
    {box : Box} {point value : Gaussian}
    (side : OutsideSide box point) (inside : box.Contains value) :
    side.margin ≤ normSq (value - point) := by
  cases side with
  | left less =>
      have gapNonnegative : 0 ≤ box.xLower - point.re :=
        RFAP.ConstructiveFraction.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ value.re - point.re :=
        RFAP.ConstructiveFraction.sub_nonneg_direct (less.le.trans inside.1)
      have gapOrder : box.xLower - point.re ≤ value.re - point.re :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.1 point.re
      calc
        (OutsideSide.left less).margin =
            (box.xLower - point.re) ^ 2 := rfl
        _ ≤ (value.re - point.re) ^ 2 :=
          sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_right
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        _ = normSq (value - point) := by
          simp only [normSq, sub_re, sub_im]
  | right less =>
      have gapNonnegative : 0 ≤ point.re - box.xUpper :=
        RFAP.ConstructiveFraction.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ point.re - value.re :=
        RFAP.ConstructiveFraction.sub_nonneg_direct
          (inside.2.1.trans less.le)
      have gapOrder : point.re - box.xUpper ≤ point.re - value.re :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct inside.2.1 point.re
      calc
        (OutsideSide.right less).margin =
            (point.re - box.xUpper) ^ 2 := rfl
        _ ≤ (point.re - value.re) ^ 2 :=
          sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ = (value.re - point.re) ^ 2 := by ring1
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_right
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        _ = normSq (value - point) := by
          simp only [normSq, sub_re, sub_im]
  | bottom less =>
      have gapNonnegative : 0 ≤ box.yLower - point.im :=
        RFAP.ConstructiveFraction.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ value.im - point.im :=
        RFAP.ConstructiveFraction.sub_nonneg_direct
          (less.le.trans inside.2.2.1)
      have gapOrder : box.yLower - point.im ≤ value.im - point.im :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.2.1 point.im
      calc
        (OutsideSide.bottom less).margin =
            (box.yLower - point.im) ^ 2 := rfl
        _ ≤ (value.im - point.im) ^ 2 :=
          sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        _ = normSq (value - point) := by
          simp only [normSq, sub_re, sub_im]
  | top less =>
      have gapNonnegative : 0 ≤ point.im - box.yUpper :=
        RFAP.ConstructiveFraction.sub_nonneg_direct less.le
      have coordinateNonnegative : 0 ≤ point.im - value.im :=
        RFAP.ConstructiveFraction.sub_nonneg_direct
          (inside.2.2.2.trans less.le)
      have gapOrder : point.im - box.yUpper ≤ point.im - value.im :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct inside.2.2.2 point.im
      calc
        (OutsideSide.top less).margin =
            (point.im - box.yUpper) ^ 2 := rfl
        _ ≤ (point.im - value.im) ^ 2 :=
          sq_le_sq_of_nonneg gapOrder gapNonnegative coordinateNonnegative
        _ = (value.im - point.im) ^ 2 := by ring1
        _ ≤ (value.re - point.re) ^ 2 +
            (value.im - point.im) ^ 2 :=
          le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        _ = normSq (value - point) := by
          simp only [normSq, sub_re, sub_im]

end OutsideSide

/-- A refined winding state carrying a uniform positive lower bound for one
decoder denominator. -/
structure SeparationOutput
    (p : GaussianPolynomial) (ambient : Box)
    (current : WindingOneState p ambient) (matrix : Mat2) where
  state : WindingOneState p ambient
  refines : state.box.Refines current.box
  margin : Coordinate
  margin_pos : 0 < margin
  lower : ∀ {value : Gaussian}, state.box.Contains value →
    margin ≤ normSq (CCL.RawParser.denominator matrix value)

namespace SeparationOutput

/-- Restrict a denominator certificate to any later explicit subbox. -/
def restrict
    {p : GaussianPolynomial} {ambient : Box}
    {current : WindingOneState p ambient} {matrix : Mat2}
    (output : SeparationOutput p ambient current matrix)
    (later : WindingOneState p ambient)
    (laterRefines : later.box.Refines output.state.box) :
    SeparationOutput p ambient current matrix where
  state := later
  refines := laterRefines.trans output.refines
  margin := output.margin
  margin_pos := output.margin_pos
  lower := fun inside => output.lower (laterRefines.contains inside)

end SeparationOutput

/-- A constant nonzero lower row already has a uniform denominator margin. -/
def separateConstant
    {p : GaussianPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) (matrix : Mat2)
    (lowerLeftZero : matrix.c = 0) (lowerRightNonzero : matrix.d ≠ 0) :
    SeparationOutput p ambient current matrix where
  state := current
  refines := RFAP.Boxes.Box.refines_refl current.box
  margin := normSq matrix.d
  margin_pos := normSq_pos lowerRightNonzero
  lower := by
    intro value _inside
    simp only [CCL.RawParser.denominator, lowerLeftZero,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add]
    exact le_rfl

/-- An already-excluded pole yields an immediate positive denominator
margin, whether or not that pole is a different polynomial root. -/
def separateOutside
    {p : GaussianPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) (matrix : Mat2)
    (lowerLeftNonzero : matrix.c ≠ 0)
    (outside : ¬current.box.Contains (decoderPole matrix)) :
    SeparationOutput p ambient current matrix := by
  let side := outsideSide outside
  refine
    { state := current
      refines := RFAP.Boxes.Box.refines_refl current.box
      margin := normSq matrix.c * side.margin
      margin_pos := RFAP.ConstructiveFraction.mul_pos_direct
        (normSq_pos lowerLeftNonzero) side.margin_pos
      lower := ?_ }
  intro value inside
  have distance := side.margin_le_normSq_sub inside
  rw [denominator_eq_mul_sub_pole matrix lowerLeftNonzero value, normSq_mul]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distance
    (normSq_nonneg matrix.c)

/-- One winding refinement excludes a nonroot pole and therefore supplies a
positive uniform denominator margin. -/
def separateNonroot
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (matrix : Mat2)
    (lowerLeftNonzero : matrix.c ≠ 0)
    (nonroot : p.eval (decoderPole matrix) ≠ 0) :
    SeparationOutput p ambient current matrix := by
  let state := CCL.WindingPointExclusion.refinePastPoint
    track current (decoderPole matrix) nonroot
  have refines :=
    CCL.WindingPointExclusion.refinePastPoint_refines
      track current (decoderPole matrix) nonroot
  have outside :=
    CCL.WindingPointExclusion.refinePastPoint_excludes
      degreePositive track current (decoderPole matrix) nonroot
  let side := outsideSide outside
  refine
    { state := state
      refines := refines
      margin := normSq matrix.c * side.margin
      margin_pos := RFAP.ConstructiveFraction.mul_pos_direct
        (normSq_pos lowerLeftNonzero) side.margin_pos
      lower := ?_ }
  intro value inside
  have distance := side.margin_le_normSq_sub inside
  rw [denominator_eq_mul_sub_pole matrix lowerLeftNonzero value, normSq_mul]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distance
    (normSq_nonneg matrix.c)

/-- Exact finite outcome: either the decoder pole is a displayed root in the
current box, or a refined state has a positive uniform denominator margin. -/
inductive Decision
    (p : GaussianPolynomial) (ambient : Box)
    (current : WindingOneState p ambient) (matrix : Mat2) where
  | exact (point : Gaussian) (root : p.eval point = 0)
      (inside : current.box.Contains point)
      (denominatorZero :
        CCL.RawParser.denominator matrix point = 0)
  | separated (output : SeparationOutput p ambient current matrix)

/-- Decide the pole case using only the displayed lower-row nonzeroness and
one exact polynomial evaluation. -/
def decide
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (matrix : Mat2)
    (lowerRowNonzero : matrix.c ≠ 0 ∨ matrix.d ≠ 0) :
    Decision p ambient current matrix := by
  by_cases lowerLeftZero : matrix.c = 0
  · have lowerRightNonzero : matrix.d ≠ 0 :=
      lowerRowNonzero.resolve_left (fun nonzero => nonzero lowerLeftZero)
    exact .separated
      (separateConstant current matrix lowerLeftZero lowerRightNonzero)
  · by_cases root : p.eval (decoderPole matrix) = 0
    · by_cases inside : current.box.Contains (decoderPole matrix)
      · exact .exact (decoderPole matrix) root inside
          (denominator_at_decoderPole matrix lowerLeftZero)
      · exact .separated
          (separateOutside current matrix lowerLeftZero inside)
    · exact .separated
        (separateNonroot degreePositive track current matrix lowerLeftZero root)

end CCL.CCLDenominator
