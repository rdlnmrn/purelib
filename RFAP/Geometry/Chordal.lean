import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.Boxes

/-!
# Affine chordal quadrance over constructive Gaussian fractions

The first paper only needs the affine chart of projective chordal distance.
Keeping that formula here avoids importing the continued-logarithm project's
homogeneous-coordinate and matrix layers into RFAP.
-/

namespace RFAP.Chordal

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- Exact squared chordal quadrance between two displayed affine Gaussian
rationals.  The squared form needs no square root or completed real number. -/
def affineChordalSq (z w : Gaussian) : Coordinate :=
  normSq (z - w) / ((1 + normSq z) * (1 + normSq w))

theorem affineChordalSq_nonneg (z w : Gaussian) :
    0 <= affineChordalSq z w := by
  exact RFAP.ConstructiveFraction.div_nonneg_direct (normSq_nonneg _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (add_nonneg (by decide) (normSq_nonneg z))
      (add_nonneg (by decide) (normSq_nonneg w)))

/-- Affine squared chordal quadrance is at most ordinary displayed Gaussian
squared distance. -/
theorem affineChordalSq_le_normSq (z w : Gaussian) :
    affineChordalSq z w <= normSq (z - w) := by
  have leftOne : (1 : Coordinate) <= 1 + normSq z :=
    le_add_of_nonneg_right (normSq_nonneg z)
  have rightOne : (1 : Coordinate) <= 1 + normSq w :=
    le_add_of_nonneg_right (normSq_nonneg w)
  have denominatorOne : (1 : Coordinate) <=
      (1 + normSq z) * (1 + normSq w) := by
    calc
      1 = 1 * 1 := by ring1
      _ <= (1 + normSq z) * (1 + normSq w) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct leftOne rightOne
          (by decide) (add_nonneg (by decide) (normSq_nonneg z))
  have quotientBound :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (normSq_nonneg (z - w)) (show (0 : Coordinate) < 1 by decide)
      denominatorOne
  have divideOne : normSq (z - w) / 1 = normSq (z - w) := by
    calc
      normSq (z - w) / 1 = (normSq (z - w) / 1) * 1 :=
        (RFAP.ConstructiveFraction.mul_one_direct _).symm
      _ = normSq (z - w) :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (normSq (z - w)) 1 (show (1 : Coordinate) ≠ 0 by decide)
  exact quotientBound.trans_eq divideOne

/-- Any two displayed points in one rational box are chordally within its
squared diagonal. -/
theorem affineChordalSq_le_box_diagonal
    {box : RFAP.Boxes.Box} {z w : Gaussian}
    (zInside : box.Contains z) (wInside : box.Contains w) :
    affineChordalSq z w <= box.diagonalSq :=
  (affineChordalSq_le_normSq z w).trans
    (box.normSq_sub_le_diagonalSq zInside wInside)

/-- The displayed corner opposite the fixed lower-left box anchor. -/
def oppositeCorner (box : RFAP.Boxes.Box) : Gaussian :=
  ⟨box.xUpper, box.yUpper⟩

theorem normSq_anchor_sub_oppositeCorner
    (box : RFAP.Boxes.Box) :
    normSq (box.anchor - oppositeCorner box) = box.diagonalSq := by
  simp only [RFAP.Boxes.Box.anchor, oppositeCorner, normSq,
    sub_re, sub_im, RFAP.Boxes.Box.diagonalSq]
  ring1

/-- Exact finite conversion between Euclidean squared box diagonal and the
affine chordal quadrance of the two displayed opposite corners. -/
theorem diagonalSq_eq_cornerWeight_mul_affineChordalSq
    (box : RFAP.Boxes.Box) :
    box.diagonalSq =
      ((1 + normSq box.anchor) * (1 + normSq (oppositeCorner box))) *
        affineChordalSq box.anchor (oppositeCorner box) := by
  let weight :=
    (1 + normSq box.anchor) * (1 + normSq (oppositeCorner box))
  have leftPositive : (0 : Coordinate) < 1 + normSq box.anchor :=
    (show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right (normSq_nonneg box.anchor))
  have rightPositive : (0 : Coordinate) <
      1 + normSq (oppositeCorner box) :=
    (show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right (normSq_nonneg (oppositeCorner box)))
  have weightNonzero : weight ≠ 0 := ne_of_gt
    (RFAP.ConstructiveFraction.mul_pos_direct leftPositive rightPositive)
  have numerator :
      normSq (box.anchor - oppositeCorner box) = box.diagonalSq :=
    normSq_anchor_sub_oppositeCorner box
  unfold affineChordalSq
  change box.diagonalSq = weight *
    (normSq (box.anchor - oppositeCorner box) / weight)
  rw [numerator, RFAP.ConstructiveFraction.mul_comm]
  exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
    box.diagonalSq weight weightNonzero).symm

end RFAP.Chordal
