module
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Geometry.Rational.Box.Square.Centered

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

/-!
# Box bounds for affine chordal quadrance

The denominator-cleared rational budget transports a displayed chordal bound
into the original witness-centred box. The same retained box also bounds the
chordal quadrance of any two contained affine points and relates its squared
diagonal to the exact opposite-corner weight.
-/

namespace Purelib.Geometry.Projective.Chordal.Box

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Projective
open Purelib.Geometry.Projective.Chordal
open Purelib.Geometry.Projective.Line
open Purelib.Geometry.Rational.Box.Square

public section

/-- The denominator-cleared accuracy test used by the executable boxed-name constructor. -/
@[expose] public def CompletedBoxBudget (K epsilon Q : Fraction.Rational) : Prop :=
  (1 + K) ^ 2 * Q ≤ (epsilon / 4) ^ 2

/-- Decide the cleared box-accuracy budget by exact rational comparison. -/
instance completedBoxBudgetDecidable (K epsilon Q : Fraction.Rational) :
    Decidable (Purelib.Geometry.Projective.Chordal.Box.CompletedBoxBudget K epsilon Q) := by
  unfold Purelib.Geometry.Projective.Chordal.Box.CompletedBoxBudget
  infer_instance

/-- The paper's displayed smallness hypothesis implies the executable denominator-cleared budget. -/
theorem completedBoxBudget_of_paper_bound
    {K epsilon Q : Fraction.Rational} (KNonnegative : 0 ≤ K)
    (paperBound : Q ≤ epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    Box.CompletedBoxBudget K epsilon Q := by
  let scale := (1 + K) ^ 2
  have onePlusPositive : (0 : Fraction.Rational) < 1 + K :=
    add_pos_of_pos_of_nonneg (by decide) KNonnegative
  have scalePositive : 0 < scale :=
    Fraction.Order.Arithmetic.pow_pos_direct onePlusPositive 2
  have denominatorPositive : (0 : Fraction.Rational) < 16 * scale :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) scalePositive
  have cancelScale :
      scale * (epsilon ^ 2 / (16 * scale)) = epsilon ^ 2 / 16 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      (scale * (epsilon ^ 2 / (16 * scale))) * (16 * scale) =
          scale * ((epsilon ^ 2 / (16 * scale)) * (16 * scale)) := by ring1
      _ = scale * epsilon ^ 2 := by
        exact congrArg (fun value => scale * value)
          (Fraction.Field.div_mul_cancel_of_ne _ _
            denominatorPositive.ne')
      _ = epsilon ^ 2 * scale := Fraction.Field.mul_comm _ _
      _ = ((epsilon ^ 2 / 16) * 16) * scale := by
        exact congrArg (fun value => value * scale)
          (Fraction.Field.div_mul_cancel_of_ne _ _
            (show (16 : Fraction.Rational) ≠ 0 by decide)).symm
      _ = (epsilon ^ 2 / 16) * (16 * scale) := by ring1
  unfold Box.CompletedBoxBudget
  change scale * Q ≤ (epsilon / 4) ^ 2
  calc
    scale * Q ≤ scale * (epsilon ^ 2 / (16 * scale)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        paperBound scalePositive.le
    _ = epsilon ^ 2 / 16 := cancelScale
    _ = (epsilon / 4) ^ 2 := (Purelib.Data.Rat.Bounds.Quarter.quarter_square epsilon).symm

/-- Direct finite form of Proposition 7.25: a pairwise chordal certificate, a common affine norm bound, and the paper's
displayed smallness inequality place the supplied value in the explicit witness-centred box. -/
theorem epsilonBox_contains_of_chordalSq_le
    {witness value : Data.Gaussian.Basic.Canonical} {K Q epsilon : Fraction.Rational}
    (KNonnegative : 0 ≤ K) (QNonnegative : 0 ≤ Q)
    (epsilonPositive : 0 < epsilon)
    (witnessNorm : Data.Gaussian.Norm.Basic.normSq witness ≤ K) (valueNorm :
      Data.Gaussian.Norm.Basic.normSq value ≤ K)
    (chordalBound : Chordal.Basic.chordalSq (Proj.affine value)
      (Proj.affine witness) ≤ Q)
    (paperBound : Q ≤ epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (Centered.epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold Centered.epsilonBox
  apply Centered.centeredBox_contains_of_normSq_sub_le
  exact (Affine.normSq_sub_le_of_chordalSq_le KNonnegative QNonnegative
    valueNorm witnessNorm chordalBound).trans
      (Geometry.Projective.Chordal.Box.completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- Every two affine points in one rational box are projectively at most the box's squared diagonal apart. Thus
winding-box refinement and projective cylinder refinement can be compared in the same `chi^2` metric. -/
theorem chordalSq_affine_le_box_diagonal
    {box : Rational.Box} {z w : Data.Gaussian.Basic.Canonical}
    (zInside : box.Contains z) (wInside : box.Contains w) :
    Chordal.Basic.chordalSq (Proj.affine z) (Proj.affine w) ≤ box.diagonalSq :=
  (Affine.chordalSq_affine_le_normSq z w).trans
    (box.normSq_sub_le_diagonalSq zInside wInside)

/-- Any two displayed points in one rational box are chordally within its squared diagonal. -/
theorem affineChordalSq_le_box_diagonal
    {box : Rational.Box} {z w : Data.Gaussian.Basic.Canonical}
    (zInside : box.Contains z) (wInside : box.Contains w) :
    Affine.affineChordalSq z w <= box.diagonalSq :=
  (Affine.affineChordalSq_le_normSq z w).trans
    (box.normSq_sub_le_diagonalSq zInside wInside)

/-- Exact finite conversion between Euclidean squared box diagonal and the affine chordal quadrance of the two displayed
opposite corners. -/
theorem diagonalSq_eq_cornerWeight_mul_affineChordalSq
    (box : Rational.Box) :
    box.diagonalSq =
      ((1 + Data.Gaussian.Norm.Basic.normSq box.anchor) * (1 + Data.Gaussian.Norm.Basic.normSq
        (Rational.Box.Bounds.oppositeCorner box))) *
        Affine.affineChordalSq box.anchor (Rational.Box.Bounds.oppositeCorner box) := by
  let weight :=
    (1 + Data.Gaussian.Norm.Basic.normSq box.anchor) * (1 + Data.Gaussian.Norm.Basic.normSq
      (Rational.Box.Bounds.oppositeCorner box))
  have leftPositive : (0 : Fraction.Rational) < 1 + Data.Gaussian.Norm.Basic.normSq box.anchor :=
    (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg box.anchor))
  have rightPositive : (0 : Fraction.Rational) <
      1 + Data.Gaussian.Norm.Basic.normSq (Rational.Box.Bounds.oppositeCorner box) :=
    (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg (Rational.Box.Bounds.oppositeCorner box)))
  have weightNonzero : weight ≠ 0 := ne_of_gt
    (Fraction.Order.Arithmetic.mul_pos_direct leftPositive rightPositive)
  have numerator :
      Data.Gaussian.Norm.Basic.normSq (box.anchor - Rational.Box.Bounds.oppositeCorner box) = box.diagonalSq :=
    Rational.Box.Bounds.normSq_anchor_sub_oppositeCorner box
  unfold Affine.affineChordalSq
  change box.diagonalSq = weight *
    (Data.Gaussian.Norm.Basic.normSq (box.anchor - Rational.Box.Bounds.oppositeCorner box) / weight)
  rw [numerator, Fraction.Field.mul_comm]
  exact (Fraction.Field.div_mul_cancel_of_ne
    box.diagonalSq weight weightNonzero).symm

end

end Purelib.Geometry.Projective.Chordal.Box
