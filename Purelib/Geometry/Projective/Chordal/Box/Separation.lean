module
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation.Certificate
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# Separating persistent CCL events across winding regions

Finite winding boxes and finite boundary-event cylinders now shrink in the
same squared-chordal metric.  This module supplies the missing quantitative
separation bridge: a positive coordinate gap between two rational boxes gives
a positive projective gap between all of their affine points.  Consequently a
sufficiently narrow nonzero boundary-event cylinder cannot meet both boxes.

Every bound is a displayed constructive rational.  No point at infinity,
completed root, compactness argument, or selected limiting parameter occurs.
-/

namespace Purelib.Geometry.Projective.Chordal.Box.Separation

/-- Uniform upper bound for the homogeneous weight of affine points in one rational box. -/
def affineWeightUpper (box : Rational.Box) :
  Fraction.Rational := 1 + box.normSqBound

/-- The affine homogeneous-weight bound of any rational box is strictly positive. -/
theorem affineWeightUpper_pos (box :
  Rational.Box) : 0 < affineWeightUpper box :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le
    (le_add_of_nonneg_right box.normSqBound_nonneg)

/-- An affine point inside a box has homogeneous weight at most the retained box bound. -/
theorem affine_weight_le
    {box : Rational.Box} {point : Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    Proj.weight (Proj.affine point) ≤
      affineWeightUpper box := by
  simp only [Proj.weight, Proj.affine, Data.Gaussian.Norm.Basic.normSq_one,
    affineWeightUpper]
  calc
    Data.Gaussian.Norm.Basic.normSq point + 1 = 1 + Data.Gaussian.Norm.Basic.normSq point := by ring1
    _ ≤ 1 + box.normSqBound :=
      add_le_add_right (box.normSq_le_normSqBound inside) 1

/-- Projective separation obtained from a displayed positive coordinate gap. The two box-weight factors are finite
coefficient data. -/
def chordalGap
    (left right : Rational.Box) (coordinateGap : Fraction.Rational) : Fraction.Rational :=
  coordinateGap ^ 2 /
    (affineWeightUpper left *
      affineWeightUpper right)

/-- A strictly positive coordinate gap gives a strictly positive squared-chordal gap. -/
theorem chordalGap_pos
    (left right : Rational.Box) {coordinateGap : Fraction.Rational}
    (positive : 0 < coordinateGap) :
    0 < chordalGap left right coordinateGap :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
    (Fraction.Order.Arithmetic.mul_pos_direct
      (affineWeightUpper_pos left)
        (affineWeightUpper_pos right))

/-- The displayed projective gap is below the squared-chordal distance of any two box points whenever the coordinate gap
bounds their squared distance. -/
theorem chordalGap_le_affine
    {left right : Rational.Box} {coordinateGap : Fraction.Rational}
    {leftPoint rightPoint : Data.Gaussian.Basic.Canonical}
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint)
    (distanceLower : coordinateGap ^ 2 ≤
      Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint)) :
    chordalGap left right coordinateGap ≤
      Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) := by
  let actualDenominator :=
    (1 + Data.Gaussian.Norm.Basic.normSq leftPoint) * (1 + Data.Gaussian.Norm.Basic.normSq rightPoint)
  let upperDenominator := affineWeightUpper left *
    affineWeightUpper right
  have actualPositive : 0 < actualDenominator :=
    Fraction.Order.Arithmetic.mul_pos_direct
      ((show (0 : Fraction.Rational) < 1 by decide).trans_le
        (le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg leftPoint)))
      ((show (0 : Fraction.Rational) < 1 by decide).trans_le
        (le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg rightPoint)))
  have upperPositive : 0 < upperDenominator :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (affineWeightUpper_pos left)
        (affineWeightUpper_pos right)
  have actualUpper : actualDenominator ≤ upperDenominator := by
    dsimp only [actualDenominator, upperDenominator]
    have leftWeight : 1 + Data.Gaussian.Norm.Basic.normSq leftPoint ≤
      affineWeightUpper left := by
      simpa only [Proj.weight, Proj.affine,
        Data.Gaussian.Norm.Basic.normSq_one, Fraction.Field.add_comm] using
          affine_weight_le leftInside
    have rightWeight : 1 + Data.Gaussian.Norm.Basic.normSq rightPoint ≤
      affineWeightUpper right := by
      simpa only [Proj.weight, Proj.affine,
        Data.Gaussian.Norm.Basic.normSq_one, Fraction.Field.add_comm] using
          affine_weight_le rightInside
    exact Fraction.Order.Arithmetic.mul_le_mul_direct leftWeight rightWeight
      (add_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg rightPoint))
      (affineWeightUpper_pos left).le
  have numeratorNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) :=
    Data.Gaussian.Norm.Basic.normSq_nonneg _
  calc
    chordalGap left right coordinateGap =
        coordinateGap ^ 2 / upperDenominator := rfl
    _ ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) / upperDenominator := by
      apply (Fraction.Order.Field.div_le_iff_pos upperPositive).2
      have cancel : Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) / upperDenominator *
          upperDenominator = Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) :=
        Fraction.Field.div_mul_cancel_of_ne
          (Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint)) upperDenominator upperPositive.ne'
      rw [cancel]
      exact distanceLower
    _ ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) / actualDenominator :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative actualPositive actualUpper
    _ = Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) := by
      rw [Affine.chordalSq_affine]

/-- Executable positive squared-chordal gap obtained by scanning the four coordinate separations of two rational boxes.
-/
def separatedChordalGap
    {left right : Rational.Box} (separated : left.Separated right) : Fraction.Rational :=
  chordalGap left right
    (Rational.Box.separationCertificate separated).gap

/-- The executable gap of two certified separated boxes is strictly positive. -/
theorem separatedChordalGap_pos
    {left right : Rational.Box} (separated : left.Separated right) :
    0 < separatedChordalGap separated :=
  chordalGap_pos left right
    (Rational.Box.separationCertificate separated).positive

/-- The retained separation gap bounds the squared-chordal distance between any points in the two boxes. -/
theorem separatedChordalGap_le_affine
    {left right : Rational.Box} (separated : left.Separated right)
    {leftPoint rightPoint : Data.Gaussian.Basic.Canonical}
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint) :
    separatedChordalGap separated ≤
      Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) :=
  chordalGap_le_affine leftInside rightInside
    ((Rational.Box.separationCertificate separated).lower
      leftInside rightInside)

/-- Compatibility wrapper exposing the executable gap together with its positive and pointwise lower-bound certificates.
-/
theorem separated_chordalGap
    {left right : Rational.Box} (separated : left.Separated right) :
    ∃ gap : Fraction.Rational, 0 < gap ∧
      ∀ {leftPoint rightPoint : Data.Gaussian.Basic.Canonical},
        left.Contains leftPoint → right.Contains rightPoint →
          gap ≤ Chordal.Basic.chordalSq
            (Proj.affine leftPoint) (Proj.affine rightPoint) :=
  ⟨separatedChordalGap separated,
    separatedChordalGap_pos separated,
    separatedChordalGap_le_affine separated⟩
end Purelib.Geometry.Projective.Chordal.Box.Separation

end
