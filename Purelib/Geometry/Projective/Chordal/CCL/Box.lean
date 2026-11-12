module
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Box
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding.Cylinder.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Projective

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Rational.Box.Square

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Geometry.Projective.Chordal.CCL.Box

/-- Specialization of the preceding affine estimate to two supplied finite realizations of the same completed CCL block
list. -/
theorem completed_affine_normSq_sub_le
    {blocks : List Block} {left right : Data.Gaussian.Basic.Canonical} {K : Fraction.Rational}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : Realizes blocks
      (Proj.affine left))
    (rightRealizes : Realizes blocks
      (Proj.affine right))
    (leftNorm : Basic.normSq left ≤ K) (rightNorm : Basic.normSq
      right ≤ K) :
    Basic.normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Fraction.Rational) ^ blocks.length := by
  apply Affine.normSq_sub_le_of_chordalSq_le KNonnegative
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  exact Realizes.chordalSq_le_half_pow
    leftRealizes rightRealizes

/-- The same affine estimate for integral decoders which retain their explicit homogeneous rescaling at every completed
block. -/
theorem projectiveCompleted_affine_normSq_sub_le
    {blocks : List Block} {left right : Data.Gaussian.Basic.Canonical} {K : Fraction.Rational}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : ProjectiveRealizes blocks
      (Proj.affine left))
    (rightRealizes : ProjectiveRealizes blocks
      (Proj.affine right))
    (leftNorm : Basic.normSq left ≤ K) (rightNorm : Basic.normSq
      right ≤ K) :
    Basic.normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Fraction.Rational) ^ blocks.length := by
  apply Affine.normSq_sub_le_of_chordalSq_le KNonnegative
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  exact ProjectiveRealizes.chordalSq_le_half_pow
    leftRealizes rightRealizes

/-- The integral encoder's exact interface: the realized homogeneous pairs need only be explicitly equivalent to the two
affine values. -/
theorem projectiveCompleted_equivalentAffine_normSq_sub_le
    {blocks : List Block} {left right : Data.Gaussian.Basic.Canonical}
    {leftPoint rightPoint : GaussianLine} {K : Fraction.Rational}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : ProjectiveRealizes blocks
      leftPoint)
    (rightRealizes : ProjectiveRealizes blocks
      rightPoint)
    (leftEquivalent : leftPoint.Equivalent (Proj.affine left))
    (rightEquivalent : rightPoint.Equivalent (Proj.affine right))
    (leftNorm : Basic.normSq left ≤ K) (rightNorm : Basic.normSq
      right ≤ K) :
    Basic.normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Fraction.Rational) ^ blocks.length := by
  apply Affine.normSq_sub_le_of_chordalSq_le KNonnegative
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  have leftValid :=
    ProjectiveRealizes.valid leftRealizes
  have rightValid :=
    ProjectiveRealizes.valid rightRealizes
  have affineLeftValid := Proj.affine_hasNonzeroCoordinate left
  have affineRightValid := Proj.affine_hasNonzeroCoordinate right
  calc
    Basic.chordalSq (Proj.affine left) (Proj.affine right) =
        Basic.chordalSq (Proj.affine left) rightPoint :=
      (Equivalence.chordalSq_eq_of_equivalent_right rightValid affineRightValid
        rightEquivalent (Proj.affine left)).symm
    _ = Basic.chordalSq leftPoint rightPoint :=
      (Equivalence.chordalSq_eq_of_equivalent_left leftValid affineLeftValid
        leftEquivalent rightPoint).symm
    _ ≤ (1 / 2 : Fraction.Rational) ^ blocks.length :=
      ProjectiveRealizes.chordalSq_le_half_pow
        leftRealizes rightRealizes

/-- A completed-block cylinder satisfying the finite cleared accuracy test is contained in the paper's explicit rational
box about any supplied rational witness realization. -/
theorem completed_affine_epsilonBox_contains
    {blocks : List Block} {witness value : Data.Gaussian.Basic.Canonical}
    {K epsilon : Fraction.Rational} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : Realizes blocks
      (Proj.affine witness))
    (valueRealizes : Realizes blocks
      (Proj.affine value))
    (witnessNorm : Basic.normSq witness ≤ K) (valueNorm :
      Basic.normSq value ≤ K)
    (budget : Box.CompletedBoxBudget K epsilon
      ((1 / 2 : Fraction.Rational) ^ blocks.length)) :
    (Centered.epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold Centered.epsilonBox
  apply Centered.centeredBox_contains_of_normSq_sub_le
  exact (completed_affine_normSq_sub_le KNonnegative valueRealizes
    witnessRealizes valueNorm witnessNorm).trans budget

/-- Completed-block specialization using exactly the smallness inequality printed in the manuscript. -/
theorem completed_affine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Data.Gaussian.Basic.Canonical}
    {K epsilon : Fraction.Rational} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : Realizes blocks
      (Proj.affine witness))
    (valueRealizes : Realizes blocks
      (Proj.affine value))
    (witnessNorm : Basic.normSq witness ≤ K) (valueNorm :
      Basic.normSq value ≤ K)
    (paperBound : (1 / 2 : Fraction.Rational) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (Centered.epsilonBox witness epsilon epsilonPositive).Contains value := by
  exact completed_affine_epsilonBox_contains KNonnegative epsilonPositive
    witnessRealizes valueRealizes witnessNorm valueNorm
    (Box.completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- Homogeneously rescaled completed-block specialization of the same paper bound. -/
theorem projectiveCompleted_affine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Data.Gaussian.Basic.Canonical}
    {K epsilon : Fraction.Rational} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : ProjectiveRealizes blocks
      (Proj.affine witness))
    (valueRealizes : ProjectiveRealizes blocks
      (Proj.affine value))
    (witnessNorm : Basic.normSq witness ≤ K) (valueNorm :
      Basic.normSq value ≤ K)
    (paperBound : (1 / 2 : Fraction.Rational) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (Centered.epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold Centered.epsilonBox
  apply Centered.centeredBox_contains_of_normSq_sub_le
  exact (projectiveCompleted_affine_normSq_sub_le KNonnegative valueRealizes
    witnessRealizes valueNorm witnessNorm).trans
      (Box.completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- Witness-centred box theorem in the exact equivalence-bearing form returned by the integral encoder. -/
theorem
  projectiveCompleted_equivalentAffine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Data.Gaussian.Basic.Canonical}
    {witnessPoint valuePoint : GaussianLine} {K epsilon : Fraction.Rational}
    (KNonnegative : 0 ≤ K) (epsilonPositive : 0 < epsilon)
    (witnessRealizes : ProjectiveRealizes blocks
      witnessPoint)
    (valueRealizes : ProjectiveRealizes blocks
      valuePoint)
    (witnessEquivalent : witnessPoint.Equivalent (Proj.affine witness))
    (valueEquivalent : valuePoint.Equivalent (Proj.affine value))
    (witnessNorm : Basic.normSq witness ≤ K) (valueNorm :
      Basic.normSq value ≤ K)
    (paperBound : (1 / 2 : Fraction.Rational) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (Centered.epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold Centered.epsilonBox
  apply Centered.centeredBox_contains_of_normSq_sub_le
  exact (projectiveCompleted_equivalentAffine_normSq_sub_le KNonnegative
    valueRealizes witnessRealizes valueEquivalent witnessEquivalent
    valueNorm witnessNorm).trans
      (Box.completedBoxBudget_of_paper_bound KNonnegative paperBound)
end Purelib.Geometry.Projective.Chordal.CCL.Box

end
