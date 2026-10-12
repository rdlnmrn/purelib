module
public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

/-!
# Coordinate certificates for separated boxes

Four ordered coordinate comparisons retain the first positive gap. Its
squared-distance certificate concerns the same original boxes and points.
-/

namespace Purelib.Geometry.Rational.Box

set_option genInjectivity false in
/-- A positive coordinate gap with a uniform squared-distance certificate.

The original two boxes index the gap and its lower bound. Every displayed
point in each box satisfies the same squared-gap comparison. -/
public structure SeparationCertificate (left right : Rational.Box) where
  /-- The displayed rational coordinate separation. -/ gap : Fraction.Rational
  /-- The retained separation gap is strictly positive. -/ positive : 0 < gap
  /-- Every pair of points in the two original boxes has squared distance at least the squared retained gap. -/ lower :
    ∀ {leftPoint rightPoint : Data.Gaussian.Basic.Canonical},
    left.Contains leftPoint → right.Contains rightPoint →
      gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint)

constructive_injectivity SeparationCertificate

/-- A nonnegative real-coordinate gap bounds squared Gaussian distance.

The supplied gap is bounded by the ordered real-coordinate difference of the
two points. Its square is therefore bounded by their complete squared distance. -/
private theorem forwardRealGapLower
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {leftPoint rightPoint : Data.Gaussian.Basic.Canonical}
    (gapLe : gap ≤ rightPoint.re - leftPoint.re) :
    gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative gapLe 2
  calc
    gap ^ 2 ≤ (rightPoint.re - leftPoint.re) ^ 2 := squares
    _ = (leftPoint.re - rightPoint.re) ^ 2 := by ring1
    _ = (leftPoint.re - rightPoint.re) ^ 2 + 0 := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) :=
      add_le_add (le_refl _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (leftPoint.im - rightPoint.im))

/-- A nonnegative imaginary-coordinate gap bounds squared Gaussian distance.

The supplied gap is bounded by the ordered imaginary-coordinate difference of
the two points. Its square is bounded by their complete squared distance. -/
private theorem forwardImaginaryGapLower
    {gap : Fraction.Rational} (gapNonnegative : 0 ≤ gap)
    {leftPoint rightPoint : Data.Gaussian.Basic.Canonical}
    (gapLe : gap ≤ rightPoint.im - leftPoint.im) :
    gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) := by
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    gapNonnegative gapLe 2
  calc
    gap ^ 2 ≤ (rightPoint.im - leftPoint.im) ^ 2 := squares
    _ = (leftPoint.im - rightPoint.im) ^ 2 := by ring1
    _ = 0 + (leftPoint.im - rightPoint.im) ^ 2 := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) :=
      add_le_add
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (leftPoint.re - rightPoint.re))
        (le_refl _)

/-- Return the first certified positive coordinate gap between two boxes.

The original ordered comparisons test left, right, below and above separation.
A successful branch retains its computed gap and uniform squared-distance
certificate; failure retains the original absent result. -/
@[expose] public def separationCertificate? (left right : Rational.Box) :
    Option (Geometry.Rational.Box.SeparationCertificate left right) := by
  if leftOf : left.xUpper < right.xLower then
    let gap := right.xLower - left.xUpper
    exact some
      { gap := gap
        positive := Fraction.Order.Arithmetic.sub_pos_direct leftOf
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ rightPoint.re - leftPoint.re :=
            Fraction.Order.Arithmetic.sub_le_sub_direct rightInside.1 leftInside.2.1
          exact Geometry.Rational.Box.forwardRealGapLower
            (Fraction.Order.Arithmetic.sub_pos_direct leftOf).le gapLe }
  else if rightOf : right.xUpper < left.xLower then
    let gap := left.xLower - right.xUpper
    exact some
      { gap := gap
        positive := Fraction.Order.Arithmetic.sub_pos_direct rightOf
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ leftPoint.re - rightPoint.re :=
            Fraction.Order.Arithmetic.sub_le_sub_direct leftInside.1 rightInside.2.1
          have reverse := Geometry.Rational.Box.forwardRealGapLower
            (Fraction.Order.Arithmetic.sub_pos_direct rightOf).le
            (leftPoint := rightPoint) (rightPoint := leftPoint) gapLe
          calc
            gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (rightPoint - leftPoint) := reverse
            _ = Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) := by
              simp only [Data.Gaussian.Norm.Basic.normSq, Purelib.Data.Gaussian.Basic.sub_re,
                Purelib.Data.Gaussian.Basic.sub_im]
              ring1 }
  else if below : left.yUpper < right.yLower then
    let gap := right.yLower - left.yUpper
    exact some
      { gap := gap
        positive := Fraction.Order.Arithmetic.sub_pos_direct below
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ rightPoint.im - leftPoint.im :=
            Fraction.Order.Arithmetic.sub_le_sub_direct rightInside.2.2.1 leftInside.2.2.2
          exact Geometry.Rational.Box.forwardImaginaryGapLower
            (Fraction.Order.Arithmetic.sub_pos_direct below).le gapLe }
  else if above : right.yUpper < left.yLower then
    let gap := left.yLower - right.yUpper
    exact some
      { gap := gap
        positive := Fraction.Order.Arithmetic.sub_pos_direct above
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ leftPoint.im - rightPoint.im :=
            Fraction.Order.Arithmetic.sub_le_sub_direct leftInside.2.2.1 rightInside.2.2.2
          have reverse := Geometry.Rational.Box.forwardImaginaryGapLower
            (Fraction.Order.Arithmetic.sub_pos_direct above).le
            (leftPoint := rightPoint) (rightPoint := leftPoint) gapLe
          calc
            gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (rightPoint - leftPoint) := reverse
            _ = Data.Gaussian.Norm.Basic.normSq (leftPoint - rightPoint) := by
              simp only [Data.Gaussian.Norm.Basic.normSq, Purelib.Data.Gaussian.Basic.sub_re,
                Purelib.Data.Gaussian.Basic.sub_im]
              ring1 }
  else
    exact none

/-- A coordinate-separation witness makes the finite gap search successful.

The original four comparisons test the same two boxes. If all four tests fail,
each alternative of the supplied separation witness is excluded directly. -/
public theorem separationCertificate?_ne_none
    {left right : Rational.Box} (separated : left.Separated right) :
    Geometry.Rational.Box.separationCertificate? left right ≠ none := by
  unfold Geometry.Rational.Box.separationCertificate?
  by_cases leftOf : left.xUpper < right.xLower
  · rewrite [dif_pos leftOf]
    exact Option.some_ne_none _
  · rewrite [dif_neg leftOf]
    by_cases rightOf : right.xUpper < left.xLower
    · rewrite [dif_pos rightOf]
      exact Option.some_ne_none _
    · rewrite [dif_neg rightOf]
      by_cases below : left.yUpper < right.yLower
      · rewrite [dif_pos below]
        exact Option.some_ne_none _
      · rewrite [dif_neg below]
        by_cases above : right.yUpper < left.yLower
        · rewrite [dif_pos above]
          exact Option.some_ne_none _
        · rcases separated with positive | positive | positive | positive
          · exact (leftOf positive).elim
          · exact (rightOf positive).elim
          · exact (below positive).elim
          · exact (above positive).elim

/-- Retain the computed separation certificate for two certified separated boxes.

The finite comparison procedure supplies the original gap and quantitative
witness. The separation proof only eliminates its impossible absent branch;
it selects no replacement gap or point. -/
@[expose] public def separationCertificate
    {left right : Rational.Box} (separated : left.Separated right) :
    Geometry.Rational.Box.SeparationCertificate left right :=
  match found : Geometry.Rational.Box.separationCertificate? left right with
  | some certificate => certificate
  | none => False.elim (Geometry.Rational.Box.separationCertificate?_ne_none separated found)

end Purelib.Geometry.Rational.Box
