module
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Geometry.Rational.Box.Interior

/-- Minimum of the four displayed coordinate gaps around a strict interior point. -/
def strictCoordinateGap (box : Rational.Box) (point :
  Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  min (point.re - box.xLower)
    (min (box.xUpper - point.re)
      (min (point.im - box.yLower) (box.yUpper - point.im)))

/-- Minimum of the four rational margins from a strictly interior box to its outer box. -/
def strictBoxGap (inner outer : Rational.Box) :
  Fraction.Rational :=
  min (inner.xLower - outer.xLower)
    (min (outer.xUpper - inner.xUpper)
      (min (inner.yLower - outer.yLower)
        (outer.yUpper - inner.yUpper)))

/-- Strict containment of boxes gives a positive minimum side gap. -/
theorem strictBoxGap_pos
    {inner outer : Rational.Box} (strict : inner.StrictInterior outer) :
    0 < strictBoxGap inner outer := by
  unfold strictBoxGap
  exact Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.left)
    (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.right)
      (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.bottom)
        (Fraction.Order.Arithmetic.sub_pos_direct strict.top)))

/-- A point within the computed coordinate radius of a strictly interior box is already in the outer box. -/
theorem contains_of_within_strictBoxGap
    {inner outer : Rational.Box} {point : Data.Gaussian.Basic.Canonical}
    (near :
      inner.xLower - strictBoxGap inner outer < point.re ∧
      point.re < inner.xUpper + strictBoxGap inner outer ∧
      inner.yLower - strictBoxGap inner outer < point.im ∧
      point.im < inner.yUpper + strictBoxGap inner outer) :
    outer.Contains point := by
  let gap := strictBoxGap inner outer
  have gapLeft : gap ≤ inner.xLower - outer.xLower := by
    simpa only [gap, strictBoxGap] using
      (Fraction.Order.Basic.min_le_left (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))))
  have gapRight : gap ≤ outer.xUpper - inner.xUpper := by
    simpa only [gap, strictBoxGap] using
      (Fraction.Order.Basic.min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans (Fraction.Order.Basic.min_le_left _ _)
  have gapBottom : gap ≤ inner.yLower - outer.yLower := by
    simpa only [gap, strictBoxGap] using
      (Fraction.Order.Basic.min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans
        ((Fraction.Order.Basic.min_le_right (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))).trans (Fraction.Order.Basic.min_le_left _ _))
  have gapTop : gap ≤ outer.yUpper - inner.yUpper := by
    simpa only [gap, strictBoxGap] using
      (Fraction.Order.Basic.min_le_right (inner.xLower - outer.xLower)
        (min (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper)))).trans
        ((Fraction.Order.Basic.min_le_right (outer.xUpper - inner.xUpper)
          (min (inner.yLower - outer.yLower)
            (outer.yUpper - inner.yUpper))).trans (Fraction.Order.Basic.min_le_right _ _))
  have outerLeft : outer.xLower ≤ inner.xLower - gap := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_left_direct gapLeft inner.xLower
    have restore : inner.xLower - (inner.xLower - outer.xLower) = outer.xLower := by ring1
    rewrite [restore] at shifted
    exact shifted
  have outerRight : inner.xUpper + gap ≤ outer.xUpper := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct gapRight inner.xUpper
    have restore : (outer.xUpper - inner.xUpper) + inner.xUpper = outer.xUpper := by ring1
    have commute : gap + inner.xUpper = inner.xUpper + gap := by ring1
    rewrite [restore, commute] at shifted
    exact shifted
  have outerBottom : outer.yLower ≤ inner.yLower - gap := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_left_direct gapBottom inner.yLower
    have restore : inner.yLower - (inner.yLower - outer.yLower) = outer.yLower := by ring1
    rewrite [restore] at shifted
    exact shifted
  have outerTop : inner.yUpper + gap ≤ outer.yUpper := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct gapTop inner.yUpper
    have restore : (outer.yUpper - inner.yUpper) + inner.yUpper = outer.yUpper := by ring1
    have commute : gap + inner.yUpper = inner.yUpper + gap := by ring1
    rewrite [restore, commute] at shifted
    exact shifted
  exact
    ⟨outerLeft.trans_lt near.1 |>.le,
      near.2.1.trans_le outerRight |>.le,
      outerBottom.trans_lt near.2.2.1 |>.le,
      near.2.2.2.trans_le outerTop |>.le⟩

/-- Strict membership gives a positive minimum gap from the point to the four box sides. -/
theorem strictCoordinateGap_pos
    {box : Rational.Box} {point : Data.Gaussian.Basic.Canonical} (strict : box.StrictContains point) :
    0 < strictCoordinateGap box point := by
  unfold strictCoordinateGap
  exact Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.1)
    (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.2.1)
      (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.2.2.1)
        (Fraction.Order.Arithmetic.sub_pos_direct strict.2.2.2)))

/-- Leaving a box costs at least the square of the minimum strict coordinate gap in ordinary Gaussian quadrance. -/
theorem strictCoordinateGap_sq_le_normSq_sub_of_outside
    {box : Rational.Box} {point other : Data.Gaussian.Basic.Canonical}
    (strict : box.StrictContains point) (outside : ¬box.Contains other) :
    strictCoordinateGap box point ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (point -
      other) := by
  let gap := strictCoordinateGap box point
  have gapNonnegative : 0 ≤ gap := (strictCoordinateGap_pos strict).le
  by_cases left : box.xLower ≤ other.re
  · by_cases right : other.re ≤ box.xUpper
    · by_cases bottom : box.yLower ≤ other.im
      · by_cases top : other.im ≤ box.yUpper
        · exact (outside ⟨left, right, bottom, top⟩).elim
        · have above : box.yUpper < other.im := lt_of_not_ge top
          have gapLeEdge : gap ≤ box.yUpper - point.im := by
            exact (Fraction.Order.Basic.min_le_right _ _).trans
              ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
          have edgeLe : box.yUpper - point.im ≤ other.im - point.im :=
            Fraction.Order.Arithmetic.sub_le_sub_right_direct above.le point.im
          exact Data.Gaussian.Norm.Bounds.sq_le_normSq_sub_of_imaginary_reverse gapNonnegative
            (gapLeEdge.trans edgeLe)
      · have below : other.im < box.yLower := lt_of_not_ge bottom
        have gapLeEdge : gap ≤ point.im - box.yLower := by
          exact (Fraction.Order.Basic.min_le_right _ _).trans
            ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
        have edgeLe : point.im - box.yLower ≤ point.im - other.im :=
          Fraction.Order.Arithmetic.sub_le_sub_left_direct below.le point.im
        exact Data.Gaussian.Norm.Bounds.sq_le_normSq_sub_of_imaginary_forward gapNonnegative
          (gapLeEdge.trans edgeLe)
    · have rightOf : box.xUpper < other.re := lt_of_not_ge right
      have gapLeEdge : gap ≤ box.xUpper - point.re :=
        (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
      have edgeLe : box.xUpper - point.re ≤ other.re - point.re :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct rightOf.le point.re
      exact Data.Gaussian.Norm.Bounds.sq_le_normSq_sub_of_real_reverse gapNonnegative
        (gapLeEdge.trans edgeLe)
  · have leftOf : other.re < box.xLower := lt_of_not_ge left
    have gapLeEdge : gap ≤ point.re - box.xLower := Fraction.Order.Basic.min_le_left _ _
    have edgeLe : point.re - box.xLower ≤ point.re - other.re :=
      Fraction.Order.Arithmetic.sub_le_sub_left_direct leftOf.le point.re
    exact Data.Gaussian.Norm.Bounds.sq_le_normSq_sub_of_real_forward gapNonnegative
      (gapLeEdge.trans edgeLe)

/-- A radius fitting strictly between the point and all four box sides is at most the minimum coordinate gap. -/
private theorem radius_le_strictCoordinateGap
    {box : Rational.Box} {point : Data.Gaussian.Basic.Canonical} {radius : Fraction.Rational}
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper) :
    radius ≤ strictCoordinateGap box point := by
  have leftGap : radius < point.re - box.xLower := by
    calc
      radius = (box.xLower + radius) + -box.xLower := by ring1
      _ < point.re + -box.xLower :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct left (-box.xLower)
      _ = point.re - box.xLower := by ring1
  have rightGap : radius < box.xUpper - point.re := by
    calc
      radius = (point.re + radius) + -point.re := by ring1
      _ < box.xUpper + -point.re :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct right (-point.re)
      _ = box.xUpper - point.re := by ring1
  have bottomGap : radius < point.im - box.yLower := by
    calc
      radius = (box.yLower + radius) + -box.yLower := by ring1
      _ < point.im + -box.yLower :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct bottom (-box.yLower)
      _ = point.im - box.yLower := by ring1
  have topGap : radius < box.yUpper - point.im := by
    calc
      radius = (point.im + radius) + -point.im := by ring1
      _ < box.yUpper + -point.im :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct top (-point.im)
      _ = box.yUpper - point.im := by ring1
  unfold strictCoordinateGap
  exact le_min leftGap.le (le_min rightGap.le (le_min bottomGap.le topGap.le))

/-- The uniform four-coordinate strip supplies the same ordinary distance lower bound at every point carrying it. -/
theorem interiorStripRadius_sq_le_normSq_sub_of_outside
    {box : Rational.Box} {point other : Data.Gaussian.Basic.Canonical} {radius : Fraction.Rational}
    (positive : 0 < radius)
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper)
    (outside : ¬box.Contains other) :
    radius ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (point - other) := by
  have strict : box.StrictContains point :=
    ⟨(show box.xLower < box.xLower + radius by
        calc
          box.xLower = box.xLower + 0 := by ring1
          _ < box.xLower + radius :=
            Fraction.Order.Arithmetic.add_lt_add_left_direct positive
              box.xLower).trans left,
      (show point.re < point.re + radius by
        calc
          point.re = point.re + 0 := by ring1
          _ < point.re + radius :=
            Fraction.Order.Arithmetic.add_lt_add_left_direct positive
              point.re).trans right,
      (show box.yLower < box.yLower + radius by
        calc
          box.yLower = box.yLower + 0 := by ring1
          _ < box.yLower + radius :=
            Fraction.Order.Arithmetic.add_lt_add_left_direct positive
              box.yLower).trans bottom,
      (show point.im < point.im + radius by
        calc
          point.im = point.im + 0 := by ring1
          _ < point.im + radius :=
            Fraction.Order.Arithmetic.add_lt_add_left_direct positive
              point.im).trans top⟩
  have radiusLe := radius_le_strictCoordinateGap left right bottom top
  have squareLe := Fraction.Order.Arithmetic.pow_le_pow_direct positive.le
    radiusLe 2
  exact squareLe.trans
    (strictCoordinateGap_sq_le_normSq_sub_of_outside strict outside)
end Purelib.Geometry.Rational.Box.Interior

end

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.Geometry.Rational.Box.Interior

/-- Pure rational-box geometry used after the winding comparison. If `inner` stays more than `margin` from every side of
`outer`, and a box lying within `margin` of `sample` is not separated from `inner`, then the displayed sample lies in
`outer`. No limiting point is introduced. -/
theorem contains_sample_of_not_separated_of_protected_margin
    {outer inner nearby : Rational.Box}
    {sample : Data.Gaussian.Basic.Canonical}
    {margin : Fraction.Rational}
    (innerLeft : outer.xLower + margin < inner.xLower)
    (innerRight : inner.xUpper < outer.xUpper - margin)
    (innerBottom : outer.yLower + margin < inner.yLower)
    (innerTop : inner.yUpper < outer.yUpper - margin)
    (nearbyLeft : sample.re - margin ≤ nearby.xLower)
    (nearbyRight : nearby.xUpper ≤ sample.re + margin)
    (nearbyBottom : sample.im - margin ≤ nearby.yLower)
    (nearbyTop : nearby.yUpper ≤ sample.im + margin)
    (notSeparated : ¬nearby.Separated inner) :
    outer.Contains sample := by
  have notLeft : ¬nearby.xUpper < inner.xLower :=
    fun separated => notSeparated (Or.inl separated)
  have notRight : ¬inner.xUpper < nearby.xLower :=
    fun separated => notSeparated (Or.inr (Or.inl separated))
  have notBelow : ¬nearby.yUpper < inner.yLower :=
    fun separated => notSeparated (Or.inr (Or.inr (Or.inl separated)))
  have notAbove : ¬inner.yUpper < nearby.yLower :=
    fun separated => notSeparated (Or.inr (Or.inr (Or.inr separated)))
  have leftWithMargin : outer.xLower + margin < sample.re + margin :=
    innerLeft.trans_le ((le_of_not_gt notLeft).trans nearbyRight)
  have rightWithMargin : sample.re - margin < outer.xUpper - margin :=
    nearbyLeft.trans_lt ((le_of_not_gt notRight).trans_lt innerRight)
  have bottomWithMargin : outer.yLower + margin < sample.im + margin :=
    innerBottom.trans_le ((le_of_not_gt notBelow).trans nearbyTop)
  have topWithMargin : sample.im - margin < outer.yUpper - margin :=
    nearbyBottom.trans_lt ((le_of_not_gt notAbove).trans_lt innerTop)
  exact
    ⟨(Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
        leftWithMargin).le,
      (Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct (by
        simpa only [sub_eq_add_neg] using rightWithMargin)).le,
      (Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
        bottomWithMargin).le,
      (Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct (by
        simpa only [sub_eq_add_neg] using topWithMargin)).le⟩

end Purelib.Geometry.Rational.Box.Interior

end
