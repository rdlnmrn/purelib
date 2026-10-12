module

public import Purelib.Geometry.Rational.Box.Neighborhood
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Retained parabolic samples inside proper rational boxes

A positive centred square strictly inside the original box contains an
explicit parabolic arc. Its two varying coordinates make restrictions of
nonzero Hermitian forms nonzero univariate polynomials.
-/

public section

namespace Purelib.Geometry.Rational.Box.Sample

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational

set_option genInjectivity false in
/-- Retain a positive centred square and its explicit parabolic sampling arc inside one original box.

The original centre and positive radius determine the two coordinate
polynomials. The cached square has those exact endpoints and lies strictly
inside the retained parent box.
-/
structure Parabola (outer : Box) where
  /-- The retained centre of the sampling square. -/ center : Gaussian.Basic.Canonical
  /-- The retained common positive coordinate step. -/ radius : Fraction.Rational
  /-- The actual coordinate step is positive. -/ positive : 0 < radius
  /-- The cached centred square containing the arc. -/ square : Box
  /-- The square uses this same centre, step and positivity certificate. -/ squareSpec :
    square = Box.Square.Centered.Affine.centeredSquare center radius positive.le
  /-- The sampling square lies strictly inside the original parent box. -/ nested : square.StrictInterior outer

namespace Parabola

/-- Construct the sampling arc using the original midpoint and its cached neighbourhood radius. -/
@[expose] def ofBox (outer : Box) (proper : outer.Proper) : Parabola outer := by
  let center := outer.midpoint
  have strict : outer.StrictContains center := Box.midpoint_strictContains proper
  have onePositive : (0 : Fraction.Rational) < 1 := by decide
  let radius := Box.Neighborhood.radius outer center 1
  have positive : 0 < radius := Box.Neighborhood.radius_pos strict onePositive
  let square := Box.Neighborhood.innerBox outer center strict 1 onePositive
  exact
    { center := center
      radius := radius
      positive := positive
      square := square
      squareSpec := rfl
      nested := Box.Neighborhood.innerBox_strictInterior strict onePositive }

/-- Evaluate the retained parabolic arc at one rational parameter. -/
@[expose] def point {outer : Box} (arc : Parabola outer) (parameter : Fraction.Rational) : Gaussian.Basic.Canonical :=
  ⟨arc.center.re + arc.radius * parameter, arc.center.im + arc.radius * parameter ^ 2⟩

/-- Every unit-interval arc sample lies strictly inside the original retained parent box. -/
theorem point_strictContains {outer : Box} (arc : Parabola outer) {parameter : Fraction.Rational}
    (nonnegative : 0 ≤ parameter) (bounded : parameter ≤ 1) : outer.StrictContains (arc.point parameter) := by
  have radialNonnegative := arc.positive.le
  have realNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct radialNonnegative nonnegative
  have imaginaryNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct radialNonnegative
    (Fraction.Order.Arithmetic.sq_nonneg_direct parameter)
  have realBound : arc.radius * parameter ≤ arc.radius := by
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded radialNonnegative).trans_eq
      (Fraction.Field.mul_one_direct _)
  have squareBound : parameter ^ 2 ≤ (1 : Fraction.Rational) :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative bounded 2).trans_eq (by decide)
  have imaginaryBound : arc.radius * parameter ^ 2 ≤ arc.radius := by
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareBound radialNonnegative).trans_eq
      (Fraction.Field.mul_one_direct _)
  have inside : arc.square.Contains (arc.point parameter) := by
    rewrite [arc.squareSpec]
    have negativeRadius : -arc.radius ≤ (0 : Fraction.Rational) :=
      (Fraction.Order.Arithmetic.neg_le_neg_direct radialNonnegative).trans_eq (by decide)
    refine ⟨?_, ?_, ?_, ?_⟩
    · change arc.center.re - arc.radius ≤ arc.center.re + arc.radius * parameter
      rewrite [show arc.center.re - arc.radius = arc.center.re + (-arc.radius) by ring1]
      exact Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (negativeRadius.trans realNonnegative)
    · exact Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) realBound
    · change arc.center.im - arc.radius ≤ arc.center.im + arc.radius * parameter ^ 2
      rewrite [show arc.center.im - arc.radius = arc.center.im + (-arc.radius) by ring1]
      exact Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (negativeRadius.trans imaginaryNonnegative)
    · exact Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) imaginaryBound
  exact ⟨arc.nested.left.trans_le inside.1, inside.2.1.trans_lt arc.nested.right,
    arc.nested.bottom.trans_le inside.2.2.1, inside.2.2.2.trans_lt arc.nested.top⟩

end Parabola

end Purelib.Geometry.Rational.Box.Sample
