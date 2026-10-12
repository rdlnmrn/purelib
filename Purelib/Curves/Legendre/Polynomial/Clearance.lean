module
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Curves.Legendre.Polynomial
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication

open Purelib

open Purelib.Curves.Legendre

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Clearance.Box.Boundary.Basic

open Purelib.Polynomial.Clearance.Box.Boundary.Translated

open Purelib.Polynomial.Dense.Gaussian.Linear.Translated

section
public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Curves.Legendre.Polynomial.Clearance

/-- Multiply the retained zero, moving and one affine-factor clearances on the same original box. -/
@[expose] def factorsClearance {lambda :
  Data.Gaussian.Basic.Canonical} {box : Rational.Box}
    (zero : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 0) box)
    (moving : Boundary.Basic.BoundaryClearance
      (translatedCoordinate lambda) box)
    (one : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 1) box) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) box :=
  BoundaryClearance.mul
    (BoundaryClearance.mul zero moving) one
end Purelib.Curves.Legendre.Polynomial.Clearance

end

section
public section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

namespace Purelib.Curves.Legendre.Polynomial.Clearance

/-- Certify the Legendre product on the zero sample box when the moving root lies strictly to its left. -/
@[expose] def lowerSampleZeroClearance (lambda :
  Data.Gaussian.Basic.Canonical)
    (movingLeft : lambda.re < (Centered.sampleBox 0).xLower) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) (Centered.sampleBox 0) :=
  factorsClearance
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (ExplicitLegendreSegment.leftClearance lambda movingLeft)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))

/-- Certify the Legendre product on the moving sample box when the fixed roots zero and one both lie strictly to its
right. -/
@[expose] def lowerSampleMovingClearance (lambda :
  Data.Gaussian.Basic.Canonical)
    (zeroRight : (Centered.sampleBox lambda).xUpper < (0 : Data.Gaussian.Basic.Canonical).re)
    (oneRight : (Centered.sampleBox lambda).xUpper < (1 : Data.Gaussian.Basic.Canonical).re) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) (Centered.sampleBox lambda) :=
  factorsClearance
    (ExplicitLegendreSegment.rightClearance 0 zeroRight)
    (ExplicitLegendreSegment.centeredClearance lambda
      (by
        change lambda.re - 1 / 16 < lambda.re
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re - 0 = lambda.re := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.re < lambda.re + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re + 0 = lambda.re :=
          (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im - 1 / 16 < lambda.im
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im - 0 = lambda.im := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im < lambda.im + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im + 0 = lambda.im :=
          (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated))
    (ExplicitLegendreSegment.rightClearance 1 oneRight)

/-- Certify the Legendre product on the one sample box when the moving root lies strictly to its left. -/
@[expose] def lowerSampleOneClearance (lambda :
  Data.Gaussian.Basic.Canonical)
    (movingLeft : lambda.re < (Centered.sampleBox 1).xLower) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) (Centered.sampleBox 1) :=
  factorsClearance
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.leftClearance lambda movingLeft)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

/-- Certify the Legendre product on the zero sample box when the moving root lies strictly to its right. -/
@[expose] def lowerRightSampleZeroClearance (lambda :
  Data.Gaussian.Basic.Canonical)
    (movingRight : (Centered.sampleBox 0).xUpper < lambda.re) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) (Centered.sampleBox 0) :=
  factorsClearance
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (ExplicitLegendreSegment.rightClearance lambda movingRight)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))

/-- Certify the Legendre product on the moving sample box when zero lies strictly to its left and one strictly to its
right. -/
@[expose] def lowerRightSampleMovingClearance (lambda :
  Data.Gaussian.Basic.Canonical)
    (zeroLeft : (0 : Data.Gaussian.Basic.Canonical).re < (Centered.sampleBox lambda).xLower)
    (oneRight : (Centered.sampleBox lambda).xUpper < (1 : Data.Gaussian.Basic.Canonical).re) :
    Boundary.Basic.BoundaryClearance (Polynomial.factorsAt lambda) (Centered.sampleBox lambda) :=
  factorsClearance
    (ExplicitLegendreSegment.leftClearance 0 zeroLeft)
    (ExplicitLegendreSegment.centeredClearance lambda
      (by
        change lambda.re - 1 / 16 < lambda.re
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re - 0 = lambda.re := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.re < lambda.re + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re + 0 = lambda.re :=
          (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im - 1 / 16 < lambda.im
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im - 0 = lambda.im := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im < lambda.im + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im + 0 = lambda.im :=
          (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated))
    (ExplicitLegendreSegment.rightClearance 1 oneRight)
end Purelib.Curves.Legendre.Polynomial.Clearance

end
