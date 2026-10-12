module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Content.Lp.L2
public import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Root-free finite Lp bounds

Square roots of rational second moments need not be rational.  The primitive
L2 quantity here is therefore the exact powered norm `integral (f^2)`.  Its
Cauchy--Schwarz inequality is stated after squaring, and so remains wholly
rational and executable.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Take the expectation of an observable's square in the original finite distribution.

Retain the rational squared quantity without taking a square root. -/
def poweredL2 {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.poweredL2 value

/-- Expected square is nonnegative. -/
theorem poweredL2_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    0 ≤ distribution.poweredL2 value :=
  distribution.toContent.poweredL2_nonnegative value

end

/-- The zero observable has expected square zero. -/
@[simp] theorem poweredL2_zero {α : Type}
    (distribution : Distribution α) :
    distribution.poweredL2 (fun _ => 0) = 0 :=
  distribution.toContent.poweredL2_zero

open Purelib.Data.Rat
/-- Scaling an observable scales expected square by the factor's square. -/
theorem poweredL2_scale {α : Type} (distribution : Distribution α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    distribution.poweredL2 (fun item => factor * value item) =
      factor ^ 2 * distribution.poweredL2 value :=
  distribution.toContent.poweredL2_scale factor value

/-- The square of a product expectation is bounded by the product of the original square expectations. -/
theorem productExpectation_sq_le_poweredL2_mul {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.expectation (fun item => left item * right item) ^ 2 ≤
      distribution.poweredL2 left * distribution.poweredL2 right :=
  distribution.toContent.productIntegral_sq_le_poweredL2_mul left right

/-- Take the expectation of the square of the exact pointwise difference of two observables. -/
def poweredL2Distance {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.poweredL2Distance left right

/-- Expected squared distance is nonnegative. -/
theorem poweredL2Distance_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    0 ≤ distribution.poweredL2Distance left right :=
  distribution.toContent.poweredL2Distance_nonnegative left right

/-- Expected squared distance from an observable to itself vanishes. -/
@[simp] theorem poweredL2Distance_refl {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL2Distance value value = 0 :=
  distribution.toContent.poweredL2Distance_refl value

/-- Exchanging the two observables preserves expected squared distance. -/
theorem poweredL2Distance_symm {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL2Distance left right =
      distribution.poweredL2Distance right left :=
  distribution.toContent.poweredL2Distance_symm left right

/-- Scaling both observables scales expected squared distance by the factor's square. -/
theorem poweredL2Distance_scale {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
    distribution.poweredL2Distance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      factor ^ 2 * distribution.poweredL2Distance left right :=
  distribution.toContent.poweredL2Distance_scale factor left right

/-- Two nonnegative radius bounds through the same middle observable give the summed radius squared as a distance bound.
-/
theorem poweredL2Distance_le_radius_add_sq {α : Type}
    (distribution : Distribution α) (left middle right : α → Fraction.Rational)
    (leftRadius rightRadius : Fraction.Rational)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : distribution.poweredL2Distance left middle ≤
      leftRadius ^ 2)
    (rightBound : distribution.poweredL2Distance middle right ≤
      rightRadius ^ 2) :
    distribution.poweredL2Distance left right ≤
      (leftRadius + rightRadius) ^ 2 :=
  distribution.toContent.poweredL2Distance_le_radius_add_sq
    left middle right leftRadius rightRadius leftRadiusNonnegative
    rightRadiusNonnegative leftBound rightBound

end Distribution

end Purelib.Measure

end

section
section
@[expose] public section

/-!
# Root-free finite L2 geometry

The exact rational primitive is the powered quantity `∫ f²`, not a chosen
square root.  The parallelogram identity remains exact, while a direct
two-factor quasi-triangle inequality gives an unconditional rational bound.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

open Purelib.Data.Rat
/-- Expected squares of the sum and difference total twice the sum of the original expected squares. -/
theorem poweredL2_add_sub {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.poweredL2 (fun item => left item + right item) +
        distribution.poweredL2 (fun item => left item - right item) =
      2 * (distribution.poweredL2 left + distribution.poweredL2 right) :=
  distribution.toContent.poweredL2_add_sub left right

/-- Expected square of a sum is at most twice the sum of the original square expectations. -/
theorem poweredL2_add_le_two_mul_add {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL2 (fun item => left item + right item) ≤
      2 * (distribution.poweredL2 left + distribution.poweredL2 right) :=
  distribution.toContent.poweredL2_add_le_two_mul_add left right

/-- Expected squared distance is at most twice the sum of squared distances through the same middle observable. -/
theorem poweredL2Distance_le_two_mul_add {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Fraction.Rational) :
    distribution.poweredL2Distance left right ≤
      2 * (distribution.poweredL2Distance left middle +
        distribution.poweredL2Distance middle right) :=
  distribution.toContent.poweredL2Distance_le_two_mul_add
    left middle right

end Distribution

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite martingale differences

Every step of a displayed finite martingale has a rational difference whose
conditional expectation on the preceding partition is zero.  Consequently
the difference is orthogonal to every explicitly cellwise observable.  A
finite induction then gives exact second-moment and variance growth formulas.

There is no unbounded time index, limiting process, or stopping theorem here:
the expected quadratic variation below is a finite rational sum carried by
the inductive martingale itself.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Expected squared distance from zero equals the original observable's expected square. -/
theorem poweredL2Distance_zero {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.poweredL2Distance value (fun _ => 0) =
      distribution.poweredL2 value := by
  unfold poweredL2Distance poweredL2 Content.poweredL2Distance
    Content.poweredL2
  exact distribution.toContent.integral_congr _ _
    (fun item => by ring1)

/-- The retained powered-L2 quantity is the original expectation of the pointwise square. -/
theorem poweredL2_eq_expectation_sq {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL2 value =
      distribution.expectation (fun item => value item ^ 2) := rfl

end Distribution

end Purelib.Measure

end

