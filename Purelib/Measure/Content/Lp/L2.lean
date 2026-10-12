module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Quadratic.Nonnegative

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Distribution.Basic
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
namespace Content

section
open Purelib.Data.Rat
/-- Integrate the square of an observable over the exact finite content.

This is the rational squared quantity; it introduces no square root or completed function space. -/
def poweredL2 {α : Type} (content : Content α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item => value item ^ 2

/-- Pointwise equal observables have equal square integrals. -/
theorem poweredL2_congr {α : Type} (content : Content α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    content.poweredL2 left = content.poweredL2 right := by
  unfold poweredL2
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun value => value ^ 2) (pointwise item))

/-- Integrate the pointwise product of the two observables over the same retained content. -/
def productIntegral {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item => left item * right item

/-- An observable's square integral is nonnegative. -/
theorem poweredL2_nonnegative {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    0 ≤ content.poweredL2 value := by
  apply content.integral_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.sq_nonneg_direct _

/-- The zero observable has zero square integral. -/
@[simp] theorem poweredL2_zero {α : Type} (content : Content α) :
    content.poweredL2 (fun _ => 0) = 0 := by
  unfold poweredL2
  calc
    content.integral (fun _ : α => (0 : Fraction.Rational) ^ 2) =
        content.integral (fun _ => (0 : Fraction.Rational)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- Scaling an observable scales its square integral by the square of the factor. -/
theorem poweredL2_scale {α : Type} (content : Content α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    content.poweredL2 (fun item => factor * value item) =
      factor ^ 2 * content.poweredL2 value := by
  unfold poweredL2
  calc
    content.integral (fun item => (factor * value item) ^ 2) =
        content.integral (fun item => factor ^ 2 * value item ^ 2) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * content.integral (fun item => value item ^ 2) :=
      content.integral_scale _ _

/-- Exchanging the two observable factors preserves their product integral. -/
theorem productIntegral_symm {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.productIntegral left right =
      content.productIntegral right left := by
  unfold productIntegral
  exact content.integral_congr _ _ (fun item => by ring1)

/-- The square integral of a linear combination expands into the two square integrals and their product integral. -/
theorem poweredL2_linearCombination {α : Type}
    (content : Content α) (leftFactor rightFactor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
    content.poweredL2 (fun item =>
        leftFactor * left item + rightFactor * right item) =
      leftFactor ^ 2 * content.poweredL2 left +
        rightFactor ^ 2 * content.poweredL2 right +
        2 * leftFactor * rightFactor *
          content.productIntegral left right := by
  unfold poweredL2 productIntegral
  calc
    content.integral (fun item =>
        (leftFactor * left item + rightFactor * right item) ^ 2) =
        content.integral (fun item =>
          leftFactor ^ 2 * left item ^ 2 +
            rightFactor ^ 2 * right item ^ 2 +
            (2 * leftFactor * rightFactor) *
              (left item * right item)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = leftFactor ^ 2 * content.integral (fun item => left item ^ 2) +
          rightFactor ^ 2 * content.integral (fun item => right item ^ 2) +
          2 * leftFactor * rightFactor *
            content.integral (fun item => left item * right item) := by
      rw [content.integral_add, content.integral_add,
        content.integral_scale, content.integral_scale,
        content.integral_scale]

end

open Purelib in
open Purelib.Data.Rat in
/-- The square of the product integral is bounded by the product of the two square integrals.

The finite rational proof uses nonnegativity of every scalar linear-combination square integral, retaining the original
weighted content. -/
theorem productIntegral_sq_le_poweredL2_mul {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.productIntegral left right ^ 2 ≤
      content.poweredL2 left * content.poweredL2 right := by
  apply Data.Rat.quadratic_cauchy_sq_le
  · exact content.poweredL2_nonnegative left
  · exact content.poweredL2_nonnegative right
  · intro leftFactor rightFactor
    rw [← content.poweredL2_linearCombination leftFactor rightFactor
      left right]
    exact content.poweredL2_nonnegative _

open Purelib.Data.Rat
/-- The square integral of a sum equals the two square integrals plus twice their product integral. -/
theorem poweredL2_add {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL2 (fun item => left item + right item) =
      content.poweredL2 left + content.poweredL2 right +
        2 * content.productIntegral left right := by
  have formula := content.poweredL2_linearCombination 1 1 left right
  calc
    content.poweredL2 (fun item => left item + right item) =
        content.poweredL2 (fun item =>
          1 * left item + 1 * right item) :=
      content.poweredL2_congr _ _ (fun item => by ring1)
    _ =
        1 ^ 2 * content.poweredL2 left +
          1 ^ 2 * content.poweredL2 right +
          2 * 1 * 1 * content.productIntegral left right := formula
    _ = content.poweredL2 left + content.poweredL2 right +
          2 * content.productIntegral left right := by
      ring1

/-- Nonnegative radii bounding the two square integrals give their summed radius as a square-integral bound for the sum.
-/
theorem poweredL2_add_le_radius_add_sq {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (leftRadius rightRadius : Fraction.Rational)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : content.poweredL2 left ≤ leftRadius ^ 2)
    (rightBound : content.poweredL2 right ≤ rightRadius ^ 2) :
    content.poweredL2 (fun item => left item + right item) ≤
      (leftRadius + rightRadius) ^ 2 := by
  have rightPowerNonnegative := content.poweredL2_nonnegative right
  have radiusProductNonnegative : 0 ≤ leftRadius * rightRadius :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      leftRadiusNonnegative rightRadiusNonnegative
  have productSquares := content.productIntegral_sq_le_poweredL2_mul
    left right
  have momentProductBound :
      content.poweredL2 left * content.poweredL2 right ≤
        leftRadius ^ 2 * rightRadius ^ 2 := by
    calc
      content.poweredL2 left * content.poweredL2 right ≤
          leftRadius ^ 2 * content.poweredL2 right :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          leftBound rightPowerNonnegative
      _ ≤ leftRadius ^ 2 * rightRadius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          rightBound (Fraction.Order.Arithmetic.sq_nonneg_direct leftRadius)
  have mixedSquareBound :
      content.productIntegral left right ^ 2 ≤
        (leftRadius * rightRadius) ^ 2 := by
    calc
      content.productIntegral left right ^ 2 ≤
          content.poweredL2 left * content.poweredL2 right := productSquares
      _ ≤ leftRadius ^ 2 * rightRadius ^ 2 := momentProductBound
      _ = (leftRadius * rightRadius) ^ 2 := by ring1
  have mixedBound : content.productIntegral left right ≤
      leftRadius * rightRadius :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      radiusProductNonnegative mixedSquareBound
  rw [content.poweredL2_add]
  calc
    content.poweredL2 left + content.poweredL2 right +
          2 * content.productIntegral left right ≤
        leftRadius ^ 2 + rightRadius ^ 2 +
          2 * (leftRadius * rightRadius) := by
      exact add_le_add (add_le_add leftBound rightBound)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          mixedBound (by decide))
    _ = (leftRadius + rightRadius) ^ 2 := by ring1

/-- Integrate the square of the exact pointwise difference of two observables. -/
def poweredL2Distance {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  content.poweredL2 fun item => left item - right item

/-- The squared integrated distance is nonnegative. -/
theorem poweredL2Distance_nonnegative {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    0 ≤ content.poweredL2Distance left right :=
  content.poweredL2_nonnegative _

/-- An observable's squared integrated distance from itself is zero. -/
@[simp] theorem poweredL2Distance_refl {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.poweredL2Distance value value = 0 := by
  unfold poweredL2Distance poweredL2
  calc
    content.integral (fun item => (value item - value item) ^ 2) =
        content.integral (fun _ => (0 : Fraction.Rational)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- Exchanging the two observables preserves their squared integrated distance. -/
theorem poweredL2Distance_symm {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL2Distance left right =
      content.poweredL2Distance right left := by
  unfold poweredL2Distance poweredL2
  exact content.integral_congr _ _ (fun item => by ring1)

/-- Scaling both observables scales their squared integrated distance by the square of the factor. -/
theorem poweredL2Distance_scale {α : Type}
    (content : Content α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
    content.poweredL2Distance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      factor ^ 2 * content.poweredL2Distance left right := by
  unfold poweredL2Distance
  calc
    content.poweredL2 (fun item =>
        factor * left item - factor * right item) =
        content.poweredL2 (fun item => factor * (left item - right item)) :=
      content.poweredL2_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * content.poweredL2 (fun item =>
          left item - right item) :=
      content.poweredL2_scale factor _

/-- Two nonnegative radius bounds through the same middle observable give a summed-radius squared distance bound. -/
theorem poweredL2Distance_le_radius_add_sq {α : Type}
    (content : Content α) (left middle right : α → Fraction.Rational)
    (leftRadius rightRadius : Fraction.Rational)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : content.poweredL2Distance left middle ≤ leftRadius ^ 2)
    (rightBound : content.poweredL2Distance middle right ≤ rightRadius ^ 2) :
    content.poweredL2Distance left right ≤
      (leftRadius + rightRadius) ^ 2 := by
  have bound := content.poweredL2_add_le_radius_add_sq
    (fun item => left item - middle item)
    (fun item => middle item - right item)
    leftRadius rightRadius leftRadiusNonnegative rightRadiusNonnegative
    leftBound rightBound
  calc
    content.poweredL2Distance left right =
        content.poweredL2 (fun item =>
          (left item - middle item) + (middle item - right item)) := by
      unfold poweredL2Distance
      exact content.poweredL2_congr _ _ (fun item => by ring1)
    _ ≤ (leftRadius + rightRadius) ^ 2 := bound
end Content

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

open Purelib.Data.Rat in
/-- The square integrals of a sum and difference total twice the sum of the original square integrals. -/
theorem poweredL2_add_sub {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL2 (fun item => left item + right item) +
        content.poweredL2 (fun item => left item - right item) =
      2 * (content.poweredL2 left + content.poweredL2 right) := by
  unfold poweredL2
  calc
    content.integral (fun item => (left item + right item) ^ 2) +
          content.integral (fun item => (left item - right item) ^ 2) =
        content.integral (fun item =>
          (left item + right item) ^ 2 +
            (left item - right item) ^ 2) :=
      (content.integral_add _ _).symm
    _ = content.integral (fun item =>
          2 * left item ^ 2 + 2 * right item ^ 2) := by
      exact content.integral_congr _ _ (fun item => by ring1)
    _ = 2 * (content.integral (fun item => left item ^ 2) +
          content.integral (fun item => right item ^ 2)) := by
      rw [content.integral_add, content.integral_scale,
        content.integral_scale]
      ring1

open Purelib in
open Purelib.Data.Rat in
/-- The square integral of a sum is at most twice the sum of the original square integrals. -/
theorem poweredL2_add_le_two_mul_add {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.poweredL2 (fun item => left item + right item) ≤
      2 * (content.poweredL2 left + content.poweredL2 right) := by
  unfold poweredL2
  calc
    content.integral (fun item => (left item + right item) ^ 2) ≤
        content.integral (fun item =>
          2 * (left item ^ 2 + right item ^ 2)) := by
      apply content.integral_mono
      intro atom member
      exact Data.Rat.add_sq_le_two_mul_add_sq (left atom.item) (right atom.item)
    _ = 2 * (content.integral (fun item => left item ^ 2) +
          content.integral (fun item => right item ^ 2)) := by
      rw [content.integral_scale, content.integral_add]

open Purelib.Data.Rat in
/-- Squared integrated distance is at most twice the sum of the two squared distances through the same middle
observable. -/
theorem poweredL2Distance_le_two_mul_add {α : Type}
    (content : Content α)
    (left middle right : α → Fraction.Rational) :
    content.poweredL2Distance left right ≤
      2 * (content.poweredL2Distance left middle +
        content.poweredL2Distance middle right) := by
  have bound := content.poweredL2_add_le_two_mul_add
    (fun item => left item - middle item)
    (fun item => middle item - right item)
  calc
    content.poweredL2Distance left right =
        content.poweredL2 (fun item =>
          (left item - middle item) + (middle item - right item)) := by
      unfold poweredL2Distance
      exact content.poweredL2_congr _ _ (fun item => by ring1)
    _ ≤ 2 * (content.poweredL2Distance left middle +
          content.poweredL2Distance middle right) := bound

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end

end

