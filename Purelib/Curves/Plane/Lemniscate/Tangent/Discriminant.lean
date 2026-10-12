module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.QuadraticPart
import Purelib.Curves.Plane.Lemniscate.Basic
public import Purelib.Curves.Plane.Lemniscate.Tangent.Conic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Lemniscate

open Purelib.Curves.Plane.Lemniscate.Tangent.Conic

open Purelib.Geometry

@[expose] public section

namespace Purelib.Curves.Plane.Lemniscate.Tangent.Discriminant

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The conic whose equation is `8(x²-y²)=A`. -/
def discriminantConic [Nontrivial K]
    (parameter : K) (eightNonzero : (8 : K) ≠ 0) : Conic K where
  d := 8
  e := 0
  f := -8
  a := 0
  b := 0
  c := -parameter
  quadratic_nonzero := Or.inl eightNonzero

/-- Evaluate the discriminant conic polynomial `8(x² - y²) - parameter` at the original point. -/
def discriminantValue (parameter : K) (point :
  Geometry.Plane.Point K) : K :=
  8 * (point.x ^ 2 - point.y ^ 2) - parameter

/-- The retained discriminant conic evaluates to its displayed scalar polynomial. -/
theorem discriminantConic_evaluate [Nontrivial K]
    (parameter : K) (eightNonzero : (8 : K) ≠ 0) (point : Geometry.Plane.Point K) :
    (discriminantConic parameter eightNonzero).evaluate
      point =
      discriminantValue parameter point := by
  unfold discriminantConic Conic.evaluate
    discriminantValue
  ring1

/-- The displayed tangent-conic discriminant factorization. -/
theorem tangentConic_discriminant
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : Conic.IsSecondOrderNonSingularAt parameter point) :
    (Conic.tangentConic parameter point
      secondOrderNonSingular).centerDiscriminant =
      4 * (-8 * parameter * point.x ^ 2 +
        8 * parameter * point.y ^ 2 + parameter ^ 2) := by
  unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
  unfold Conic.centerDiscriminant Conic.tangentConic Conic.tangentD Conic.tangentE
    Conic.tangentF
  calc
    (4 * point.x * point.y) ^ 2 -
          4 * (3 * point.x ^ 2 + point.y ^ 2 - parameter) *
            (point.x ^ 2 + 3 * point.y ^ 2 + parameter) =
        4 * (-8 * parameter * point.x ^ 2 +
            8 * parameter * point.y ^ 2 + parameter ^ 2) -
          12 * ((point.x ^ 2 + point.y ^ 2) ^ 2 -
            2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
    _ = 4 * (-8 * parameter * point.x ^ 2 +
        8 * parameter * point.y ^ 2 + parameter ^ 2) := by
      rw [onLemniscate]
      ring1

/-- The same calculation exposes the discriminant conic as one product. -/
theorem tangentConic_discriminant_factor
    (parameter : K) (point : Geometry.Plane.Point K)
    (onLemniscate : Lemniscate.Contains parameter point)
    (secondOrderNonSingular : Conic.IsSecondOrderNonSingularAt parameter point) :
    (Conic.tangentConic parameter point secondOrderNonSingular).centerDiscriminant =
      -(4 * parameter) * discriminantValue parameter
        point := by
  rw [tangentConic_discriminant parameter point onLemniscate]
  unfold discriminantValue
  ring1

/-- For nonzero `4A`, the tangent conic is central exactly away from the displayed discriminant conic. This theorem
records the equality criterion used in the source. -/
theorem tangentConic_discriminant_eq_zero_iff
    (parameter : K) (point : Geometry.Plane.Point K)
    (fourParameterNonzero : (4 : K) * parameter ≠ 0)
    (onLemniscate : Lemniscate.Contains parameter point)
    (secondOrderNonSingular : Conic.IsSecondOrderNonSingularAt parameter point) :
    (Conic.tangentConic parameter point secondOrderNonSingular).centerDiscriminant =
        0 ↔
      discriminantValue parameter point = 0 := by
  rw [tangentConic_discriminant_factor parameter point
    onLemniscate]
  constructor
  · intro productZero
    have negativeFactorNonzero : -((4 : K) * parameter) ≠ 0 := by
      intro negativeZero
      apply fourParameterNonzero
      calc
        (4 : K) * parameter = -(-((4 : K) * parameter)) := by ring1
        _ = 0 := by rw [negativeZero]; ring1
    exact Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left negativeFactorNonzero productZero
  · intro valueZero
    rw [valueZero]
    ring1
end Lemniscate

end Purelib.Curves.Plane.Lemniscate.Tangent.Discriminant

end
