module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.ExplicitOrder.Basic
public import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field.ExplicitOrder.Basic

open Purelib.Data.Rat

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Field-specific claims between the numbered results

The paper makes several mathematical assertions in the prose surrounding
Theorems 24 and 29.  This module records them explicitly.  Ordered and
rational claims are proved directly from finite coordinates.  The assertion
that every half-spread value occurs over a finite field is computed from an
explicit finite carrier and cached square table, with no choice-derived
enumeration or witness.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

namespace Purelib.Geometry.Quadratic.Space3.Ordered.RationalFieldClaims

/-- Rational vector quadrance is a visibly nonnegative sum of three stored squares. -/
theorem vector_quadrance_nonnegative (vector :
  Coordinates3.Vector Fraction.Rational) :
    0 ≤ vector.quadrance := by
  have tNonnegative : 0 ≤ vector.t * vector.t := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.sq_nonneg_direct vector.t
  have rNonnegative : 0 ≤ vector.r * vector.r := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.sq_nonneg_direct vector.r
  have sNonnegative : 0 ≤ vector.s * vector.s := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.sq_nonneg_direct vector.s
  unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  exact add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative

end Purelib.Geometry.Quadratic.Space3.Ordered.RationalFieldClaims

end

/-! ## Ordered half-spread interval -/

section

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

namespace Purelib.Rotations.OrderedFieldClaims

/-- Use the ordered field's explicit equality decision. -/
local instance instDecidableEq_purelib : DecidableEq F :=
  OrderedExplicitField.eq_decidable

end Purelib.Rotations.OrderedFieldClaims

end

section
variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

attribute [local instance] Purelib.Rotations.OrderedFieldClaims.instDecidableEq_purelib

section

namespace Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims

/-- Every nonzero three-coordinate vector has positive sum-of-squares quadrance.

The coefficient field supplies a compatible order; positivity follows by separating the three nonnegative squares. -/
public theorem
  vectorQuadrancePositive
  (vector : Coordinates3.Vector F)
    (nonzero : vector ≠ Coordinates3.Vector.zero) : 0 < vector.quadrance := by
  by_cases tZero : vector.t = 0
  · by_cases rZero : vector.r = 0
    · by_cases sZero : vector.s = 0
      · exact False.elim (nonzero (Coordinates3.Vector.ext tZero rZero sZero))
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [tZero, rZero]
        simpa only [zero_mul, zero_add] using
          OrderedExplicitField.mul_self_pos_direct sZero
    · have rPositive := OrderedExplicitField.mul_self_pos_direct rZero
      by_cases sZero : vector.s = 0
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [tZero, sZero]
        simpa only [zero_mul, zero_add, add_zero] using rPositive
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [tZero, zero_mul, zero_add]
        exact OrderedExplicitField.add_pos_direct rPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)
  · have tPositive := OrderedExplicitField.mul_self_pos_direct tZero
    by_cases rZero : vector.r = 0
    · by_cases sZero : vector.s = 0
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [rZero, sZero]
        simpa only [zero_mul, add_zero] using tPositive
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [rZero, zero_mul, add_zero]
        exact OrderedExplicitField.add_pos_direct tPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)
    · have firstTwoPositive := OrderedExplicitField.add_pos_direct tPositive
        (OrderedExplicitField.mul_self_pos_direct rZero)
      by_cases sZero : vector.s = 0
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        rw [sZero]
        simpa only [zero_mul, add_zero] using firstTwoPositive
      · unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        exact OrderedExplicitField.add_pos_direct firstTwoPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)

end Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims

end
end

end

end

section
@[expose] public section

/-!
# Rational rotations, section 8: handedness

Handedness is stored as the determinant of the displayed frame formed by an
anchor axis, a perpendicular vector, and its rotated image.  The determinant
formula is valid over every explicit field.  Positivity is separated into a
small coherent ordered-field interface so the algebraic theorem remains
available over finite fields.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section Ordered

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

namespace Purelib.Geometry.Quadratic.Space3.Ordered

/-- Use the ordered field's explicit equality decision. -/
local instance instDecidableEq_purelib_1 : DecidableEq F :=
  OrderedExplicitField.eq_decidable

end Purelib.Geometry.Quadratic.Space3.Ordered

end Ordered

end

end

public section

section

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign

variable {F : Type*} [RayOrderedExplicitField F]

namespace Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims

/-- Scalar equality uses the decision retained by the original ordered field. -/
local instance : DecidableEq F := OrderedExplicitField.eq_decidable

/-- A null vector in a ray-ordered field is the zero vector.

The original three-coordinate quadrance is positive for every nonzero vector;
the retained positive cone excludes a positive zero.
-/
theorem only_zero_null_vector (vector : Coordinates3.Vector F)
    (null : vector.IsNull) : vector = Coordinates3.Vector.zero := by
  by_cases zero : vector = Coordinates3.Vector.zero
  · exact zero
  · have positive := vectorQuadrancePositive vector zero
    exact False.elim (RayOrderedExplicitField.positive_ne_zero_direct positive null)

/-- The spread of two non-null vectors lies in the closed unit interval.

The two disjunctions retain endpoint equality or strict positivity directly.
The upper comparison uses the supplied difference law for the same field and
order operations; no additional non-strict comparison instance is required.
-/
theorem spread_unit_interval (law : OrderDifferenceLaw F)
    (left right : Coordinates3.Vector F)
    (leftNonNull : left.quadrance ≠ 0) (rightNonNull : right.quadrance ≠ 0) :
    (Coordinates3.Vector.spread left right leftNonNull rightNonNull = 0 ∨
      0 < Coordinates3.Vector.spread left right leftNonNull rightNonNull) ∧
    (Coordinates3.Vector.spread left right leftNonNull rightNonNull = 1 ∨
      Coordinates3.Vector.spread left right leftNonNull rightNonNull < 1) := by
  have leftNonzero : left ≠ Coordinates3.Vector.zero := by
    intro zero
    exact leftNonNull (zero ▸ Coordinates3.Vector.quadrance_zero)
  have rightNonzero : right ≠ Coordinates3.Vector.zero := by
    intro zero
    exact rightNonNull (zero ▸ Coordinates3.Vector.quadrance_zero)
  have denominatorPositive := OrderedExplicitField.mul_pos_direct
    (vectorQuadrancePositive left leftNonzero) (vectorQuadrancePositive right rightNonzero)
  have inversePositive := OrderedExplicitField.inv_pos_direct denominatorPositive
  constructor
  · by_cases crossZero : Coordinates3.Vector.cross left right = Coordinates3.Vector.zero
    · left
      rw [Coordinates3.Vector.spread_eq_cross_quadrance, crossZero,
        Coordinates3.Vector.quadrance_zero, ExplicitField.zero_div]
    · right
      rw [Coordinates3.Vector.spread_eq_cross_quadrance, ExplicitField.div_eq_mul_inv]
      exact OrderedExplicitField.mul_pos_direct
        (vectorQuadrancePositive (Coordinates3.Vector.cross left right) crossZero) inversePositive
  · by_cases dotZero : left.dot right = 0
    · left
      unfold Coordinates3.Vector.spread
      rw [dotZero]
      simp only [pow_two, zero_mul, ExplicitField.zero_div, -eq_self, -iff_self]
      ring1
    · right
      apply (law.lt_one_iff _).mpr
      have difference :
          1 - Coordinates3.Vector.spread left right leftNonNull rightNonNull =
            (left.dot right) ^ 2 / (left.quadrance * right.quadrance) := by
        unfold Coordinates3.Vector.spread
        ring1
      rw [difference, ExplicitField.div_eq_mul_inv, pow_two]
      exact OrderedExplicitField.mul_pos_direct
        (OrderedExplicitField.mul_self_pos_direct dotZero) inversePositive

end Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims

end
