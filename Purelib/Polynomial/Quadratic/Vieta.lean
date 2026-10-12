module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

section
public section

/-!
# Divine Proportions, Theorem 112: cyclic quadrilateral quadrea

The source obtains the quadrea equation through two diagonal quotients and a
long circumquadrance elimination.  The finite polynomial underneath is much
shorter: for any four displayed points, the difference between the requested
quadrea polynomial and zero is `-64` times the square of their circle
determinant.  Cyclicity therefore proves Theorem 112 directly, without the
source's solvability and nonzero-product assumptions.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- Two distinct roots of a monic quadratic have the prescribed average and product.

The average identity requires the retained witness that two is nonzero in the explicit coefficient field. -/
theorem cyclicQuadrea_roots_vieta
    (firstArea secondArea m p : K)
    (twoNonzero : (2 : K) ≠ 0)
    (areasDistinct : firstArea ≠ secondArea)
    (firstRoot : firstArea ^ 2 - 2 * m * firstArea + p = 0)
    (secondRoot : secondArea ^ 2 - 2 * m * secondArea + p = 0) :
    (firstArea + secondArea) / 2 = m ∧
      firstArea * secondArea = p := by
  have differenceNonzero : firstArea - secondArea ≠ 0 := by
    intro differenceZero
    apply areasDistinct
    exact Group.eq_of_sub_eq_zero differenceZero
  have factoredDifference :
      (firstArea - secondArea) *
        (firstArea + secondArea - 2 * m) = 0 := by
    calc
      (firstArea - secondArea) *
          (firstArea + secondArea - 2 * m) =
        (firstArea ^ 2 - 2 * m * firstArea + p) -
          (secondArea ^ 2 - 2 * m * secondArea + p) := by ring1
      _ = 0 := by rw [firstRoot, secondRoot]; ring1
  have sumDifferenceZero : firstArea + secondArea - 2 * m = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_left differenceNonzero factoredDifference
  have sumEquation : firstArea + secondArea = 2 * m :=
    Group.eq_of_sub_eq_zero sumDifferenceZero
  constructor
  · apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      ((firstArea + secondArea) / 2) * 2 = firstArea + secondArea :=
        ExplicitField.div_mul_cancel _ twoNonzero
      _ = 2 * m := sumEquation
      _ = m * 2 := by ring1
  · calc
      firstArea * secondArea =
          firstArea * (2 * m - firstArea) := by rw [← sumEquation]; ring1
      _ = p - (firstArea ^ 2 - 2 * m * firstArea + p) := by ring1
      _ = p := by rw [firstRoot]; ring1

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

end
