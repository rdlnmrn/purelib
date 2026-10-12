module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.Characteristic.Nonzero
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

namespace Purelib.Geometry.Polygons.Regular.Pentagon.MetricScalars

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Derive the pentagon's radius, median and diagonal scalar identities.

Assume nonzero spreads and two, the logistic spread relation, and the stated side and diagonal quadrance equations. The
conclusions express each metric using the side quadrance and spreads. -/
public theorem metricScalars (a b q r d : K)
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (betaValue : b = 4 * a * (1 - a))
    (sideValue : r = 4 * a * q)
    (diagonalValue : d = 16 * a * (1 - a) * q) :
    q = (1 - a) * r / b ∧
      q = r / (4 * a) ∧
      (2 * (q + q) - r) / 4 = (1 - a) * r / (4 * a) ∧
      d / 4 = (1 - a) * r ∧
      d = 4 * (1 - a) * r ∧
      d = b * r / a := by
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have fourANonzero : (4 : K) * a ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero fourNonzero aNonzero
  have radiusFirst : q = (1 - a) * r / b := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right bNonzero
    calc
      q * b = q * (4 * a * (1 - a)) := by rw [betaValue]
      _ = (1 - a) * r := by rw [sideValue]; ring1
      _ = ((1 - a) * r / b) * b :=
        (Algebra.Field.ExplicitField.div_mul_cancel _ bNonzero).symm
  have radiusSecond : q = r / (4 * a) := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right fourANonzero
    calc
      q * (4 * a) = r := by rw [sideValue]; ring1
      _ = (r / (4 * a)) * (4 * a) :=
        (Algebra.Field.ExplicitField.div_mul_cancel _ fourANonzero).symm
  have midpointValue :
      (2 * (q + q) - r) / 4 = (1 - a) * r / (4 * a) := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right
      (Algebra.Field.ExplicitField.mul_ne_zero fourNonzero fourANonzero)
    calc
      ((2 * (q + q) - r) / 4) * (4 * (4 * a)) =
          (((2 * (q + q) - r) / 4) * 4) * (4 * a) := by ring1
      _ = (2 * (q + q) - r) * (4 * a) := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ fourNonzero]
      _ = ((1 - a) * r) * 4 := by rw [sideValue]; ring1
      _ = (((1 - a) * r / (4 * a)) * (4 * a)) * 4 := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel _ fourANonzero]
      _ = ((1 - a) * r / (4 * a)) * (4 * (4 * a)) := by ring1
  have diagonalSide : d = 4 * (1 - a) * r := by
    rw [diagonalValue, sideValue]
    ring1
  have halfDiagonal : d / 4 = (1 - a) * r := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      (d / 4) * 4 = d :=
        Algebra.Field.ExplicitField.div_mul_cancel _ fourNonzero
      _ = 4 * (1 - a) * r := diagonalSide
      _ = ((1 - a) * r) * 4 := by ring1
  have diagonalRatio : d = b * r / a := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right aNonzero
    calc
      d * a = (4 * (1 - a) * r) * a := by rw [diagonalSide]
      _ = b * r := by rw [betaValue]; ring1
      _ = (b * r / a) * a :=
        (Algebra.Field.ExplicitField.div_mul_cancel _ aNonzero).symm
  exact ⟨radiusFirst, radiusSecond, midpointValue, halfDiagonal,
    diagonalSide, diagonalRatio⟩

end Purelib.Geometry.Polygons.Regular.Pentagon.MetricScalars

end
