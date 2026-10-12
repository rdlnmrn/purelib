module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Resource.Components
import Purelib.Data.Nat.Division
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast

open Purelib.Data.Rat

open Purelib.Algebra

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Data.Rat.Fraction.ScaledNumerator

open Purelib.Data.Nat
open Purelib.Algebra Purelib.Algebra.Ring

/-- Compute an integer numerator at a supplied natural denominator scale.

Multiply the retained reduced numerator by the natural quotient of scale by reduced denominator. The exact scaling
identity requires that denominator to divide the scale. -/
def scaledCoordinateNumerator (scale : Nat) (value : Fraction.Rational)
  : Int :=
  let reduced := Fraction.Basic.representative value
  reduced.num * (scale / reduced.den : Nat)

/-- Scaling a coordinate numerator reads back as multiplication by its natural scale.

The retained divisibility witness fixes the multiplier of the original reduced
positive denominator. Its quotient and numerator are used without renormalizing. -/
theorem scaledCoordinateNumerator_spec (scale : Nat) (value :
  Fraction.Rational)
    (divides : (Fraction.Basic.representative value).den ∣ scale) :
    (scaledCoordinateNumerator scale value : Fraction.Rational) =
      (scale : Fraction.Rational) * value := by
  let reduced := Fraction.Basic.representative value
  rcases divides with ⟨factor, scaleIdentity⟩
  have denominatorPositive := reduced.den_pos
  have recovered := Fraction.Cast.representative_mul_den value
  change value * (reduced.den : Fraction.Rational) =
    (reduced.num : Fraction.Rational) at recovered
  unfold scaledCoordinateNumerator
  rw [scaleIdentity]
  change
    ((reduced.num *
      ((reduced.den * factor) / reduced.den : Nat) : Int) : Fraction.Rational) =
      ((reduced.den * factor : Nat) : Fraction.Rational) * value
  rw [Division.mul_div_cancel_left factor denominatorPositive, IntCast.intCast_mul,
    Int.cast_natCast, NatCast.mul, ← recovered]
  ring1
end Purelib.Data.Rat.Fraction.ScaledNumerator

end

section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Data.Rat.Fraction.ScaledNumerator

open Purelib.Data.Int Purelib.Data.Nat

/-- The scaled numerator magnitude is bounded by the reduced component magnitude times the natural scale. -/
theorem scaledCoordinateNumerator_le (scale : Nat)
    (coordinate : Fraction.Rational) :
    (scaledCoordinateNumerator scale coordinate).natAbs ≤
      Fraction.Resource.Components.NormalizedFraction.componentMagnitude
          (Fraction.Basic.ofRational coordinate) * scale := by
  let reduced := Fraction.Basic.representative coordinate
  change (reduced.num * ((scale / reduced.den : Nat) : Int)).natAbs ≤ _
  rw [Arithmetic.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul
    (Fraction.Resource.Components.NormalizedFraction.numerator_le_componentMagnitude reduced)
    (Division.div_le_self scale reduced.den)
end Purelib.Data.Rat.Fraction.ScaledNumerator

end
