module
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Order.MinMax
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Division
import Purelib.Data.Int.Arithmetic

section
@[expose] public section

/-!
# Calculation-size bounds for canonical fractions

These bounds describe the integer and natural records actually formed by the
reduction-aware operations.  They retain the RFAP-2 discipline that a final
normalization must not hide an unnecessarily inflated intermediate product.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Components

open Purelib.Data.Nat

open Purelib.Data.Rat.Fraction

open Purelib.Data
open Purelib.Data.Rat.Fraction.Resource

/-- Reducing a fraction cannot increase its numerator magnitude.

The original gcd divides the retained numerator magnitude, so the normalized
magnitude is its natural quotient by that gcd. -/
theorem normalize_numerator_le (fraction : RawFraction) :
    (normalize fraction).num.natAbs ≤ fraction.num.natAbs := by
  change (fraction.num / (GCD.Scalar.gcd fraction.num.natAbs fraction.den : Int)).natAbs ≤ _
  rw [GCD.Scalar.gcd_eq_compute]
  let result := GCD.Extended.compute fraction.num.natAbs fraction.den
  have specification :=
    GCD.Extended.compute_spec fraction.num.natAbs fraction.den
  have divisorPositive : 0 < result.gcd :=
    GCD.Extended.compute_gcd_positive_right fraction.num.natAbs
      fraction.den_pos
  change (fraction.num / (result.gcd : Int)).natAbs ≤ fraction.num.natAbs
  rw [natAbs_ediv_of_dvd divisorPositive specification.2.1]
  exact Nat.Division.div_le_self _ _

/-- Reducing a fraction cannot increase its displayed denominator. -/
theorem normalize_denominator_le (fraction : RawFraction) :
    (normalize fraction).den ≤ fraction.den := by
  exact Nat.Division.div_le_self _ _

/-- The left reduced addition factor does not exceed its original denominator. -/
theorem Size.additionLeftQuotient_le (left right : Rational) :
    additionLeftQuotient left right ≤ left.den :=
  Nat.Division.div_le_self _ _

/-- The right reduced addition factor does not exceed its original denominator. -/
theorem Size.additionRightQuotient_le (left right : Rational) :
    additionRightQuotient left right ≤ right.den :=
  Nat.Division.div_le_self _ _

open Purelib.Data.Rat in
/-- The reduced-denominator sum display has denominator at most the product of the input denominators. -/
theorem addRaw_denominator_le (left right : Rational) :
    (addRaw left right).den ≤ left.den * right.den := by
  change additionLeftQuotient left right * right.den ≤
    left.den * right.den
  exact Nat.mul_le_mul_right right.den (Components.Size.additionLeftQuotient_le left right)

/-- The raw sum numerator is bounded by the original cross-product magnitudes.

The bound uses the actual reduced denominator quotients of both summands;
each quotient is bounded by its original denominator. -/
theorem addRaw_numerator_le (left right : Rational) :
    (addRaw left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  change
    (left.num * (additionRightQuotient left right : Int) +
      right.num * (additionLeftQuotient left right : Int)).natAbs ≤ _
  calc
    _ ≤ (left.num * (additionRightQuotient left right : Int)).natAbs +
          (right.num * (additionLeftQuotient left right : Int)).natAbs :=
      Int.Arithmetic.natAbs_add_le _ _
    _ = left.num.natAbs * additionRightQuotient left right +
        right.num.natAbs * additionLeftQuotient left right := by
      rw [Int.Arithmetic.natAbs_mul, Int.Arithmetic.natAbs_mul, Int.natAbs_natCast,
        Int.natAbs_natCast]
    _ ≤ left.num.natAbs * right.den + right.num.natAbs * left.den :=
      Nat.add_le_add
        (Nat.mul_le_mul_left left.num.natAbs
          (Components.Size.additionRightQuotient_le left right))
        (Nat.mul_le_mul_left right.num.natAbs
          (Components.Size.additionLeftQuotient_le left right))

/-- The cross-cancelled product denominator does not exceed the original product. -/
theorem mulRaw_denominator_le (left right : Rational) :
    (mulRaw left right).den ≤ left.den * right.den := by
  change
    cancelNatural left.den (multiplicationRightCommon left right) *
        cancelNatural right.den (multiplicationLeftCommon left right) ≤
      left.den * right.den
  exact Nat.mul_le_mul (Nat.Division.div_le_self _ _) (Nat.Division.div_le_self _ _)

/-- Cancelling a positive divisor cannot increase an integer magnitude.

The retained divisibility witness identifies the cancelled magnitude with its
natural quotient; the divisor must be positive. -/
theorem cancelInteger_natAbs_le (value : Int) {divisor : Nat}
    (divisorPositive : 0 < divisor) (divides : divisor ∣ value.natAbs) :
    (cancelInteger value divisor).natAbs ≤ value.natAbs := by
  change (value / (divisor : Int)).natAbs ≤ value.natAbs
  rw [natAbs_ediv_of_dvd divisorPositive divides]
  exact Nat.Division.div_le_self _ _

/-- The cross-cancelled product numerator is bounded by the original magnitudes.

Both retained gcd divisors are positive and divide their original numerator
magnitudes, so cancellation bounds each actual integer factor. -/
theorem mulRaw_numerator_le (left right : Rational) :
    (mulRaw left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs := by
  have leftSpecification :=
    GCD.Scalar.gcd_dvd left.num.natAbs right.den
  have rightSpecification :=
    GCD.Scalar.gcd_dvd right.num.natAbs left.den
  change
    (cancelInteger left.num (multiplicationLeftCommon left right) *
      cancelInteger right.num (multiplicationRightCommon left right)).natAbs ≤ _
  rw [Int.Arithmetic.natAbs_mul]
  exact Nat.mul_le_mul
    (cancelInteger_natAbs_le left.num
      (multiplicationLeftCommon_pos left right) leftSpecification.1)
    (cancelInteger_natAbs_le right.num
      (multiplicationRightCommon_pos left right) rightSpecification.1)

section
open Purelib.Data.Rat
/-- The canonical sum denominator is bounded by the product of the input denominators. -/
theorem Size.add_denominator_le (left right : Rational) :
    (left + right).den ≤ left.den * right.den := by
  change (add left right).den ≤ _
  rw [add_eq_normalize]
  exact (normalize_denominator_le (addRaw left right)).trans
    (addRaw_denominator_le left right)

/-- The canonical sum numerator magnitude is bounded by the sum of the two cross-product magnitudes. -/
theorem Size.add_numerator_le (left right : Rational) :
    (left + right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  change (add left right).num.natAbs ≤ _
  rw [add_eq_normalize]
  exact (normalize_numerator_le (addRaw left right)).trans
    (addRaw_numerator_le left right)

/-- The canonical product denominator is bounded by the product of the input denominators. -/
theorem Size.mul_denominator_le (left right : Rational) :
    (left * right).den ≤ left.den * right.den :=
  mulRaw_denominator_le left right

/-- The canonical product numerator magnitude is bounded by the product of the input numerator magnitudes. -/
theorem Size.mul_numerator_le (left right : Rational) :
    (left * right).num.natAbs ≤ left.num.natAbs * right.num.natAbs :=
  mulRaw_numerator_le left right

end

/-- Canonical negation preserves the retained denominator exactly. -/
@[simp] theorem neg_denominator (source : Rational) :
    (-source).den = source.den := rfl

/-- Canonical negation preserves the retained numerator magnitude exactly. -/
@[simp] theorem neg_numerator_natAbs (source : Rational) :
    (-source).num.natAbs = source.num.natAbs :=
  Int.natAbs_neg source.num

/-- Measure a reduced fraction by the maximum of its numerator magnitude and positive denominator.

The measure uses the stored reduced coordinates directly. It bounds both the numerator magnitude and denominator, so the
subsequent arithmetic envelopes account for both parts of the same canonical record. -/
def Size.componentMagnitude (source : Rational) : Nat :=
  max source.num.natAbs source.den

/-- The numerator magnitude does not exceed the larger displayed component. -/
theorem Size.numerator_le_componentMagnitude (source : Rational) :
    source.num.natAbs ≤ Components.Size.componentMagnitude source :=
  Nat.Order.le_max_left _ _

/-- The denominator does not exceed the larger displayed component. -/
theorem Size.denominator_le_componentMagnitude (source : Rational)
  :
    source.den ≤ Components.Size.componentMagnitude source :=
  Nat.Order.le_max_right _ _

/-- Bound addition by the larger of its cross-numerator sum and denominator product.

The numerator term is the sum of the two cross-product magnitudes, and the denominator term is the product of the
positive input denominators. Taking their maximum bounds both coordinates before any further reduction. -/
def Size.addComponentEnvelope (left right : Rational) : Nat :=
  max
    (left.num.natAbs * right.den + right.num.natAbs * left.den)
    (left.den * right.den)

/-- Bound multiplication by the larger of its numerator product and denominator product.

Take the maximum of the product of numerator magnitudes and the product of denominators. Cross-cancellation and
normalization can only lower the corresponding retained components. -/
def Size.mulComponentEnvelope (left right : Rational) : Nat :=
  max (left.num.natAbs * right.num.natAbs) (left.den * right.den)

/-- The sum component magnitude is bounded by its cross-product envelope. -/
theorem componentMagnitude_add_le (left right : Rational) :
    Components.Size.componentMagnitude (left + right) ≤ Components.Size.addComponentEnvelope left right := by
  apply Nat.Order.max_le
  · exact (Components.Size.add_numerator_le left right).trans (Nat.Order.le_max_left _ _)
  · exact (Components.Size.add_denominator_le left right).trans (Nat.Order.le_max_right _ _)

/-- The product component magnitude is bounded by its product envelope. -/
theorem componentMagnitude_mul_le (left right : Rational) :
    Components.Size.componentMagnitude (left * right) ≤ Components.Size.mulComponentEnvelope left right := by
  apply Nat.Order.max_le
  · exact (Components.Size.mul_numerator_le left right).trans (Nat.Order.le_max_left _ _)
  · exact (Components.Size.mul_denominator_le left right).trans (Nat.Order.le_max_right _ _)

/-- Negating a reduced fraction preserves its component magnitude. -/
theorem componentMagnitude_neg (source : Rational) :
    Components.Size.componentMagnitude (-source) = Components.Size.componentMagnitude source := by
  change Nat.max (-source.num).natAbs source.den = Nat.max source.num.natAbs source.den
  rw [Int.natAbs_neg]

/-- Taking a reciprocal cannot increase the largest displayed component.

A nonzero numerator swaps its magnitude with the denominator. The sign branch
preserves both magnitudes, and the zero fraction remains zero. -/
theorem Size.componentMagnitude_inv_le (source : Rational) :
    Components.Size.componentMagnitude source⁻¹ ≤ Components.Size.componentMagnitude source := by
  by_cases numeratorZero : source.num = 0
  · have sourceZero : source = 0 :=
      (eq_zero_iff_num_zero source).mpr numeratorZero
    rw [sourceZero, inv_zero]
  · by_cases numeratorPositive : 0 < source.num
    · change Nat.max (inv source).num.natAbs (inv source).den ≤
        Nat.max source.num.natAbs source.den
      unfold inv
      rw [dif_neg numeratorZero, dif_pos numeratorPositive]
      change Nat.max (source.den : Int).natAbs source.num.natAbs ≤ _
      rw [Int.natAbs_natCast, Nat.Order.max_comm]
    · change Nat.max (inv source).num.natAbs (inv source).den ≤
        Nat.max source.num.natAbs source.den
      unfold inv
      rw [dif_neg numeratorZero, dif_neg numeratorPositive]
      change Nat.max (-(source.den : Int)).natAbs source.num.natAbs ≤ _
      rw [Int.natAbs_neg, Int.natAbs_natCast, Nat.Order.max_comm]
end Purelib.Data.Rat.Fraction.Resource.Components

end

end

section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Components

open Purelib.Data
open Purelib.Data.Rat.Fraction.Resource

/-- The left addition quotient is bounded by its retained denominator. -/
theorem NormalizedFraction.additionLeftQuotient_le (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Arithmetic.additionLeftQuotient left right ≤ left.den :=
  Nat.Division.div_le_self _ _

/-- The right addition quotient is bounded by its retained denominator. -/
theorem NormalizedFraction.additionRightQuotient_le (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Arithmetic.additionRightQuotient left right ≤ right.den :=
  Nat.Division.div_le_self _ _

/-- The canonical sum denominator is bounded by the product of the input denominators. -/
theorem NormalizedFraction.add_denominator_le (left right :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.add left right).den ≤ left.den * right.den := by
  exact Components.Size.add_denominator_le left right

open Purelib.Data.Rat in
/-- The canonical sum numerator magnitude is bounded by the sum of the two cross-product magnitudes. -/
theorem NormalizedFraction.add_numerator_le (left right :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.add left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  exact Components.Size.add_numerator_le left right

/-- The canonical product denominator is bounded by the product of the input denominators. -/
theorem NormalizedFraction.mul_denominator_le (left right :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.mul left right).den ≤ left.den * right.den := by
  exact Components.Size.mul_denominator_le left right

open Purelib.Data.Rat in
/-- The canonical product numerator magnitude is bounded by the product of the input numerator magnitudes. -/
theorem NormalizedFraction.mul_numerator_le (left right :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.mul left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs := by
  exact Components.Size.mul_numerator_le left right

section
open Purelib.Data.Rat
/-- Negation does not increase the denominator of a reduced fraction. -/
theorem neg_denominator_le (source :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.neg source).den ≤ source.den := by
  exact Nat.le_refl source.den

/-- Negation does not increase the numerator magnitude of a reduced fraction. -/
theorem neg_numerator_le (source : Fraction.Basic.ReducedFraction)
  :
    (Fraction.Arithmetic.neg source).num.natAbs ≤ source.num.natAbs := by
  change (-source.num).natAbs ≤ source.num.natAbs
  rw [Int.natAbs_neg]

end

/-- The reciprocal denominator is bounded by the larger original component magnitude. -/
theorem inv_denominator_le (source :
  Fraction.Basic.ReducedFraction) :
    (Fraction.Arithmetic.inv source).den ≤ max source.num.natAbs source.den := by
  exact (Components.Size.denominator_le_componentMagnitude
      (Fraction.Arithmetic.inv source)).trans
    (Components.Size.componentMagnitude_inv_le source)

/-- The reciprocal numerator magnitude is bounded by the larger original component magnitude. -/
theorem inv_numerator_le (source : Fraction.Basic.ReducedFraction)
  :
    (Fraction.Arithmetic.inv source).num.natAbs ≤ max source.num.natAbs source.den := by
  exact (Components.Size.numerator_le_componentMagnitude
      (Fraction.Arithmetic.inv source)).trans
    (Components.Size.componentMagnitude_inv_le source)

open Purelib.Data.Rat in
/-- Measure a reduced fraction by the maximum of its numerator magnitude and positive denominator.

The measure uses the stored reduced coordinates directly. It bounds both the numerator magnitude and denominator, so the
subsequent arithmetic envelopes account for both parts of the same canonical record. -/
def NormalizedFraction.componentMagnitude (source :
  Fraction.Basic.ReducedFraction) : Nat :=
  max source.num.natAbs source.den

/-- The numerator magnitude does not exceed the larger displayed component. -/
theorem NormalizedFraction.numerator_le_componentMagnitude (source
  : Fraction.Basic.ReducedFraction) :
    source.num.natAbs ≤ Components.NormalizedFraction.componentMagnitude source :=
  Nat.Order.le_max_left _ _

/-- The denominator does not exceed the larger displayed component. -/
theorem NormalizedFraction.denominator_le_componentMagnitude
  (source : Fraction.Basic.ReducedFraction) :
    source.den ≤ Components.NormalizedFraction.componentMagnitude source :=
  Nat.Order.le_max_right _ _

/-- Bound a sum from two component-magnitude bounds by twice their product. -/
def additiveMagnitudeEnvelope (left right : Nat) : Nat :=
  left * right + left * right

/-- Bound a product from two component-magnitude bounds by their product. -/
def multiplicativeMagnitudeEnvelope (left right : Nat) : Nat :=
  left * right

section
open Purelib.Data.Rat
/-- Bound addition by the larger of its cross-numerator sum and denominator product.

The numerator term is the sum of the two cross-product magnitudes, and the denominator term is the product of the
positive input denominators. Taking their maximum bounds both coordinates before any further reduction. -/
def NormalizedFraction.addComponentEnvelope (left right :
  Fraction.Basic.ReducedFraction) : Nat :=
  max (left.num.natAbs * right.den + right.num.natAbs * left.den)
    (left.den * right.den)

/-- Bound multiplication by the larger of its numerator product and denominator product.

Take the maximum of the product of numerator magnitudes and the product of denominators. Cross-cancellation and
normalization can only lower the corresponding retained components. -/
def NormalizedFraction.mulComponentEnvelope (left right :
  Fraction.Basic.ReducedFraction) : Nat :=
  max (left.num.natAbs * right.num.natAbs) (left.den * right.den)

end

/-- The reduced sum component magnitude is bounded by its addition envelope. -/
theorem add_componentMagnitude_le (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.add left right) ≤
      Components.NormalizedFraction.addComponentEnvelope left right := by
  apply Nat.Order.max_le
  · exact (Components.NormalizedFraction.add_numerator_le left right).trans (Nat.Order.le_max_left _ _)
  · exact (Components.NormalizedFraction.add_denominator_le left right).trans (Nat.Order.le_max_right _ _)

/-- The reduced product component magnitude is bounded by its multiplication envelope. -/
theorem mul_componentMagnitude_le (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.mul left right) ≤
      Components.NormalizedFraction.mulComponentEnvelope left right := by
  apply Nat.Order.max_le
  · exact (Components.NormalizedFraction.mul_numerator_le left right).trans (Nat.Order.le_max_left _ _)
  · exact (Components.NormalizedFraction.mul_denominator_le left right).trans (Nat.Order.le_max_right _ _)

/-- The addition envelope is bounded by twice the product of input magnitudes.

Each retained numerator and denominator is bounded by its own input component
magnitude, which bounds both signed cross-product contributions. -/
theorem addComponentEnvelope_le_magnitudeEnvelope
    (left right : Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.addComponentEnvelope left right ≤
      additiveMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  apply Nat.Order.max_le
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul (Components.NormalizedFraction.numerator_le_componentMagnitude left)
        (Components.NormalizedFraction.denominator_le_componentMagnitude right)
    · calc
        right.num.natAbs * left.den ≤
            Components.NormalizedFraction.componentMagnitude right * Components.NormalizedFraction.componentMagnitude
              left :=
          Nat.mul_le_mul (Components.NormalizedFraction.numerator_le_componentMagnitude right)
            (Components.NormalizedFraction.denominator_le_componentMagnitude left)
        _ = Components.NormalizedFraction.componentMagnitude left * Components.NormalizedFraction.componentMagnitude
          right :=
          Nat.mul_comm _ _
  · have productBound := Nat.mul_le_mul
      (Components.NormalizedFraction.denominator_le_componentMagnitude left)
      (Components.NormalizedFraction.denominator_le_componentMagnitude right)
    exact productBound.trans (Nat.le_add_right _ _)

/-- The multiplication envelope is bounded by the product of input magnitudes.

The retained numerator pair and denominator pair are each bounded by the same
product of the two original component magnitudes. -/
theorem mulComponentEnvelope_le_magnitudeEnvelope
    (left right : Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.mulComponentEnvelope left right ≤
      multiplicativeMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  apply Nat.Order.max_le
  · exact Nat.mul_le_mul
      (Components.NormalizedFraction.numerator_le_componentMagnitude left)
      (Components.NormalizedFraction.numerator_le_componentMagnitude right)
  · exact Nat.mul_le_mul
      (Components.NormalizedFraction.denominator_le_componentMagnitude left)
      (Components.NormalizedFraction.denominator_le_componentMagnitude right)

/-- The canonical sum magnitude is at most twice the product of the input component magnitudes. -/
theorem componentMagnitude_add_le_magnitudeEnvelope (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.add left right) ≤
      additiveMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) :=
  (add_componentMagnitude_le left right).trans
    (addComponentEnvelope_le_magnitudeEnvelope left right)

/-- The canonical product magnitude is at most the product of the input component magnitudes. -/
theorem componentMagnitude_mul_le_magnitudeEnvelope (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.mul left right) ≤
      multiplicativeMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) :=
  (mul_componentMagnitude_le left right).trans
    (mulComponentEnvelope_le_magnitudeEnvelope left right)

/-- Negation does not increase a reduced fraction component magnitude. -/
theorem componentMagnitude_neg_le (source :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.neg source) ≤
      Components.NormalizedFraction.componentMagnitude source := by
  apply Nat.Order.max_le
  · exact (neg_numerator_le source).trans
      (Components.NormalizedFraction.numerator_le_componentMagnitude source)
  · exact (neg_denominator_le source).trans
      (Components.NormalizedFraction.denominator_le_componentMagnitude source)

/-- Reciprocation does not increase a reduced fraction component magnitude. -/
theorem NormalizedFraction.componentMagnitude_inv_le (source :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.inv source) ≤
      Components.NormalizedFraction.componentMagnitude source := by
  apply Nat.Order.max_le
  · exact inv_numerator_le source
  · exact inv_denominator_le source

section
open Purelib.Data.Rat
/-- Increasing either natural input bound increases the additive magnitude envelope. -/
theorem additiveMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    additiveMagnitudeEnvelope left right ≤
      additiveMagnitudeEnvelope leftBound rightBound := by
  exact Nat.add_le_add (Nat.mul_le_mul leftLe rightLe)
    (Nat.mul_le_mul leftLe rightLe)

/-- Increasing either natural input bound increases the multiplicative magnitude envelope. -/
theorem multiplicativeMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    multiplicativeMagnitudeEnvelope left right ≤
      multiplicativeMagnitudeEnvelope leftBound rightBound :=
  Nat.mul_le_mul leftLe rightLe

end

/-- The difference magnitude is bounded by the additive envelope of the input magnitudes. -/
theorem componentMagnitude_sub_le (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.sub left right) ≤
      additiveMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  exact (componentMagnitude_add_le_magnitudeEnvelope left (Fraction.Arithmetic.neg right)).trans
    (additiveMagnitudeEnvelope_mono (le_refl _)
      (componentMagnitude_neg_le right))

/-- The quotient magnitude is bounded by the multiplicative envelope of the input magnitudes. -/
theorem componentMagnitude_div_le (left right :
  Fraction.Basic.ReducedFraction) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Arithmetic.div left right) ≤
      multiplicativeMagnitudeEnvelope (Components.NormalizedFraction.componentMagnitude left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  exact (componentMagnitude_mul_le_magnitudeEnvelope left (Fraction.Arithmetic.inv right)).trans
    (multiplicativeMagnitudeEnvelope_mono (le_refl _)
      (Components.NormalizedFraction.componentMagnitude_inv_le right))

open Purelib.Data.Rat in
/-- The component magnitude of a natural cast is the maximum of that natural number and one. -/
@[simp] theorem componentMagnitude_ofNat (source : Nat) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Cast.ofNat source) = max source 1 := by
  rfl

/-- Increasing a natural number cannot decrease its fraction component magnitude.

The canonical natural display has numerator equal to the input and denominator
one, so its component magnitude is their natural maximum. -/
theorem componentMagnitude_natCast_mono {left right : Nat}
    (order : left ≤ right) :
    Components.NormalizedFraction.componentMagnitude (Fraction.Basic.ofRational (left : Fraction.Rational)) ≤
      Components.NormalizedFraction.componentMagnitude (Fraction.Basic.ofRational (right : Fraction.Rational)) := by
  rw [Fraction.Cast.ofRational_natCast, Fraction.Cast.ofRational_natCast,
    componentMagnitude_ofNat, componentMagnitude_ofNat]
  exact Nat.Order.max_le_max order (le_refl 1)

end Purelib.Data.Rat.Fraction.Resource.Components

end
