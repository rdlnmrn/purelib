module

import Purelib.Data.Int.Order
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Raw rational certificate displays

A signed integer numerator and positive natural denominator retain an
unreduced rational display. Finite arithmetic preserves that display and its
positivity evidence; cross-product certificates justify canonical readback.
-/

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Ring

namespace Purelib.Data.Rat.Certificate.Raw

/-- The natural schema version of the retained raw rational certificate representation. -/
@[expose] public def schemaVersion : Nat := 1

set_option genInjectivity false in
/-- Retain an integer numerator, a natural denominator and evidence that the denominator is positive.

The display need not be reduced. Arithmetic preserves an explicit positive denominator, while equality and ordering are
checked using integer cross-products before transport to the canonical rational carrier. -/
public structure RationalData where
  /-- The retained signed integer numerator. -/ numerator : Int
  /-- The retained natural denominator. -/ denominator : Nat
  /-- Evidence that the retained natural denominator is strictly positive. -/ denominatorPositive : 0 < denominator

constructive_injectivity RationalData

/-- Read a raw positive-denominator display as the quotient of its canonical rational casts.

The retained denominator is positive, so the quotient reads the displayed
integer numerator and natural denominator into the canonical rational carrier. -/
@[expose] public def RationalData.toRational (value : RationalData) : Fraction.Rational :=
  (value.numerator : Fraction.Rational) / (value.denominator : Fraction.Rational)

/-- Negate a raw rational numerator while retaining its denominator and positivity evidence.

Only the signed numerator changes. The positive denominator and its
original proof are retained by the returned raw display. -/
@[expose] public def RationalData.neg (value : RationalData) : RationalData where
  numerator := -value.numerator
  denominator := value.denominator
  denominatorPositive := value.denominatorPositive

/-- Multiply raw rational numerators and positive denominators without normalization.

The displayed product multiplies the two original integer numerators and
natural denominators, retaining constructive positivity of the denominator product. -/
@[expose] public def RationalData.mul (left right : RationalData) : RationalData where
  numerator := left.numerator * right.numerator
  denominator := left.denominator * right.denominator
  denominatorPositive :=
    Nat.mul_pos left.denominatorPositive right.denominatorPositive

/-- Subtract raw rational displays by the cross-numerator formula over the product denominator.

The original cross-numerator formula and product denominator retain the two
supplied displays. Positivity certifies the same displayed product denominator. -/
@[expose] public def RationalData.sub (left right : RationalData) : RationalData where
  numerator :=
    left.numerator * (right.denominator : Int) -
      right.numerator * (left.denominator : Int)
  denominator := left.denominator * right.denominator
  denominatorPositive :=
    Nat.mul_pos left.denominatorPositive right.denominatorPositive

/-- Add raw rational displays by subtracting the negated right display.

Subtraction of the negated right numerator retains the original denominator
product and its evidence, yielding the sum of the two supplied displays. -/
@[expose] public def RationalData.add (left right : RationalData) : RationalData :=
  RationalData.sub left (RationalData.neg right)

/-- Compare raw rational displays by their integer cross-products.

The positive denominators permit comparison by the original signed integer
cross-products without first reducing either rational display. -/
@[expose] public def RationalData.Le (left right : RationalData) : Prop :=
  left.numerator * (right.denominator : Int) <=
    right.numerator * (left.denominator : Int)

/-- Decide the raw rational cross-product comparison by the explicit integer arithmetic.

The decision is the original integer cross-product comparison or equality.
It uses both displayed numerators and denominators directly. -/
public instance RationalData.instDecidableLe (left right : RationalData) : Decidable (RationalData.Le left right) :=
  inferInstanceAs (Decidable
    (left.numerator * (right.denominator : Int) <=
      right.numerator * (left.denominator : Int)))

/-- Compare raw rational displays for equality of their integer cross-products.

Equality of the original integer cross-products compares both unreduced
displays while retaining their separate numerators and positive denominators. -/
@[expose] public def RationalData.Eq (left right : RationalData) : Prop :=
  left.numerator * (right.denominator : Int) =
    right.numerator * (left.denominator : Int)

/-- Decide the raw rational cross-product equality by the explicit integer arithmetic.

The decision is the original integer cross-product comparison or equality.
It uses both displayed numerators and denominators directly. -/
public instance RationalData.instDecidableEq (left right : RationalData) : Decidable (RationalData.Eq left right) :=
  inferInstanceAs (Decidable
    (left.numerator * (right.denominator : Int) =
      right.numerator * (left.denominator : Int)))

/-- The stored positive denominator of a raw rational display has positive canonical rational cast.

The stored natural denominator is strictly positive. Its canonical
natural rational cast preserves that same strict comparison with zero. -/
private theorem RationalData.denominatorCastPositive (value : RationalData) :
    (0 : Fraction.Rational) < value.denominator :=
  Fraction.Cast.Order.natCast_pos_direct value.denominatorPositive

/-- Canonical rational casting preserves multiplication of natural numbers.

The original integer bridge identifies natural and integer denominator casts.
Integer multiplication readback then identifies the same canonical rational product. -/
private theorem RationalData.natCastMul (left right : Nat) :
    ((left * right : Nat) : Fraction.Rational) =
      (left : Fraction.Rational) * (right : Fraction.Rational) := by
  calc
    ((left * right : Nat) : Fraction.Rational) =
        (((left * right : Nat) : Int) : Fraction.Rational) := by
      rw [Int.cast_natCast]
    _ = (((left : Int) * (right : Int) : Int) : Fraction.Rational) := by
      rw [Int.natCast_mul]
    _ = ((left : Int) : Fraction.Rational) * ((right : Int) : Fraction.Rational) :=
      Fraction.Cast.intCast_mul_direct _ _
    _ = (left : Fraction.Rational) * (right : Fraction.Rational) := by
      rw [Int.cast_natCast, Int.cast_natCast]

/-- Reading back raw rational negation agrees with canonical negation.

The original integer negation is transported through its retained ring cast
equation, while the denominator and rational division operation are unchanged. -/
public theorem RationalData.neg_toRational (value : RationalData) :
    value.neg.toRational = -value.toRational := by
  unfold RationalData.neg RationalData.toRational
  have negationCast : ((-value.numerator : Int) : Fraction.Rational) =
      -(value.numerator : Fraction.Rational) := by
    change ((Int.neg value.numerator : Int) : Fraction.Rational) = _
    exact IntCast.neg value.numerator
  rw [negationCast]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Reading back raw rational multiplication agrees with canonical multiplication.

The product display retains both numerator and denominator products.
Their original scalar cast equations identify the canonical quotient product. -/
public theorem RationalData.mul_toRational (left right : RationalData) :
    (RationalData.mul left right).toRational =
      left.toRational * right.toRational := by
  unfold RationalData.mul RationalData.toRational
  rw [Fraction.Field.div_mul_div_direct]
  rw [Fraction.Cast.intCast_mul_direct]
  rw [RationalData.natCastMul]

/-- Reading back raw rational subtraction agrees with canonical subtraction.

The retained positive denominators justify common-denominator subtraction.
Direct integer addition and negation cast equations transport its original
cross-numerator to the same rational expression. -/
public theorem RationalData.sub_toRational (left right : RationalData) :
    (RationalData.sub left right).toRational =
      left.toRational - right.toRational := by
  unfold RationalData.sub RationalData.toRational
  change
    ((left.numerator * (right.denominator : Int) -
          right.numerator * (left.denominator : Int) : Int) : Fraction.Rational) /
        ((left.denominator * right.denominator : Nat) : Fraction.Rational) =
      (left.numerator : Fraction.Rational) / left.denominator -
        (right.numerator : Fraction.Rational) / right.denominator
  rw [Fraction.Field.div_sub_div_direct _ _ _ _
    (RationalData.denominatorCastPositive left).ne'
    (RationalData.denominatorCastPositive right).ne']
  rw [Int.sub_eq_add_neg, IntCast.add]
  have negationCast :
      ((-(right.numerator * (left.denominator : Int)) : Int) : Fraction.Rational) =
        -((right.numerator * (left.denominator : Int) : Int) : Fraction.Rational) := by
    change ((Int.neg (right.numerator * (left.denominator : Int)) : Int) :
      Fraction.Rational) = _
    exact IntCast.neg _
  rw [negationCast, ← sub_eq_add_neg]
  rw [Fraction.Cast.intCast_mul_direct,
    Fraction.Cast.intCast_mul_direct, Int.cast_natCast,
    Int.cast_natCast, RationalData.natCastMul]

/-- Reading back raw rational addition agrees with canonical addition.

The original display adds by subtracting the negated right display.
The same subtraction and negation readbacks identify canonical rational addition. -/
public theorem RationalData.add_toRational (left right : RationalData) :
    (RationalData.add left right).toRational =
      left.toRational + right.toRational := by
  rw [show RationalData.add left right = RationalData.sub left (RationalData.neg right) by rfl,
    RationalData.sub_toRational, RationalData.neg_toRational]
  ring1

/-- Positive natural denominators transport an integer cross-product comparison to the canonical rational quotients.

The two retained denominators are strictly positive. Their product permits
cancellation of the common rational factor after transporting the integer bound. -/
private theorem RationalData.divLeDivOfCrossMul
    {leftNumerator rightNumerator : Int}
    {leftDenominator rightDenominator : Nat}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross :
      leftNumerator * (rightDenominator : Int) <=
        rightNumerator * (leftDenominator : Int)) :
    (leftNumerator : Fraction.Rational) / (leftDenominator : Fraction.Rational) <=
      (rightNumerator : Fraction.Rational) / (rightDenominator : Fraction.Rational) := by
  have leftDenominatorPositive : (0 : Fraction.Rational) < leftDenominator :=
    Fraction.Cast.Order.natCast_pos_direct leftPositive
  have rightDenominatorPositive : (0 : Fraction.Rational) < rightDenominator :=
    Fraction.Cast.Order.natCast_pos_direct rightPositive
  apply Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (leftDenominator : Fraction.Rational) * rightDenominator) _
    (Order.Arithmetic.mul_pos_direct leftDenominatorPositive
      rightDenominatorPositive)
  calc
    (leftNumerator : Fraction.Rational) / (leftDenominator : Fraction.Rational) *
        ((leftDenominator : Fraction.Rational) * rightDenominator) =
      ((leftNumerator : Fraction.Rational) / leftDenominator * leftDenominator) *
        rightDenominator := by ring1
    _ = (leftNumerator : Fraction.Rational) * rightDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        leftDenominatorPositive.ne']
    _ <= (rightNumerator : Fraction.Rational) * leftDenominator := by
      have crossCast :
          ((leftNumerator * (rightDenominator : Int) : Int) : Fraction.Rational) <=
            ((rightNumerator * (leftDenominator : Int) : Int) : Fraction.Rational) :=
        (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2 cross
      simpa only [Fraction.Cast.intCast_mul_direct,
        Int.cast_natCast] using crossCast
    _ = ((rightNumerator : Fraction.Rational) / rightDenominator *
          rightDenominator) * leftDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        rightDenominatorPositive.ne']
    _ = (rightNumerator : Fraction.Rational) /
        (rightDenominator : Fraction.Rational) *
          ((leftDenominator : Fraction.Rational) * rightDenominator) := by ring1

/-- A checked raw cross-product comparison implies comparison of the rational readbacks.

The checked integer cross-product inequality uses the retained positive
denominators. It transports to the canonical quotients of those same displays. -/
public theorem RationalData.le_sound {left right : RationalData} (checked : RationalData.Le left right) :
    left.toRational <= right.toRational :=
  RationalData.divLeDivOfCrossMul left.denominatorPositive right.denominatorPositive checked

/-- Checked equality of raw cross-products implies equality of the rational readbacks.

The retained scalar equality supplies both integer comparisons by reflexivity.
Their positive denominators transport these comparisons to the original rational
readbacks, whose opposite bounds certify equality. -/
public theorem RationalData.eq_sound {left right : RationalData} (checked : RationalData.Eq left right) :
    left.toRational = right.toRational := by
  unfold RationalData.Eq at checked
  apply le_antisymm
  · exact RationalData.divLeDivOfCrossMul left.denominatorPositive
      right.denominatorPositive (checked ▸ Int.Order.le_refl _)
  · exact RationalData.divLeDivOfCrossMul right.denominatorPositive
      left.denominatorPositive (checked.symm ▸ Int.Order.le_refl _)

/-- Construct the original raw rational display with the supplied numerator, denominator and positivity witness.

The returned display retains the supplied integer numerator, natural
denominator and exactly its original positivity witness, without normalization. -/
@[expose] public def QuarticPeriodCertificates.rational (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : RationalData where
  numerator := numerator
  denominator := denominator
  denominatorPositive := positive

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem generatedCycleRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- The canonical readback of a raw denominator-one display is exactly its integer numerator cast.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem generatedCycleRational_denominator_one_eq (numerator : Int)
    (positive : 0 < 1) :
    (QuarticPeriodCertificates.rational numerator
      1 positive).toRational = (numerator : Fraction.Rational) := by
  rw [generatedCycleRational_eq]
  simp only [Nat.cast_one,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
    Fraction.Field.mul_one_direct]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem generatedABackwardRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem bBackwardGeneratedRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- The canonical readback of a raw denominator-one display is exactly its integer numerator cast.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem bBackwardGeneratedRational_denominator_one_eq
    (numerator : Int) (positive : 0 < 1) :
    (QuarticPeriodCertificates.rational numerator
      1 positive).toRational = (numerator : Fraction.Rational) := by
  rw [bBackwardGeneratedRational_eq]
  simp only [Nat.cast_one,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
    Fraction.Field.mul_one_direct]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem generatedBBackwardRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem bForwardGeneratedRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- The canonical readback of a raw denominator-one display is exactly its integer numerator cast.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem bForwardGeneratedRational_denominator_one_eq
    (numerator : Int) (positive : 0 < 1) :
    (QuarticPeriodCertificates.rational numerator
      1 positive).toRational = (numerator : Fraction.Rational) := by
  rw [bForwardGeneratedRational_eq]
  simp only [Nat.cast_one,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
    Fraction.Field.mul_one_direct]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem generatedBForwardRational_eq (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator
      denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The displayed constructor retains the original numerator, denominator and
positivity witness, so this readback equation follows by definition. -/
public theorem generatedRational_eq
    (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational
        numerator denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- The canonical readback of a raw denominator-one display is exactly its integer numerator cast.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem generatedRational_denominator_one_eq (numerator : Int)
    (positive : 0 < 1) :
    (QuarticPeriodCertificates.rational
        numerator 1 positive).toRational = (numerator : Fraction.Rational) := by
  rw [generatedRational_eq]
  simp only [Nat.cast_one,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
    Fraction.Field.mul_one_direct]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The positive-denominator constructor retains the supplied raw display.
Its canonical readback uses the same numerator and denominator casts. -/
public theorem ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryGeneratedRational_toRational
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading a raw display with natural numerator gives the quotient of the corresponding natural rational casts.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryGeneratedNaturalRational_toRational
    (numerator denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational (numerator : Int) denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rw [ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryGeneratedRational_toRational, Int.cast_natCast]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The positive-denominator constructor retains the supplied raw display.
Its canonical readback uses the same numerator and denominator casts. -/
public theorem ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryGeneratedPeriodRational_toRational
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational
      numerator denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The positive-denominator constructor retains the supplied raw display.
Its canonical readback uses the same numerator and denominator casts. -/
public theorem ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryGeneratedRational_toRational
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational numerator denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Reading a raw display with natural numerator gives the quotient of the corresponding natural rational casts.

The positive-denominator constructor retains the supplied raw display.
The original cast equation identifies its canonical denominator-one or natural readback. -/
public theorem ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryGeneratedNaturalRational_toRational
    (numerator denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational (numerator : Int) denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rw [ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryGeneratedRational_toRational, Int.cast_natCast]

/-- Reading the retained positive-denominator raw display gives the quotient of its canonical numerator and denominator
casts.

The positive-denominator constructor retains the supplied raw display.
Its canonical readback uses the same numerator and denominator casts. -/
public theorem ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryGeneratedPeriodRational_toRational
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    (QuarticPeriodCertificates.rational
      numerator denominator positive).toRational =
      (numerator : Fraction.Rational) / (denominator : Fraction.Rational) := by
  rfl

/-- Construct the original raw rational display with the supplied numerator, denominator and positivity witness.

The returned display retains the supplied integer numerator, natural
denominator and exactly its original positivity witness, without normalization. -/
@[expose] public def QuarticPreparedBankReplayDataBase.rational (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : RationalData where
  numerator := numerator
  denominator := denominator
  denominatorPositive := positive

end Purelib.Data.Rat.Certificate.Raw
