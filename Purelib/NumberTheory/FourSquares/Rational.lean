module

-- Exposed denominator clearing retains the direct natural cast certificates.
public import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.SumsOfSquares.Four
public import Purelib.NumberTheory.FourSquares.Natural
public import Purelib.NumberTheory.SquareClass.Rational.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.NumberTheory.FourSquares.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory

open Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo
  (PositiveSquareClassRepresentative)

/-!
# Four-square representations over the canonical rational field

The retained natural algorithm represents the exact numerator-denominator
product. Dividing its same four roots by the retained denominator produces
a rational representation of the original positive square-class value.
-/

namespace Purelib.NumberTheory.FourSquares.Rational.TheoremSixtyTwo

open Purelib.Algebra

@[expose] public section

set_option genInjectivity false in
/-- Four retained natural roots represent their indexed natural value.

The original scalar, t, r and s coordinates retain their exact order. Their
square-sum equation identifies the same supplied natural index. -/
structure NaturalFourSquareRepresentation (value : Nat) where
  /-- The retained natural `scalar` square root. -/ scalar : Nat
  /-- The retained natural `t` square root. -/ t : Nat
  /-- The retained natural `r` square root. -/ r : Nat
  /-- The retained natural `s` square root. -/ s : Nat
  /-- The four retained natural squares sum to the original indexed value. -/ equation : scalar ^ 2 + t ^ 2 + r ^ 2 + s
    ^ 2 = value

constructive_injectivity NaturalFourSquareRepresentation

set_option genInjectivity false in
/-- A displayed algorithm computes four natural roots of every indexed value.

Its original dependent function retains the selected roots and their exact
square-sum equation. No witness is hidden behind an existential proposition. -/
structure NaturalFourSquareAlgorithm where
  /-- Compute four natural roots and their sum-of-squares certificate for every supplied value. -/ represent : (value :
    Nat) → NaturalFourSquareRepresentation value

constructive_injectivity NaturalFourSquareAlgorithm

end

/-- Compute the original four natural roots by finite Lagrange descent.

The retained natural representation supplies each output coordinate directly.
Its original square-sum certificate is retained at the same natural index. -/
@[expose] public def lagrangeAlgorithm : NaturalFourSquareAlgorithm where
  represent value := by
    let output := FourSquares.Natural.naturalRepresentation value
    exact
      { scalar := output.first
        t := output.second
        r := output.third
        s := output.fourth
        equation := output.equation }

/-- Represent the retained natural numerator-denominator product.

The supplied algorithm receives that exact product once and returns its
original four roots and indexed equation. Neither coordinate is reconstructed. -/
@[expose] public def naturalRepresentation (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    NaturalFourSquareRepresentation (target.numerator * target.denominator) :=
  algorithm.represent (target.numerator * target.denominator)

/-- Divide the original four natural roots by the retained rational denominator.

The natural square-sum certificate represents the same numerator-denominator
product. The nonzero retained denominator clears that equation to the exact
original positive rational square-class value. -/
@[expose] public def rationalRepresentation (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    Algebra.Field.SumsOfSquares.Four.FourSquareRepresentation target.representative.value := by
  let output := naturalRepresentation algorithm target
  let denominator : Fraction.Rational := target.denominator
  refine
    { scalar := (output.scalar : Fraction.Rational) / denominator
      t := (output.t : Fraction.Rational) / denominator
      r := (output.r : Fraction.Rational) / denominator
      s := (output.s : Fraction.Rational) / denominator
      equation := ?_ }
  have outputEquation := congrArg (fun value : Nat => (value : Fraction.Rational))
    output.equation
  have outputEquationCast :
      (output.scalar : Fraction.Rational) ^ 2 + (output.t : Fraction.Rational) ^ 2 +
          (output.r : Fraction.Rational) ^ 2 + (output.s : Fraction.Rational) ^ 2 =
        (target.numerator : Fraction.Rational) * (target.denominator : Fraction.Rational) := by
    rewrite [NatCast.add, NatCast.add, NatCast.add,
      NatCast.pow, NatCast.pow, NatCast.pow, NatCast.pow,
      NatCast.mul] at outputEquation
    exact outputEquation
  have denominatorNonzero : denominator ≠ 0 :=
    target.denominator_cast_ne_zero
  have denominatorCancel :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  change
    ((output.scalar : Fraction.Rational) / denominator) ^ 2 +
        ((output.t : Fraction.Rational) / denominator) ^ 2 +
        ((output.r : Fraction.Rational) / denominator) ^ 2 +
        ((output.s : Fraction.Rational) / denominator) ^ 2 =
      target.representative.value
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    ((output.scalar : Fraction.Rational) * denominator⁻¹) ^ 2 +
          ((output.t : Fraction.Rational) * denominator⁻¹) ^ 2 +
          ((output.r : Fraction.Rational) * denominator⁻¹) ^ 2 +
          ((output.s : Fraction.Rational) * denominator⁻¹) ^ 2 =
        ((output.scalar : Fraction.Rational) ^ 2 + (output.t : Fraction.Rational) ^ 2 +
          (output.r : Fraction.Rational) ^ 2 + (output.s : Fraction.Rational) ^ 2) *
            denominator⁻¹ ^ 2 := by ring1
    _ = ((target.numerator : Fraction.Rational) *
          (target.denominator : Fraction.Rational)) * denominator⁻¹ ^ 2 := by
      rw [outputEquationCast]
    _ = (target.numerator : Fraction.Rational) * denominator⁻¹ := by
      change
        (target.numerator : Fraction.Rational) * denominator * denominator⁻¹ ^ 2 =
          (target.numerator : Fraction.Rational) * denominator⁻¹
      calc
        (target.numerator : Fraction.Rational) * denominator * denominator⁻¹ ^ 2 =
            (target.numerator : Fraction.Rational) * denominator⁻¹ *
              (denominator * denominator⁻¹) := by ring1
        _ = (target.numerator : Fraction.Rational) * denominator⁻¹ := by
          rw [denominatorCancel, mul_one]
    _ = (target.numerator : Fraction.Rational) / (target.denominator : Fraction.Rational) := rfl
    _ = target.representative.value := target.value_eq_div.symm
end Purelib.NumberTheory.FourSquares.Rational.TheoremSixtyTwo
