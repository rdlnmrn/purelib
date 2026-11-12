module

public import Purelib.Approximation.AccuracyRequest
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Difference quotients of independently observed base and slope readings

The output reading and actual increment stay fixed. Original quotient,
base-reading and slope-reading payments give the error for the new pair;
no derivative or limiting equality is assumed for either displayed slope.
-/

public section

namespace Purelib.Calculus.Jet.DifferenceQuotient

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Changing only the displayed base and slope gives the exact two-reading quotient perturbation. -/
theorem perturbation_eq (increment base output slope oldBase oldSlope : Canonical) :
    (output - base) / increment - slope =
      ((output - oldBase) / increment - oldSlope) -
        ((base - oldBase) / increment + (slope - oldSlope)) := by
  change (output - base) * increment⁻¹ - slope =
    ((output - oldBase) * increment⁻¹ - oldSlope) -
      ((base - oldBase) * increment⁻¹ + (slope - oldSlope))
  ring1

/-- Three independently paid readings give a strict requested quotient error at the actual nonzero unit increment.

The two original reading discrepancies are paid by tolerance times
increment quadrance divided by sixteen. Division pays the base term;
the unit bound pays the slope term. Two original two-leg norm estimates
and the strict original quotient payment give ten sixteenths of the target.
-/
theorem perturbation_lt (accuracy : AccuracyRequest) (increment base output slope oldBase oldSlope : Canonical)
    (nonzero : increment ≠ 0) (unit : Norm.Basic.normSq increment ≤ 1)
    (basePaid : Norm.Basic.normSq (base - oldBase) <
      (accuracy.tolerance / 16) * Norm.Basic.normSq increment)
    (slopePaid : Norm.Basic.normSq (slope - oldSlope) <
      (accuracy.tolerance / 16) * Norm.Basic.normSq increment)
    (originalPaid : Norm.Basic.normSq ((output - oldBase) / increment - oldSlope) < accuracy.tolerance / 16) :
    Norm.Basic.normSq ((output - base) / increment - slope) < accuracy.tolerance := by
  let share := accuracy.tolerance / 16
  let original := (output - oldBase) / increment - oldSlope
  let baseError := (base - oldBase) / increment
  let slopeError := slope - oldSlope
  have positive := Order.Field.div_pos_direct accuracy.positive (show (0 : Rational) < 16 by decide +kernel)
  have divided : Norm.Basic.normSq baseError < share :=
    ((Gaussian.Field.normSq_div (base - oldBase) increment nonzero).trans
      (Field.div_eq_mul_inv_direct _ _).symm).trans_lt
      ((Order.Field.div_lt_iff_pos (Norm.Basic.normSq_pos nonzero)).mpr basePaid)
  have slopeBound : Norm.Basic.normSq slopeError < share := slopePaid.trans_le
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unit positive.le).trans_eq (Field.mul_one_direct share))
  have two : (0 : Rational) < 2 := by decide +kernel
  have small := Order.Arithmetic.mul_lt_mul_of_pos_left_direct two
    (Order.Arithmetic.add_lt_add_direct originalPaid
      (Order.Arithmetic.mul_lt_mul_of_pos_left_direct two
        (Order.Arithmetic.add_lt_add_direct divided slopeBound)))
  have inner := Norm.Bounds.normSq_add_le_two baseError slopeError
  have outer := Norm.Bounds.normSq_sub_le_two original (baseError + slopeError)
  have inflated := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl (Norm.Basic.normSq original)) inner) two.le
  have actual := (congrArg Norm.Basic.normSq
    (perturbation_eq increment base output slope oldBase oldSlope)).trans_le (outer.trans inflated)
  have scalar : 2 * (share + 2 * (share + share)) = (10 / 16 : Rational) * accuracy.tolerance := by
    dsimp only [share]
    simp only [Field.div_eq_mul_inv_direct]
    ring1
  have strict := (Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (show (10 / 16 : Rational) < 1 by decide +kernel) accuracy.positive).trans_eq
      (Field.one_mul accuracy.tolerance)
  exact actual.trans_lt ((small.trans_eq scalar).trans strict)

end Purelib.Calculus.Jet.DifferenceQuotient

end
