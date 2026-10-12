module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Per-piece budgets pay the complete-face concatenation, the endpoint
polygon and the two-sheet reindexing before the global face sum. -/
namespace Purelib.Integration.Budget.Surface.Contact

open Purelib
open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Divide the original synchronized surface contact target by eight times the sum of the squared piece count and one.
-/
@[expose] def pieceContactTarget (genus faces pieces : Nat) (allowance : Fraction.Rational) : Fraction.Rational :=
  NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.contactTarget genus faces allowance / (8 *
    ((Budget.Aggregate.countCoordinate pieces)^2 + 1))

open Purelib.Data.Rat in
/-- The exact piece-contact denominator is positive for every retained piece count. -/
private theorem denominator_positive (pieces : Nat) : 0 < (8 : Fraction.Rational) * ((pieces : Fraction.Rational)^2 + 1)
  :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by
    calc
      0 < (1 : Fraction.Rational) := by decide
      _ = 0 + 1 := by ring1
      _ ≤ (pieces : Fraction.Rational)^2 + 1 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          (Fraction.Order.Arithmetic.sq_nonneg_direct _) 1)

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Riemann.RootContinuation
/-- A positive original allowance gives a positive retained piece-contact target. -/
theorem pieceContactTarget_positive {genus faces pieces : Nat} {allowance : Fraction.Rational} (positive : 0 <
  allowance) :
    0 < Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance := by
  unfold Budget.Surface.Contact.pieceContactTarget
  rw [Budget.Aggregate.countCoordinate_eq]
  exact Fraction.Order.Field.div_pos_direct
    (NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.contactTarget_positive positive)
    (Budget.Surface.Contact.denominator_positive pieces)

/-- The exact squared-count and single-piece contact contributions reconstruct the original surface contact target. -/
theorem pieceContactTarget_paid (genus faces pieces : Nat) (allowance : Fraction.Rational) :
    8 * ((pieces : Fraction.Rational)^2 * Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance +
      Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance) =
        NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.contactTarget genus faces allowance := by
  calc
    _ = Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance * (8 * ((pieces : Fraction.Rational)^2 +
      1)) := by
      ring1
    _ = _ := by
      unfold Budget.Surface.Contact.pieceContactTarget
      rw [Budget.Aggregate.countCoordinate_eq]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (Budget.Surface.Contact.denominator_positive pieces).ne'

end

open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Riemann.RootContinuation in
/-- The genus and coefficient-scaled piece contributions equal one quarter of the corresponding original face contact
target. -/
theorem pieceContactTarget_face (genus faces pieces : Nat) (allowance coefficientNorm : Fraction.Rational) :
    2 * (genus : Fraction.Rational)^2 * coefficientNorm^2 *
      ((pieces : Fraction.Rational)^2 * Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance +
        Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance) =
      (genus : Fraction.Rational)^2 * coefficientNorm^2 *
        NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.contactTarget genus faces allowance / 4 := by
  rw [← Budget.Surface.Contact.pieceContactTarget_paid genus faces pieces allowance]
  rw [Fraction.Field.div_eq_mul_inv_direct]
  have four : (4 : Fraction.Rational)⁻¹ * 8 = 2 := by decide
  calc
    _ = ((genus : Fraction.Rational)^2 * coefficientNorm^2 *
      ((pieces : Fraction.Rational)^2 * Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance +
        Budget.Surface.Contact.pieceContactTarget genus faces pieces allowance)) * 2 := by ring1
    _ = _ := by rw [← four]; ring1

end Purelib.Integration.Budget.Surface.Contact
