module

public import Mathlib.Algebra.Group.Nat.Defs

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
-- The exposed reversal certificate retains its scalar integer commutativity proof.
public import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Divisibility
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Multiplication
-- The public power statement retains ordinary natural powers with clean laws.
public import Purelib.Algebra.Semiring.Nat
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Retained Bézout certificates for natural coprimality

Each certificate stores the original two integer coefficients and their
unit linear combination of the displayed natural inputs. Divisibility
transports use those same coefficients and ordinary natural powers.
-/

namespace Purelib.Data.Nat.Coprime.Basic

open Purelib.Data Purelib.Data.Int
open Purelib.Algebra

attribute [local instance high] Semiring.Nat.commSemiring
attribute [local instance high] CommSemiring.toSemiring Semiring.toMonoid

set_option genInjectivity false in
/-- Retain integer Bézout coefficients witnessing coprimality of two naturals.

The left and right integer fields multiply the corresponding natural inputs cast to
Int. Their certified sum is one, so the coefficients remain executable data rather
than existentially selected witnesses. -/
structure CoprimeCertificate (leftInput rightInput : Nat) where
  /-- The integer coefficient of the left natural input. -/ left : Int
  /-- The integer coefficient of the right natural input. -/ right : Int
  /-- The retained integer coefficients give a linear combination equal to one. -/ identity : left * (leftInput : Int) +
    right * (rightInput : Int) = 1

constructive_injectivity CoprimeCertificate

/-- A Bézout certificate cancels its right input from a divisible product.

The retained unit linear combination supplies a divisibility witness for
the other factor whenever the left input divides that product. -/
theorem CoprimeCertificate.dvd_of_dvd_mul_right
    {leftInput rightInput value : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (dividesProduct : leftInput ∣ value * rightInput) :
    leftInput ∣ value := by
  have castDividesProduct :
      (leftInput : Int) ∣ (value : Int) * (rightInput : Int) := by
    rw [← Int.natCast_mul]
    exact Int.Divisibility.of_nat dividesProduct
  have dividesFirstTerm :
      (leftInput : Int) ∣
        ((value : Int) * certificate.left) * (leftInput : Int) :=
    ⟨(value : Int) * certificate.left, Arithmetic.mul_comm _ _⟩
  have dividesSecondTerm :
      (leftInput : Int) ∣
        certificate.right * ((value : Int) * (rightInput : Int)) :=
    Int.Divisibility.mul_left castDividesProduct certificate.right
  have dividesSum :
      (leftInput : Int) ∣
        ((value : Int) * certificate.left) * (leftInput : Int) +
          certificate.right * ((value : Int) * (rightInput : Int)) :=
    Int.Divisibility.add dividesFirstTerm dividesSecondTerm
  have sumEquals :
      ((value : Int) * certificate.left) * (leftInput : Int) +
          certificate.right * ((value : Int) * (rightInput : Int)) =
        (value : Int) := by
    calc
      ((value : Int) * certificate.left) * (leftInput : Int) +
            certificate.right * ((value : Int) * (rightInput : Int)) =
          (value : Int) *
            (certificate.left * (leftInput : Int) +
              certificate.right * (rightInput : Int)) := by
          rw [Arithmetic.mul_add]
          apply congrArg₂ (· + ·)
          · exact Arithmetic.mul_assoc _ _ _
          · calc
              certificate.right *
                    ((value : Int) * (rightInput : Int)) =
                  (certificate.right * (value : Int)) *
                    (rightInput : Int) := (Arithmetic.mul_assoc _ _ _).symm
              _ = ((value : Int) * certificate.right) *
                    (rightInput : Int) := by
                  rw [Arithmetic.mul_comm certificate.right (value : Int)]
              _ = (value : Int) *
                    (certificate.right * (rightInput : Int)) :=
                  Arithmetic.mul_assoc _ _ _
      _ = (value : Int) * 1 := by rw [certificate.identity]
      _ = (value : Int) := Arithmetic.mul_one _
  rw [sumEquals] at dividesSum
  exact Int.Divisibility.to_nat dividesSum

/-- A Bézout certificate cancels every natural power of its right input.

Repeated factor cancellation retains the original certificate for the fixed
input pair. The conclusion holds for every natural exponent, including zero. -/
theorem CoprimeCertificate.dvd_of_dvd_mul_right_pow
    {leftInput rightInput value : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) :
    ∀ exponent : Nat, leftInput ∣ value * rightInput ^ exponent →
      leftInput ∣ value
  | 0 => by
      intro divides
      rw [Nat.pow_zero, Nat.mul_one] at divides
      exact divides
  | exponent + 1 => by
      intro divides
      have grouped :
          leftInput ∣ (value * rightInput ^ exponent) * rightInput := by
        rw [Nat.pow_succ, ← Multiplication.mul_assoc] at divides
        exact divides
      have previous : leftInput ∣ value * rightInput ^ exponent :=
        certificate.dvd_of_dvd_mul_right grouped
      exact certificate.dvd_of_dvd_mul_right_pow exponent previous

/-- A displayed common natural divisor of both Bézout inputs is one.

The retained coefficients express one as a signed sum of multiples of the
inputs. A common divisor therefore divides one and is itself one. -/
theorem CoprimeCertificate.eq_one_of_dvd
    {leftInput rightInput divisor : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (dividesLeft : divisor ∣ leftInput)
    (dividesRight : divisor ∣ rightInput) : divisor = 1 := by
  have castDividesLeft : (divisor : Int) ∣ (leftInput : Int) := by
    exact Int.Divisibility.of_nat dividesLeft
  have castDividesRight : (divisor : Int) ∣ (rightInput : Int) := by
    exact Int.Divisibility.of_nat dividesRight
  have dividesFirst : (divisor : Int) ∣
      certificate.left * (leftInput : Int) :=
    Int.Divisibility.mul_left castDividesLeft certificate.left
  have dividesSecond : (divisor : Int) ∣
      certificate.right * (rightInput : Int) :=
    Int.Divisibility.mul_left castDividesRight certificate.right
  have dividesOneInteger : (divisor : Int) ∣ 1 := by
    rw [← certificate.identity]
    exact Int.Divisibility.add dividesFirst dividesSecond
  have dividesOne : divisor ∣ 1 := by
    exact Int.Divisibility.to_nat dividesOneInteger
  exact Divisibility.eq_one_of_dvd_one dividesOne

/-- Swap the inputs of a Bézout certificate and its two retained coefficients.

The same two stored integers exchange positions. Integer commutativity
transports their original unit equation to the reversed input pair. -/
@[expose] def CoprimeCertificate.symm {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) :
    CoprimeCertificate rightInput leftInput :=
  ⟨certificate.right, certificate.left, by
    rw [Arithmetic.add_comm]
    exact certificate.identity⟩

/-- A zero left input in a Bézout certificate forces its right input to be one.

The left term of the certified identity vanishes, so the natural right input divides
one. -/
theorem CoprimeCertificate.right_eq_one_of_left_eq_zero
    {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (leftZero : leftInput = 0) : rightInput = 1 := by
  have identityZero := certificate.identity
  have castLeftZero : (leftInput : Int) = 0 := congrArg Int.ofNat leftZero
  rw [castLeftZero, Int.mul_zero, Arithmetic.zero_add] at identityZero
  exact Divisibility.eq_one_of_dvd_one (Int.Divisibility.to_nat
    ⟨certificate.right, identityZero.symm.trans (Arithmetic.mul_comm _ _)⟩)

end Purelib.Data.Nat.Coprime.Basic

end
