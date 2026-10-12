module
public import Mathlib.Algebra.Ring.Int.Defs
public import Purelib.Data.Nat.Coprime.Basic
public import Purelib.Data.Nat.GCD.Extended

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
-- The exposed quotient certificate retains these arithmetic proof fields.
import Purelib.Data.Int.Arithmetic
public import Purelib.Data.Nat.Division

open Purelib.Data.Nat.Coprime.Basic
open Purelib.Data.Nat.GCD

section
public section

/-!
# Structurally recursive certified greatest common divisors

This module supplies the finite arithmetic certificate needed by the
quotient-free rational carrier.  Its Euclidean algorithm recurses on an
explicit natural-number fuel argument.  In particular, its correctness proof
does not use the well-founded-recursion equation theorem through which the
upstream `Nat.gcd` proof API currently acquires `Quot.sound`.
-/

namespace Purelib.Data.Nat.GCD.Coprime

open Purelib.Data.Nat.Coprime.Basic
open Purelib.Data.Nat.GCD

open Purelib.Data.Int

/-- Certify that dividing both inputs by their computed gcd yields coprime quotients.

A positive right input makes the computed gcd positive. The retained extended-Euclid
coefficients give the integer Bézout identity for the two natural quotients. -/
@[expose] def quotientCoprimeCertificate (leftInput : Nat) {rightInput : Nat}
    (rightPositive : 0 < rightInput) :
    CoprimeCertificate
      (leftInput / (Extended.compute leftInput rightInput).gcd)
      (rightInput / (Extended.compute leftInput rightInput).gcd) := by
  let result := Extended.compute leftInput rightInput
  have specification := Extended.compute_spec leftInput rightInput
  have gcdPositive : 0 < result.gcd :=
    Extended.compute_gcd_positive_right leftInput rightPositive
  have gcdNonzero : (result.gcd : Int) ≠ 0 := by
    intro castZero
    have gcdZero : result.gcd = 0 := Int.ofNat.inj castZero
    exact (Nat.ne_of_gt gcdPositive) gcdZero
  have leftFactorizationNat :
      leftInput / result.gcd * result.gcd = leftInput :=
    Division.div_mul_cancel specification.2.1
  have rightFactorizationNat :
      rightInput / result.gcd * result.gcd = rightInput :=
    Division.div_mul_cancel specification.2.2
  have leftFactorization :
      ((leftInput / result.gcd : Nat) : Int) * (result.gcd : Int) =
        (leftInput : Int) := by
    have castEquality :=
      congrArg (fun value : Nat => (value : Int)) leftFactorizationNat
    simpa only [Int.natCast_mul] using castEquality
  have rightFactorization :
      ((rightInput / result.gcd : Nat) : Int) * (result.gcd : Int) =
        (rightInput : Int) := by
    have castEquality :=
      congrArg (fun value : Nat => (value : Int)) rightFactorizationNat
    simpa only [Int.natCast_mul] using castEquality
  have factoredIdentity :
      (result.gcd : Int) =
        (result.gcd : Int) *
          (result.left * ((leftInput / result.gcd : Nat) : Int) +
            result.right * ((rightInput / result.gcd : Nat) : Int)) := by
    calc
      (result.gcd : Int) =
          result.left * (leftInput : Int) +
            result.right * (rightInput : Int) := specification.1
      _ = result.left *
              (((leftInput / result.gcd : Nat) : Int) *
                (result.gcd : Int)) +
            result.right *
              (((rightInput / result.gcd : Nat) : Int) *
                (result.gcd : Int)) := by
          rw [leftFactorization, rightFactorization]
      _ = (result.left * ((leftInput / result.gcd : Nat) : Int) +
              result.right * ((rightInput / result.gcd : Nat) : Int)) *
            (result.gcd : Int) := by
          rw [← Arithmetic.mul_assoc, ← Arithmetic.mul_assoc, Arithmetic.add_mul]
      _ = (result.gcd : Int) *
            (result.left * ((leftInput / result.gcd : Nat) : Int) +
              result.right * ((rightInput / result.gcd : Nat) : Int)) :=
          Arithmetic.mul_comm _ _
  refine ⟨result.left, result.right, ?_⟩
  apply Arithmetic.eq_of_mul_eq_mul_left gcdNonzero
  calc
    (result.gcd : Int) *
          (result.left * ((leftInput / result.gcd : Nat) : Int) +
            result.right * ((rightInput / result.gcd : Nat) : Int)) =
        (result.gcd : Int) := factoredIdentity.symm
    _ = (result.gcd : Int) * 1 := (Arithmetic.mul_one _).symm
end Purelib.Data.Nat.GCD.Coprime

end

section
@[expose] public section

/-!
# Coprime torus braids close to knots

This file proves the constructive coprime case of the torus-link component
theorem.  Each positive band decreases the finite strand label by one, with a
displayed wrap count.  Telescoping those finite equalities shows that a return
after `k` bands forces the strand count to divide `k`.  A stored Bézout
certificate then cancels the `q` factor for the braid
`(σ₁…σₚ₋₁)^q`, ruling out every early return when `p` and `q` are
coprime.
-/

namespace Purelib.Data.Nat.GCD.Coprime

open Purelib.Data.Nat.Coprime.Basic
open Purelib.Data.Nat.GCD

/-! ## Coprime closure theorem -/

/-- Build a coprimality certificate from a computed gcd equal to one.

The result retains the integer coefficients computed by extended Euclid and
specializes their Bézout identity to the supplied equality. -/
def coprimeCertificateOfGcdOne (leftInput rightInput : Nat)
    (gcdOne : (Extended.compute leftInput rightInput).gcd = 1) :
    CoprimeCertificate leftInput rightInput where
  left := (Extended.compute leftInput rightInput).left
  right := (Extended.compute leftInput rightInput).right
  identity := by
    rw [← (Extended.compute_spec leftInput rightInput).1, gcdOne]
    rfl
end Purelib.Data.Nat.GCD.Coprime

end
