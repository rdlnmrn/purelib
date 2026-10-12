module

import Purelib.Tactic.Ring
public import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs
public import Purelib.Data.Nat.Coprime.Basic
-- Exposed divisor transport retains the exact-division proof in its certificate.
public import Purelib.Data.Nat.Division
-- The regression statement retains the original divisibility witness.
public import Purelib.Data.Nat.Divisibility

open Purelib.Data.Nat.Coprime

@[expose] public section

/-!
# Finite arithmetic on retained coprimality witnesses

These constructors combine the existing integer Bézout coefficients directly.
They do not run another gcd calculation or extract executable data from an
existential proposition.  Divisor transport computes its quotient explicitly;
the divisibility premise is used only to verify its reconstruction identity.

Reduced fraction arithmetic uses these witnesses to certify its cancelled
addition and multiplication displays without normalizing the large result again.
-/

namespace Purelib.Data.Nat.Coprime.Arithmetic

open Purelib.Data.Nat.Coprime.Basic
open Purelib.Data.Nat

variable {a b c d divisor : Nat}

/-- A divisor of the first input retains coprimality with the second input.

The first coefficient is multiplied by the ordinary quotient. Its retained
divisibility witness certifies reconstruction, including a zero divisor. -/
def of_dvd_left (certificate : CoprimeCertificate a b) (divides : divisor ∣ a) :
    CoprimeCertificate divisor b where
  left := certificate.left * (a / divisor : Nat)
  right := certificate.right
  identity := by
    have reconstruct : ((a / divisor : Nat) : Int) * (divisor : Int) = (a : Int) := by
      rw [← Int.natCast_mul]
      exact congrArg (fun value : Nat => (value : Int)) (Division.div_mul_cancel divides)
    calc
      _ = certificate.left * (((a / divisor : Nat) : Int) * (divisor : Int)) +
          certificate.right * (b : Int) := by ring1
      _ = 1 := by rw [reconstruct]; exact certificate.identity

/-- Transport a Bézout certificate to a divisor of its second input.

Symmetry reduces the operation to first-input transport, preserving the explicit
quotient calculation and then restoring the input order. -/
def of_dvd_right (certificate : CoprimeCertificate a b) (divides : divisor ∣ b) :
    CoprimeCertificate a divisor :=
  (Arithmetic.of_dvd_left certificate.symm divides).symm

/-- Combine two Bézout certificates with a common first input.

Multiplying their identities produces explicit coefficients certifying that the
common input is coprime to the product of their second inputs. -/
def mul_right (first : CoprimeCertificate a b) (second : CoprimeCertificate a c) :
    CoprimeCertificate a (b * c) where
  left := first.left * second.left * (a : Int) +
    first.left * second.right * (c : Int) + first.right * second.left * (b : Int)
  right := first.right * second.right
  identity := by
    rw [Int.natCast_mul]
    calc
      _ = (first.left * (a : Int) + first.right * (b : Int)) *
          (second.left * (a : Int) + second.right * (c : Int)) := by ring1
      _ = 1 := by rw [first.identity, second.identity]; rfl

/-- Combine two Bézout certificates with a common second input.

The resulting coefficients certify the product of the first inputs against that same
second input, using symmetry and the corresponding product constructor. -/
def mul_left (first : CoprimeCertificate a c) (second : CoprimeCertificate b c) :
    CoprimeCertificate (a * b) c :=
  (Arithmetic.mul_right first.symm second.symm).symm

/-- Combine four pairwise Bézout certificates into a certificate for two products.

Each first factor is certified against each second factor. Composing the finite
product constructors retains explicit coefficients for the resulting product pair. -/
def mul_mul (firstFirst : CoprimeCertificate a c) (firstSecond : CoprimeCertificate a d)
    (secondFirst : CoprimeCertificate b c) (secondSecond : CoprimeCertificate b d) :
    CoprimeCertificate (a * b) (c * d) :=
  Arithmetic.mul_right (Arithmetic.mul_left firstFirst secondFirst) (Arithmetic.mul_left firstSecond secondSecond)

/-- Adjust an integer coefficient to the sign of a supplied integer.

Nonnegative values leave the coefficient unchanged; negative values negate it. This
transports multiplication between the integer and its natural absolute-value display. -/
def signedCoefficient (value coefficient : Int) : Int :=
  match value with
  | .ofNat _ => coefficient
  | .negSucc _ => -coefficient

/-- A sign-adjusted coefficient times the integer equals the original coefficient times
its magnitude. -/
theorem signedCoefficient_mul_value (value coefficient : Int) :
    Arithmetic.signedCoefficient value coefficient * value = coefficient * (value.natAbs : Int) := by
  cases value with
  | ofNat value => rfl
  | negSucc value =>
      change (-coefficient) * (-((value + 1 : Nat) : Int)) =
        coefficient * ((value + 1 : Nat) : Int)
      ring1

/-- A sign-adjusted coefficient times the magnitude equals the original coefficient times
the integer. -/
theorem signedCoefficient_mul_natAbs (value coefficient : Int) :
    Arithmetic.signedCoefficient value coefficient * (value.natAbs : Int) = coefficient * value := by
  cases value with
  | ofNat value => rfl
  | negSucc value =>
      change (-coefficient) * ((value + 1 : Nat) : Int) =
        coefficient * (-((value + 1 : Nat) : Int))
      ring1

/-- Preserve a Bézout certificate when adding an integer multiple of its second input.

The first input is the natural magnitude of a signed integer. Explicit sign
adjustments and coefficient subtraction certify the magnitude of the shifted integer
against the original second input, including sign changes. -/
def add_int_mul {value : Int} (certificate : CoprimeCertificate value.natAbs b)
    (multiple : Int) : CoprimeCertificate (value + multiple * (b : Int)).natAbs b where
  left := Arithmetic.signedCoefficient (value + multiple * (b : Int))
    (Arithmetic.signedCoefficient value certificate.left)
  right := certificate.right - Arithmetic.signedCoefficient value certificate.left * multiple
  identity := by
    rw [Arithmetic.signedCoefficient_mul_natAbs]
    calc
      _ = Arithmetic.signedCoefficient value certificate.left * value +
          certificate.right * (b : Int) := by ring1
      _ = 1 := by rw [Arithmetic.signedCoefficient_mul_value]; exact certificate.identity

/-- Check the retained Bézout coefficients after a shift that changes the numerator's
sign.

The displayed certificate for two and five is shifted by minus three times five, and
the resulting coefficients are checked by kernel evaluation. -/
theorem signed_arithmetic_regressions :
    let original : CoprimeCertificate 2 5 := ⟨-2, 1, by decide +kernel⟩
    let shifted := Arithmetic.add_int_mul original (value := 2) (-3)
    shifted.left = 2 ∧ shifted.right = -5 := by
  decide +kernel

/-- Check explicit Bézout data for divisor transport and products.

The examples include transport to a zero divisor, a nontrivial quotient adjustment,
and the four-certificate construction for the pair six and thirty-five. -/
theorem arithmetic_regressions :
    let zero : CoprimeCertificate 0 1 := ⟨37, 1, by decide +kernel⟩
    let six : CoprimeCertificate 6 35 := ⟨6, -1, by decide +kernel⟩
    let twoFive : CoprimeCertificate 2 5 := ⟨-2, 1, by decide +kernel⟩
    let twoSeven : CoprimeCertificate 2 7 := ⟨-3, 1, by decide +kernel⟩
    let threeFive : CoprimeCertificate 3 5 := ⟨2, -1, by decide +kernel⟩
    let threeSeven : CoprimeCertificate 3 7 := ⟨-2, 1, by decide +kernel⟩
    (Arithmetic.of_dvd_left zero (Divisibility.refl 0)).left = 0 ∧
      (Arithmetic.of_dvd_left six (show 2 ∣ 6 from ⟨3, rfl⟩)).left = 18 ∧
      let product := Arithmetic.mul_mul twoFive twoSeven threeFive threeSeven
      product.left * 6 + product.right * 35 = 1 := by
  decide +kernel

end Purelib.Data.Nat.Coprime.Arithmetic

end
