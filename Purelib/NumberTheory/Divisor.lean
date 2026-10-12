module

import Purelib.Data.Nat.Division

/-!
# Complementary coordinates of natural divisors

A retained divisibility witness reconstructs the original natural number from
its quotient and divisor. Positive values keep both complementary coordinates
nonzero, and dividing by the complementary coordinate recovers the divisor.
-/

namespace Purelib.NumberTheory.Divisor

open Purelib.Data.Nat

/-- A quotient coordinate of a divisor of a positive number is positive.

The retained divisibility certificate reconstructs the original number. A zero
quotient would make that positive number the displayed zero product. -/
public theorem divisorQuotient_positive {divisor number : Nat}
    (numberPositive : 0 < number) (divides : divisor ∣ number) :
    0 < number / divisor := by
  apply Nat.pos_of_ne_zero
  intro quotientZero
  have reconstruction := Division.div_mul_cancel divides
  rewrite [quotientZero, Nat.zero_mul] at reconstruction
  exact (Nat.ne_of_gt numberPositive) reconstruction.symm

/-- The complementary quotient of a displayed natural divisor divides the number.

The retained quotient reconstruction supplies the original divisor itself as
its multiplication witness. Neither the divisor nor the quotient is recomputed. -/
public theorem divisorQuotient_dvd {divisor number : Nat}
    (divides : divisor ∣ number) : number / divisor ∣ number :=
  ⟨divisor, (Division.div_mul_cancel divides).symm⟩

/-- A positive proper natural divisor has quotient coordinate at least two.

The original quotient cannot be zero at a positive number, and a unit quotient
would identify the proper divisor with that number. Every remaining successor
of a successor supplies the displayed lower bound. -/
public theorem divisorQuotient_two_le {divisor number : Nat}
    (divisorPositive : 0 < divisor) (divides : divisor ∣ number)
    (proper : divisor < number) : 2 ≤ number / divisor := by
  have reconstruction := Division.div_mul_cancel divides
  have numberPositive : 0 < number := Nat.lt_trans divisorPositive proper
  cases quotientEquation : number / divisor with
  | zero =>
      rewrite [quotientEquation, Nat.zero_mul] at reconstruction
      exact (Nat.not_lt_zero 0 (reconstruction.symm ▸ numberPositive)).elim
  | succ predecessor =>
      cases predecessor with
      | zero =>
          rewrite [quotientEquation, Nat.one_mul] at reconstruction
          exact (Nat.lt_irrefl divisor (reconstruction.symm ▸ proper)).elim
      | succ predecessor =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le predecessor))

/-- Dividing by the complementary coordinate recovers a positive natural divisor.

Both quotient reconstructions retain the original divisor witnesses. Positive
complementary quotient evidence permits cancellation of their common factor. -/
public theorem divide_by_divisorQuotient {divisor number : Nat}
    (numberPositive : 0 < number) (divides : divisor ∣ number) :
    number / (number / divisor) = divisor := by
  have reconstruction := Division.div_mul_cancel divides
  have quotientPositive := divisorQuotient_positive numberPositive divides
  have quotientDivides := divisorQuotient_dvd divides
  have secondReconstruction := Division.div_mul_cancel quotientDivides
  apply Nat.eq_of_mul_eq_mul_right quotientPositive
  calc
    number / (number / divisor) * (number / divisor) = number :=
      secondReconstruction
    _ = divisor * (number / divisor) :=
      reconstruction.symm.trans (Nat.mul_comm _ _)

end Purelib.NumberTheory.Divisor
