module

public import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Gaussian-integer natural powers

Successive multiplication computes the original explicit powers. The displayed
integral and natural norms certify nonzero powers and norm multiplicativity.
-/

namespace Purelib.Data.GaussianInt

open Purelib.Data

public section

/-- Compute a Gaussian-integer natural power by multiplying through the displayed
exponent.

The zero exponent returns one; each successor multiplies the previous result by the
same retained base. -/
@[expose] def natPow (z : GaussianInt) : Nat → GaussianInt
  | 0 => 1
  | exponent + 1 => natPow z exponent * z

/-- Every explicit natural power of a nonzero Gaussian integer remains nonzero.

Induction on the exponent uses multiplicativity and definiteness of the integral norm
at each retained multiplication. -/
theorem natPow_ne_zero (z : GaussianInt) (nonzero : z ≠ 0) :
    ∀ exponent : Nat, natPow z exponent ≠ 0
  | 0 => by
      intro oneZero
      have realOneZero := congrArg GaussianInt.re oneZero
      exact (show (1 : Int) ≠ 0 by decide) realOneZero
  | exponent + 1 => by
      intro productZero
      have normProduct :
          normInt (natPow z exponent) * normInt z = 0 := by
        rw [← normInt_mul]
        exact normInt_eq_zero.mpr productZero
      rcases Int.Arithmetic.eq_zero_of_mul_eq_zero normProduct with leftZero | rightZero
      · exact natPow_ne_zero z nonzero exponent (normInt_eq_zero.mp leftZero)
      · exact nonzero (normInt_eq_zero.mp rightZero)

/-- An explicit successor power is the preceding power multiplied by its retained base. -/
@[simp] theorem natPow_succ (z : GaussianInt) (exponent : Nat) :
    natPow z (exponent + 1) = natPow z exponent * z := rfl

/-- The explicit zeroth power of any Gaussian integer is one. -/
@[simp] theorem natPow_zero (z : GaussianInt) : natPow z 0 = 1 := rfl

namespace Power

/-- The natural norm of a Gaussian-integer power is the same power of its natural norm.

Each successor step uses the original multiplication recurrence and natural
norm multiplicativity, retaining the same base and exponent. -/
@[simp] theorem normNat_pow (value : GaussianInt) (exponent : Nat) :
    normNat (value ^ exponent) = Nat.pow (normNat value) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [pow_succ value exponent]
      change normNat (value ^ exponent * value) =
        Nat.pow (normNat value) exponent * normNat value
      rw [normNat_mul, inductionHypothesis]

end Power

end

end Purelib.Data.GaussianInt
