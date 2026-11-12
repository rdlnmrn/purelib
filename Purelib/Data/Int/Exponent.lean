module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.Data.Int

/-! ## Signed powers and finite Laurent term lists -/

set_option genInjectivity false in
/-- A finite signed exponent syntax with a unique representation of zero.

The nonnegative constructor stores its natural exponent directly. The negative
constructor stores a predecessor and denotes `-(predecessor + 1)`, so every
negative exponent is strictly below zero. -/
inductive Exponent where
  /-- Represent a nonnegative exponent by its natural value. -/ | nonnegative : Nat → Exponent
  /-- Represent a strictly negative exponent as minus the successor of the stored natural. -/ | negative : Nat →
    Exponent
deriving DecidableEq

constructive_injectivity Exponent

namespace Exponent.nonnegative

end Exponent.nonnegative
namespace Exponent.negative

end Exponent.negative
end Purelib.Data.Int

end

namespace Purelib.Data.Int.Exponent

/-- Read the signed integer denoted by the original exponent constructor. -/
@[expose] public def value : Exponent → Int
  | .nonnegative degree => Int.ofNat degree
  | .negative predecessor => Int.negSucc predecessor

/-- Construct the original signed exponent from its unique integer representation. -/
@[expose] public def ofInt : Int → Exponent
  | .ofNat degree => .nonnegative degree
  | .negSucc predecessor => .negative predecessor

/-- Integer readback of the retained signed-exponent constructor is exact. -/
public theorem value_ofInt (integer : Int) : (ofInt integer).value = integer := by
  cases integer <;> rfl

/-- Reconstructing a signed exponent from its integer readback retains its constructor. -/
public theorem ofInt_value (exponent : Exponent) : ofInt exponent.value = exponent := by
  cases exponent <;> rfl

/-- The smallest natural shift which makes this displayed exponent nonnegative. -/
@[expose] public def negativeMagnitude : Exponent → Nat
  | .nonnegative _ => 0
  | .negative predecessor => predecessor + 1

/-- The natural exponent after a supplied polynomializing shift.

A shift below the negative magnitude saturates at zero; polynomialization
identities therefore retain an explicit sufficient-shift certificate. -/
@[expose] public def shifted (shift : Nat) : Exponent → Nat
  | .nonnegative degree => shift + degree
  | .negative predecessor => shift - (predecessor + 1)

/-- A sufficient shift has the exact nonnegative signed-integer readback. -/
public theorem shifted_value (exponent : Exponent) (shift : Nat)
    (sufficient : exponent.negativeMagnitude ≤ shift) :
    (exponent.shifted shift : Int) = exponent.value + (shift : Int) := by
  cases exponent with
  | nonnegative degree => change ((shift + degree : Nat) : Int) = (degree : Int) + shift; omega0
  | negative predecessor =>
      change predecessor + 1 ≤ shift at sufficient
      change ((shift - (predecessor + 1) : Nat) : Int) = Int.negSucc predecessor + shift
      omega0

/-- Add signed exponents in their original unique constructor representation. -/
@[expose] public def add (left right : Exponent) : Exponent :=
  ofInt (left.value + right.value)

/-- Integer readback sends signed-exponent addition to integer addition. -/
public theorem add_value (left right : Exponent) :
    (add left right).value = left.value + right.value := value_ofInt _

/-- Adding two nonnegative original exponents introduces no negative magnitude. -/
public theorem negativeMagnitude_add_eq_zero (left right : Exponent)
    (leftZero : left.negativeMagnitude = 0) (rightZero : right.negativeMagnitude = 0) :
    (add left right).negativeMagnitude = 0 := by
  cases left with
  | negative predecessor => exact (Nat.succ_ne_zero predecessor leftZero).elim
  | nonnegative leftDegree =>
      cases right with
      | negative predecessor => exact (Nat.succ_ne_zero predecessor rightZero).elim
      | nonnegative rightDegree => rfl

/-- Negate the retained signed integer without introducing a second zero representation. -/
@[expose] public def neg (exponent : Exponent) : Exponent := ofInt (-exponent.value)

/-- Negating the original exponent negates its exact integer reading. -/
public theorem neg_value (exponent : Exponent) : exponent.neg.value = -exponent.value := value_ofInt _

/-- Negating an original exponent twice retains its same constructor. -/
public theorem neg_neg (exponent : Exponent) : exponent.neg.neg = exponent := by
  change ofInt (-exponent.neg.value) = exponent
  rewrite [neg_value, show -(-exponent.value) = exponent.value by omega0]
  exact ofInt_value exponent

end Purelib.Data.Int.Exponent
