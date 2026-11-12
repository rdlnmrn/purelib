module

-- The exposed scalar evaluator retains the original Core gcd operation.
public import Init.Data.Nat.Gcd
public import Purelib.Data.Nat.GCD.Extended
public import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.Remainder
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Nat.GCD

public section

/-!
# Scalar projection of the certified Euclidean algorithm

Fraction normalization only consumes the gcd, not its Bézout coefficients.
The retained fueled calculation omits coefficient updates and is equal to
the extended calculation at every finite fuel, input and coefficient state.
The public constructor delegates to Core gcd and retains exact equalities to
both the binary-width and original sufficient-fuel evaluations. Structural fuel
induction uses only the zero-left and successor equations of Core gcd.
-/

namespace Purelib.Data.Nat.GCD.Scalar

open Purelib.Data.Nat

/-- Compute only the scalar Euclidean result with explicit natural fuel.

A zero right input or exhausted fuel returns the left input. Otherwise the recursion
replaces the pair by the right input and the remainder; it computes no Bézout
coefficients. -/
@[expose] def gcdAux : Nat → Nat → Nat → Nat
  | 0, leftInput, _ => leftInput
  | _ + 1, leftInput, 0 => leftInput
  | fuel + 1, leftInput, rightInput + 1 =>
      Purelib.Data.Nat.GCD.Scalar.gcdAux fuel (rightInput + 1) (leftInput % (rightInput + 1))

/-- Compute finite Euclidean steps while retaining the exact original right operand.

The zero test avoids subtracting and rebuilding a large natural merely to
recognize its successor form. Exhausted fuel and a zero right input still
return the same original left input as the retained scalar evaluator.
-/
@[expose] def reduceAux : Nat → Nat → Nat → Nat
  | 0, leftInput, _ => leftInput
  | fuel + 1, leftInput, rightInput =>
      if rightInput = 0 then leftInput
      else reduceAux fuel rightInput (leftInput % rightInput)

/-- Retaining the original right operand preserves the scalar result at every fuel and pair of inputs. -/
theorem reduceAux_eq_gcdAux (fuel leftInput rightInput : Nat) :
    reduceAux fuel leftInput rightInput = gcdAux fuel leftInput rightInput := by
  induction fuel generalizing leftInput rightInput with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero => rfl
      | succ rightInput =>
          rewrite [reduceAux, if_neg (Nat.succ_ne_zero rightInput)]
          exact inductionHypothesis (rightInput + 1) (leftInput % (rightInput + 1))

/-- Scalar Euclidean recursion equals the gcd projection of extended execution.

The equality holds at every fuel and for every accumulated coefficient state,
including the total zero-fuel branch. -/
theorem gcdAux_eq_computeTailAux_gcd (fuel leftInput rightInput : Nat)
    (leftLeft leftRight rightLeft rightRight : Int) :
    Scalar.gcdAux fuel leftInput rightInput =
      (Extended.computeTailAux fuel leftInput rightInput leftLeft leftRight rightLeft rightRight).gcd := by
  induction fuel generalizing leftInput rightInput leftLeft leftRight rightLeft rightRight with
  | zero => rfl
  | succ fuel ih =>
      cases rightInput with
      | zero => rfl
      | succ rightInput =>
          exact ih (rightInput + 1) (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft - (leftInput / (rightInput + 1) : Nat) * rightLeft)
            (leftRight - (leftInput / (rightInput + 1) : Nat) * rightRight)

/-- Two nonterminal Euclidean remainders reduce the original right input by more than half.

If the first remainder is at most half, its own remainder is smaller still.
Otherwise the original right input fits once into that first remainder, and the
second remainder is its difference. -/
private theorem pair_remainder_half (leftInput rightInput : Nat)
    (rightPositive : 0 < rightInput) (remainderPositive : 0 < leftInput % rightInput) :
    2 * (rightInput % (leftInput % rightInput)) < rightInput := by
  have firstBound := Nat.mod_lt leftInput rightPositive
  have secondBound := Nat.mod_lt rightInput remainderPositive
  by_cases small : 2 * (leftInput % rightInput) ≤ rightInput
  · omega0
  · have differenceBound : rightInput - leftInput % rightInput < leftInput % rightInput := by omega0
    rewrite [Remainder.mod_eq_sub_mod (Nat.le_of_lt firstBound),
      Remainder.mod_eq_of_lt differenceBound]
    omega0

/-- Binary-width fuel reproduces an original sufficiently fueled scalar run.

Every two nonterminal steps halve the right input. Induction on its displayed
power-of-two ceiling therefore permits two steps per binary digit and retains
the original left and right inputs and original fuel on the other side. -/
theorem gcdAux_binaryFuel_eq (width fuel leftInput rightInput : Nat)
    (bound : rightInput < 2 ^ width) (enough : rightInput < fuel) :
    gcdAux (2 * width + 1) leftInput rightInput = gcdAux fuel leftInput rightInput := by
  induction width generalizing fuel leftInput rightInput with
  | zero =>
      have rightZero : rightInput = 0 := by change rightInput < 1 at bound; omega0
      cases rightZero
      cases fuel with
      | zero => exact (Nat.not_lt_zero 0 enough).elim
      | succ fuel => rfl
  | succ width inductionHypothesis =>
      cases fuel with
      | zero => exact (Nat.not_lt_zero rightInput enough).elim
      | succ fuel =>
          cases rightInput with
          | zero => rfl
          | succ rightInput =>
              have firstBelowFuel : leftInput % (rightInput + 1) < fuel :=
                Nat.lt_of_lt_of_le (Nat.mod_lt leftInput (Nat.zero_lt_succ rightInput))
                  (Nat.le_of_lt_succ enough)
              rewrite [show 2 * (width + 1) + 1 = (2 * width + 1) + 1 + 1 by omega0]
              rewrite [gcdAux, gcdAux]
              generalize remainderEq : leftInput % (rightInput + 1) = remainder at *
              cases remainder with
              | zero =>
                  cases fuel with
                  | zero => exact (Nat.not_lt_zero 0 firstBelowFuel).elim
                  | succ fuel => rfl
              | succ remainder =>
                  have halfBound := pair_remainder_half leftInput (rightInput + 1)
                    (Nat.zero_lt_succ rightInput) (by rewrite [remainderEq]; exact Nat.zero_lt_succ remainder)
                  rewrite [remainderEq] at halfBound
                  have smallerBound : (rightInput + 1) % (remainder + 1) < 2 ^ width := by
                    rewrite [Nat.pow_succ] at bound
                    omega0
                  cases fuel with
                  | zero => exact (Nat.not_lt_zero (remainder + 1) firstBelowFuel).elim
                  | succ fuel =>
                      rewrite [gcdAux, gcdAux]
                      exact inductionHypothesis fuel (remainder + 1) ((rightInput + 1) % (remainder + 1))
                        smallerBound
                        (Nat.lt_of_lt_of_le (Nat.mod_lt (rightInput + 1) (Nat.zero_lt_succ remainder))
                          (Nat.le_of_lt_succ firstBelowFuel))

/-- Sufficient explicit fuel agrees with the original Core Euclidean recursion.

The right input is strictly below the retained fuel. Each nonzero step replaces
it by a smaller remainder, so structural fuel induction uses only Core's zero
and successor equations and preserves the original operand orientation.
-/
private theorem gcdAux_eq_natGcd (fuel leftInput rightInput : Nat)
    (enough : rightInput < fuel) :
    gcdAux fuel leftInput rightInput = Nat.gcd rightInput leftInput := by
  induction fuel generalizing leftInput rightInput with
  | zero => exact (Nat.not_lt_zero rightInput enough).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero => exact (Nat.gcd_zero_left leftInput).symm
      | succ rightInput =>
          rewrite [gcdAux, Nat.gcd_succ]
          exact inductionHypothesis (rightInput + 1) (leftInput % (rightInput + 1))
            (Nat.lt_of_lt_of_le (Nat.mod_lt leftInput (Nat.zero_lt_succ rightInput))
              (Nat.le_of_lt_succ enough))

/-- Compute the natural gcd with Core's original arbitrary-precision backend.

The operands retain the orientation of the fueled Euclidean recursion. Exact
readbacks identify this evaluator with both the original sufficiently fueled
run and the retained-right binary-width evaluator at every pair of inputs.
-/
@[expose] def gcd (leftInput rightInput : Nat) : Nat :=
  Nat.gcd rightInput leftInput

/-- The scalar gcd equals its original sufficiently fueled scalar execution. -/
theorem gcd_eq_gcdAux (leftInput rightInput : Nat) :
    gcd leftInput rightInput = gcdAux (rightInput + 1) leftInput rightInput :=
  (gcdAux_eq_natGcd (rightInput + 1) leftInput rightInput (Nat.lt_succ_self rightInput)).symm

/-- The scalar gcd equals the retained-right evaluator with binary-width fuel. -/
theorem gcd_eq_reduceAux (leftInput rightInput : Nat) :
    gcd leftInput rightInput =
      reduceAux (2 * BitWidth.natWidth rightInput + 1) leftInput rightInput :=
  (gcd_eq_gcdAux leftInput rightInput).trans
    ((reduceAux_eq_gcdAux (2 * BitWidth.natWidth rightInput + 1) leftInput rightInput).trans
      (gcdAux_binaryFuel_eq (BitWidth.natWidth rightInput) (rightInput + 1) leftInput rightInput
        (BitWidth.lt_two_pow_natWidth rightInput) (Nat.lt_succ_self rightInput))).symm

/-- The scalar gcd equals the scalar projection of the computed extended result. -/
theorem gcd_eq_compute (leftInput rightInput : Nat) :
    Scalar.gcd leftInput rightInput = (Extended.compute leftInput rightInput).gcd :=
  (gcd_eq_gcdAux leftInput rightInput).trans
    (Scalar.gcdAux_eq_computeTailAux_gcd (rightInput + 1) leftInput rightInput 1 0 0 1)

/-- The computed scalar gcd divides both natural inputs. -/
theorem gcd_dvd (leftInput rightInput : Nat) :
    Scalar.gcd leftInput rightInput ∣ leftInput ∧ Scalar.gcd leftInput rightInput ∣ rightInput := by
  rw [Scalar.gcd_eq_compute]
  exact (Extended.compute_spec leftInput rightInput).2

/-- The computed scalar gcd is positive when the right input is positive. -/
theorem gcd_positive_right (leftInput : Nat) {rightInput : Nat}
    (positive : 0 < rightInput) : 0 < Scalar.gcd leftInput rightInput := by
  rw [Scalar.gcd_eq_compute]
  exact Extended.compute_gcd_positive_right leftInput positive

/-- Check scalar gcd values at zero, coprime, and nontrivial inputs.

Kernel evaluation verifies both zero-input orientations, gcd(1071, 462) = 21, and
gcd(37, 101) = 1. -/
theorem gcd_regressions :
    Scalar.gcd 0 0 = 0 ∧ Scalar.gcd 0 37 = 37 ∧ Scalar.gcd 37 0 = 37 ∧
      Scalar.gcd 1071 462 = 21 ∧ Scalar.gcd 37 101 = 1 := by decide +kernel

end Purelib.Data.Nat.GCD.Scalar
