module
public import Purelib.Data.Nat.GCD.Extended

open Purelib.Data.Nat.GCD

public section

/-!
# Scalar projection of the certified Euclidean algorithm

Fraction normalization only consumes the gcd, not its Bézout coefficients.
This structurally recursive calculation omits the coefficient updates and
is equal to the existing extended calculation for every finite fuel, input
and coefficient state.  The public constructor uses exactly the same
internally sufficient fuel; no upstream `Nat.gcd` equation theorem is used.
-/

namespace Purelib.Data.Nat.GCD.Scalar

/-- Compute only the scalar Euclidean result with explicit natural fuel.

A zero right input or exhausted fuel returns the left input. Otherwise the recursion
replaces the pair by the right input and the remainder; it computes no Bézout
coefficients. -/
@[expose] def gcdAux : Nat → Nat → Nat → Nat
  | 0, leftInput, _ => leftInput
  | _ + 1, leftInput, 0 => leftInput
  | fuel + 1, leftInput, rightInput + 1 =>
      Purelib.Data.Nat.GCD.Scalar.gcdAux fuel (rightInput + 1) (leftInput % (rightInput + 1))

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

/-- Compute the natural gcd using scalar Euclidean recursion.

The evaluator supplies rightInput + 1 units of fuel and performs no integer
coefficient updates. The projection theorem relates this exact execution to extended
Euclid. -/
@[expose] def gcd (leftInput rightInput : Nat) : Nat :=
  Scalar.gcdAux (rightInput + 1) leftInput rightInput

/-- The scalar gcd equals the scalar projection of the computed extended result. -/
theorem gcd_eq_compute (leftInput rightInput : Nat) :
    Scalar.gcd leftInput rightInput = (Extended.compute leftInput rightInput).gcd :=
  Scalar.gcdAux_eq_computeTailAux_gcd (rightInput + 1) leftInput rightInput 1 0 0 1

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
