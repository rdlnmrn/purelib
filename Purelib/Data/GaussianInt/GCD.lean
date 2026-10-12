module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Fraction.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Result

open Purelib.Data

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Division

public section

/-!
# Constructive extended Euclidean certificates over the Gaussian integers

Nearest-Gaussian-integer division gives a Euclidean recursion whose measure is
the displayed natural quadrance.  This file packages that recursion with all
of the data needed downstream: a Bezout identity and explicit quotients
showing that the returned gcd divides both inputs.  The construction is a
finite program and introduces neither choice nor a completed carrier.
-/

namespace Purelib.Data.GaussianInt.GCD

set_option genInjectivity false in
/-- Retain extended Gaussian Euclidean data for two original integral inputs.

The record stores their common divisor, explicit Bezout coefficients and both exact
quotients. All three retained identities refer to the same computed divisor and
original inputs. -/
structure Certificate (left right : GaussianInt) where
  /-- The computed Gaussian common divisor of the original two inputs. -/ gcd : GaussianInt
  /-- The retained Bezout coefficient of the original left input. -/ leftCoefficient : GaussianInt
  /-- The retained Bezout coefficient of the original right input. -/ rightCoefficient : GaussianInt
  /-- The exact retained quotient of the original left input by the computed divisor. -/ leftQuotient : GaussianInt
  /-- The exact retained quotient of the original right input by the computed divisor. -/ rightQuotient : GaussianInt
  /-- The retained linear combination of the original inputs equals the computed divisor. -/ bezout :
    gcd = leftCoefficient * left + rightCoefficient * right
  /-- The computed divisor times its retained left quotient equals the original left input. -/ left_factor : left = gcd
    * leftQuotient
  /-- The computed divisor times its retained right quotient equals the original right input. -/ right_factor : right =
    gcd * rightQuotient

constructive_injectivity Certificate

open Purelib.Data.GaussianInt.GCD in
/-- Compute an extended Gaussian Euclidean certificate by deterministic nearest-integer
division.

Each nonzero right input produces an exact quotient and a strictly smaller remainder
quadrance. The terminating recursion retains Bezout coefficients and both factor
quotients for the original pair. -/
@[expose] def extendedGCD (left right : GaussianInt) : Certificate left right := by
  by_cases rightZero : right = 0
  · exact
      { gcd := left
        leftCoefficient := 1
        rightCoefficient := 0
        leftQuotient := 1
        rightQuotient := 0
        bezout := by rw [rightZero]; ring1
        left_factor := by ring1
        right_factor := by rw [rightZero]; ring1 }
  · let fraction : Fraction :=
      { numerator := left
        denominator := right
        denominatorNonzero := rightZero }
    let quotient := Division.Nearest.digit fraction
    let remainderValue := Division.Nearest.remainder fraction
    let recursive := extendedGCD right remainderValue
    exact
      { gcd := recursive.gcd
        leftCoefficient := recursive.rightCoefficient
        rightCoefficient :=
          recursive.leftCoefficient - recursive.rightCoefficient * quotient
        leftQuotient :=
          quotient * recursive.leftQuotient + recursive.rightQuotient
        rightQuotient := recursive.leftQuotient
        bezout := by
          have recursiveBezout := recursive.bezout
          have division := Division.Nearest.digit_mul_denominator_add_remainder fraction
          dsimp only [fraction, quotient, remainderValue] at recursiveBezout division
          rw [recursiveBezout]
          calc
            recursive.leftCoefficient * right +
                recursive.rightCoefficient * remainderValue =
              recursive.rightCoefficient *
                  (quotient * right + remainderValue) +
                (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right := by
              apply GaussianInt.ext <;>
                simp only [GaussianInt.add_re,
                  GaussianInt.add_im,
                  GaussianInt.sub_re,
                  GaussianInt.sub_im,
                  GaussianInt.mul_re,
                  GaussianInt.mul_im] <;>
                ring1
            _ = recursive.rightCoefficient * left +
                (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right :=
              congrArg
                (fun value => recursive.rightCoefficient * value +
                  (recursive.leftCoefficient -
                    recursive.rightCoefficient * quotient) * right)
                division
        left_factor := by
          have recursiveLeft := recursive.left_factor
          have recursiveRight := recursive.right_factor
          have division := Division.Nearest.digit_mul_denominator_add_remainder fraction
          dsimp only [fraction, quotient, remainderValue] at recursiveLeft recursiveRight division
          calc
            left = quotient * right + remainderValue := division.symm
            _ = quotient * (recursive.gcd * recursive.leftQuotient) +
                remainderValue :=
              congrArg (fun value => quotient * value + remainderValue)
                recursiveLeft
            _ = quotient * (recursive.gcd * recursive.leftQuotient) +
                recursive.gcd * recursive.rightQuotient :=
              congrArg
                (fun value => quotient *
                    (recursive.gcd * recursive.leftQuotient) + value)
                recursiveRight
            _ = recursive.gcd *
                (quotient * recursive.leftQuotient +
                  recursive.rightQuotient) := by
              apply GaussianInt.ext <;>
                simp only [GaussianInt.add_re,
                  GaussianInt.add_im,
                  GaussianInt.mul_re,
                  GaussianInt.mul_im] <;>
                ring1
        right_factor := by
          exact recursive.left_factor }
termination_by GaussianInt.normNat right
decreasing_by
  all_goals simpa only [fraction] using Division.Nearest.remainder_norm_lt_denominator fraction
end Purelib.Data.GaussianInt.GCD

end
