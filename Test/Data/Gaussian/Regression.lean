module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Constants
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Executable regression table for canonical Gaussian rationals

The checks exercise structural Gaussian multiplication and total reciprocal
over quotient-free canonical coordinates in both the kernel and the compiled
evaluator.
-/

namespace Test.Data.Gaussian.Regression

open scoped Purelib.Data.Nat

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical (gamma)

/-- The normalized rational one half. -/
private def oneHalf : Rational :=
  ⟨1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The normalized rational negative one half. -/
private def negativeOneHalf : Rational :=
  ⟨-1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The exact Gaussian value twice the imaginary unit. -/
private def gammaSquared : Canonical := ⟨0, 2⟩

/-- The exact Gaussian inverse of one plus the imaginary unit. -/
private def gammaInverse : Canonical := ⟨oneHalf, negativeOneHalf⟩

section
open Test.Data.Gaussian.Regression
/-- Kernel evaluation squares one plus the imaginary unit to twice the imaginary unit. -/
theorem regression_gamma_multiplication :
    let gammaSquared : Canonical := ⟨0, 2⟩
    gamma * gamma = gammaSquared := by
  decide

/-- Kernel evaluation gives the exact rational-coordinate reciprocal of one plus the imaginary unit. -/
theorem regression_gamma_inverse :
    let oneHalf : Rational := ⟨1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let negativeOneHalf : Rational := ⟨-1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let gammaInverse : Canonical := ⟨oneHalf, negativeOneHalf⟩
    gamma⁻¹ = gammaInverse := by
  decide

/-- One executable Boolean used by the compiled regression runner. -/
def compiledGaussianRegressionPassed : Bool :=
  let oneHalf : Rational := ⟨1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let negativeOneHalf : Rational := ⟨-1, 2, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let gammaSquared : Canonical := ⟨0, 2⟩
  let gammaInverse : Canonical := ⟨oneHalf, negativeOneHalf⟩
  decide (gamma * gamma = gammaSquared) && decide (gamma⁻¹ = gammaInverse)

end

/-- The executable Gaussian multiplication and inverse regression table passes. -/
theorem compiledGaussianRegressionPassed_eq_true :
    Regression.compiledGaussianRegressionPassed = true := by
  decide

end Test.Data.Gaussian.Regression
