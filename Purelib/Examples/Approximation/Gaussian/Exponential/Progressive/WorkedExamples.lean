module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sequence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace Purelib.Examples.Approximation.Gaussian.Exponential.Progressive.WorkedExamples

open Purelib.Data.Gaussian
open Purelib.Examples
open Purelib.Approximation.Gaussian

/-! ## 2. Liouville factorial-position digits to a rational ball -/

/-! ## A shared finite exponential process for Examples 3 and 4 -/

/-- The Gaussian rational input (1/2,1/3). -/
def input : Basic.Canonical := ⟨1
  / 2, 1 / 3⟩

/-- The displayed Gaussian input has squared norm at most one. -/
theorem input_unit :
    Data.Gaussian.Norm.Basic.normSq input ≤ 1 := by
  decide

/-- The certified relative-Horner exponential approximation at the displayed input.

Retains its unit-disk certificate and the original finite refinement and error schedule. -/
def approximation :
  Sequence.ApproximationData :=
  Exponential.Horner.Relative.Sequence.expRelApproximation
    input
    input_unit

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

/-! ## 4. The same finite exponential process in redundant signed digits -/

end Purelib.Examples.Approximation.Gaussian.Exponential.Progressive.WorkedExamples

end
