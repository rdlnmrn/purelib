module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
public import Purelib.Approximation.Gaussian.Enclosure.Residual
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball

section
@[expose] public section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Enclosure

/-- Conservative enclosure of `factor * z`. -/
def scaledBall (factor : Canonical)
  (input : Approximation.Gaussian.Enclosure.Ball) : Approximation.Gaussian.Enclosure.Ball :=
  (Ball.point factor).mul input

/-- Conservative enclosure of `factor * z - 1`. -/
def numeratorBall (factor :
  Canonical) (input : Approximation.Gaussian.Enclosure.Ball) : Approximation.Gaussian.Enclosure.Ball
      :=
  (scaledBall factor input).sub (Ball.point 1)

/-- Conservative enclosure of `factor * z + 1`. -/
def denominatorBall (factor :
  Canonical) (input : Approximation.Gaussian.Enclosure.Ball) : Approximation.Gaussian.Enclosure.Ball
      :=
  (scaledBall factor input).add (Ball.point 1)

/-- The scaled chart ball admits the factor times every reading of the original input ball. -/
theorem scaledBall_contains {factor value :
  Canonical} {input : Approximation.Gaussian.Enclosure.Ball}
    (inside : input.Contains value) :
    (scaledBall factor input).Contains (factor * value) :=
  Approximation.Gaussian.Enclosure.Ball.contains_mul
    (Ball.contains_point factor) inside

/-- The chart numerator ball admits the transformed reading factor times value minus one. -/
theorem numeratorBall_contains {factor value :
  Canonical} {input : Approximation.Gaussian.Enclosure.Ball}
    (inside : input.Contains value) :
    (numeratorBall factor input).Contains (factor * value - 1) :=
  Approximation.Gaussian.Enclosure.Ball.contains_sub
    (scaledBall_contains inside) (Ball.contains_point 1)

/-- The chart denominator ball admits the transformed reading factor times value plus one. -/
theorem denominatorBall_contains {factor value :
  Canonical} {input : Approximation.Gaussian.Enclosure.Ball}
    (inside : input.Contains value) :
    (denominatorBall factor input).Contains (factor * value + 1) :=
  Approximation.Gaussian.Enclosure.Ball.contains_add
    (scaledBall_contains inside) (Ball.contains_point 1)

/-- Exact rational sufficient test for separating every transformed denominator candidate from zero. -/
def DenominatorSeparated (factor :
  Canonical) (input : Approximation.Gaussian.Enclosure.Ball) : Prop :=
  2 * (denominatorBall factor input).radiusSq <
    Data.Gaussian.Norm.Basic.normSq (denominatorBall factor
      input).center

/-- Decide the finite sufficient denominator-separation test by exact rational comparison. -/
instance denominatorSeparatedDecidable (factor :
  Canonical) (input : Approximation.Gaussian.Enclosure.Ball) :
    Decidable (DenominatorSeparated factor input) := by
  unfold DenominatorSeparated
  infer_instance

/-- The finite denominator certificate obtained from the rational separation test. -/
def denominatorApart {factor :
  Canonical} {input : Approximation.Gaussian.Enclosure.Ball}
    (separated : DenominatorSeparated factor input) :
    Ball.Apart (denominatorBall factor input) :=
  Residual.apartOfCenter
    (denominatorBall factor input) separated

/-- Conservative enclosure of the reduced chart argument. -/
def reducedBall {factor : Canonical}
  {input : Approximation.Gaussian.Enclosure.Ball}
    (separated : DenominatorSeparated factor input) :
        Approximation.Gaussian.Enclosure.Ball
      :=
  (numeratorBall factor input).div
    (denominatorBall factor input)
    (denominatorApart separated)
end Purelib.Approximation.Gaussian.Logarithm.Chart.Enclosure

end
