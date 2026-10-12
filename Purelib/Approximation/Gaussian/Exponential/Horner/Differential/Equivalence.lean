module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Law
import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Addition

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Differential.Equivalence

/-- The translated product computation used in the exact secant identities is operationally the direct `exp(base +
increment)` computation. Thus the factorization is about the CCL-computable exponential, not a separate formal
surrogate. -/
def expDifferential_equivalent_direct
  {base increment : Data.Gaussian.Basic.Canonical}
    (baseUnit : Data.Gaussian.Norm.Basic.normSq base ≤ 1) (incrementUnit :
      Data.Gaussian.Norm.Basic.normSq increment ≤ 1)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (base + increment) ≤ 1) :
    Gaussian.Equivalence.Equivalent
      (Sequence.expProductApproximation
        base increment baseUnit incrementUnit)
      (Sequence.approximation
        (base + increment) sumUnit) :=
  Law.exp_add_equivalent
    baseUnit incrementUnit sumUnit

end Purelib.Approximation.Gaussian.Exponential.Horner.Differential.Equivalence

end
