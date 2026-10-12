module
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Arithmetic.Exact

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat

section
public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

/-- Actual addition of two terminating displayed Gaussian-rational names. -/
@[expose] def exactAdd_named_equivalent (left right : Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.exact left)
        (Named.exact right))
      (Named.exact (left + right)) :=
  Equivalent.of_constant_samples
    _ _ (left + right) (by intro index; rfl) (by intro index; rfl)

end

public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

/-- Exact zero and exact one are not operationally equivalent.

The separation is witnessed by one finite request at squared tolerance `1 / 2`; there is no appeal to a completed value.
-/
theorem exactZero_not_equivalent_exactOne :
    Gaussian.Equivalence.NamedEquivalent
      (Named.exact 0)
      (Named.exact 1) → False := by
  intro equivalent
  let comparison := equivalent.compare 0 0 (1 / 2) (by decide)
  have impossible := comparison.close
    (Nat.le_refl comparison.leftIndex)
    (Nat.le_refl comparison.rightIndex)
  have one_lt_half : (1 : Fraction.Rational) < 1 / 2 := by
    simpa only [
      Sampling.approximation,
      Gaussian.Process.Sampling.witnessAt,
      Gaussian.Process.Sampling.stateAt,
      Process.exact,
      Named.exact,
      Data.Gaussian.Basic.zero_sub,
      Data.Gaussian.Norm.Basic.normSq_neg,
      Data.Gaussian.Norm.Basic.normSq_one] using impossible
  exact (by decide : ¬ ((1 : Fraction.Rational) < 1 / 2))
    one_lt_half

end

end

end Purelib.Approximation.Gaussian.Arithmetic.Exact
