module
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Approximation.Rational

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Sampling.Dyadic

/-- The scale-four quarter-radius allowance is four times the indexed process sampling request. -/
public theorem quarterRadius_four_eq_four_refinementTarget (index
  : Nat) :
    Geometric.Basic.quarterRadius 4 index =
      4 * Gaussian.Process.Sampling.refinementTarget index := by
  rw [Gaussian.Process.Sampling.refinementTarget,
    Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

end Purelib.Approximation.Gaussian.Sampling.Dyadic

end
