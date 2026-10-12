module
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Constant

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Sequence

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Zero

/-- The finite unit-disk exponential approximation at Gaussian input zero. -/
def expZeroApproximation :
  ApproximationData :=
  Sequence.approximation 0 (by decide)

/-- Every finite exponential sample at zero is exactly one. -/
theorem expZero_sample (index : Nat) :
    expZeroApproximation.sample index = 1 :=
  Sample.sample_zero index

/-- Constructive finite-request meaning of `exp(0) = 1`. In fact both sides display the same rational value at every
index, so no refinement is required. -/
def exp_zero_equivalent_one :
  Gaussian.Equivalence.Equivalent expZeroApproximation
  Constant.oneApproximation :=
  Equivalent.of_constant_samples
    expZeroApproximation Constant.oneApproximation 1
      expZero_sample Constant.one_sample

end Purelib.Approximation.Gaussian.Exponential.Horner.Zero

end
