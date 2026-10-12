module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.ContractiveScale
public import Purelib.Data.Gaussian.Dyadic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Data.Gaussian

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- Canonical finite approximation of an arbitrary name scaled by one displayed inverse dyadic. -/
@[expose] def dyadicScaledApproximation (exponent : Nat) (input : Gaussian.Name.Basic.Named) :
    Gaussian.Sequence.ApproximationData :=
  ContractiveScale.contractiveScaleApproximation (Dyadic.inverseDyadicAt exponent)
    (Dyadic.normSq_inverseDyadicAt_le_one exponent)
    (Sampling.approximation input)

/-- Sampling the inverse-dyadically scaled approximation multiplies the original canonical sample by the displayed
inverse dyadic factor. -/
@[simp] theorem dyadicScaledApproximation_sample
    (exponent : Nat) (input : Gaussian.Name.Basic.Named) (index : Nat) :
    (Approximation.Gaussian.Sequence.Arithmetic.DyadicScale.dyadicScaledApproximation exponent input).sample index =
      Dyadic.inverseDyadicAt exponent *
        (Sampling.approximation input).sample index :=
  rfl

end

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale
