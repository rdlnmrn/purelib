module
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Factorization

/-- Multiplying the finite one-plus logarithm derivative sample by `1 + u` leaves the exact geometric remainder.

The identity holds at every displayed finite index and for every Gaussian rational input. -/
theorem
  log1pDerivative_geometric_remainder
  (u : Data.Gaussian.Basic.Canonical) (index : Nat) :
    (1 + u) * Sample.log1pDerivativeSample u index =
      1 - (-u) ^ (index + 1) := by
  rw [Sample.log1pDerivativeSample]
  induction index with
  | zero =>
      rw [Prefix.sum_succ,
        Prefix.sum_zero, pow_zero, pow_one]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im, Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im,
            Data.Gaussian.Basic.one_re, Data.Gaussian.Basic.one_im] <;> ring1
  | succ index inductionHypothesis =>
      rw [Prefix.sum_succ]
      calc
        (1 + u) *
            (Prefix.sum
                (fun termIndex => (-u) ^ termIndex) (index + 1) +
              (-u) ^ (index + 1)) =
          (1 - (-u) ^ (index + 1)) +
            (1 + u) * (-u) ^ (index + 1) := by
              rw [mul_add, inductionHypothesis]
        _ = 1 - (-u) ^ (index + 1 + 1) := by
          rw [show (-u) ^ (index + 1 + 1) =
            (-u) ^ (index + 1) * (-u) by
              exact pow_succ (-u) (index + 1)]
          apply Data.Gaussian.Basic.ext <;>
            simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
              Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
              Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im, Data.Gaussian.Basic.one_re,
                Data.Gaussian.Basic.one_im] <;> ring1
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Factorization

end
