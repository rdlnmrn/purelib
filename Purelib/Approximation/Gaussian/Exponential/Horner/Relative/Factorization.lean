module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Relative

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Factorization

/-- Exact finite-depth factorization. It is valid at zero because no division has been performed. -/
theorem expSample_sub_one_factor (z :
  Data.Gaussian.Basic.Canonical) (index : Nat) :
    Sample.sample z index - 1 =
      z * Sample.expRelSample z index := by
  rw [Sample.sample,
    Horner.Basic.step_eq]
  rw [show (1 / ((1 : Nat) : Fraction.Rational)) = 1 by decide]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.one_re, Data.Gaussian.Basic.one_im,
        Sample.expRelSample] <;> ring1
end Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Factorization

end
