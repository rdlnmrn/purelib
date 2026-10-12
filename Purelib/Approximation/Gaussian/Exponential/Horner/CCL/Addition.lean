module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Law
import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Data.CCL.Transducer.Machine.Advance

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Addition

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.CCL.Addition

/-- The product of the two unit-disk exponential names emits exactly the requested finite bit count and preserves its
initial prefix. -/
theorem expProductNamed_productive (x y :
  Data.Gaussian.Basic.Canonical)
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
      (count : Nat) :
    (Law.expProductNamed x y xUnit yUnit).machine.emitted.IsPrefix
        (Advance.advance
          (Law.expProductNamed x y xUnit yUnit).machine count).emitted ∧
      (Advance.advance
          (Law.expProductNamed x y xUnit yUnit).machine count).emitted.length =
        count :=
  (Sequence.expProductApproximation x y xUnit yUnit).output_productive count

/-- The exponential name of the retained unit-disk sum emits exactly the requested finite bit count and preserves its
initial prefix. -/
theorem expSumNamed_productive (x y :
  Data.Gaussian.Basic.Canonical)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) (count : Nat) :
    (Law.expSumNamed x y sumUnit).machine.emitted.IsPrefix
        (Advance.advance
          (Law.expSumNamed x y sumUnit).machine count).emitted ∧
      (Advance.advance
          (Law.expSumNamed x y sumUnit).machine count).emitted.length = count :=
  (Sequence.approximation
    (x + y) sumUnit).output_productive count
end Purelib.Approximation.Gaussian.Exponential.Horner.CCL.Addition

end
