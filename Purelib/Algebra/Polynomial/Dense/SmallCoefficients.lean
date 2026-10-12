module

public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.DropWhile.Basic

/-!
# Exact addition for short dense coefficient tables

A displayed nonzero leading coefficient prevents normalization from discarding
any retained degree slot. Constant addition therefore changes only the trailing
coefficient of the original dense list.
-/

namespace Purelib.Algebra.Polynomial.Dense.SmallCoefficients

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic (GaussianPolynomial)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.List

/-- Adding a constant changes only the trailing coefficient of an exact quartic.

The leading coefficient is nonzero, so normalization retains the displayed five-entry coefficient list. -/
public theorem quartic_add_constant
    {leading : Canonical} (second third fourth trailing constantTerm : Canonical)
    (leadingNonzero : leading ≠ 0) :
    (⟨[leading, second, third, fourth, trailing]⟩ : GaussianPolynomial) +
        DensePolynomial.constant constantTerm =
      ⟨[leading, second, third, fourth, trailing + constantTerm]⟩ := by
  apply DensePolynomial.ext
  change ([leading + (0 : Canonical), second + 0, third + 0, fourth + 0,
    trailing + constantTerm].dropWhile (fun value => decide (value = 0))) =
      [leading, second, third, fourth, trailing + constantTerm]
  rw [_root_.add_zero, _root_.add_zero, _root_.add_zero, _root_.add_zero]
  exact DropWhile.cons_of_false (fun value : Canonical => decide (value = 0))
    leading [second, third, fourth, trailing + constantTerm]
    (decide_eq_false leadingNonzero)

end Purelib.Algebra.Polynomial.Dense.SmallCoefficients
