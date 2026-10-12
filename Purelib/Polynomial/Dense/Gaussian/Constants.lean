module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

/-!
# Constant dense Gaussian polynomials

A retained Gaussian coefficient forms a one-entry descending coefficient
list. Horner evaluation returns that same coefficient at every Gaussian point.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Constants

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- Construct the dense constant polynomial with the retained Gaussian coefficient.

The original one-entry descending coefficient list is retained directly.
No normalization or coefficient conversion is performed. -/
@[expose] public def gaussianConstant (c : Canonical) : DensePolynomial Canonical :=
  DensePolynomial.constant c

/-- A Gaussian constant polynomial evaluates to its retained coefficient.

The finite Horner scan consumes the single coefficient and returns it for
any Gaussian evaluation point, including zero. -/
@[simp] public theorem gaussianConstant_eval (c z : Canonical) :
    (gaussianConstant c).eval z = c :=
  DensePolynomial.eval_constant c z

end Purelib.Polynomial.Dense.Gaussian.Constants
