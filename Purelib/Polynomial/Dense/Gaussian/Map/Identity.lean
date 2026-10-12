module

public import Purelib.Algebra.Field.Embedding
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Map.Identity
open Purelib.Algebra.Polynomial.DensePolynomial

/-- The field embedding from normalized Gaussian records to their canonical values.

The record retains injectivity and preservation of zero, one, addition, negation, multiplication and inversion. -/
def eraseEmbedding :
    Algebra.Field.Embedding Gaussian.Basic.Number Gaussian.Basic.Canonical where
  toFun := Gaussian.Basic.value
  injective := Gaussian.Basic.value_injective
  map_zero := Gaussian.Basic.value_zero
  map_one := Gaussian.Basic.value_one
  map_add := Gaussian.Basic.value_add_instance
  map_neg := Gaussian.Basic.value_neg_instance
  map_mul := Gaussian.Basic.value_mul_instance
  map_inv := Gaussian.Field.value_inv_instance
end Purelib.Polynomial.Dense.Gaussian.Map.Identity

end
