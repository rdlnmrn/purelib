module

public import Purelib.Data.Gaussian.Resource.Model
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Resource
-- The public retained-coordinate bound uses this exact defaulting reader.
public import Purelib.Data.List.GetD

/-!
# Resource bounds for retained Gaussian polynomial coordinates

The original list, natural coordinate and zero fallback determine a Gaussian
polynomial. A uniform bound on its displayed entries therefore bounds every
coordinate, including zero beyond the same original finite list.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Resource.List

open Purelib.Data
open Purelib.Polynomial

set_option backward.match.sparseCases false in
/-- Defaulting finite-list lookup preserves a uniform Gaussian polynomial resource bound.

The original head retains its supplied membership certificate, and a successor
coordinate consumes the same original tail. Out-of-range coordinates return the
original zero polynomial, which satisfies the same resource bound. -/
public theorem getD_within {coefficients : List Dense.Gaussian.NormalizedPolynomial}
    {bound : Nat}
    (allWithin : ∀ polynomial ∈ coefficients,
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
        polynomial bound) (index : Nat) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (Purelib.Data.List.getD coefficients index 0) bound := by
  induction coefficients generalizing index with
  | nil => exact Dense.Resource.zero_within Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => exact allWithin head (List.Mem.head tail)
      | succ index =>
          apply inductionHypothesis
          intro polynomial member
          exact allWithin polynomial (List.Mem.tail head member)

end Purelib.Polynomial.Dense.Gaussian.Resource.List
