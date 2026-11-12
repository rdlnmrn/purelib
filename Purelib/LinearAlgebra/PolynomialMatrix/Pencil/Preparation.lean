module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients
public import Purelib.Polynomial.Dense.Leading
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Exact finite checks for a monic matrix-pencil scalar and its retained inverse -/

public section

namespace Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Preparation

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic (ScaledInverseData)
open Purelib.Polynomial.Dense

variable {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}

set_option genInjectivity false in
/-- The same original polynomial matrix and proposed data with complete products and the actual monic target degree. -/
structure Checked (matrix : Basic.Matrix K n) (data : ScaledInverseData K n) where
  /-- Both original coefficient products were computed and checked on the same retained data. -/
  products : Inverse.Scaled.Coefficients.Products matrix data
  /-- The actual retained scalar is normalized, nonzero and monic at the requested matrix dimension. -/
  leading : Leading.LeadingTerm data.scalar n 1

constructive_injectivity Checked

set_option genInjectivity false in
/-- A proved failed scalar or product condition on this same proposed pencil data.

Each outcome retains the violated condition. Product failures preserve their
actual checked matrices, while scalar failures concern this same original
proposal. None asserts invalidity of the original matrix.
-/
inductive Invalid (matrix : Basic.Matrix K n) (data : ScaledInverseData K n) where
  /-- The proposed scalar has unremoved leading zero coefficients. -/
  | normalization (failed : data.scalar.normalize ≠ data.scalar)
  /-- The proposed scalar is not a nonzero coefficient polynomial. -/
  | zero (failed : data.scalar.isZero ≠ false)
  /-- The actual proposed scalar degree differs from the original matrix dimension. -/
  | degree (failed : data.scalar.natDegree ≠ n)
  /-- The actual proposed leading coefficient differs from one. -/
  | leading (failed : data.scalar.leadingCoeff ≠ 1)
  /-- One complete original coefficient product is invalid. -/
  | products (failure : Inverse.Scaled.Coefficients.Invalid matrix data)

constructive_injectivity Invalid

/-- Check the proposed actual scalar and both original coefficient products without a producer-success hypothesis.

Success retains the complete checked products and the same monic scalar's
actual degree. Failure identifies its original violated condition and permits
a separately certified total fallback on the unchanged matrix.
-/
def check (matrix : Basic.Matrix K n) (data : ScaledInverseData K n) :
    Except (Invalid matrix data) (Checked matrix data) :=
  if normalized : data.scalar.normalize = data.scalar then
    if nonzero : data.scalar.isZero = false then
      if degree : data.scalar.natDegree = n then
        if leading : data.scalar.leadingCoeff = 1 then
          match Inverse.Scaled.Coefficients.check matrix data with
          | .ok products => .ok ⟨products, ⟨normalized, nonzero, degree, leading⟩⟩
          | .error failure => .error (.products failure)
        else .error (.leading leading)
      else .error (.degree degree)
    else .error (.zero nonzero)
  else .error (.normalization normalized)

end Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Preparation

end
