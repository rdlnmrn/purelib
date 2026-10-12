module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib

open Purelib.LinearAlgebra

section
section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

set_option genInjectivity false in
/-- A retained polynomial scalar and square inverse matrix of the supplied dimension.

This is executable data; the two-sided scaled identities are certified separately after evaluation or coefficient
comparison. -/
structure Inverse.Scaled.Basic.ScaledInverseData (K : Type*) (n : Nat)
  where
  /-- The retained dense polynomial scalar. -/ scalar : PolynomialMatrix.Basic.Polynomial K
  /-- The retained structural matrix of inverse-entry polynomials. -/ inverse : PolynomialMatrix.Basic.Matrix K n

constructive_injectivity Inverse.Scaled.Basic.ScaledInverseData

end Purelib.LinearAlgebra.PolynomialMatrix

end

end

section
@[expose] public section

/-!
# Resource bounds for displayed fraction-free Bézout cofactors

The separated-Sylvester scalar is only one component of the certificate.
This module also bounds the coefficient slots of every polynomial in the
scaled inverse.  The recurrence is source-only: a Schur round doubles the
matrix slot bound, and unwinding a block adds twice the current bound.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
/-- Retained scaled-inverse data over dense Gaussian rational polynomials. -/
abbrev GaussianScaledInverseData
  (count : Nat) :=
  ScaledInverseData Data.Gaussian.Basic.Number count

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
end
