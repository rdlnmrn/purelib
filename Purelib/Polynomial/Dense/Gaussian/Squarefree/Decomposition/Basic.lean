module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# General finite squarefree-factor preprocessing

The executable squarefreeness decision either returns a finite Bézout
certificate or splits the input by its computed nonconstant gcd with the
derivative.  Both displayed factors then have strictly smaller positive
degree.  Recursing on those natural degrees produces a finite occurrence list
of squarefree factors whose evaluated product is the normalized input.

Repeated factors appear as repeated squarefree occurrences at this layer;
the following multiplicity layer canonically groups associates without
creating duplicate root-isolation machines.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree

namespace Decomposition.Basic

set_option genInjectivity false in
/-- One positive-degree squarefree occurrence returned by preprocessing. -/
structure Factor where
  /-- The retained dense Gaussian polynomial for this factor occurrence. -/ polynomial :
    Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The retained factor table has no leading zero coefficients. -/ normalized : polynomial.normalize = polynomial
  /-- The retained factor is nonzero. -/ nonzero : polynomial.isZero = false
  /-- This occurrence has strictly positive degree. -/ degreePositive : 0 < polynomial.natDegree
  /-- The executable squarefree certificate for this exact factor. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial

constructive_injectivity Factor

end Decomposition.Basic

namespace Decomposition.Basic.Factor.mk

end Decomposition.Basic.Factor.mk

namespace Decomposition.Basic.Factor.mk

end Decomposition.Basic.Factor.mk

namespace Decomposition.Basic

/-- Finite product of the displayed squarefree occurrences. -/
@[expose] def factorProduct : List Dense.Gaussian.Squarefree.Decomposition.Basic.Factor →
  Basic.CanonicalCoefficients.CoefficientPolynomial
  | [] => Dense.Basic.DensePolynomial.constant 1
  | factor :: factors => factor.polynomial *
    Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct factors

end Decomposition.Basic

namespace Decomposition.Basic

/-- Evaluating the product of two appended occurrence lists equals the product of their separate evaluations. -/
theorem factorProduct_append_eval (left right : List Dense.Gaussian.Squarefree.Decomposition.Basic.Factor) (point :
  Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct (left ++ right)).eval point =
      (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct left).eval point *
        (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct right).eval point := by
  induction left with
  | nil =>
      simp only [List.nil_append, Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct,
        Dense.Basic.DensePolynomial.eval_constant, one_mul, -eq_self]
      rfl
  | cons factor factors inductionHypothesis =>
      simp only [List.cons_append, Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct,
        Dense.Basic.DensePolynomial.eval_mul,
        inductionHypothesis, -eq_self]
      rw [Gaussian.Basic.mul_assoc]

end Decomposition.Basic

set_option genInjectivity false in
/-- A complete squarefree occurrence decomposition of a normalized positive-
degree polynomial. -/
structure Decomposition (p : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The finite ordered list of squarefree occurrences, retaining repetitions. -/ factors : List
    Dense.Gaussian.Squarefree.Decomposition.Basic.Factor
  /-- The positive-degree decomposition has at least one occurrence. -/ factorsNonempty : factors ≠ []
  /-- The original polynomial evaluation equals the finite product of its retained factor occurrences at every displayed
    point. -/ evalIdentity : ∀ point : Gaussian.Basic.Canonical,
    p.eval point = (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct factors).eval point
  /-- The sum of the original occurrence degrees equals the source polynomial degree. -/ degreeSum : (factors.map fun
    factor => factor.polynomial.natDegree).sum =
    p.natDegree

constructive_injectivity Decomposition

namespace Decomposition.mk

end Decomposition.mk

namespace Decomposition.mk

end Decomposition.mk

end Purelib.Polynomial.Dense.Gaussian.Squarefree

end
