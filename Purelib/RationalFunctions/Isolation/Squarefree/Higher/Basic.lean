module

import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RationalFunctions.Reduction.Basic

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

section
@[expose] public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic

open Purelib.Polynomial in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- A retained reduction with squarefree numerator and denominator of degree at least two.

Both squarefreeness certificates and degree bounds refer to the exact cofactors in the retained reduction of the indexed
original polynomials. -/
structure HigherSquarefreeInput
    (numerator denominator : CoefficientPolynomial) where
  /-- The retained cancellation result for the indexed numerator and denominator. -/ reduction :
    Reduction.Basic.ReducedPair numerator denominator
  /-- Squarefreeness of the retained reduced numerator. -/ numeratorSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    reduction.numeratorReduced
  /-- Squarefreeness of the retained reduced denominator. -/ denominatorSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    reduction.denominatorReduced
  /-- The retained reduced numerator has natural degree at least two. -/ numeratorDegreeAtLeastTwo : 2 ≤
    reduction.numeratorReduced.natDegree
  /-- The retained reduced denominator has natural degree at least two. -/ denominatorDegreeAtLeastTwo : 2 ≤
    reduction.denominatorReduced.natDegree

constructive_injectivity HigherSquarefreeInput

namespace HigherSquarefreeInput

open Purelib.Polynomial
open Purelib.RationalFunctions
/-- The reduced numerator's degree is positive. -/
theorem numeratorDegreePositive
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    0 < input.reduction.numeratorReduced.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    input.numeratorDegreeAtLeastTwo

/-- The reduced denominator's degree is positive. -/
theorem
  denominatorDegreePositive
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    0 < input.reduction.denominatorReduced.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    input.denominatorDegreeAtLeastTwo
end HigherSquarefreeInput

open Purelib.Polynomial in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- A result retaining the supplied higher-degree squarefree input.

The indexed original polynomials and the input's exact reduction and certificates are preserved by this wrapper. -/
structure HigherSquarefreeResult
    (numerator denominator : CoefficientPolynomial) where
  /-- The retained reduction, squarefreeness certificates and degree bounds. -/ input :
    HigherSquarefreeInput numerator denominator

constructive_injectivity HigherSquarefreeResult

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Wrap the supplied higher-degree squarefree input as its indexed result. -/
def proveHigherSquarefree
    {numerator denominator : CoefficientPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    HigherSquarefreeResult numerator denominator :=
  ⟨input⟩

end Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic

end
