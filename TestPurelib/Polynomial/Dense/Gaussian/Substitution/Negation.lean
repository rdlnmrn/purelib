module

import Purelib.Polynomial.Dense.Gaussian.Substitution.Negation
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-! # Degree-generic negative-argument substitution on original coefficient tables -/

namespace TestPurelib.Polynomial.Dense.Gaussian.Substitution.Negation

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Substitution
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)

example (polynomial : CoefficientPolynomial) :
    (Negation.negateVariable polynomial).natDegree = polynomial.natDegree := Negation.natDegree polynomial

example (polynomial : CoefficientPolynomial) (point : Canonical) :
    (Negation.negateVariable polynomial).eval (-point) = polynomial.eval point := Negation.eval_neg polynomial point

/-- Check zero, linear, cubic, quartic and complex nonmonic tables with their exact original argument readings. -/
public def check : IO Unit := do
  let tables : List (List Canonical) :=
    [[], [0], [2], [1, -2], [1, 0, 0, -2], [1, 2, -3, 0, 4], [0, 0, ⟨1, 2⟩, 0, -3],
      [⟨2, -1⟩, 0, ⟨-3, 4⟩, 2, 0, -5, 7]]
  for coefficients in tables do
    let polynomial : CoefficientPolynomial := ⟨coefficients⟩
    let transformed := Negation.negateVariable polynomial
    unless transformed.natDegree = polynomial.natDegree do
      throw (IO.userError "negative-argument substitution changed the original polynomial degree")
    for point in ([0, 1, -2, ⟨1, 2⟩] : List Canonical) do
      unless transformed.eval point = polynomial.eval (-point) ∧
          transformed.eval (-point) = polynomial.eval point do
        throw (IO.userError "negative-argument substitution changed an original scalar readback")
  let cubic : CoefficientPolynomial := ⟨[1, 0, 0, -2]⟩
  unless (Negation.negateVariable cubic).coeffs = [-1, 0, 0, -2] do
    throw (IO.userError "cubic negative-argument substitution lost its actual retained coefficient table")
  System.IO.println "degree-generic negative-argument substitution retains original coefficient and argument readings"

end TestPurelib.Polynomial.Dense.Gaussian.Substitution.Negation
