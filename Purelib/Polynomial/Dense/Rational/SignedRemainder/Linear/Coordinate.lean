module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
public import Purelib.Polynomial.Dense.Rational.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

/-!
# Coordinate signed-remainder chains

The original monic coordinate and two-slot rational constant supply exact finite signed-remainder chains. Nonzero
constant coefficients determine the same normalized negated final table.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Coordinate

open Purelib.Data.Rat

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-- The signed remainder chain of the coordinate and a nonzero raw constant is exactly that pair.

The original monic coordinate and nonzero constant form the complete two-entry chain. The retained constant has one
normalized degree slot, so the algorithm stops after these two entries. -/
public theorem signedChain_variable_rawLinearConstant
    {c : Fraction.Rational} (nonzero : c ≠ 0) :
    Basic.Sturm.signedRemainderChain
      Monomial.Coordinate.coordinateVariable (Constants.RawLinear.rawConstant c) =
      [Monomial.Coordinate.coordinateVariable, Constants.RawLinear.rawConstant c] :=
  Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
    (Constants.RawLinear.rawConstant_isZero_false nonzero)
    (Constants.RawLinear.rawConstant_degreeCount nonzero)

/-- A nonzero raw constant followed by the coordinate has a three-entry signed chain.

The final entry is the negated normalized raw constant, retaining the original coefficient representation in the first
entry. -/
public theorem signedChain_rawLinearConstant_variable
    {c : Fraction.Rational} (nonzero : c ≠ 0) :
    Basic.Sturm.signedRemainderChain (⟨[0, c]⟩ : CoordinatePolynomial)
        (⟨[1, 0]⟩ : CoordinatePolynomial) =
      [(⟨[0, c]⟩ : CoordinatePolynomial), (⟨[1, 0]⟩ : CoordinatePolynomial),
        -((⟨[0, c]⟩ : CoordinatePolynomial).normalize)] := by
  change Basic.Sturm.signedRemainderChain
      (Constants.RawLinear.rawConstant c)
      Monomial.Coordinate.coordinateVariable =
    [Constants.RawLinear.rawConstant c,
      Monomial.Coordinate.coordinateVariable,
      -(Constants.RawLinear.rawConstant c).normalize]
  rw [Basic.signedRemainderChain_eq_cons_of_degree_lt
    (p := Constants.RawLinear.rawConstant c)
    (q := Monomial.Coordinate.coordinateVariable)
    (Constants.RawLinear.rawConstant_isZero_false nonzero)
    Monomial.Coordinate.coordinateVariable_isZero_false (by
      have coordinateDegree : Monomial.Coordinate.coordinateVariable.natDegree = 1 :=
        Monomial.Coordinate.coordinateVariable_natDegree
      rw [Constants.RawLinear.rawConstant_natDegree nonzero, coordinateDegree]
      decide)]
  have negativeNonzero :
      (-(Constants.RawLinear.rawConstant c).normalize).isZero = false := by
    rewrite [Basic.DensePolynomial.isZero_neg, Basic.DensePolynomial.isZero_normalize]
    exact Constants.RawLinear.rawConstant_isZero_false nonzero
  have negativeCount :
      (-(Constants.RawLinear.rawConstant c).normalize).degreeCount = 1 := by
    rewrite [Basic.DensePolynomial.degreeCount_neg, Basic.DensePolynomial.degreeCount_normalize]
    exact Constants.RawLinear.rawConstant_degreeCount nonzero
  rw [Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
    (p := Monomial.Coordinate.coordinateVariable)
    (q := -(Constants.RawLinear.rawConstant c).normalize)
    negativeNonzero negativeCount]

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Coordinate
