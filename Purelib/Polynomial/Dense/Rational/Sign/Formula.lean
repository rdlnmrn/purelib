module

import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.Sign.Atom
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

section

namespace Purelib.Polynomial.Dense.Rational.Sign

set_option genInjectivity false in
/-- Finite Boolean formulas over univariate rational-polynomial atoms. -/
inductive PolynomialFormula where
  /-- The formula that holds at every parameter. -/ | truth
  /-- The formula that holds at no parameter. -/ | falsity
  /-- A single retained polynomial sign test. -/ | atom (value : Dense.Rational.Sign.PolynomialAtom)
  /-- Conjunction of two retained formulas. -/ | and (left right :
    PolynomialFormula)
  /-- Disjunction of two retained formulas. -/ | or (left right :
    PolynomialFormula)
deriving DecidableEq

constructive_injectivity PolynomialFormula

end Purelib.Polynomial.Dense.Rational.Sign

section

namespace Purelib.Polynomial.Dense.Rational.Sign.PolynomialFormula

/-- Interpret a finite polynomial sign formula at a rational parameter.

Truth, falsity, atomic sign tests, conjunction and disjunction retain their ordinary propositional meanings. -/
def Holds : PolynomialFormula →
  Fraction.Rational → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .atom value, parameter => value.Holds parameter
  | .and left right, parameter =>
      left.Holds parameter ∧ right.Holds parameter
  | .or left right, parameter =>
      left.Holds parameter ∨ right.Holds parameter

/-- Decide formula satisfaction by structural recursion through its finite sign tests. -/
def holdsDecidable : (formula :
  PolynomialFormula) →
    (parameter : Fraction.Rational) → Decidable (formula.Holds parameter)
  | .truth, _ => isTrue True.intro
  | .falsity, _ => isFalse id
  | .atom value, parameter => by
      change Decidable (value.Holds parameter)
      exact inferInstance
  | .and left right, parameter =>
      @instDecidableAnd (left.Holds parameter) (right.Holds parameter)
        (holdsDecidable left parameter)
          (holdsDecidable right parameter)
  | .or left right, parameter =>
      @instDecidableOr (left.Holds parameter) (right.Holds parameter)
        (holdsDecidable left parameter)
          (holdsDecidable right parameter)

end Purelib.Polynomial.Dense.Rational.Sign.PolynomialFormula

namespace Purelib.CCL.Boundary.CurveFormula.PolynomialFormula

/-- Use the structural formula evaluator to decide satisfaction at a rational parameter. -/
instance (formula : Dense.Rational.Sign.PolynomialFormula) (parameter : Fraction.Rational) :
    Decidable (formula.Holds parameter) :=
  Dense.Rational.Sign.PolynomialFormula.holdsDecidable formula parameter

end Purelib.CCL.Boundary.CurveFormula.PolynomialFormula

namespace Purelib.Polynomial.Dense.Rational.Sign.PolynomialFormula

/-- List the formula's atom occurrences in left-to-right order, retaining duplicates. -/
def atoms : PolynomialFormula → List
  Dense.Rational.Sign.PolynomialAtom
  | .truth | .falsity => []
  | .atom value => [value]
  | .and left right | .or left right => left.atoms ++ right.atoms

/-- Read the polynomial of each atom occurrence in the formula. -/
def polynomials (formula :
  PolynomialFormula) : List (Dense.Basic.DensePolynomial Fraction.Rational) :=
  formula.atoms.map fun atom => atom.polynomial

end Purelib.Polynomial.Dense.Rational.Sign.PolynomialFormula

end
end

end
