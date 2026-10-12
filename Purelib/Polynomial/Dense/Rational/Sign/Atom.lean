module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.SignTest
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

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
/-- One rational-polynomial sign atom obtained from a Hermitian atom. -/
structure PolynomialAtom where
  /-- The retained rational polynomial whose value is tested. -/ polynomial : Dense.Basic.RationalPolynomial
  /-- The finite sign predicate applied to the polynomial value. -/ sign : Data.Rat.SignTest
deriving DecidableEq

constructive_injectivity PolynomialAtom

end Purelib.Polynomial.Dense.Rational.Sign

section

namespace Purelib.Polynomial.Dense.Rational.Sign.PolynomialAtom

/-- Evaluate the polynomial atom at the displayed rational parameter. -/
def Holds (atom : PolynomialAtom)
  (parameter : Fraction.Rational) : Prop :=
  atom.sign.Holds (atom.polynomial.eval parameter)

end Purelib.Polynomial.Dense.Rational.Sign.PolynomialAtom

namespace Purelib.CCL.Boundary.CurveFormula.PolynomialAtom

/-- Decide a polynomial sign atom by exact rational evaluation and its retained sign test. -/
instance (atom : Dense.Rational.Sign.PolynomialAtom) (parameter : Fraction.Rational) :
    Decidable (atom.Holds parameter) := by
  unfold Dense.Rational.Sign.PolynomialAtom.Holds
  infer_instance

end Purelib.CCL.Boundary.CurveFormula.PolynomialAtom

end
end

end
