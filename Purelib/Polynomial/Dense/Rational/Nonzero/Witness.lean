module
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Witness

/-- A finite coefficient-count search supplies one displayed nonzero value
of every represented nonzero coordinate polynomial. -/
def nonzeroParameter (p :
  Dense.Rational.Basic.CoordinatePolynomial) (nonzero : p.isZero = false) :
    Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue p p.natDegree
    (a := 0) (b := 1) (by decide) nonzero (Nat.le_refl _)

/-- The displayed parameter returned by the finite central-third search has nonzero polynomial evaluation. -/
theorem eval_nonzeroParameter
    (p : Dense.Rational.Basic.CoordinatePolynomial) (nonzero : p.isZero = false) :
    p.eval (nonzeroParameter p nonzero) ≠ 0 :=
  (Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec p p.natDegree
    (a := 0) (b := 1) (by decide) nonzero (Nat.le_refl _)).1
end Purelib.Polynomial.Dense.Rational.Nonzero.Witness

end
