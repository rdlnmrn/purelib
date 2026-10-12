module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Parity
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Rational.Pair.Path.NoCommonZero
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

/-- Twice the Cauchy index carried by one oriented polynomial edge. -/
def doubledWinding (edge :
  PolynomialEdge) : Int :=
  Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 edge.realPart edge.imagPart
    edge.start edge.stop

/-- Reversing the displayed edge negates its doubled winding. -/
@[simp] theorem doubledWinding_reverse
    (edge : PolynomialEdge) :
    edge.reverse.doubledWinding = -edge.doubledWinding := by
  exact Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse edge.realPart edge.imagPart
    edge.start edge.stop

/-- Doubled winding adds over consecutive restrictions of the same polynomial edge. -/
theorem doubledWinding_restrict_add
    (edge : PolynomialEdge) (a b c : Fraction.Rational) :
    (edge.restrict a b).doubledWinding +
        (edge.restrict b c).doubledWinding =
      (edge.restrict a c).doubledWinding := by
  exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add
    edge.realPart edge.imagPart a b c).symm

/-- A coprime edge has the parity of the difference of its imaginary-coordinate
endpoint-zero flags. -/
theorem doubledWinding_sub_imagZeroFlags_even
    (edge : PolynomialEdge) (coprime : edge.Coprime) :
    Even (edge.doubledWinding -
      ((if edge.imagPart.eval edge.start = 0 then 1 else 0) -
        (if edge.imagPart.eval edge.stop = 0 then 1 else 0))) := by
  exact Dense.Rational.CauchyIndex.Parity.cauchyIndex2_sub_secondZeroFlags_even
    coprime edge.start edge.stop
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

end
