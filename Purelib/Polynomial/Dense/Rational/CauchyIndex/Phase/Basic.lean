module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Sign.CauchyIndex.Phase
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic

/-- Quarter-sector phase of an actual displayed polynomial pair at one
rational parameter. -/
def endpointQuarterPhase
    (R S : CoordinatePolynomial) (x : Fraction.Rational) : Int :=
  Data.Sign.CauchyIndex.Phase.signQuarterPhase
    (Data.Sign.ofCoordinate (R.eval x))
    (Data.Sign.ofCoordinate (S.eval x))

set_option genInjectivity false in
/-- Proof-bearing modulo-four formula on one displayed interval. -/
structure PhaseFormula
    (R S : CoordinatePolynomial) (a b : Fraction.Rational) where
  /-- The retained integral number of full turns in the phase formula. -/ turns : Int
  /-- The doubled Cauchy index is the endpoint quarter-phase difference plus four times the retained turns. -/ index_eq
    : Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S a b =
    endpointQuarterPhase R S b -
      endpointQuarterPhase R S a + 4 * turns

constructive_injectivity PhaseFormula

/-- Adjacent phase formulas telescope at their common rational endpoint. -/
def PhaseFormula.add
    {R S : CoordinatePolynomial} {a b c : Fraction.Rational}
    (left : PhaseFormula R S a b) (right :
      PhaseFormula R S b c) :
    PhaseFormula R S a c where
  turns := left.turns + right.turns
  index_eq := by
    rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add R S a b c,
      left.index_eq, right.index_eq]
    ring1
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Basic

end
