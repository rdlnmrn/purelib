module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
public import Purelib.RootIsolation.FTA.Positive.Build
public import Purelib.RootIsolation.Squarefree.Observation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
namespace SquarefreeSideInput

/-- Observe the original squarefree side of a coprime polynomial pair.

Distinguish constant degree, an exact linear root with opposite-side nonvanishing, and the complete higher-degree box
family. -/
def observe
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite) :
    Squarefree.Observation.Basic.SquarefreeObservation input := by
  by_cases degreeZero : source.natDegree = 0
  · exact .constant degreeZero
  · have degreePositive : 0 < source.natDegree :=
      Nat.pos_of_ne_zero degreeZero
    cases FTA.Positive.Build.provePositive
        { squarefree := input.sourceSquarefree
          degreePositive := degreePositive } with
    | linear root degreeOne =>
        have alternative := input.sourceOppositeCoprime.eval_ne_zero
          root.point
        have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
          rcases alternative with sourceNonzero | oppositeNonzero
          · exact (sourceNonzero root.root).elim
          · exact oppositeNonzero
        exact .exact root degreeOne oppositeAtRoot
    | higher boxes degreeAtLeastTwo =>
        exact .higher boxes degreeAtLeastTwo
end SquarefreeSideInput

end Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide

end
