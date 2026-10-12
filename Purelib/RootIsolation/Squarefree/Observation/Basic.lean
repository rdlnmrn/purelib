module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
public import Purelib.RootIsolation.FTA.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

section

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

namespace Purelib.RootIsolation.Squarefree.Observation.Basic

set_option genInjectivity false in
/-- A squarefree side has no sites when constant, one exact displayed
Gaussian-rational site when linear, or a degree-indexed shrinking family in
higher degree. -/
inductive SquarefreeObservation
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite) : Type where
  /-- The original squarefree side polynomial has degree zero. -/ | constant (degreeZero : source.natDegree = 0)
  /-- An exact root of the original degree-one side, with the opposite polynomial nonzero at that same point. -/ | exact
      (root : Dense.Gaussian.Roots.Certificate.ExactRoot source)
      (degreeOne : source.natDegree = 1)
      (oppositeAtRoot : opposite.eval root.point ≠ 0)
  /-- The original complete degree-indexed shrinking-box isolation for a side of degree at least two. -/ | higher
      (boxes : FTA.Squarefree.BoxResult source)
      (degreeAtLeastTwo : 2 ≤ source.natDegree)

constructive_injectivity SquarefreeObservation

end Purelib.RootIsolation.Squarefree.Observation.Basic

end

end
