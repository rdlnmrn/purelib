module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Total analysis of a described CCL boundary

Parameterized boundaries are sent directly to the cleared-gcd/Sturm event
classifier.  Finite zero sets are evaluated pointwise, and a universal form
is retained explicitly.  This is the finite dispatch layer between formula
provenance and equality ownership.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation

/-- Exact evaluation decision at one member of a finite atom zero set. -/
inductive PointDecision (p :
  CoefficientPolynomial)
  (point : Gaussian.Basic.Canonical) where
  /-- The displayed point has zero polynomial value. -/ | root (equal : p.eval point = 0)
  /-- The displayed point has nonzero polynomial value. -/ | clear (nonzero : p.eval point ≠ 0)

/-- Decide exactly whether the displayed Gaussian point is a polynomial root.

The result retains either the zero evaluation equality or evidence of a nonzero value. -/
def decidePoint (p :
  CoefficientPolynomial) (point :
  Gaussian.Basic.Canonical) :
    PointDecision p point := by
  if equal : p.eval point = 0 then
    exact .root equal
  else
    exact .clear equal

set_option genInjectivity false in
/-- One point bundled with its exact polynomial-evaluation decision. -/
structure EvaluatedPoint (p :
  CoefficientPolynomial)
  where
  /-- The retained Gaussian evaluation point. -/ point : Gaussian.Basic.Canonical
  /-- The exact evaluation decision for the retained point and original polynomial. -/ decision :
    PointDecision p point

constructive_injectivity EvaluatedPoint

/-- Evaluate a finite list of Gaussian points and retain each exact root-or-clear decision. -/
def evaluatePoints (p :
  CoefficientPolynomial) (points
  : List Gaussian.Basic.Canonical) :
    List (EvaluatedPoint p) :=
  points.map fun point => ⟨point, decidePoint p point⟩
end Purelib.Polynomial.Dense.Gaussian.Evaluation

end
