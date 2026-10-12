module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RationalFunctions.Winding.Box.Quotient
import Purelib.RootIsolation.FTA.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Squarefree.Observation.Track
import Purelib.Tactic.Ring

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

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- A protected squarefree source track has ordinary quotient winding one.

The source has winding one in its retained box, and its coprime opposite polynomial has winding zero there. -/
theorem trackBoxWinding
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite)
    (boxes : FTA.Squarefree.BoxResult source)
    (index : Fin source.natDegree) :
    Winding.Box.Basic.rationalBoxWinding source opposite
      (input.trackState boxes index).box = 1 := by
  apply Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  let state := input.trackState boxes index
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      source opposite state.box state.proper state.clearance
      (input.trackOppositeClearance boxes index)
  have oppositeZero : Winding.Box.Basic.quadrupledBoxWinding opposite state.box = 0 := by
    simpa only [state] using input.trackOppositeWinding_zero boxes index
  rw [quotient, state.rawWindingFour, oppositeZero]
  ring1

/-- Exchanging source and opposite gives ordinary quotient winding minus one on the same protected squarefree track. -/
theorem trackPoleBoxWinding
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite)
    (boxes : FTA.Squarefree.BoxResult source)
    (index : Fin source.natDegree) :
    Winding.Box.Basic.rationalBoxWinding opposite source
      (input.trackState boxes index).box = -1 := by
  apply Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  let state := input.trackState boxes index
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      opposite source state.box state.proper
      (input.trackOppositeClearance boxes index) state.clearance
  have oppositeZero : Winding.Box.Basic.quadrupledBoxWinding opposite state.box = 0 := by
    simpa only [state] using input.trackOppositeWinding_zero boxes index
  rw [quotient, oppositeZero, state.rawWindingFour]
  ring1

end SquarefreeSideInput

end Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide

end
