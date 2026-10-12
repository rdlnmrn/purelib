module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
public import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Protection
public import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RationalFunctions.Winding.Box.Quotient
import Purelib.RootIsolation.Isolation.Coprime.Protection

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RationalFunctions.Winding.Box.Outer
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

namespace Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput
section HigherSquarefreeInput

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The common outer square of a higher squarefree input has quadrupled winding four times the reduced degree
difference. -/
theorem
  commonOuter_rationalWinding_eq_degreeDifference
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    Winding.Box.Basic.rationalQuadrupledWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.commonOuterBox =
      (4 : Int) * input.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.reduction.denominatorReduced.natDegree :=
  input.nonzeroInput.outer_rationalWinding_eq_degreeDifference

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Each protected numerator state has quadrupled quotient winding four.

Its numerator winding is four and its protected denominator winding is zero. -/
theorem
  numeratorState_rationalWinding
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    Winding.Box.Basic.rationalQuadrupledWinding
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      (input.numeratorState index).box = 4 := by
  let track := input.numeratorTrack index
  let state := input.numeratorState index
  have denominatorZero :=
    Isolation.Coprime.Protection.protectedState_rightWinding_zero
      input.numeratorDegreePositive
      input.denominatorDegreePositive input.reduction.coprime
      track track.initial
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      state.box state.proper state.clearance
      (input.numeratorState_denominatorClearance index)
  have denominatorZero' :
      Winding.Box.Basic.quadrupledBoxWinding input.reduction.denominatorReduced state.box = 0 := by
    simpa only [state, Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput.numeratorState] using denominatorZero
  rw [quotient, state.rawWindingFour, denominatorZero']
  ring1

/-- Each protected denominator state has quadrupled quotient winding minus four.

Its denominator winding is four and its protected numerator winding is zero. -/
theorem
  denominatorState_rationalWinding
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    Winding.Box.Basic.rationalQuadrupledWinding
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      (input.denominatorState index).box = -4 := by
  let track := input.denominatorTrack index
  let state := input.denominatorState index
  let symmetric :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      input.reduction.coprime
  have numeratorZero :=
    Isolation.Coprime.Protection.protectedState_rightWinding_zero
      input.denominatorDegreePositive
      input.numeratorDegreePositive symmetric track track.initial
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      state.box state.proper
      (input.denominatorState_numeratorClearance index) state.clearance
  have numeratorZero' :
      Winding.Box.Basic.quadrupledBoxWinding input.reduction.numeratorReduced state.box = 0 := by
    simpa only [state, Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput.denominatorState] using numeratorZero
  rw [quotient, numeratorZero', state.rawWindingFour]
  ring1
end HigherSquarefreeInput

end Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput

end
