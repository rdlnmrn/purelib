module
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
public import Purelib.RootIsolation.Isolation.Coprime.Protection
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Build
public import Purelib.RationalFunctions.Reduction.Coprime

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

section
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Construct the numerator track state protected from the reduced denominator.

Select the degree-indexed numerator track and refine its initial state with the reduction's retained coprimality
certificate. -/
def numeratorState
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    State.WindingOne.Basic.WindingOneState input.reduction.numeratorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.numeratorReduced) :=
  let track := input.numeratorTrack index
  Isolation.Coprime.Protection.protectedState input.reduction.coprime
    track track.initial

/-- Construct the denominator track state protected from the reduced numerator.

Select the degree-indexed denominator track and refine its initial state using the symmetric retained coprimality
certificate. -/
def denominatorState
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    State.WindingOne.Basic.WindingOneState
      input.reduction.denominatorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.denominatorReduced) :=
  let track := input.denominatorTrack index
  let symmetric :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      input.reduction.coprime
  Isolation.Coprime.Protection.protectedState symmetric track track.initial

/-- Construct the reduced-denominator boundary clearance on the protected numerator state. -/
def
  numeratorState_denominatorClearance
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      input.reduction.denominatorReduced (input.numeratorState index).box := by
  let track := input.numeratorTrack index
  exact Isolation.Coprime.Protection.protectedState_rightBoundaryClearance
    input.numeratorDegreePositive input.reduction.coprime
    track track.initial

/-- Construct the reduced-numerator boundary clearance on the protected denominator state. -/
def
  denominatorState_numeratorClearance
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      input.reduction.numeratorReduced (input.denominatorState index).box := by
  let track := input.denominatorTrack index
  let symmetric :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      input.reduction.coprime
  exact Isolation.Coprime.Protection.protectedState_rightBoundaryClearance
    input.denominatorDegreePositive symmetric track track.initial
end

end HigherSquarefreeInput

end Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput

end
