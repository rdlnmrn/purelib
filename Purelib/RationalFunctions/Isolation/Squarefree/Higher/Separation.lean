module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
import Purelib.RootIsolation.Isolation.Coprime.Separation
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Build
import Purelib.RationalFunctions.Reduction.Coprime
public import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Protection

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

namespace Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
namespace HigherSquarefreeInput

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Refine a denominator track below the numerator-side coprimality margin.

The margin comes from the retained Bézout certificate on the numerator's large square. Its uniform residual radius
controls the denominator refinement; the numerator index is retained in the interface. -/
def denominatorCrossState
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (_numeratorIndex : Fin input.reduction.numeratorReduced.natDegree)
    (denominatorIndex : Fin input.reduction.denominatorReduced.natDegree) :
    State.WindingOne.Basic.WindingOneState
      input.reduction.denominatorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.denominatorReduced) :=
  let track := input.denominatorTrack denominatorIndex
  let margin := Dense.Gaussian.Coprime.Bounds.Box.rightMargin
    input.reduction.coprime
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      input.reduction.numeratorReduced)
  track.refine track.initial
    (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius
      input.reduction.denominatorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.denominatorReduced) margin)
    (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius_pos
      input.reduction.denominatorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.denominatorReduced)
      (Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos input.reduction.coprime
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
          input.reduction.numeratorReduced)))

/-- Protected numerator and sufficiently refined denominator track boxes are separated.

Both finite observations come from the same retained reduced coprimality certificate and their original degree-indexed
tracks. -/
theorem crossSeparated
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (numeratorIndex : Fin input.reduction.numeratorReduced.natDegree)
    (denominatorIndex : Fin input.reduction.denominatorReduced.natDegree) :
    (input.numeratorState numeratorIndex).box.Separated
      (input.denominatorCrossState numeratorIndex denominatorIndex).box := by
  let numeratorTrack := input.numeratorTrack numeratorIndex
  let denominatorTrack := input.denominatorTrack denominatorIndex
  exact
    Isolation.Coprime.Separation.protectedState_separated_uniformlySmallState
      input.numeratorDegreePositive
      input.denominatorDegreePositive input.reduction.coprime
      numeratorTrack numeratorTrack.initial denominatorTrack
      denominatorTrack.initial

end HigherSquarefreeInput

end Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic

end
