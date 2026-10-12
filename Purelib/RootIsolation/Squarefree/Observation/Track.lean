module
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
public import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.Isolation.Coprime.Protection
public import Purelib.RootIsolation.Isolation.Coprime.Protection.Request
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.FTA.Squarefree (BoxResult)

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

/-- Refine the selected original squarefree-factor track to the retained coprime protection radius. -/
def trackState
    {source opposite : CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite)
    (boxes : BoxResult source)
    (index : Fin source.natDegree) :
    State.WindingOne.Basic.WindingOneState source
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox source) :=
  let track := boxes.isolation.trackAt index
  Isolation.Coprime.Protection.protectedState
    input.sourceOppositeCoprime track track.initial

/-- Retain boundary clearance for the opposite polynomial on the exact protected original track box. -/
def trackOppositeClearance
    {source opposite : CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite)
    (boxes : BoxResult source)
    (index : Fin source.natDegree) :
    Clearance.Box.Boundary.Basic.BoundaryClearance opposite
      (input.trackState boxes index).box := by
  let track := boxes.isolation.trackAt index
  exact Isolation.Coprime.Protection.protectedState_rightBoundaryClearance
    index.pos
    input.sourceOppositeCoprime track track.initial

/-- The opposite polynomial has zero raw winding on the selected original protected track box. -/
theorem trackOppositeWinding_zero
    {source opposite : CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite)
    (boxes : BoxResult source)
    (index : Fin source.natDegree) :
    Winding.Box.Basic.quadrupledBoxWinding opposite (input.trackState boxes index).box = 0 := by
  let track := boxes.isolation.trackAt index
  have zero :=
    Isolation.Coprime.Protection.Request.protectedStateAt_rightWinding_zero_of_nonzero
      index.pos
      input.oppositeNonzero input.sourceOppositeCoprime track track.initial
      (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos
        input.sourceOppositeCoprime
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox source)) le_rfl
  simpa only [trackState,
    Isolation.Coprime.Protection.protectedState,
    Isolation.Coprime.Protection.Request.protectedStateAt] using zero
end SquarefreeSideInput

end Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide

end
