module
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.Isolation.Coprime.Protection.Request
public import Purelib.RootIsolation.Multiplicity.Site.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.RootIsolation.Multiplicity.Site.Basic.TrackSiteInput

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.RootIsolation

/-- One request no larger than either of the two separately computed
protection radii. -/
@[expose] def protectionRequest
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) : Fraction.Rational :=
  min
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius input.otherCoprime
      input.ambient)
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius
      input.focusOppositeCoprime input.ambient)

/-- The joint focused-site protection request is strictly positive. -/
theorem protectionRequest_pos
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    0 < input.protectionRequest :=
  Fraction.Order.Basic.lt_min
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos input.otherCoprime
      input.ambient)
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos
      input.focusOppositeCoprime input.ambient)

/-- The joint request fits the other-factor protection radius. -/
theorem protectionRequest_le_other
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    input.protectionRequest ≤
      Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius input.otherCoprime
        input.ambient :=
  Fraction.Order.Basic.min_le_left _ _

/-- The joint request fits the opposite-polynomial protection radius. -/
theorem protectionRequest_le_opposite
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    input.protectionRequest ≤
      Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius
        input.focusOppositeCoprime input.ambient :=
  Fraction.Order.Basic.min_le_right _ _

/-- The one jointly protected observation of the focused shrinking track. -/
@[expose] def state
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    State.WindingOne.Basic.WindingOneState input.context.focus.part.polynomial
      input.ambient :=
  Isolation.Coprime.Protection.Request.protectedStateAt input.track input.current
    input.protectionRequest input.protectionRequest_pos

/-- Retain other-factor boundary clearance on the exact jointly protected site box. -/
@[expose] def otherClearance
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Clearance.Box.Boundary.Basic.BoundaryClearance (input.context.otherPolynomial input.decomposition)
      input.state.box :=
  Isolation.Coprime.Protection.Request.protectedStateAt_rightBoundaryClearance
    input.context.focus.degreePositive input.otherCoprime input.track
    input.current input.protectionRequest_pos input.protectionRequest_le_other

/-- Retain opposite-polynomial boundary clearance on the exact jointly protected site box. -/
@[expose] def oppositeClearance
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Clearance.Box.Boundary.Basic.BoundaryClearance opposite input.state.box :=
  Isolation.Coprime.Protection.Request.protectedStateAt_rightBoundaryClearance
    input.context.focus.degreePositive input.focusOppositeCoprime input.track
    input.current input.protectionRequest_pos
    input.protectionRequest_le_opposite

/-- The other factor has zero raw winding on the retained jointly protected site box. -/
theorem otherWinding_zero
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.quadrupledBoxWinding
      (input.context.otherPolynomial input.decomposition) input.state.box = 0 :=
  Isolation.Coprime.Protection.Request.protectedStateAt_rightWinding_zero_of_nonzero
    input.context.focus.degreePositive input.otherNonzero input.otherCoprime
    input.track input.current input.protectionRequest_pos
    input.protectionRequest_le_other

/-- The opposite polynomial has zero raw winding on the retained jointly protected site box. -/
theorem oppositeWinding_zero
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.quadrupledBoxWinding opposite input.state.box = 0 :=
  Isolation.Coprime.Protection.Request.protectedStateAt_rightWinding_zero_of_nonzero
    input.context.focus.degreePositive input.oppositeNonzero
    input.focusOppositeCoprime input.track input.current
    input.protectionRequest_pos input.protectionRequest_le_opposite
end Purelib.RootIsolation.Multiplicity.Site.Basic.TrackSiteInput

end
