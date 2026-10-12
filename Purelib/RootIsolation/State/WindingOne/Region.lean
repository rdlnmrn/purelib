module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Clearance.Box.Region (ProtectedAmbient)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

section

namespace Purelib.Polynomial.Clearance.Box.Region.ProtectedAmbient

/-- Forget the winding count of an ordinary winding-one state. -/
def ofWindingOne
    {p : CoefficientPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) : ProtectedAmbient p ambient where
  box := state.box
  refinesAmbient := state.refinesAmbient
  proper := state.proper
  clearance := state.clearance

end Purelib.Polynomial.Clearance.Box.Region.ProtectedAmbient

namespace Purelib.RootIsolation.Winding.Residual

/-- Read the protected geometry of a winding-one state, preserving its exact box and clearance. -/
instance {p : CoefficientPolynomial} {ambient : Box} :
    Coe (WindingOneState p ambient) (ProtectedAmbient p ambient) where
  coe := ProtectedAmbient.ofWindingOne

end Purelib.RootIsolation.Winding.Residual

end

end

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

section

namespace Purelib.RootIsolation.State.WindingOne.Region

/-- The residual-localization layer needs only the protected geometry of a
winding-one state, not its winding count. -/
abbrev protectedAmbient
    {p : CoefficientPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) :
    ProtectedAmbient p ambient :=
  ProtectedAmbient.ofWindingOne state

end Purelib.RootIsolation.State.WindingOne.Region

end

end
