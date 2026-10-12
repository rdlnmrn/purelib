module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.State.WindingOne.Family.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.State.WindingOne.Family.Later
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Purelib.Data.Rat.Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## Persistent later-state provider -/

set_option genInjectivity false in
/-- Finite numerical data supplying one later refinement and one executable
track interface for every state in the winding family. -/
structure LaterStateProvider
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) where
  /-- The actual executable track interface retained for each original state index. -/ trackAt : (index : Fin
    family.boxes.length) → Track.Basic.WindingOneTrack p ambient
  /-- The actual later winding-one state retained at each original family index. -/ laterAt : (index : Fin
    family.boxes.length) → State.WindingOne.Basic.WindingOneState p ambient
  /-- Each retained later box refines its exact original indexed state box. -/ laterRefines : ∀ index,
    (laterAt index).box.Refines (family.stateAtBoxIndex index).box

constructive_injectivity LaterStateProvider

end Boundary

end Purelib.RootIsolation.State.WindingOne.Family.Later

end
