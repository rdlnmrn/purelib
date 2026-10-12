module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite separation certificates for shrinking tracks

The original polynomial tracks and their displayed current states index the retained refined states. The certificate
concerns either exclusion of the exact point or positive separation of the two retained boxes.
-/

public section

namespace Purelib.RootIsolation.Track.Separation.Coprime.Basic

set_option genInjectivity false in
/-- A finite refined track box that excludes one displayed exact root of a
coprime factor.

The original polynomial tracks and their displayed current states index the retained refined states. The certificate
concerns either exclusion of the exact point or positive separation of the two retained boxes. -/
structure ExactTrackSeparation
    {trackPolynomial exactPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box}
    (track : Basic.WindingOneTrack trackPolynomial ambient)
    (current : State.WindingOne.Basic.WindingOneState trackPolynomial ambient)
    (point : Gaussian.Basic.Canonical) where
  /-- The retained winding-one state excluding the specified exact point. -/ state :
    State.WindingOne.Basic.WindingOneState trackPolynomial ambient
  /-- The specified original point is outside the retained state box. -/ excludes : ¬state.box.Contains point

constructive_injectivity ExactTrackSeparation

set_option genInjectivity false in
/-- Explicit pair-dependent refinements witnessing separation of two
coprime shrinking tracks.  These finite witnesses establish distinct sites;
all later refinements preserve the separation.

The original polynomial tracks and their displayed current states index the retained refined states. The certificate
concerns either exclusion of the exact point or positive separation of the two retained boxes. -/
structure TrackPairSeparation
    {p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {pAmbient qAmbient : Box}
    (pTrack : Basic.WindingOneTrack p pAmbient)
    (pCurrent : State.WindingOne.Basic.WindingOneState p pAmbient)
    (qTrack : Basic.WindingOneTrack q qAmbient)
    (qCurrent : State.WindingOne.Basic.WindingOneState q qAmbient) where
  /-- The retained left polynomial's winding-one state. -/ left :
    State.WindingOne.Basic.WindingOneState p pAmbient
  /-- The retained right polynomial's winding-one state. -/ right :
    State.WindingOne.Basic.WindingOneState q qAmbient
  /-- The two retained boxes are positively separated. -/ separated : left.box.Separated right.box

constructive_injectivity TrackPairSeparation

end Purelib.RootIsolation.Track.Separation.Coprime.Basic

end
