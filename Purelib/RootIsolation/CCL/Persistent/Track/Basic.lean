module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Persistent CCL observations of one Paper-I winding track

This is the finite request object shared by the box and CCL sides.  Its
numerical component follows one Paper-I winding-one track, so returned boxes
are nested and meet every requested rational diagonal bound.  Its CCL
component is one running redundant arithmetic cursor: later requests append
to the same exposed raw word and refine its quantitative projective cylinder
without restarting the cursor.

Both components retain the same explicit track index and initial isolated
box.  Exact cursor semantics places every admitted projective candidate in
that initial site box.  This is finite site ownership, not an assertion that
an unnamed completed root has been selected.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Track.Basic

set_option genInjectivity false in
/-- Joint finite state of one higher-degree site. -/
structure State
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) where
  /-- The actual retained winding-one state of the original track. -/ numerical : State.WindingOne.Basic.WindingOneState
    p ambient
  /-- The current numerical box refines the original track's initial box. -/ numericalRefinesInitial :
    numerical.box.Refines track.initial.box
  /-- The persistent CCL cursor indexed by the original track process and initial state. -/ cursor :
    Data.CCL.Progressive.Cursor.Request.State
    (Track.Approximation.Process.toProcess track) track.initial

constructive_injectivity State

namespace State

/-- Empty-word persistent state at the displayed initial winding box. -/
@[expose] def initial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) : CCL.Persistent.Track.Basic.State track :=
  { numerical := track.initial
    numericalRefinesInitial := Box.refines_refl track.initial.box
    cursor := Data.CCL.Progressive.Cursor.Request.State.initial
      (Track.Approximation.Process.toProcess track) track.initial }
end State
end Purelib.RootIsolation.CCL.Persistent.Track.Basic

end
