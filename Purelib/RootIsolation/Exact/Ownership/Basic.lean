module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Retained owner selection for an exact root partition

An owner selection keeps the actual finite index in the original partition
and a strict-interior certificate for the supplied track's assignment-radius
refinement. Both the partition output and that exact refinement remain the
indices of the certificate.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Basic

set_option genInjectivity false in
/-- An original partition-track index containing the supplied track's ownership-radius refinement.

The retained strict-interior certificate uses the partition's computed positive assignment radius and that exact track
refinement. -/
public structure OwnerSelection
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (track : Track.Basic.WindingOneTrack p ambient)
      where
  /-- The actual index of the selected original partition track. -/ owner : Fin output.tracks.length
  /-- The supplied track's assignment-radius refinement lies strictly inside the selected original owner box. -/ strict
    :
    let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
    let refined := track.refine track.initial radius
      (Exact.Ownership.Radius.assignmentRadius_pos p ambient output)
    refined.box.StrictInterior (output.tracks.get owner).initial.box

set_option cleanup.letToHave false in
constructive_injectivity OwnerSelection

end Purelib.RootIsolation.Exact.Ownership.Basic
