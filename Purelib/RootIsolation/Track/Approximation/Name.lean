module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding-one tracks as progressive arithmetic processes

Paper I supplies independently shrinking rational boxes without asserting a
completed root.  This module exposes each such finite track directly through
the CCL-2 squared-error process interface.  The possibility predicate is
the current box predicate itself; no point is selected from an intersection.
-/

namespace Purelib.RootIsolation.Track.Approximation.Name

/-- Arithmetic entry point at any displayed state of the track. -/
def toNamedAt {p :
  CoefficientPolynomial} {ambient :
  Box}
    (track : WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient) :
    Named :=
  { process := Track.Approximation.Process.toProcess track
    state := state }

/-- Arithmetic entry point at the track's initial finite box. -/
def initialNamed {p :
  CoefficientPolynomial}
  {ambient : Box}
    (track : WindingOneTrack p ambient) : Named :=
  toNamedAt track track.initial

/-- Start an arithmetic cursor at one explicitly requested later box of the
winding track.  This is the finite box-descent/CCL handoff used by CCL-2. -/
def refinedNamed
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) : Named :=
  toNamedAt track (track.refine state epsilon positive)
end Purelib.RootIsolation.Track.Approximation.Name

end
