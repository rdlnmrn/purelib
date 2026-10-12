module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free exact finite isolation

A finite list of clear constructive-rational regions carries an exact raw
winding total.  Each step selects the first positive region, extracts one
strictly interior Newton band of raw winding four, and replaces the region by
the eight clear cells of its complement.  Global nonnegativity makes exactly
`count` such steps possible when the initial raw winding is `4 * count`.
-/

namespace Purelib.RootIsolation.Track.Separation.Basic

/-- The original initial boxes of two winding-one tracks are positively separated. -/
def trackSeparated
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (left right : Track.Basic.WindingOneTrack p ambient) : Prop :=
  left.initial.box.Separated right.initial.box

/-- Separation of the original track boxes is symmetric. -/
theorem trackSeparated_symm
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {left right : Track.Basic.WindingOneTrack p ambient}
    (separated : trackSeparated left right) : trackSeparated right left :=
  Box.separated_symm separated
end Purelib.RootIsolation.Track.Separation.Basic

end
