module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic

set_option genInjectivity false in
/-- One finite positive enclosure, retained with its exact source state. Only this one positivity witness is needed for
all subsequent integral rows. -/
structure PositiveEnclosure (tau :
  Coherent.CoherentNamed) where
  /-- The original process state whose ball carries the positive enclosure. -/ state : tau.name.process.State
  /-- The retained rational lower bound for imaginary coordinates. -/ lower : Fraction.Rational
  /-- The retained imaginary-coordinate lower bound is strictly positive. -/ positive : 0 < lower
  /-- Every point in the retained source ball has imaginary coordinate at least the displayed lower bound. -/
    inside_lower : forall {value : Data.Gaussian.Basic.Canonical},
    (tau.name.process.ball state).Contains value → lower ≤ value.im

constructive_injectivity PositiveEnclosure

namespace PositiveEnclosure

/-- Restrict the coherent name to the future of the exact state carrying the positive enclosure. -/
def based {tau :
  Coherent.CoherentNamed} (certificate : Approximation.Gaussian.Process.Imaginary.Positive.Basic.PositiveEnclosure tau)
  :
    Coherent.CoherentNamed := tau.based certificate.state

/-- Every possible reading in the based process satisfies the original enclosure's imaginary-coordinate lower bound. -/
theorem possible_lower {tau :
  Coherent.CoherentNamed}
    (certificate : Approximation.Gaussian.Process.Imaginary.Positive.Basic.PositiveEnclosure tau)
    (state : certificate.based.name.process.State) {value : Data.Gaussian.Basic.Canonical}
    (possible : certificate.based.name.process.Possible state value) :
    certificate.lower ≤ value.im :=
  certificate.inside_lower (tau.name.process.possible_inside
    (state.persists possible))

end PositiveEnclosure
end Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic

end
