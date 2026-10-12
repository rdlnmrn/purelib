module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
-/

namespace Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Data.Gaussian.Cast (integralGaussian)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- A retained positive lower bound on squared imaginary coordinates.

Every possible value at the selected state has imaginary square at least the square of the positive gap. This unsigned
condition chooses neither an imaginary sign nor a square root. -/
structure Separation (tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
  where
  /-- The exact process state whose possible values satisfy the squared lower bound. -/ state : tau.name.process.State
  /-- The retained rational magnitude of the imaginary separation. -/ gap : Fraction.Rational
  /-- The retained separation magnitude is strictly positive. -/ positive : 0 < gap
  /-- Every possible value at the retained state has imaginary square at least the squared gap. -/ squared_lower : ∀
    {value : Gaussian}, tau.name.process.Possible state value → gap ^ 2 ≤ value.im ^ 2

constructive_injectivity Separation

namespace Separation.mk

end Separation.mk

namespace Separation

/-- Rebase the coherent input at the state carrying its imaginary separation certificate. -/
def based {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
  (certificate : Separation tau) :
    Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  tau.based certificate.state

/-- Every value possible at a based state retains the original squared imaginary lower bound. -/
theorem possible_squared_lower {tau
  : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed} (certificate :
    Separation tau)
    (state : certificate.based.name.process.State) {value : Gaussian}
    (possible : certificate.based.name.process.Possible state value) :
    certificate.gap ^ 2 ≤ value.im ^ 2 := certificate.squared_lower (state.persists possible)

/-- Carry an imaginary separation certificate to a state whose possibilities persist at the certified state. -/
def after {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
  (certificate : Separation tau)
    (state : tau.name.process.State)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible state value →
      tau.name.process.Possible certificate.state value) :
        Separation tau :=
  { state := state
    gap := certificate.gap
    positive := certificate.positive
    squared_lower := fun possible => certificate.squared_lower (persists possible) }

end Separation

end Purelib.Approximation.Gaussian.Process.Imaginary

end
