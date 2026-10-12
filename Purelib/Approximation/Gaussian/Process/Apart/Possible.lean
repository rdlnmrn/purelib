module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Apart.Possible

set_option genInjectivity false in
/-- A positive lower norm for every candidate admitted by every finite state. Unlike `Process.Apart`, this initially
says nothing about spurious points in the enclosing ball. -/
structure PossibleApart (process :
  Approximation.Gaussian.Process) where
  /-- The retained uniform rational lower bound on possible reading squared norms. -/ lowerSq : Fraction.Rational
  /-- The retained possible-reading lower quadrance is strictly positive. -/ positive : 0 < lowerSq
  /-- Every reading possible at any retained state meets the uniform lower quadrance. -/ lower : ∀ (state :
    process.State) {value : Data.Gaussian.Basic.Canonical},
    process.Possible state value → lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value

constructive_injectivity PossibleApart

namespace PossibleApart

/-- One twelfth of the retained possible-reading lower quadrance is positive. -/
theorem twelfth_pos {process :
  Approximation.Gaussian.Process} (apart : Approximation.Gaussian.Process.Apart.Possible.PossibleApart process) :
    0 < apart.lowerSq / 12 :=
  Fraction.Order.Field.div_pos_direct apart.positive (by decide)

/-- One eighth of the retained possible-reading lower quadrance is positive. -/
theorem eighth_pos {process :
  Approximation.Gaussian.Process} (apart : Approximation.Gaussian.Process.Apart.Possible.PossibleApart process) :
    0 < apart.lowerSq / 8 :=
  Fraction.Order.Field.div_pos_direct apart.positive (by decide)

end PossibleApart
end Purelib.Approximation.Gaussian.Process.Apart.Possible

end
