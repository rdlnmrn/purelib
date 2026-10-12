module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Approximation.Gaussian.Name

set_option genInjectivity false in
/-- Finite positive-real branch information at one displayed input state. -/
structure PositiveReal (input : Gaussian.Name.Basic.Named)
  where
  /-- The retained rational lower bound on possible real coordinates. -/ lower : Fraction.Rational
  /-- The retained real-coordinate lower bound is strictly positive. -/ lowerPositive : 0 < lower
  /-- Every possible reading at the named state is real and meets the retained positive lower bound. -/
    possible_real_lower : ∀ {value : Data.Gaussian.Basic.Canonical},
    input.process.Possible input.state value →
      value.im = 0 ∧ lower ≤ value.re

constructive_injectivity PositiveReal

namespace PositiveReal.mk

end PositiveReal.mk

namespace PositiveReal

/-- Certify the exact positive rational name with that same rational as its retained lower bound. -/
def exact (value : Fraction.Rational)
  (positive : 0 < value) :
    PositiveReal (Named.exact ⟨value, 0⟩) where
  lower := value
  lowerPositive := positive
  possible_real_lower := by
    intro candidate possible
    change candidate = ⟨value, 0⟩ at possible
    rw [possible]
    exact ⟨rfl, le_rfl⟩

end PositiveReal
end Purelib.Approximation.Gaussian.Name

end
