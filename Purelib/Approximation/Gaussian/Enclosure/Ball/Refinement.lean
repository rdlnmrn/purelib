module
import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement
open Purelib.Data.Gaussian.Basic.Canonical

section Ball

/-- Pointwise refinement is the honest order on isolated balls: every reading of the inner ball is also a reading of the
outer ball. -/
def Refines (inner outer :
  Ball) : Prop :=
  ∀ {value : Data.Gaussian.Basic.Canonical}, inner.Contains value → outer.Contains value

/-- Every isolated rational ball refines itself. -/
theorem refines_refl (ball :
  Ball) : Refines ball ball :=
  fun inside => inside

/-- Compose two pointwise refinements of isolated rational balls. -/
theorem refines_trans {inner middle outer :
  Ball}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) :
      Refines inner outer :=
  fun inside => middleOuter (innerMiddle inside)
end Ball
end Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement

end
