module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace Purelib.Approximation.Gaussian

/-! ## Stateful progressive names

`Name` above isolates the quantitative calculation.  The stateful interface
below also records persistence.  Its `Possible` predicate is local to one
explicit finite state; it does not select a completed value.  Refinement only
has to prove that every later finite possibility was already an earlier one.
This is the invariant needed to keep previously emitted CCL digits valid.
-/

set_option genInjectivity false in
/-- A finite enclosure process with persistent possibilities and terminating refinement.

Each state retains a ball and an actual possible rational witness; refinement preserves earlier possibilities and meets
every positive error request with a uniform centre bound. -/
structure Process where
  /-- The finite state type retained by this enclosure process. -/ State : Type
  /-- The rational ball observed at each retained state. -/ ball : State → Enclosure.Ball
  /-- The predicate of Gaussian rational readings admitted at a retained state. -/ Possible : State →
    Data.Gaussian.Basic.Canonical → Prop
  /-- An explicit possible Gaussian rational reading at every retained state. -/ witness : (state : State) → { value :
    Data.Gaussian.Basic.Canonical // Possible state value }
  /-- Every possible reading belongs to the ball observed at that same state. -/ possible_inside : ∀ {state : State}
    {value : Data.Gaussian.Basic.Canonical},
    Possible state value → (ball state).Contains value
  /-- Refine a retained state for a displayed positive squared-error target. -/ refine : (state : State) → (target :
    Fraction.Rational) → 0 < target → State
  /-- Every possible reading after refinement was possible at the original state. -/ refine_persists : ∀ (state : State)
    (target : Fraction.Rational)
      (positive : 0 < target) {value : Data.Gaussian.Basic.Canonical},
    Possible (refine state target positive) value → Possible state value
  /-- The refined state's ball has squared radius strictly below the requested target. -/ accurate : ∀ (state : State)
    (target : Fraction.Rational)
      (positive : 0 < target),
    (ball (refine state target positive)).radiusSq < target
  /-- The retained uniform rational upper bound on squared centre norms. -/ centerBound : Fraction.Rational
  /-- The retained uniform centre bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every retained state's ball centre meets the uniform squared-norm bound. -/ center_bounded : ∀ (state : State),
    Data.Gaussian.Norm.Basic.normSq (ball state).center ≤ centerBound

constructive_injectivity Process

namespace Process.mk

end Process.mk

namespace Process

/-- A finite exact rational name. This constructor is intentionally about a displayed Gaussian rational, not an asserted
non-rational completed root. -/
def exact (value : Data.Gaussian.Basic.Canonical) :
  Process where
  State := Unit
  ball _ :=
    { center := value
      radiusSq := 0
      radiusSq_nonneg := le_rfl }
  Possible _ candidate := candidate = value
  witness _ := ⟨value, rfl⟩
  possible_inside := by
    intro _state candidate equal
    subst candidate
    unfold Purelib.Approximation.Gaussian.Enclosure.Ball.Contains
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
  refine _ _ _ := ()
  refine_persists := by
    intro _state _target _positive candidate equal
    exact equal
  accurate := by
    intro _state _target positive
    exact positive
  centerBound := Data.Gaussian.Norm.Basic.normSq value
  centerBound_nonneg := Data.Gaussian.Norm.Basic.normSq_nonneg value
  center_bounded := by intro _state; exact le_rfl
end Process

end Purelib.Approximation.Gaussian

end

section
section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

section Purelib.CCL.Translation
open Purelib.Data.Gaussian

section Ball
end Ball
end Purelib.CCL.Translation

end

end
