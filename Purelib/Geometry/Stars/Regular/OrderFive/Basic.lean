module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Line
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

namespace Purelib.Geometry.Stars.Regular.OrderFive.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A regular star of order five, with the cyclic indexing written out. -/
structure RegularFiveStar (K : Type*) [Algebra.Field.ExplicitField
  K] [DecidableEq K] where
  /-- The displayed line at cyclic index 0. -/ line₀ : Plane.Line K
  /-- The displayed line at cyclic index 1. -/ line₁ : Plane.Line K
  /-- The displayed line at cyclic index 2. -/ line₂ : Plane.Line K
  /-- The displayed line at cyclic index 3. -/ line₃ : Plane.Line K
  /-- The displayed line at cyclic index 4. -/ line₄ : Plane.Line K
  /-- The line at cyclic index 0 has nonzero direction quadrance. -/ line₀NonNull : ¬ line₀.IsNull
  /-- The line at cyclic index 1 has nonzero direction quadrance. -/ line₁NonNull : ¬ line₁.IsNull
  /-- The line at cyclic index 2 has nonzero direction quadrance. -/ line₂NonNull : ¬ line₂.IsNull
  /-- The line at cyclic index 3 has nonzero direction quadrance. -/ line₃NonNull : ¬ line₃.IsNull
  /-- The line at cyclic index 4 has nonzero direction quadrance. -/ line₄NonNull : ¬ line₄.IsNull
  /-- The lines at indices 0 and 1 have nonparallel directions. -/ line₀Line₁Nonparallel : ¬ line₀.Parallel line₁
  /-- The lines at indices 0 and 2 have nonparallel directions. -/ line₀Line₂Nonparallel : ¬ line₀.Parallel line₂
  /-- The lines at indices 0 and 3 have nonparallel directions. -/ line₀Line₃Nonparallel : ¬ line₀.Parallel line₃
  /-- The lines at indices 0 and 4 have nonparallel directions. -/ line₀Line₄Nonparallel : ¬ line₀.Parallel line₄
  /-- The lines at indices 1 and 2 have nonparallel directions. -/ line₁Line₂Nonparallel : ¬ line₁.Parallel line₂
  /-- The lines at indices 1 and 3 have nonparallel directions. -/ line₁Line₃Nonparallel : ¬ line₁.Parallel line₃
  /-- The lines at indices 1 and 4 have nonparallel directions. -/ line₁Line₄Nonparallel : ¬ line₁.Parallel line₄
  /-- The lines at indices 2 and 3 have nonparallel directions. -/ line₂Line₃Nonparallel : ¬ line₂.Parallel line₃
  /-- The lines at indices 2 and 4 have nonparallel directions. -/ line₂Line₄Nonparallel : ¬ line₂.Parallel line₄
  /-- The lines at indices 3 and 4 have nonparallel directions. -/ line₃Line₄Nonparallel : ¬ line₃.Parallel line₄
  /-- Reflecting line 4 in line 0 gives a line equivalent to line 1. -/ reflectAround₀ :
    (Line.reflectLine line₀ line₄ line₀NonNull).Equivalent line₁
  /-- Reflecting line 0 in line 1 gives a line equivalent to line 2. -/ reflectAround₁ :
    (Line.reflectLine line₁ line₀ line₁NonNull).Equivalent line₂
  /-- Reflecting line 1 in line 2 gives a line equivalent to line 3. -/ reflectAround₂ :
    (Line.reflectLine line₂ line₁ line₂NonNull).Equivalent line₃
  /-- Reflecting line 2 in line 3 gives a line equivalent to line 4. -/ reflectAround₃ :
    (Line.reflectLine line₃ line₂ line₃NonNull).Equivalent line₄
  /-- Reflecting line 3 in line 4 gives a line equivalent to line 0. -/ reflectAround₄ :
    (Line.reflectLine line₄ line₃ line₄NonNull).Equivalent line₀

constructive_injectivity RegularFiveStar

namespace RegularFiveStar

variable [DecidableEq K]

/-- The initial adjacent pair for the finite reflection iterator. -/
def initialPair (star :
  RegularFiveStar K) : Iteration.ReflectionPair K where
  previous := star.line₀
  current := star.line₁
  previousNonNull := star.line₀NonNull
  currentNonNull := star.line₁NonNull

/-- The second reflection iterate represents the third displayed star line. -/
theorem lineAtTwo_equivalent (star :
  RegularFiveStar K) :
    (Iteration.reflectionLineAt star.initialPair 2).Equivalent star.line₂ := by
  rw [show (2 : Nat) = 0 + 2 by decide,
    Iteration.reflectionLineAt_succ_succ star.initialPair 0]
  exact star.reflectAround₁

/-- The third reflection iterate represents the fourth displayed star line. -/
theorem lineAtThree_equivalent (star :
  RegularFiveStar K) :
    (Iteration.reflectionLineAt star.initialPair 3).Equivalent star.line₃ := by
  rw [show (3 : Nat) = 1 + 2 by decide,
    Iteration.reflectionLineAt_succ_succ star.initialPair 1]
  have congruent := Line.reflectLine_equivalent_of_equivalent
    (Iteration.reflectionLineAt star.initialPair 2) star.line₂
    (Iteration.reflectionLineAt star.initialPair 1) star.line₁
    (Iteration.reflectionLineAt_nonNull star.initialPair 2) star.line₂NonNull
    star.lineAtTwo_equivalent (Plane.Line.equivalent_refl star.line₁)
  exact Relations.line_equivalent_trans congruent star.reflectAround₂

/-- The fourth reflection iterate represents the fifth displayed star line. -/
theorem lineAtFour_equivalent (star :
  RegularFiveStar K) :
    (Iteration.reflectionLineAt star.initialPair 4).Equivalent star.line₄ := by
  rw [show (4 : Nat) = 2 + 2 by decide,
    Iteration.reflectionLineAt_succ_succ star.initialPair 2]
  have congruent := Line.reflectLine_equivalent_of_equivalent
    (Iteration.reflectionLineAt star.initialPair 3) star.line₃
    (Iteration.reflectionLineAt star.initialPair 2) star.line₂
    (Iteration.reflectionLineAt_nonNull star.initialPair 3) star.line₃NonNull
    star.lineAtThree_equivalent star.lineAtTwo_equivalent
  exact Relations.line_equivalent_trans congruent star.reflectAround₃

/-- The fifth reflection iterate returns to the first displayed star line. -/
theorem lineAtFive_equivalent (star :
  RegularFiveStar K) :
    (Iteration.reflectionLineAt star.initialPair 5).Equivalent star.line₀ := by
  rw [show (5 : Nat) = 3 + 2 by decide,
    Iteration.reflectionLineAt_succ_succ star.initialPair 3]
  have congruent := Line.reflectLine_equivalent_of_equivalent
    (Iteration.reflectionLineAt star.initialPair 4) star.line₄
    (Iteration.reflectionLineAt star.initialPair 3) star.line₃
    (Iteration.reflectionLineAt_nonNull star.initialPair 4) star.line₄NonNull
    star.lineAtFour_equivalent star.lineAtThree_equivalent
  exact Relations.line_equivalent_trans congruent star.reflectAround₄

end RegularFiveStar

/-- The scalar conditions in Theorem 96. -/
def OrderFiveStarParameters : Prop :=
  ∃ root : K, root ≠ 0 ∧ root ^ 2 = 5 ∧ Squares.IsSquare (2 * (5 - root))
end Purelib.Geometry.Stars.Regular.OrderFive.Basic

end
