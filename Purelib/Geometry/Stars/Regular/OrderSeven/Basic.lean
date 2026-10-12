module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Plane.Reflection.Iteration
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

namespace Purelib.Geometry.Stars.Regular.OrderSeven.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A regular order-seven star represented by one finite reflection orbit. Pairwise nonparallelism ranges over the
finite type `Fin 7`, and the two closing representatives make the recurrence cyclic. -/
structure RegularSevenStar (K : Type*)
  [Algebra.Field.ExplicitField K]
    [DecidableEq K] where
  /-- The first two non-null lines and their reflection data. -/ initial : Iteration.ReflectionPair K
  /-- Distinct indices among the first seven iterates give nonparallel lines. -/ pairwiseNonparallel :
    ∀ first second : Fin 7, first ≠ second →
      ¬ (Iteration.reflectionLineAt initial first.val).Parallel
        (Iteration.reflectionLineAt initial second.val)
  /-- The seventh iterate is equivalent to the initial previous line. -/ closesAtSeven :
    (Iteration.reflectionLineAt initial 7).Equivalent initial.previous
  /-- The eighth iterate is equivalent to the initial current line. -/ closesAtEight :
    (Iteration.reflectionLineAt initial 8).Equivalent initial.current

constructive_injectivity RegularSevenStar

/-- The scalar conditions printed in Theorem 97. -/
def OrderSevenStarParameters : Prop :=
  ∃ value : K, value ≠ 0 ∧
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ∧
    Squares.IsSquare (value * (1 - value))
end Purelib.Geometry.Stars.Regular.OrderSeven.Basic

end
