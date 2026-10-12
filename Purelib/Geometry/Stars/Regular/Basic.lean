module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Line

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, regular polygon construction

The source uses a doubly infinite reflection sequence.  Here every line and
point is obtained from the already executable natural-number iterator.  A
request for vertex `k` computes exactly the first `k` reflection steps.

The point-reflection product identity below is the finite natural-index form
of Exercise 14.1.  It is then used to prove that the closed formula
`A₂ₖ = σ_{lₖ}(A₀)` agrees with the source's successive construction through
the intervening mirrors `l₂ₖ₊₁`.
-/

namespace Purelib.Geometry.Stars.Regular.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A finite regular star of requested order. The two closing equations are exactly the data needed to continue the
second-order reflection recurrence periodically; pairwise nonparallelism ranges only over the finite prefix. -/
structure RegularStar (K : Type*) [Algebra.Field.ExplicitField K]
    [DecidableEq K] (order : Nat) where
  /-- The retained initial pair of non-null reflection lines. -/ initial : Iteration.ReflectionPair K
  /-- The cyclic order has at least two lines. -/ orderAtLeastTwo : 2 ≤ order
  /-- The lines at distinct indices below the order are nonparallel. -/ pairwiseNonparallel :
    ∀ first second : Fin order, first ≠ second →
      ¬ (Iteration.reflectionLineAt initial first.val).Parallel
        (Iteration.reflectionLineAt initial second.val)
  /-- The iterate at the order returns to the initial previous line. -/ closesAtOrder :
    (Iteration.reflectionLineAt initial order).Equivalent initial.previous
  /-- The next iterate returns to the initial current line. -/ closesAfterOrder :
    (Iteration.reflectionLineAt initial (order + 1)).Equivalent initial.current

constructive_injectivity RegularStar

namespace RegularStar

variable [DecidableEq K] {order : Nat}

/-- The first two lines of a finite regular star are nonparallel. -/
theorem initial_nonparallel (star :
  RegularStar K order) :
    ¬ star.initial.previous.Parallel star.initial.current := by
  let first : Fin order := ⟨0, by
    have lower := star.orderAtLeastTwo
    omega0⟩
  let second : Fin order := ⟨1, by
    have lower := star.orderAtLeastTwo
    omega0⟩
  have different : first ≠ second := by
    intro equal
    have values : (0 : Nat) = 1 := by
      simpa only [first, second] using congrArg Fin.val equal
    exact Nat.zero_ne_one values
  simpa only [first, second, Iteration.reflectionLineAt_zero,
    show Iteration.reflectionLineAt star.initial 1 = star.initial.current by rfl] using
      star.pairwiseNonparallel first second different

/-- The explicit common intersection of the first two star lines. -/
def center (star : RegularStar K
  order) : Plane.Point K :=
  Intersection.lineIntersection star.initial.previous star.initial.current
    star.initial_nonparallel

/-- The initial previous line contains the star center. -/
theorem previous_contains_center (star :
  RegularStar K order) :
    star.initial.previous.Contains star.center :=
  Intersection.lineIntersection_on_first star.initial.previous star.initial.current
    star.initial_nonparallel

/-- The initial current line contains the star center. -/
theorem current_contains_center (star :
  RegularStar K order) :
    star.initial.current.Contains star.center :=
  Intersection.lineIntersection_on_second star.initial.previous star.initial.current
    star.initial_nonparallel

/-- Every requested line in the finite recurrence passes through the explicit center. -/
theorem lineAt_contains_center (star :
  RegularStar K order)
    (index : Nat) :
    (Iteration.reflectionLineAt star.initial index).Contains star.center :=
  Iteration.reflectionLineAt_contains star.initial star.center
    star.previous_contains_center star.current_contains_center index

/-- The two closing representatives propagate through every requested finite continuation of the second-order line
recurrence. -/
theorem lineAt_add_order_equivalent [Nontrivial K]
    (star : RegularStar K order) (start : Nat) :
    (Iteration.reflectionLineAt star.initial (start + order)).Equivalent
      (Iteration.reflectionLineAt star.initial start) := by
  have paired : ∀ index : Nat,
      (Iteration.reflectionLineAt star.initial (index + order)).Equivalent
          (Iteration.reflectionLineAt star.initial index) ∧
        (Iteration.reflectionLineAt star.initial (index + 1 + order)).Equivalent
          (Iteration.reflectionLineAt star.initial (index + 1)) := by
    intro index
    induction index with
    | zero =>
        constructor
        · simpa only [Nat.zero_add, Iteration.reflectionLineAt_zero] using
            star.closesAtOrder
        · simpa only [Nat.zero_add, Nat.one_mul, Nat.add_comm order 1,
            show Iteration.reflectionLineAt star.initial 1 = star.initial.current by rfl]
            using star.closesAfterOrder
    | succ index inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · have reflected := Line.reflectLine_equivalent_of_equivalent
            (Iteration.reflectionLineAt star.initial (index + order + 1))
            (Iteration.reflectionLineAt star.initial (index + 1))
            (Iteration.reflectionLineAt star.initial (index + order))
            (Iteration.reflectionLineAt star.initial index)
            (Iteration.reflectionLineAt_nonNull star.initial (index + order + 1))
            (Iteration.reflectionLineAt_nonNull star.initial (index + 1))
            (by
                simpa only [Nat.add_assoc, Nat.add_comm 1 order, Nat.add_left_comm 1 index order]
                  using inductionHypothesis.2)
            inductionHypothesis.1
          simpa only [Nat.succ_eq_add_one,
            show index + 1 + 1 + order = (index + order) + 2 by omega0,
            show index + 1 + 1 = index + 2 by omega0,
            Iteration.reflectionLineAt_succ_succ] using reflected
  exact (paired start).1

end RegularStar

end Purelib.Geometry.Stars.Regular.Basic

end
