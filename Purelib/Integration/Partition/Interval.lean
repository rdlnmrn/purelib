module
import Purelib.Data.List.Membership

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Rational endpoint intervals and exact chains

An interval retains two rational endpoints without assuming orientation.
The finite chain between a supplied cut list retains every adjacent endpoint,
with exact length, membership and no-interior-cut certificates.
-/

namespace Purelib.Integration.Partition

open Purelib.Data.List
open Purelib.Data.Rat

public section
@[expose] public section
set_option genInjectivity false in
/-- An ordered pair of rational endpoint readings without an ordering assumption. -/
structure Interval where
  /-- The retained starting endpoint. -/ start : Fraction.Rational
  /-- The retained finishing endpoint. -/ finish : Fraction.Rational
deriving DecidableEq

constructive_injectivity Interval

end

namespace Interval.mk

end Interval.mk

namespace Interval.mk

end Interval.mk

namespace Interval

/-- Require an interval to have positive length inside the closed unit interval.

The starting endpoint is nonnegative, the finishing endpoint is at most one,
and the two retained endpoints are strictly ordered. -/
@[expose] def Valid (interval : Interval) : Prop :=
  0 ≤ interval.start ∧ interval.start < interval.finish ∧ interval.finish ≤ 1

end Interval

namespace Interval

/-- Join the supplied endpoints through every successive retained cut.

Each interval starts where its predecessor finishes. The last interval ends
at the supplied final endpoint, including when the cut list is empty. -/
@[expose] def intervalsBetween (start finish : Fraction.Rational) : List Fraction.Rational → List Interval
  | [] => [⟨start, finish⟩]
  | cut :: tail => ⟨start, cut⟩ :: Purelib.Integration.Partition.Interval.intervalsBetween cut finish tail

end Interval

namespace Interval

/-- An exact endpoint chain connecting the supplied start and finish through the retained interval list.

Consecutive intervals share the same intermediate endpoint; orientation and monotonicity are separate conditions. -/
inductive Chain : Fraction.Rational → Fraction.Rational → List Interval → Prop
  /-- The empty interval list chains a point to itself. -/ | nil (point : Fraction.Rational) :
    Purelib.Integration.Partition.Interval.Chain point point []
  /-- Prepend an interval ending at the exact start of the retained tail chain. -/ | cons {start middle finish :
    Fraction.Rational} {tail : List Interval}
      (rest : Purelib.Integration.Partition.Interval.Chain middle finish tail) :
        Purelib.Integration.Partition.Interval.Chain start finish (⟨start, middle⟩ :: tail)

end Interval

namespace Interval

/-- The intervals between any retained cut list form an exact chain from start to finish. -/
theorem intervalsBetween_chain (start finish : Fraction.Rational) : ∀ cuts,
    Chain start finish (intervalsBetween start finish cuts)
  | [] => .cons (.nil finish)
  | cut :: tail => .cons (Purelib.Integration.Partition.Interval.intervalsBetween_chain cut finish tail)

end Interval

namespace Interval

/-- A cut list produces exactly one more interval than its length. -/
theorem intervalsBetween_length (start finish : Fraction.Rational) : ∀ cuts,
    (intervalsBetween start finish cuts).length = cuts.length + 1
  | [] => rfl
  | cut :: tail => by
      change (intervalsBetween cut finish tail).length + 1 = (tail.length + 1) + 1
      rw [Purelib.Integration.Partition.Interval.intervalsBetween_length]

end Interval

namespace Interval

/-- A common lower bound for the start and all cuts bounds every interval start.

Each starting endpoint is the supplied start or a retained cut. A common
non-strict lower bound is therefore preserved along the exact finite chain. -/
theorem intervalsBetween_lower {bound finish : Fraction.Rational} :
    ∀ {cuts : List Fraction.Rational} {start : Fraction.Rational},
      bound ≤ start → (∀ cut ∈ cuts, bound ≤ cut) →
      ∀ interval ∈ intervalsBetween start finish cuts, bound ≤ interval.start
  | [], start, lower, _, interval, member => by
      have equal : interval = ⟨start, finish⟩ :=
        (Membership.mem_cons.mp member).resolve_right (fun impossible => by nomatch impossible)
      exact equal ▸ lower
  | cut :: tail, start, lower, bounds, interval, member => by
      rcases Membership.mem_cons.mp member with atHead | inTail
      · exact atHead ▸ lower
      · exact Purelib.Integration.Partition.Interval.intervalsBetween_lower (bounds cut List.mem_cons_self)
          (fun other otherMember => bounds other (List.mem_cons_of_mem cut otherMember))
          interval inTail

end Interval

namespace Interval

/-- Every resulting finish endpoint is the supplied final endpoint or a retained cut.

The chain retains the input cut order and uses each cut as an intermediate
finish. Its final interval ends at the supplied final endpoint. -/
theorem intervalsBetween_finish (start finish : Fraction.Rational) : ∀ cuts,
    ∀ interval ∈ intervalsBetween start finish cuts,
      interval.finish = finish ∨ interval.finish ∈ cuts
  | [], interval, member => by
      have equal : interval = ⟨start, finish⟩ :=
        (Membership.mem_cons.mp member).resolve_right (fun impossible => by nomatch impossible)
      exact Or.inl (congrArg Interval.finish equal)
  | cut :: tail, interval, member => by
      rcases Membership.mem_cons.mp member with atHead | inTail
      · exact Or.inr (atHead ▸ List.mem_cons_self)
      · rcases intervalsBetween_finish cut finish tail interval inTail with last | interior
        · exact Or.inl last
        · exact Or.inr (List.mem_cons_of_mem cut interior)

end Interval

namespace Interval

/-- No retained cut lies inside an adjacent interval of a strictly increasing list.

The interval endpoints are consecutive retained cuts or the supplied outer
endpoints. Strict pairwise order excludes every other retained cut from its interior. -/
theorem intervalsBetween_no_cut (start finish : Fraction.Rational) : ∀ {cuts},
    cuts.Pairwise (· < ·) → ∀ {cut}, cut ∈ cuts →
    ∀ {interval}, interval ∈ intervalsBetween start finish cuts →
      ¬(interval.start < cut ∧ cut < interval.finish)
  | [], _, _, member, _, _, _ => by nomatch member
  | head :: tail, sorted, cut, member, interval, inIntervals, between => by
      rcases Membership.mem_cons.mp inIntervals with atHead | inTail
      · have belowHead : cut < head := by simpa only [atHead] using between.2
        rcases Membership.mem_cons.mp member with atCut | cutInTail
        · exact lt_irrefl head (atCut ▸ belowHead)
        · exact lt_asymm belowHead ((List.pairwise_cons.mp sorted).1 cut cutInTail)
      · rcases Membership.mem_cons.mp member with atHead | cutInTail
        · have lower : head ≤ interval.start :=
            intervalsBetween_lower (show head ≤ head from le_rfl)
              (fun other otherMember => ((List.pairwise_cons.mp sorted).1 other otherMember).le)
              interval inTail
          exact (not_lt_of_ge lower) (atHead ▸ between.1)
        · exact Purelib.Integration.Partition.Interval.intervalsBetween_no_cut head finish (List.pairwise_cons.mp
            sorted).2
            cutInTail inTail between

end Interval

end

end Purelib.Integration.Partition
