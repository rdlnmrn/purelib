module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Partition.Interval
public import Purelib.Integration.Partition.Unit.Normalize
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Content.Normalization.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

/-!
# Retained unit partitions

A unit partition stores its exact normalized cut list and adjacent interval
cache. Its construction derives sortedness, interior bounds, positivity and
endpoint-chain certificates from those retained finite lists.
-/

namespace Purelib.Integration.Partition.Unit

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

public section
namespace Basic

/-- Strict interior cuts form positive-length intervals inside the unit interval.

The supplied endpoints are strictly ordered and satisfy the unit bounds.
Strict pairwise order and interior-cut bounds preserve these conditions along the chain. -/
theorem intervalsBetween_valid {finish : Fraction.Rational} (upper : finish ≤ 1) :
    ∀ {cuts : List Fraction.Rational} {start : Fraction.Rational},
      0 ≤ start → start < finish → cuts.Pairwise (· < ·) →
      (∀ cut ∈ cuts, start < cut ∧ cut < finish) →
      ∀ interval ∈ Interval.intervalsBetween start finish cuts, interval.Valid
  | [], start, nonnegative, ordered, _, _, interval, member => by
      have equal : interval = ⟨start, finish⟩ :=
        (Membership.mem_cons.mp member).resolve_right (fun impossible => by nomatch impossible)
      exact equal ▸ ⟨nonnegative, ordered, upper⟩
  | cut :: tail, start, nonnegative, ordered, sorted, inside, interval, member => by
      have cutBounds := inside cut List.mem_cons_self
      rcases Membership.mem_cons.mp member with atHead | inTail
      · exact atHead ▸ ⟨nonnegative, cutBounds.1, cutBounds.2.le.trans upper⟩
      · exact intervalsBetween_valid upper (nonnegative.trans cutBounds.1.le)
          cutBounds.2 (List.pairwise_cons.mp sorted).2
          (fun other otherMember =>
            ⟨(List.pairwise_cons.mp sorted).1 other otherMember,
              (inside other (List.mem_cons_of_mem cut otherMember)).2⟩)
          interval inTail

end Basic

set_option genInjectivity false in
/-- A normalized unit partition retaining its sorted cuts and exact derived interval list.

Every cut lies strictly between zero and one, and the interval cache is certified equal to the chain between those exact
cuts. -/
structure Normalized where
  /-- The retained normalized rational cuts. -/ cuts : List Fraction.Rational
  /-- The retained cuts are strictly increasing. -/ sorted : cuts.Pairwise (· < ·)
  /-- Every retained cut lies strictly inside the unit interval. -/ inside : ∀ cut ∈ cuts, 0 < cut ∧ cut < 1
  /-- The cached ordered interval list. -/ intervals : List Interval
  /-- The cache is exactly the interval chain between zero, the retained cuts and one. -/ intervals_eq : intervals =
    Interval.intervalsBetween 0 1 cuts

constructive_injectivity Normalized

namespace Normalized

/-- Normalize the supplied cuts once and retain their exact unit-interval chain.

The construction caches the normalized request and its adjacent intervals.
Sortedness, interior bounds and the chain identity refer to those same retained lists. -/
@[expose] def ofRequest (request : List Fraction.Rational) : Normalized :=
  let cuts := Unit.Normalize.normalize request
  { cuts := cuts
    sorted := Unit.Normalize.normalize_sorted request
    inside := fun cut member => ((Unit.Normalize.mem_normalize cut request).mp member).2
    intervals := Interval.intervalsBetween 0 1 cuts
    intervals_eq := rfl }

end Normalized

namespace Normalized

/-- Every retained partition interval has positive length and lies in the closed unit interval. -/
theorem valid (partition : Normalized) : ∀ interval ∈ partition.intervals, interval.Valid := by
  rw [partition.intervals_eq]
  exact Purelib.Integration.Partition.Unit.Basic.intervalsBetween_valid (by decide) (by decide) (by decide)
    partition.sorted partition.inside

end Normalized

namespace Normalized

/-- The exact retained interval list chains zero to one. -/
theorem chain (partition : Normalized) : Interval.Chain 0 1 partition.intervals := by
  rw [partition.intervals_eq]
  exact Interval.intervalsBetween_chain 0 1 partition.cuts

end Normalized

namespace Normalized

/-- The retained partition has one more interval than normalized cuts. -/
theorem length (partition : Normalized) : partition.intervals.length = partition.cuts.length + 1 := by
  rw [partition.intervals_eq, Interval.intervalsBetween_length]

end Normalized

namespace Normalized

/-- Every interval finish is either one or a retained normalized cut. -/
theorem finish_is_cut (partition : Normalized) {interval : Interval}
    (member : interval ∈ partition.intervals) :
    interval.finish = 1 ∨ interval.finish ∈ partition.cuts := by
  rw [partition.intervals_eq] at member
  exact Interval.intervalsBetween_finish 0 1 partition.cuts interval member

end Normalized

namespace Normalized

/-- No retained partition cut lies strictly inside one of its exact intervals. -/
theorem no_cut_inside (partition : Normalized) {cut : Fraction.Rational}
    (cutMember : cut ∈ partition.cuts) {interval : Interval}
    (intervalMember : interval ∈ partition.intervals) :
    ¬(interval.start < cut ∧ cut < interval.finish) := by
  rw [partition.intervals_eq] at intervalMember
  exact Interval.intervalsBetween_no_cut 0 1 partition.sorted cutMember intervalMember

end Normalized

end

end Purelib.Integration.Partition.Unit
