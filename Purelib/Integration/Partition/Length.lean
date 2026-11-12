module
public import Purelib.Integration.Partition.Unit.Basic
public import Purelib.Integration.Partition.Ownership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-!
# Exact lengths of rational interval chains

Signed endpoint differences telescope along the retained finite chain. Unit
partitions additionally have positive cell lengths and exact total length one.
-/

public section

namespace Purelib.Integration.Partition.Interval

open Purelib.Data.Rat

/-- The signed difference between the retained finishing and starting endpoints. -/
@[expose] def signedLength (interval : Interval) : Fraction.Rational :=
  interval.finish - interval.start

/-- Sum signed lengths over the original ordered interval occurrences. -/
@[expose] def lengthSum : List Interval → Fraction.Rational
  | [] => 0
  | interval :: remaining => interval.signedLength + lengthSum remaining

/-- A valid unit interval has strictly positive signed length. -/
theorem signedLength_pos {interval : Interval} (valid : interval.Valid) :
    0 < interval.signedLength :=
  Fraction.Order.Arithmetic.sub_pos_direct valid.2.1

/-- The signed lengths of an exact chain telescope to its endpoint difference.

The chain retains the original ordered interval list, including empty and
reversed chains. No ordering hypothesis is needed for the signed identity. -/
theorem Chain.lengthSum {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) : lengthSum intervals = finish - start := by
  induction chain with
  | nil point =>
      change (0 : Fraction.Rational) = point - point
      ring1
  | @cons start middle finish tail rest inductionHypothesis =>
      change (middle - start) + Interval.lengthSum tail = finish - start
      rw [inductionHypothesis]
      ring1

/-- Mapping every endpoint of an exact chain retains the same ordered interval occurrences.

The transformed chain connects the images of the original endpoints. The
endpoint map need not be monotone or injective. -/
theorem Chain.mapEndpoints (map : Fraction.Rational → Fraction.Rational)
    {start finish : Fraction.Rational} {intervals : List Interval} (chain : Chain start finish intervals) :
    Chain (map start) (map finish) (intervals.map (fun interval => ⟨map interval.start, map interval.finish⟩)) := by
  induction chain with
  | nil point => exact .nil (map point)
  | cons rest inductionHypothesis => exact .cons inductionHypothesis

/-- Summing transformed endpoint differences telescopes over the original exact chain. -/
theorem Chain.lengthSum_mapEndpoints (map : Fraction.Rational → Fraction.Rational)
    {start finish : Fraction.Rational} {intervals : List Interval} (chain : Chain start finish intervals) :
    Interval.lengthSum (intervals.map (fun interval => ⟨map interval.start, map interval.finish⟩)) =
      map finish - map start :=
  (chain.mapEndpoints map).lengthSum

/-- In a forward interval chain, its initial endpoint is at most every retained interval start. -/
theorem Chain.start_le_of_ordered {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) :
    (∀ interval ∈ intervals, interval.start ≤ interval.finish) →
      ∀ interval ∈ intervals, start ≤ interval.start := by
  induction chain with
  | nil point =>
      intro _ interval member
      nomatch member
  | @cons start middle finish tail rest inductionHypothesis =>
      intro ordered interval member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with first | later
      · cases first
        exact Fraction.Order.Basic.le_refl _
      · have head := ordered ⟨start, middle⟩ List.mem_cons_self
        have tailOrdered : ∀ other ∈ tail, other.start ≤ other.finish :=
          fun other present => ordered other (List.mem_cons_of_mem _ present)
        exact Fraction.Order.Basic.le_trans _ _ _ head (inductionHypothesis tailOrdered interval later)

/-- The starts of a forward chain are nondecreasing in its original occurrence order. -/
theorem Chain.starts_pairwise {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) :
    (∀ interval ∈ intervals, interval.start ≤ interval.finish) →
      intervals.Pairwise (fun first second => first.start ≤ second.start) := by
  induction chain with
  | nil point =>
      intro _
      exact List.Pairwise.nil
  | @cons start middle finish tail rest inductionHypothesis =>
      intro ordered
      have tailOrdered : ∀ interval ∈ tail, interval.start ≤ interval.finish :=
        fun interval present => ordered interval (List.mem_cons_of_mem _ present)
      apply List.pairwise_cons.mpr
      constructor
      · intro other member
        have head := ordered ⟨start, middle⟩ List.mem_cons_self
        exact Fraction.Order.Basic.le_trans _ _ _ head (rest.start_le_of_ordered tailOrdered other member)
      · exact inductionHypothesis tailOrdered

/-- Distinct intervals in a forward chain have disjoint interiors in their retained order.

Both occurrences belong to the original chain. Ordered endpoints place the
finish of one at or before the start of the other, including shared endpoints. -/
theorem Chain.disjoint_of_ne {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) :
    (∀ interval ∈ intervals, interval.start ≤ interval.finish) →
      ∀ first ∈ intervals, ∀ second ∈ intervals, first ≠ second →
        first.finish ≤ second.start ∨ second.finish ≤ first.start := by
  induction chain with
  | nil point =>
      intro _ first member
      nomatch member
  | @cons start middle finish tail rest inductionHypothesis =>
      intro ordered first firstMember second secondMember distinct
      have tailOrdered : ∀ other ∈ tail, other.start ≤ other.finish :=
        fun other present => ordered other (List.mem_cons_of_mem _ present)
      rcases Purelib.Data.List.Membership.mem_cons.mp firstMember with firstHead | firstTail
      · rcases Purelib.Data.List.Membership.mem_cons.mp secondMember with secondHead | secondTail
        · exact (distinct (firstHead.trans secondHead.symm)).elim
        · cases firstHead
          exact Or.inl (rest.start_le_of_ordered tailOrdered second secondTail)
      · rcases Purelib.Data.List.Membership.mem_cons.mp secondMember with secondHead | secondTail
        · cases secondHead
          exact Or.inr (rest.start_le_of_ordered tailOrdered first firstTail)
        · exact inductionHypothesis tailOrdered first firstTail second secondTail distinct

/-- A strictly forward interval chain has no repeated interval values.

Every later start is at or beyond the first finish, which lies strictly beyond
the first start. The argument follows the retained chain occurrences. -/
theorem Chain.nodup_of_strict {start finish : Fraction.Rational} {intervals : List Interval}
    (chain : Chain start finish intervals) :
    (∀ interval ∈ intervals, interval.start < interval.finish) → intervals.Nodup := by
  induction chain with
  | nil point =>
      intro _
      exact List.Pairwise.nil
  | @cons start middle finish tail rest inductionHypothesis =>
      intro strict
      have tailStrict : ∀ other ∈ tail, other.start < other.finish :=
        fun other present => strict other (List.mem_cons_of_mem _ present)
      have tailOrdered : ∀ other ∈ tail, other.start ≤ other.finish :=
        fun other present => (tailStrict other present).le
      apply List.pairwise_cons.mpr
      constructor
      · intro other member equal
        have lower := rest.start_le_of_ordered tailOrdered other member
        rw [← equal] at lower
        exact (strict ⟨start, middle⟩ List.mem_cons_self).2 lower
      · exact inductionHypothesis tailStrict

/-- Clamp a rational point to the displayed endpoints of an interval. -/
@[expose] def clamp (interval : Interval) (point : Fraction.Rational) : Fraction.Rational :=
  max interval.start (min interval.finish point)

/-- Read the signed length of a child's endpoints after clamping them to the parent. -/
@[expose] def clampedLength (parent child : Interval) : Fraction.Rational :=
  (⟨parent.clamp child.start, parent.clamp child.finish⟩ : Interval).signedLength

/-- Summing clamped lengths agrees with the retained endpoint-chain length sum. -/
theorem sum_clampedLength (parent : Interval) : ∀ children : List Interval,
    (children.map parent.clampedLength).sum = Interval.lengthSum
      (children.map (fun child => ⟨parent.clamp child.start, parent.clamp child.finish⟩))
  | [] => rfl
  | child :: remaining => by
      change parent.clampedLength child + (remaining.map parent.clampedLength).sum =
        parent.clampedLength child + Interval.lengthSum
          (remaining.map (fun other => ⟨parent.clamp other.start, parent.clamp other.finish⟩))
      rw [sum_clampedLength parent remaining]

/-- Clamping preserves weak order of the original rational points. -/
theorem clamp_mono (interval : Interval) {first second : Fraction.Rational} (ordered : first ≤ second) :
    interval.clamp first ≤ interval.clamp second := by
  have inner := Fraction.Order.Basic.min_le_min (Fraction.Order.Basic.le_refl interval.finish) ordered
  exact Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
    (Fraction.Order.Basic.le_trans _ _ _ inner (Fraction.Order.Basic.le_max_right _ _))

/-- Clamping to ordered endpoints produces a point between those endpoints. -/
theorem clamp_bounds (interval : Interval) (ordered : interval.start ≤ interval.finish) (point : Fraction.Rational) :
    interval.start ≤ interval.clamp point ∧ interval.clamp point ≤ interval.finish :=
  ⟨Fraction.Order.Basic.le_max_left _ _,
    Fraction.Order.Basic.max_le ordered (Fraction.Order.Basic.min_le_left _ _)⟩

/-- A forward child's clamped length is nonnegative for any retained parent endpoints. -/
theorem clampedLength_nonnegative (parent child : Interval) (ordered : child.start ≤ child.finish) :
    0 ≤ parent.clampedLength child :=
  Fraction.Order.Arithmetic.sub_nonneg_direct (parent.clamp_mono ordered)

/-- A point inside an ordered interval is unchanged by its endpoint clamp. -/
theorem clamp_inside (interval : Interval) (point : Fraction.Rational)
    (lower : interval.start ≤ point) (upper : point ≤ interval.finish) : interval.clamp point = point := by
  unfold clamp
  rw [Fraction.Order.Basic.min_eq_right upper, Fraction.Order.Basic.max_eq_right lower]

/-- A point at or before an ordered interval is clamped to its start. -/
theorem clamp_before (interval : Interval) (ordered : interval.start ≤ interval.finish)
    (point : Fraction.Rational) (before : point ≤ interval.start) : interval.clamp point = interval.start := by
  unfold clamp
  rw [Fraction.Order.Basic.min_eq_right (Fraction.Order.Basic.le_trans _ _ _ before ordered),
    Fraction.Order.Basic.max_eq_left before]

/-- A point at or after an ordered interval is clamped to its finish. -/
theorem clamp_after (interval : Interval) (ordered : interval.start ≤ interval.finish)
    (point : Fraction.Rational) (after : interval.finish ≤ point) : interval.clamp point = interval.finish := by
  unfold clamp
  rw [Fraction.Order.Basic.min_eq_left after, Fraction.Order.Basic.max_eq_right ordered]

/-- Clamping a child wholly inside its parent retains its exact signed length. -/
theorem clamp_child_length (parent child : Interval) (lower : parent.start ≤ child.start)
    (ordered : child.start ≤ child.finish) (upper : child.finish ≤ parent.finish) :
    (⟨parent.clamp child.start, parent.clamp child.finish⟩ : Interval).signedLength = child.signedLength := by
  have startUpper := Fraction.Order.Basic.le_trans _ _ _ ordered upper
  have finishLower := Fraction.Order.Basic.le_trans _ _ _ lower ordered
  change parent.clamp child.finish - parent.clamp child.start = child.finish - child.start
  rw [parent.clamp_inside child.start lower startUpper, parent.clamp_inside child.finish finishLower upper]

/-- A child ending before its ordered parent has zero clamped length. -/
theorem clamp_child_before (parent child : Interval) (parentOrdered : parent.start ≤ parent.finish)
    (childOrdered : child.start ≤ child.finish) (before : child.finish ≤ parent.start) :
    (⟨parent.clamp child.start, parent.clamp child.finish⟩ : Interval).signedLength = 0 := by
  have startBefore := Fraction.Order.Basic.le_trans _ _ _ childOrdered before
  change parent.clamp child.finish - parent.clamp child.start = 0
  rw [parent.clamp_before parentOrdered child.finish before, parent.clamp_before parentOrdered child.start startBefore]
  ring1

/-- A child starting after its ordered parent has zero clamped length. -/
theorem clamp_child_after (parent child : Interval) (parentOrdered : parent.start ≤ parent.finish)
    (childOrdered : child.start ≤ child.finish) (after : parent.finish ≤ child.start) :
    (⟨parent.clamp child.start, parent.clamp child.finish⟩ : Interval).signedLength = 0 := by
  have finishAfter := Fraction.Order.Basic.le_trans _ _ _ after childOrdered
  change parent.clamp child.finish - parent.clamp child.start = 0
  rw [parent.clamp_after parentOrdered child.finish finishAfter, parent.clamp_after parentOrdered child.start after]
  ring1

end Purelib.Integration.Partition.Interval

namespace Purelib.Integration.Partition.Unit.Normalized

/-- The cached intervals of a normalized unit partition have exact total length one. -/
theorem lengthSum (partition : Normalized) :
    Interval.lengthSum partition.intervals = 1 := by
  have telescope := partition.chain.lengthSum
  change Interval.lengthSum partition.intervals = (1 : Purelib.Data.Rat.Fraction.Rational) - 0 at telescope
  rw [telescope]
  decide

/-- A normalized unit partition retains no duplicate interval values. -/
theorem intervals_nodup (partition : Normalized) : partition.intervals.Nodup :=
  partition.chain.nodup_of_strict (fun interval member => (partition.valid interval member).2.1)

/-- Starts of the original normalized intervals are nondecreasing in their retained order. -/
theorem starts_pairwise (partition : Normalized) :
    partition.intervals.Pairwise (fun first second => first.start ≤ second.start) :=
  partition.chain.starts_pairwise (fun interval member => (partition.valid interval member).2.1.le)

/-- Clamping every unit-partition interval to ordered unit endpoints preserves their signed length.

The retained child occurrences remain in their original order. Their clamped
endpoint differences telescope from the parent's start to its finish,
including when the parent has zero length. -/
theorem clamped_lengthSum_of_bounds (partition : Normalized) (parent : Interval)
    (lower : 0 ≤ parent.start) (ordered : parent.start ≤ parent.finish) (upper : parent.finish ≤ 1) :
    Interval.lengthSum (partition.intervals.map
      (fun child => ⟨parent.clamp child.start, parent.clamp child.finish⟩)) = parent.signedLength := by
  have total := partition.chain.lengthSum_mapEndpoints parent.clamp
  have start := parent.clamp_before ordered 0 lower
  have finish := parent.clamp_after ordered 1 upper
  rw [start, finish] at total
  exact total

/-- Summed clamped lengths of a unit partition recover any ordered unit subinterval's exact length. -/
theorem clampedLength_sum_of_bounds (partition : Normalized) (parent : Interval)
    (lower : 0 ≤ parent.start) (ordered : parent.start ≤ parent.finish) (upper : parent.finish ≤ 1) :
    (partition.intervals.map parent.clampedLength).sum = parent.signedLength :=
  (Interval.sum_clampedLength parent partition.intervals).trans
    (partition.clamped_lengthSum_of_bounds parent lower ordered upper)

/-- Clamping every interval of a unit partition to a valid parent preserves exactly that parent's length. -/
theorem clamped_lengthSum (partition : Normalized) (parent : Interval) (valid : parent.Valid) :
    Interval.lengthSum (partition.intervals.map
      (fun child => ⟨parent.clamp child.start, parent.clamp child.finish⟩)) = parent.signedLength :=
  partition.clamped_lengthSum_of_bounds parent valid.1 valid.2.1.le valid.2.2

end Purelib.Integration.Partition.Unit.Normalized

namespace Purelib.Integration.Partition.Ownership

open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- An owned child has its exact length when clamped to its retained parent. -/
theorem IntervalOwner.clamp_child_length {partition : Unit.Normalized} {child : Interval}
    (owner : IntervalOwner partition.intervals child) (valid : child.Valid) :
    (⟨owner.parent.clamp child.start, owner.parent.clamp child.finish⟩ : Interval).signedLength =
      child.signedLength :=
  owner.parent.clamp_child_length child owner.start_le valid.2.1.le owner.finish_le

/-- Any different parent interval is disjoint from an owned child apart from endpoints. -/
theorem IntervalOwner.other_disjoint {partition : Unit.Normalized} {child : Interval}
    (owner : IntervalOwner partition.intervals child) (other : Interval) (member : other ∈ partition.intervals)
    (distinct : owner.parent ≠ other) : child.finish ≤ other.start ∨ other.finish ≤ child.start := by
  have parentMember := Purelib.Data.List.mem_of_getElem? partition.intervals owner.index owner.parent owner.at_index
  have ordered : ∀ interval ∈ partition.intervals, interval.start ≤ interval.finish :=
    fun interval present => (partition.valid interval present).2.1.le
  rcases partition.chain.disjoint_of_ne ordered owner.parent parentMember other member distinct with before | after
  · exact Or.inl (Fraction.Order.Basic.le_trans _ _ _ owner.finish_le before)
  · exact Or.inr (Fraction.Order.Basic.le_trans _ _ _ after owner.start_le)

/-- A child owned by a different interval contributes zero clamped length to this parent. -/
theorem IntervalOwner.other_clamped_length {partition : Unit.Normalized} {child : Interval}
    (owner : IntervalOwner partition.intervals child) (valid : child.Valid) (other : Interval)
    (member : other ∈ partition.intervals) (distinct : owner.parent ≠ other) :
    (⟨other.clamp child.start, other.clamp child.finish⟩ : Interval).signedLength = 0 := by
  have otherOrdered := (partition.valid other member).2.1.le
  rcases owner.other_disjoint other member distinct with before | after
  · exact other.clamp_child_before child otherOrdered valid.2.1.le before
  · exact other.clamp_child_after child otherOrdered valid.2.1.le after

end Purelib.Integration.Partition.Ownership

end
