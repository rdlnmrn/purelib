module
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed cached children certificate retains structural map composition.
public import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
-- The exposed cached children certificate retains structural attachment readback.
public import Purelib.Data.List.Attach
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.Ownership
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Partition.Unit.Normalize
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
public import Purelib.Integration.Partition.Unit.Ownership

/-!
# Common unit-partition refinement with both original owners

The common normalized partition retains each ordered child interval together
with its indexed parents in the two supplied partitions. The refinement caches
these entries and certifies their exact child readback against its interval list.
-/

namespace Purelib.Integration.Partition.Unit.Normalized

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

public section
/-- Normalize the concatenated original cut lists into a common unit partition. -/
@[expose] def common (left right : Normalized) : Normalized := ofRequest
  (left.cuts ++ right.cuts)

/-- Every retained left cut occurs in the common partition. -/
theorem mem_common_left (left right : Normalized) {cut : Fraction.Rational}
    (member : cut ∈ left.cuts) : cut ∈ (common left right).cuts :=
  (Unit.Normalize.mem_normalize cut (left.cuts ++ right.cuts)).mpr
    ⟨Membership.mem_append.mpr (Or.inl member), left.inside cut member⟩

/-- Every retained right cut occurs in the common partition. -/
theorem mem_common_right (left right : Normalized) {cut : Fraction.Rational}
    (member : cut ∈ right.cuts) : cut ∈ (common left right).cuts :=
  (Unit.Normalize.mem_normalize cut (left.cuts ++ right.cuts)).mpr
    ⟨Membership.mem_append.mpr (Or.inr member), right.inside cut member⟩

end

end Purelib.Integration.Partition.Unit.Normalized

namespace Purelib.Integration.Partition.Unit.Common

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

public section
set_option genInjectivity false in
/-- A common child interval with indexed containment certificates in both original partitions. -/
structure CommonEntry (left right : Normalized) where
  /-- The retained common child interval. -/ child : Interval
  /-- The child's indexed parent and containment evidence in the exact left partition. -/ leftOwner :
    Ownership.IntervalOwner left.intervals child
  /-- The child's indexed parent and containment evidence in the exact right partition. -/ rightOwner :
    Ownership.IntervalOwner right.intervals child

constructive_injectivity CommonEntry

set_option genInjectivity false in
/-- A retained common partition whose child entries keep both original interval owners.

The exact ordered child readback is certified equal to the common partition's cached interval list. -/
structure CommonRefinement (left right : Normalized) where
  /-- The retained common unit partition. -/ partition : Normalized
  /-- The ordered common child entries with both original owners. -/ entries : List (CommonEntry left right)
  /-- Reading the entry children returns exactly the retained common partition intervals. -/ children_eq : entries.map
    CommonEntry.child = partition.intervals

constructive_injectivity CommonRefinement

/-- Retain every common child together with its indexed parents in both partitions.

The common partition is constructed once. Mapping its attached interval cache
retains each original child occurrence and both independently supplied parent
partitions, with exact child-list readback proved by structural map composition. -/
@[expose] def commonRefinement (left right : Normalized) : CommonRefinement left right := by
  let partition := Normalized.common left right
  let entries : List (CommonEntry left right) := partition.intervals.attach.map fun child =>
    { child := child.val
      leftOwner := left.intervalOwner partition (fun _ member =>
        Normalized.mem_common_left left right member) child.val child.property
      rightOwner := right.intervalOwner partition (fun _ member =>
        Normalized.mem_common_right left right member) child.val child.property }
  exact
    { partition := partition, entries := entries, children_eq := by
        change (partition.intervals.attach.map _).map CommonEntry.child = partition.intervals
        rw [Map.map_map]
        change partition.intervals.attach.map Subtype.val = partition.intervals
        exact Data.List.attach_map_subtype_val _ }

end

end Purelib.Integration.Partition.Unit.Common
