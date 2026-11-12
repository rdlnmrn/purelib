module
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed cached children certificate retains structural map composition.
public import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
-- The exposed cached children certificate retains structural attachment readback.
public import Purelib.Data.List.Attach
import Purelib.Data.List.Pairwise
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.Ownership
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Partition.Unit.Normalize
import Purelib.Integration.Partition.Length
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

/-- A common child and its two original occurrence indices determine the entry.

The two indexed lookup certificates fix their respective parents. This
retains the identities of both original partitions and their occurrences.
-/
theorem CommonEntry.eq_of_fields {left right : Normalized} (first second : CommonEntry left right)
    (child : first.child = second.child) (leftIndex : first.leftOwner.index = second.leftOwner.index)
    (rightIndex : first.rightOwner.index = second.rightOwner.index) : first = second := by
  cases first with
  | mk firstChild firstLeft firstRight =>
    cases second with
    | mk secondChild secondLeft secondRight =>
      cases child
      have leftEqual := Ownership.IntervalOwner.eq_of_index_eq firstLeft secondLeft leftIndex
      have rightEqual := Ownership.IntervalOwner.eq_of_index_eq firstRight secondRight rightIndex
      cases leftEqual
      cases rightEqual
      rfl

/-- Decide equality of common entries in the same original pair of partitions. -/
@[expose] def CommonEntry.compare {left right : Normalized} (first second : CommonEntry left right) :
    Decidable (first = second) :=
  if child : first.child = second.child then
    if leftIndex : first.leftOwner.index = second.leftOwner.index then
      if rightIndex : first.rightOwner.index = second.rightOwner.index then
        .isTrue (CommonEntry.eq_of_fields first second child leftIndex rightIndex)
      else .isFalse (fun equal => rightIndex (congrArg (fun entry => entry.rightOwner.index) equal))
    else .isFalse (fun equal => leftIndex (congrArg (fun entry => entry.leftOwner.index) equal))
  else .isFalse (fun equal => child (congrArg CommonEntry.child equal))

set_option genInjectivity false in
/-- A retained common partition whose child entries keep both original interval owners.

The exact ordered child readback is certified equal to the common partition's cached interval list. -/
structure CommonRefinement (left right : Normalized) where
  /-- The retained common unit partition. -/ partition : Normalized
  /-- The ordered common child entries with both original owners. -/ entries : List (CommonEntry left right)
  /-- Reading the entry children returns exactly the retained common partition intervals. -/ children_eq : entries.map
    CommonEntry.child = partition.intervals

constructive_injectivity CommonRefinement

/-- The retained partition and ordered entries determine a common refinement.

The child readback certificate is a proof field; both original parent
partitions remain fixed indices of the compared refinements. -/
theorem CommonRefinement.eq_of_fields {left right : Normalized}
    (first second : CommonRefinement left right)
    (partition : first.partition = second.partition) (entries : first.entries = second.entries) : first = second := by
  cases first with
  | mk firstPartition firstEntries firstChildren =>
    cases second with
    | mk secondPartition secondEntries secondChildren =>
      cases partition
      cases entries
      rfl

/-- Decide equality of common refinements over the same original partitions.

The decision compares retained cuts and ordered entries directly, including
both occurrence indices in every entry; it does not rebuild interval caches. -/
@[expose] def CommonRefinement.compare {left right : Normalized} (first second : CommonRefinement left right) :
    Decidable (first = second) := by
  letI (a b : CommonEntry left right) : Decidable (a = b) := CommonEntry.compare a b
  if cuts : first.partition.cuts = second.partition.cuts then
    if entries : first.entries = second.entries then
      exact .isTrue (CommonRefinement.eq_of_fields first second (Normalized.ext_cuts cuts) entries)
    else
      exact .isFalse (fun equal => entries (congrArg CommonRefinement.entries equal))
  else
    exact .isFalse (fun equal => cuts (congrArg (fun refinement => refinement.partition.cuts) equal))

/-- Retain an already normalized finer partition with each child's two original indexed parents.

Every original cut must occur in the retained child partition. Mapping its
attached interval cache preserves its exact ordered children and both
independently supplied parent partitions. -/
@[expose] def CommonRefinement.ofPartition (left right partition : Normalized)
    (leftIncluded : ∀ cut ∈ left.cuts, cut ∈ partition.cuts)
    (rightIncluded : ∀ cut ∈ right.cuts, cut ∈ partition.cuts) : CommonRefinement left right := by
  let entries : List (CommonEntry left right) := partition.intervals.attach.map fun child =>
    { child := child.val
      leftOwner := left.intervalOwner partition leftIncluded child.val child.property
      rightOwner := right.intervalOwner partition rightIncluded child.val child.property }
  exact
    { partition := partition, entries := entries, children_eq := by
        change (partition.intervals.attach.map _).map CommonEntry.child = partition.intervals
        rw [Map.map_map]
        change partition.intervals.attach.map Subtype.val = partition.intervals
        exact Data.List.attach_map_subtype_val _ }

/-- The original coarse-owner indices increase along an attached finer partition. -/
private theorem attached_owner_pairwise (coarse partition : Normalized)
    (included : ∀ cut ∈ coarse.cuts, cut ∈ partition.cuts) :
    partition.intervals.attach.Pairwise (fun first second =>
      (coarse.intervalOwner partition included first.val first.property).index ≤
        (coarse.intervalOwner partition included second.val second.property).index) := by
  have starts := partition.starts_pairwise
  rw [← Data.List.attach_map_subtype_val partition.intervals] at starts
  have attached := Data.List.Pairwise.pairwise_map.mp starts
  have ordered : ∀ entries : List {interval // interval ∈ partition.intervals},
      entries.Pairwise (fun first second => first.val.start ≤ second.val.start) →
        entries.Pairwise (fun first second =>
          (coarse.intervalOwner partition included first.val first.property).index ≤
            (coarse.intervalOwner partition included second.val second.property).index) := by
    intro entries
    induction entries with
    | nil => intro _; exact List.Pairwise.nil
    | cons first remaining inductionHypothesis =>
        intro pairwise
        have parts := List.pairwise_cons.mp pairwise
        apply List.pairwise_cons.mpr
        constructor
        · intro second member
          exact coarse.intervalOwner_index_mono partition included first.val second.val first.property second.property
            (parts.1 second member)
        · exact inductionHypothesis parts.2
  exact ordered partition.intervals.attach attached

/-- A finer partition's retained left parent indices are nondecreasing in child order. -/
theorem CommonRefinement.ofPartition_left_indices (left right partition : Normalized)
    (leftIncluded : ∀ cut ∈ left.cuts, cut ∈ partition.cuts)
    (rightIncluded : ∀ cut ∈ right.cuts, cut ∈ partition.cuts) :
    (CommonRefinement.ofPartition left right partition leftIncluded rightIncluded).entries.Pairwise
      (fun first second => first.leftOwner.index ≤ second.leftOwner.index) := by
  change (partition.intervals.attach.map _).Pairwise _
  apply Data.List.Pairwise.pairwise_map.mpr
  exact attached_owner_pairwise left partition leftIncluded

/-- A finer partition's retained right parent indices are nondecreasing in child order. -/
theorem CommonRefinement.ofPartition_right_indices (left right partition : Normalized)
    (leftIncluded : ∀ cut ∈ left.cuts, cut ∈ partition.cuts)
    (rightIncluded : ∀ cut ∈ right.cuts, cut ∈ partition.cuts) :
    (CommonRefinement.ofPartition left right partition leftIncluded rightIncluded).entries.Pairwise
      (fun first second => first.rightOwner.index ≤ second.rightOwner.index) := by
  change (partition.intervals.attach.map _).Pairwise _
  apply Data.List.Pairwise.pairwise_map.mpr
  exact attached_owner_pairwise right partition rightIncluded

/-- Compute the common partition and retain every child with its indexed parents in both original partitions. -/
@[expose] def commonRefinement (left right : Normalized) : CommonRefinement left right :=
  CommonRefinement.ofPartition left right (Normalized.common left right)
    (fun _ member => Normalized.mem_common_left left right member)
    (fun _ member => Normalized.mem_common_right left right member)

end

end Purelib.Integration.Partition.Unit.Common
