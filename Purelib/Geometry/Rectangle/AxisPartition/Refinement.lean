module

public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitionRestriction
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Polynomial.Geometry.Grid.ClearGrid

/-! # Retained refinement of an actual finite axis partition

The original partition remains an input. The one new finite sorted bank
contains its exact original cut list followed by the additional requests;
its ordered interval decomposition is derived from the original walks.
-/

public section

namespace Purelib.Geometry.Rectangle.AxisPartition

open Purelib
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid.ClearGrid

variable {lower upper : Rational} {cuts : List Rational}

/-- The whole original extended-partition factory result, retaining the actual old partition as input. -/
@[expose] def Refinement (original : AxisPartition lower upper cuts) (additional : List Rational) : Type :=
  {value : AxisPartition lower upper (cuts ++ additional) //
    value = AxisPartition.build lower upper original.proper (cuts ++ additional)}

namespace Refinement

/-- Sort and cache the extended original cut list once. -/
def build (original : AxisPartition lower upper cuts) (additional : List Rational) :
    Refinement original additional :=
  let value := AxisPartition.build lower upper original.proper (cuts ++ additional)
  ⟨value, rfl⟩

variable {original : AxisPartition lower upper cuts} {additional : List Rational}
variable (refined : Refinement original additional)

/-- The complete retained fine partition is the exact extended-cut constructor. -/
theorem factory_eq : refined.val = AxisPartition.build lower upper original.proper (cuts ++ additional) :=
  refined.property

/-- Every original retained coordinate occurs in the new actual partition. -/
theorem original_mem {point : Rational} (member : point ∈ original.coordinates) :
    point ∈ refined.val.coordinates := by
  rcases (original.coordinates_spec point).mp member with first | last | cut
  · exact (refined.val.coordinates_spec point).mpr (Or.inl first)
  · exact (refined.val.coordinates_spec point).mpr (Or.inr (Or.inl last))
  · exact refined.val.cut_mem (List.mem_append_left _ cut.1) cut.2

/-- A coordinate of the singleton refinement is an old retained coordinate or the actual added cut.

The alternatives are geometric coordinate incidence only. They do not
identify any root, primitive, sample or query Owners at repeated points.
-/
theorem singleton_coordinate {original : AxisPartition lower upper cuts} {cut point : Rational}
    (refined : Refinement original [cut]) (member : point ∈ refined.val.coordinates) :
    point ∈ original.coordinates ∨ point = cut := by
  rcases (refined.val.coordinates_spec point).mp member with first | last | added
  · exact Or.inl ((original.coordinates_spec point).mpr (Or.inl first))
  · exact Or.inl ((original.coordinates_spec point).mpr (Or.inr (Or.inl last)))
  · rcases Membership.mem_append.mp added.1 with old | new
    · exact Or.inl (original.cut_mem old added.2)
    · exact Or.inr (Membership.mem_singleton.mp new)

/-- Every in-range additional request is an actual retained coordinate of the fine partition. -/
theorem additional_mem {point : Rational} (member : point ∈ additional)
    (inside : lower ≤ point ∧ point ≤ upper) : point ∈ refined.val.coordinates :=
  refined.val.cut_mem (List.mem_append_right _ member) inside

/-- Both endpoints of each exact original interval remain retained in the fine coordinate bank. -/
theorem interval_endpoints {interval : PreparedAxisPartitions.Interval}
    (member : interval ∈ original.intervals) :
    interval.lower ∈ refined.val.coordinates ∧ interval.upper ∈ refined.val.coordinates := by
  have ends := Interval.endpoints_mem original.coordinates original.ordered (original.intervals_eq ▸ member)
  exact ⟨refined.original_mem ends.1, refined.original_mem ends.2⟩

/-- Fine intervals are the ordered concatenation of the fine subintervals in each original retained interval.

This is a complete list identity, not a coverage, count or width equality.
The original walk keeps the exact coarse order; the fine walk cannot omit
or count an interval twice.
-/
theorem intervals_eq : refined.val.intervals = original.intervals.flatMap (fun interval =>
    refined.val.intervals.filter (fun fine => decide
      (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))) :=
  PreparedAxisPartitionRestriction.intervals_flatMap refined.val original
    (fun _ member => refined.interval_endpoints member)

/-- A strict interior point of an actual original interval is absent from its original retained coordinate bank. -/
theorem interior_not_original {interval : PreparedAxisPartitions.Interval}
    (member : interval ∈ original.intervals) {point : Rational}
    (strict : interval.lower < point ∧ point < interval.upper) : ¬ point ∈ original.coordinates := by
  intro present
  rcases original.coordinate_outside member present with before | after
  · exact (not_lt_of_ge before) strict.1
  · exact (not_lt_of_ge after) strict.2

/-- A new strict interior coordinate cannot be declared retained by the old partition without an original cut. -/
theorem not_original_coordinate {point : Rational} (strict : lower < point ∧ point < upper)
    (absent : ¬ point ∈ cuts) : ¬ point ∈ original.coordinates := by
  intro member
  rcases (original.coordinates_spec point).mp member with first | last | cut
  · exact (ne_of_gt strict.1) first
  · exact (ne_of_lt strict.2) last
  · exact absent cut.1

end Refinement
end Purelib.Geometry.Rectangle.AxisPartition

end
