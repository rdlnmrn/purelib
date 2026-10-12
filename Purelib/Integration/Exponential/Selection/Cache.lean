module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Exponential.Geometry.Policy
public import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Partition.QuadraticWeight.Cache

open Purelib.Data.Nat.Schedule (PositiveStride)
open Purelib.Integration.Exponential.Geometry (Policy)

open Purelib.Integration.Exponential (Selection)

open Purelib.Integration

/-!
# Retained finite exponential selection and observations

The original ordered geometry, positive-stride requests and polynomial depth
remain attached to their cached values and exact scalar readback certificates.
-/

public section
namespace Purelib.Integration.Exponential.Selection.Cache

open Purelib.Data.Nat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Selection
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial

set_option genInjectivity false in
/-- A retained stage index and lazy selection cache certified against the original policy and schedule.

Forcing the stored thunk returns the exact canonical selection at its retained index, preserving the original geometry
and depth owner. -/
structure SelectionCache.Entry (policy : Policy) (schedule :
  PositiveStride) where
  /-- The exact retained stage index of this cache entry. -/ index : Nat
  /-- The lazy cached selection at this original stage index. -/ value : Thunk
    (Selection index)
  /-- Forcing the cache equals the canonical selection for the original policy and schedule. -/ value_eq : value.get =
    Integration.Exponential.Selection.selection policy schedule index

constructive_injectivity SelectionCache.Entry

/-- Create the lazy initial selection entry for the exact original policy and schedule.

The thunk retains the original stage-zero geometry and depth search, with its defining equality to canonical selection.
-/
@[expose] def SelectionCache.first (policy : Policy) (schedule
  : PositiveStride) : SelectionCache.Entry policy schedule :=
  ⟨0, ⟨fun _ => Integration.Exponential.Selection.select schedule (QuadraticWeight.Cache.Geometry.canonical
    (Geometry.Policy.partitions policy 0)) 0 0⟩, rfl⟩

/-- Create the next lazy selection using the exact retained previous entry's cached depth.

The new thunk retains the previous cache and the original policy and schedule; its equality certifies the canonical next
selection. -/
@[expose] def SelectionCache.Entry.next {policy : Policy}
  {schedule : PositiveStride}
    (entry : SelectionCache.Entry policy schedule) : SelectionCache.Entry policy schedule where
  index := entry.index + 1
  value := ⟨fun _ => Integration.Exponential.Selection.select schedule
    (QuadraticWeight.Cache.Geometry.canonical (Geometry.Policy.partitions policy (entry.index + 1)))
    (entry.index + 1) entry.value.get.depth⟩
  value_eq := by
    change Integration.Exponential.Selection.select schedule _ _ entry.value.get.depth =
      Integration.Exponential.Selection.selection policy schedule (entry.index + 1)
    rw [Integration.Exponential.Selection.selection, entry.value_eq]

/-- Retain the requested number of consecutive lazy selection entries starting from the supplied original entry.

Each retained entry is followed by its lazy successor. The original thunk, policy and schedule stay attached to every
entry. -/
@[expose] def SelectionCache.buildPrefix {policy : Policy}
  {schedule : PositiveStride} :
    Nat → SelectionCache.Entry policy schedule → List (SelectionCache.Entry policy schedule)
  | 0, _ => []
  | count + 1, entry => entry :: SelectionCache.buildPrefix count
    entry.next

/-- The constructed selection-cache prefix has exactly the requested entry count.

Each positive count emits exactly one retained head entry before consuming the same count predecessor. -/
theorem SelectionCache.prefix_length {policy : Policy}
  {schedule : PositiveStride}
    (count : Nat) (entry : SelectionCache.Entry policy schedule) :
    (SelectionCache.buildPrefix count entry).length = count := by
  induction count generalizing entry with
  | zero => rfl
  | succ count ih =>
      change (SelectionCache.buildPrefix count entry.next).length + 1 = count + 1
      exact congrArg Nat.succ (ih entry.next)

/-- Use the first cache entry with the requested index, falling back to canonical selection when none matches.

Equality transports only the index of the exact retained thunk value; the original policy and schedule stay fixed. -/
@[expose] def SelectionCache.read (policy : Policy) (schedule
  : PositiveStride) (index : Nat) :
    List (SelectionCache.Entry policy schedule) → Selection index
  | [] => Integration.Exponential.Selection.selection policy schedule index
  | entry :: rest =>
      if same : entry.index = index then same ▸ entry.value.get
      else SelectionCache.read policy schedule index rest

/-- Reading any retained cache list gives the original canonical selection at the requested index.

A matching entry retains its canonical selection specification. Unmatched entries leave the same requested index and
original tail lookup unchanged. -/
theorem SelectionCache.read_eq (policy : Policy) (schedule :
  PositiveStride) (index : Nat)
    (entries : List (SelectionCache.Entry policy schedule)) :
    SelectionCache.read policy schedule index entries = Integration.Exponential.Selection.selection policy
      schedule index := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      unfold SelectionCache.read
      split
      · rename_i same
        cases same
        exact entry.value_eq
      · exact ih

end Purelib.Integration.Exponential.Selection.Cache
end
