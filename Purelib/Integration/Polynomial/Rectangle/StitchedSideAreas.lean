module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic

public import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Path.JoinedTrace
import Purelib.Tactic.Ring

public section

/-! Exact regrouping of cached side areas. The joining chord is retained even
when its two endpoint readings belong to different owners. -/
namespace Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

open scoped Purelib.Data.Nat

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
set_option genInjectivity false in
/-- An area reading with its exact starting and finishing primitive points.

The entry can be joined to another entry by adding the area of the explicit edge between their retained boundary points.
-/
structure Entry where
  /-- The retained Gaussian area reading. -/ area : Basic.Canonical
  /-- The original starting primitive point. -/ start : Stokes.PrimitivePoint
  /-- The original finishing primitive point. -/ finish : Stokes.PrimitivePoint

constructive_injectivity Entry

namespace Entry

/-- Area entries with equal area, start and finish fields are equal. -/
theorem eq_of_fields {first last : Entry} (area : first.area = last.area)
    (start : first.start = last.start) (finish : first.finish = last.finish) : first = last := by
  cases first
  cases last
  cases area
  cases start
  cases finish
  rfl

open Purelib.Topology.Polygon in
/-- Join two entries by adding their areas and the intervening boundary edge, retaining the first start and last finish.

The intervening chord connects the retained finish of the first entry to the retained start of the last. Their
individual area readings and the outer endpoints are preserved. -/
@[expose] def join (first last : Entry) : Entry :=
  ⟨first.area + Stokes.edgeArea first.finish last.start + last.area, first.start, last.finish⟩

/-- Joining retained area entries is associative.

Both parenthesizations retain the same outer endpoints and the same two intervening chords. Only the grouping of their
scalar area sum changes. -/
theorem join_assoc (first middle last : Entry) :
    (first.join middle).join last = first.join (middle.join last) := by
  unfold Entry.join
  congr 1
  ring1

/-- Join an initial area entry with an ordered list of further entries.

Each entry is joined to the assembly of its retained tail. This preserves list order and every intervening boundary
chord. -/
@[expose] def assemble (first : Entry) : List Entry → Entry
  | [] => first
  | next :: rest => first.join (Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas.Entry.assemble next rest)

/-- Assembly retains the initial entry's starting point. -/
theorem assemble_start (first : Entry) (rest : List Entry) :
    (first.assemble rest).start = first.start := by
  cases rest <;> rfl

/-- Joining the first two entries before assembly gives the same retained result.

The same first two area readings and boundary chord occur in both constructions. Associativity retains the remaining
ordered tail. -/
private theorem assemble_join (first next : Entry) (rest : List Entry) :
    (first.join next).assemble rest = first.join (next.assemble rest) := by
  cases rest with
  | nil => rfl
  | cons head tail => exact Entry.join_assoc first next (head.assemble tail)

/-- Assembly over concatenated lists agrees with successive assembly.

The two retained lists are consumed in their original order. The intermediate assembled endpoint supplies exactly the
boundary chord between them. -/
theorem assemble_append (first : Entry) (middle last : List Entry) :
    first.assemble (middle ++ last) = (first.assemble middle).assemble last := by
  induction middle generalizing first with
  | nil => rfl
  | cons next middle ih =>
      change first.join (next.assemble (middle ++ last)) = (first.join (next.assemble middle)).assemble last
      rw [ih, Entry.assemble_join]

/-- Assembling flattened entry blocks agrees with assembling each block first.

Each block retains its initial entry and ordered tail. Assembling its cached entry preserves all chords that occur in
the flattened word. -/
private theorem assemble_blocks (first : Entry) (blocks : List (Entry × List Entry)) :
    first.assemble (blocks.flatMap (fun block => block.1 :: block.2)) =
      first.assemble (blocks.map (fun block => block.1.assemble block.2)) := by
  induction blocks generalizing first with
  | nil => rfl
  | cons block blocks ih =>
      change first.join (block.1.assemble (block.2 ++ blocks.flatMap (fun entry => entry.1 :: entry.2))) =
        first.join ((block.1.assemble block.2).assemble (blocks.map (fun entry => entry.1.assemble entry.2)))
      rw [Entry.assemble_append, ih]

/-- Regrouping the retained tail into explicit blocks preserves the assembled area entry.

The explicit blocks describe the same ordered tail after the retained prefix. Their cached assemblies preserve its outer
endpoints and total area. -/
theorem regroup (first : Entry) (rest : List Entry) (blocks : List (Entry × List Entry)) :
    first.assemble (rest ++ blocks.flatMap (fun block => block.1 :: block.2)) =
      (first.assemble rest).assemble (blocks.map (fun block => block.1.assemble block.2)) := by
  rw [Entry.assemble_append, Entry.assemble_blocks]

/-- Assemble a nonempty indexed family of area entries in its original order.

The zero position supplies the initial entry. The ordered successor positions supply exactly the remaining tail through
the original list-of-functions construction. -/
@[expose] def concatenate {count : Nat} (entries : Fin (count + 1) → Entry) : Entry :=
  (entries 0).assemble (List.ofFn (fun index : Fin count => entries index.succ))

/-- The concatenated entry starts at the original first entry's start. -/
theorem concatenate_start {count : Nat} (entries : Fin (count + 1) → Entry) :
    (Entry.concatenate entries).start = (entries 0).start := Entry.assemble_start _ _

open Purelib.Data.List in
/-- The concatenated entry finishes at the original last entry's finish. -/
theorem concatenate_finish {count : Nat} (entries : Fin (count + 1) → Entry) :
    (Entry.concatenate entries).finish = (entries (Fin.last count)).finish := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold Entry.concatenate
      rw [OfFn.Basic.ofFn_succ]
      exact ih (fun index => entries index.succ)

open Purelib.Algebra in
open Purelib.Data.List in
open Purelib.Topology.Polygon in
/-- The concatenated area equals the finite component-area sum plus every consecutive joining-edge area.

Every retained finite position contributes its original area once. The exact
successor pairs contribute the joining chords between their retained endpoints. -/
theorem concatenate_area {count : Nat} (entries : Fin (count + 1) → Entry) :
    (Entry.concatenate entries).area = FiniteSum.Fin.sumFin (fun index => (entries index).area) +
      FiniteSum.Fin.sumFin (fun index : Fin count => Stokes.edgeArea (entries index.castSucc).finish (entries
        index.succ).start) := by
  induction count with
  | zero =>
      conv_lhs => simp only [Entry.concatenate,
        List.ofFn_zero, Entry.assemble]
      conv_rhs => simp only [FiniteSum.Fin.sumFin_succ]
      conv_rhs => simp only [FiniteSum.Fin.sumFin, List.ofFn_zero,
        List.foldl_nil, add_zero]
  | succ count ih =>
      unfold Entry.concatenate
      rw [OfFn.Basic.ofFn_succ]
      change (entries 0).area + Stokes.edgeArea (entries 0).finish
          ((entries (0 : Fin (count + 1)).succ).assemble
            (List.ofFn (fun index : Fin count => entries index.succ.succ))).start +
        (Entry.concatenate (fun index : Fin (count + 1) => entries index.succ)).area = _
      rw [Entry.assemble_start, ih]
      have zeroCast : (0 : Fin (count + 1)).castSucc = (0 : Fin (count + 2)) := rfl
      simp only [FiniteSum.Fin.sumFin_succ, zeroCast, Fin.castSucc_succ]
      ring1

end Entry
end Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

end
