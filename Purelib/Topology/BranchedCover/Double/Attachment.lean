module

import Purelib.Data.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Explicit hyperelliptic double-cover attaching data

The count-only model is refined here to an actual finite combinatorial
attaching model.  The base sphere is cut along an equatorial polygon.  Every
base edge has two labelled lifts.  Upper-hemisphere boundaries retain the
sheet label; lower-hemisphere boundaries use an explicit alternating sheet
trivialization.  At a ramified vertex the two labels have one common fibre
vertex, while at the unramified even-degree point at infinity they remain
separate.

Each face boundary is represented by a finite cyclic edge family with a
proof that the target of every displayed edge is the source of its successor.
Thus the model carries attaching incidence, not only Euler counts.
-/

namespace Purelib.Topology.BranchedCover.Double.Attachment

open Purelib

/-- Advance one position in a nonempty cyclic range.

Increment a nonterminal index; wrap the final index to zero using the retained positivity proof. -/
@[expose] def cyclicSucc {count : Nat} (positive : 0 < count)
    (index : Fin count) : Fin count :=
  if below : index.val + 1 < count then
    ⟨index.val + 1, below⟩
  else
    ⟨0, positive⟩

/-- The two sheet labels, represented by `Fin 2`. -/
abbrev Sheet := Fin 2

/-- The first sheet label. -/
@[expose] def sheetZero : Sheet := ⟨0, by decide⟩
/-- The second sheet label. -/
@[expose] def sheetOne : Sheet := ⟨1, by decide⟩

/-- Exchange the two sheet labels. -/
@[expose] def toggleSheet (sheet : Sheet) : Sheet :=
  if sheet.val = 0 then Attachment.sheetOne else Attachment.sheetZero

/-- Exchanging sheet zero gives sheet one. -/
theorem toggleSheet_zero : Attachment.toggleSheet
  Attachment.sheetZero = sheetOne := by
  rfl

/-- Exchanging sheet one gives sheet zero. -/
theorem toggleSheet_one : Attachment.toggleSheet
  Attachment.sheetOne = sheetZero := by
  rfl

/-- Every sheet label equals zero or one. -/
theorem sheet_eq_zero_or_one (sheet : Sheet) :
    sheet = Attachment.sheetZero \/ sheet = sheetOne := by
  refine Data.Fin.cases_induction (Or.inl rfl) (fun tail => ?_) sheet
  exact Data.Fin.cases_induction (Or.inr rfl) (fun impossible => Fin.elim0 impossible) tail

/-- Exchanging sheet labels preserves their distinctness. -/
theorem toggleSheet_injective : Function.Injective toggleSheet
  := by
  intro left right equal
  rcases sheet_eq_zero_or_one left with leftZero | leftOne <;>
    rcases sheet_eq_zero_or_one right with rightZero | rightOne
  · exact leftZero.trans rightZero.symm
  · rw [leftZero, rightOne, toggleSheet_zero, toggleSheet_one] at equal
    have valueEqual := congrArg Fin.val equal
    change (1 : Nat) = 0 at valueEqual
    omega0
  · rw [leftOne, rightZero, toggleSheet_one, toggleSheet_zero] at equal
    have valueEqual := congrArg Fin.val equal
    change (0 : Nat) = 1 at valueEqual
    omega0
  · exact leftOne.trans rightOne.symm

/-- Select the base sheet or its complement according to the lift label. -/
@[expose] def selectLift (base lift : Sheet) : Sheet
  :=
  if lift.val = 0 then base else Attachment.toggleSheet base

/-- Equal base sheets give equal selected lifts. -/
theorem selectLift_congr {left right : Sheet} (equal
  : left = right)
    (lift : Sheet) : selectLift left lift = selectLift right lift := by
  subst right
  rfl

/-- Selecting twice with a fixed base sheet recovers the lift label.

For base sheet zero selection is the identity; for base sheet one it exchanges the two labels. -/
theorem selectLift_involutive (base lift : Sheet) :
    selectLift base (selectLift base lift) = lift := by
  rcases sheet_eq_zero_or_one base with rfl | rfl <;>
    rcases sheet_eq_zero_or_one lift with rfl | rfl <;> rfl

set_option genInjectivity false in
/-- A lifted equatorial edge with its base index and sheet label.

The base index lies in the displayed finite range; the sheet distinguishes its two lifts. -/
structure Edge (baseCount : Nat) where
  /-- The bounded index of the underlying base edge. -/ base : Fin baseCount
  /-- The sheet label of this lifted edge. -/ sheet : Sheet

constructive_injectivity Edge

set_option genInjectivity false in
/-- The upper or lower hemisphere of the base sphere. -/
inductive Hemisphere : Type
  /-- The upper hemisphere of the base sphere. -/ | upper
  /-- The lower hemisphere of the base sphere. -/ | lower

constructive_injectivity Hemisphere

set_option genInjectivity false in
/-- A lifted face specified by its hemisphere and lift label.

The two hemisphere choices and two sheet labels distinguish the four lifted faces. -/
structure Face where
  /-- The base hemisphere of this lifted face. -/ hemisphere : Hemisphere
  /-- The sheet label distinguishing the two face lifts. -/ lift : Sheet

constructive_injectivity Face

set_option genInjectivity false in
/-- A finite cyclic edge walk with checked incidence.

A positive base count supplies cyclic succession. The retained edge family projects to each base index, and every edge
finishes where its successor starts. -/
structure CyclicAttachment (baseCount : Nat) (Vertex : Type)
    (edgeStart edgeFinish : Edge baseCount -> Vertex) where
  /-- The base range is nonempty, allowing cyclic succession. -/ basePositive : 0 < baseCount
  /-- The retained lifted edge at each base index. -/ edgeAt : Fin baseCount -> Edge baseCount
  /-- Each retained edge projects to its own index in the base polygon. -/ followsBase : forall index, (edgeAt
    index).base = index
  /-- The finish of each edge equals the start of its cyclic successor. -/ continuous : forall index,
    edgeFinish (edgeAt index) =
      edgeStart (edgeAt (cyclicSucc basePositive index))

constructive_injectivity CyclicAttachment

namespace CyclicAttachment

/-- Materialize the retained cyclic edge family as a finite list. -/
@[expose] def edges {baseCount : Nat} {Vertex :
  Type}
    {edgeStart edgeFinish : Edge baseCount -> Vertex}
    (attachment : CyclicAttachment baseCount Vertex edgeStart edgeFinish) :
    List (Edge baseCount) :=
  List.ofFn attachment.edgeAt

/-- The attaching word contains exactly one edge per base index. -/
@[simp] theorem edges_length {baseCount : Nat}
  {Vertex : Type}
    {edgeStart edgeFinish : Edge baseCount -> Vertex}
    (attachment : CyclicAttachment baseCount Vertex edgeStart edgeFinish) :
    attachment.edges.length = baseCount := by
  exact Data.List.OfFn.Basic.length_ofFn

end CyclicAttachment
end Purelib.Topology.BranchedCover.Double.Attachment

end
