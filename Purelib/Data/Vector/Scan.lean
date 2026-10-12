module

public import Purelib.Data.Vector.Basic
import Purelib.Data.Fin
meta import Mathlib.Tactic.Linter.Lint
meta import Mathlib.Tactic.TypeStar

public section

/-!
# Cached structural scans for finite grid transport

Shared executable scans for Boolean sheet signs and Gaussian primitive
offsets.  Lookup theorems use finite induction only; the scans materialize
their values instead of storing a function that retraverses a path.
-/

namespace Purelib.Data.Vector.Scan

open Purelib.Data.Vector

/-- The original structural finite-vector carrier as an exact reducible scan alias. -/
abbrev Spine := Vector

variable {Value Edge : Type*}

/-- Materialize the initial state and every successive state along retained structural
edges.

Each step consumes one original edge and stores the preceding state, producing
exactly one more state than edges. -/
@[expose] def scan (step : Value → Edge → Value) (initial : Value) :
    {length : Nat} → Spine Edge length → Spine Value (length + 1)
  | _, .nil => .cons initial .nil
  | _, .cons edge tail => .cons initial (Purelib.Data.Vector.Scan.scan step (step initial edge) tail)

/-- The first stored scan state is the supplied initial state. -/
theorem scan_zero {length : Nat} (step : Value → Edge → Value) (edges : Spine Edge length) (initial : Value) :
    Scan.scan step initial edges 0 = initial := by
  cases edges <;> rfl

/-- Each successor scan entry applies the retained step to its preceding state and edge.

Structural edge induction and the original finite predecessor distinguish the
first step from the unchanged remaining scan. Both lookups retain their exact
input bounds. -/
theorem scan_step {length : Nat} (step : Value → Edge → Value) (edges : Spine Edge length) (initial : Value) (index :
  Fin length) :
    Scan.scan step initial edges index.succ = step (Scan.scan step initial edges index.castSucc) (edges index) := by
  induction edges generalizing initial with
  | nil => exact Fin.elim0 index
  | cons edge tail ih =>
      refine Data.Fin.cases_induction ?_ (fun index => ?_) index
      · exact Scan.scan_zero step tail (step initial edge)
      · exact ih (step initial edge) index

/-- Apply one binary step coordinatewise to two retained equal-length vectors.

Both original spines are consumed together and each output entry is materialized from
the corresponding retained pair. -/
@[expose] def mapWith (step : Value → Edge → Value) :
    {length : Nat} → Spine Value length → Spine Edge length → Spine Value length
  | _, .nil, _ => .nil
  | _, .cons first rest, edges =>
      let paired : Edge × Spine Edge _ :=
        casesOn
          (motive := fun length _ => Nat.casesOn length PUnit (fun size => Edge × Spine Edge size))
          edges PUnit.unit (fun edge tail => (edge, tail))
      .cons (step first paired.1) (Purelib.Data.Vector.Scan.mapWith step rest paired.2)

/-- Coordinatewise lookup applies the step to the original two retained entries.

The two structural spines have the same length. Their head case reads the exact
retained pair, and the successor case transports the original bounded tail lookup. -/
theorem mapWith_apply {length : Nat} (step : Value → Edge → Value)
    (first : Spine Value length) (edges : Spine Edge length) (index : Fin length) :
    Scan.mapWith step first edges index = step (first index) (edges index) := by
  let motive : (length : Nat) → Spine Edge length → Prop := fun length =>
    Nat.casesOn length (fun _ => True)
      (fun size entries =>
        ∀ (head : Value) (tail : Spine Value size),
          (∀ (following : Spine Edge size) (position : Fin size),
            Scan.mapWith step tail following position = step (tail position) (following position)) →
          ∀ position : Fin (size + 1),
            Scan.mapWith step (.cons head tail) entries position =
              step ((cons head tail) position) (entries position))
  have retained : ∀ {length} (entries : Spine Edge length), motive length entries := by
    intro length entries
    refine casesOn (motive := motive) entries True.intro ?_
    intro size edge edges head tail ih index
    refine Data.Fin.cases_induction ?_ (fun index => ?_) index
    · rfl
    · exact ih edges index
  induction first with
  | nil => exact Fin.elim0 index
  | cons head tail ih => exact retained edges head tail ih index

/-- Materialize a sequence of vector states across retained columns of coordinate edges.

Each column updates all rows with mapWith, and every preceding state vector is
stored. The output contains the initial column followed by one state per input edge
column. -/
@[expose] def propagate {height : Nat} (step : Value → Edge → Value) (initial : Spine Value height) :
    {width : Nat} → Spine (Spine Edge height) width → Spine (Spine Value height) (width + 1)
  | _, .nil => .cons initial .nil
  | _, .cons edges tail => .cons initial (Purelib.Data.Vector.Scan.propagate step (Scan.mapWith step initial edges)
    tail)

/-- The first stored propagation column is the original initial vector. -/
theorem propagate_zero {height width : Nat} (step : Value → Edge → Value)
    (initial : Spine Value height) (edges : Spine (Spine Edge height) width) :
    Scan.propagate step initial edges 0 = initial := by
  cases edges <;> rfl

/-- Each propagated successor entry applies the step to the preceding stored entry.

The row edge comes from the same original column and row indices. Column-spine
induction uses the cached coordinatewise next state and the unchanged remaining
columns, preserving every retained finite bound. -/
theorem propagate_step {height width : Nat} (step : Value → Edge → Value)
    (initial : Spine Value height) (edges : Spine (Spine Edge height) width) (column : Fin width) (row : Fin height)
      :
    Scan.propagate step initial edges column.succ row = step (Scan.propagate step initial edges column.castSucc row)
      (edges column row) := by
  induction edges generalizing initial with
  | nil => exact Fin.elim0 column
  | cons edge tail ih =>
      refine Data.Fin.cases_induction ?_ (fun column => ?_) column
      · change Scan.propagate step (Scan.mapWith step initial edge) tail (⟨0, Nat.zero_lt_succ _⟩ : Fin _) row = step
          (initial row) (edge row)
        have first : Scan.propagate step (Scan.mapWith step initial edge) tail
            (⟨0, Nat.zero_lt_succ _⟩ : Fin _) = Scan.mapWith step initial edge := by
          cases tail <;> rfl
        rewrite [first]
        exact Scan.mapWith_apply step initial edge row
      · exact ih (Scan.mapWith step initial edge) column

end Purelib.Data.Vector.Scan

end
