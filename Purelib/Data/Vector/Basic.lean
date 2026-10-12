module

meta import Mathlib.Tactic.TypeStar
meta import Mathlib.Tactic.Linter.Lint
-- Exposed finite lookup and materialization retain direct successor evidence.
public import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.Data

open scoped Purelib.Data.Nat

universe u

set_option genInjectivity false in
/-- Retain a finite vector as a structural spine indexed by its exact natural length.

The empty and cons constructors store each entry directly. Lookup follows the
displayed spine and index without identifying vectors with functions. -/
inductive Vector (K : Type u) : Nat → Type u
  /-- The structural vector with zero retained entries. -/ | nil : Vector K 0
  /-- Retain one head followed by a structural tail of the original predecessor length. -/ | cons {n : Nat} : K →
    Vector K n → Vector K (n + 1)

constructive_injectivity Vector

namespace Vector

end Vector
open Purelib.Data.Vector

section
open Purelib.Data.Vector
namespace Vector

/-- Read a retained structural vector entry by matching its spine and bounded index
together.

Zero reads the stored head; a successor reads the retained tail at the predecessor
bound. No discarded recursive lookup is evaluated. -/
def get {K : Type*} : {n : Nat} → Vector K n → Fin n → K
  | _, .nil, index => Fin.elim0 index
  | _, .cons head _, ⟨0, _⟩ => head
  | _, .cons _ tail, ⟨index + 1, bound⟩ =>
      tail.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

end Vector
namespace Vector.Basic

/-- View a retained structural vector as its executable bounded lookup operation. -/
instance vectorCoeFun {K : Type*} {n : Nat} :
    CoeFun (Vector K n) (fun _ => Fin n → K) where
  coe := get

/-- Materialize a bounded function as an exact structural vector.

Read each retained Fin index once in increasing order, storing its value as a head
and recursively storing the successor-index tail. -/
def vectorOfFn {K : Type*} : {n : Nat} → (Fin n → K) → Vector K n
  | 0, _ => .nil
  | _ + 1, entries =>
      .cons (entries 0) (Purelib.Data.Vector.Basic.vectorOfFn fun index => entries index.succ)

end Vector.Basic
end

namespace Vector.Basic

/-- Reading a materialized finite vector recovers the original indexed value. -/
@[simp] theorem vectorOfFn_apply {K : Type*} {n : Nat}
    (entries : Fin n → K) (index : Fin n) :
    Basic.vectorOfFn entries index = entries index := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n inductionHypothesis =>
      rcases index with ⟨index, bound⟩
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis (fun nextIndex => entries nextIndex.succ)
            ⟨index, Nat.lt_of_succ_lt_succ bound⟩

open Purelib.Data.Vector in
/-- Coerce a bounded function to the structural vector containing its finite table. -/
instance vectorOfFnCoe {K : Type*} {n : Nat} :
    Coe (Fin n → K) (Vector K n) where
  coe := Basic.vectorOfFn

/-- Matching dimensions and entries identify two stored finite vector spines.

The two dimensions are compared explicitly before identifying the retained
tails. Entry transport changes only the finite index's bound certificate. -/
private theorem vector_heq_of_entries
    {leftSize : Nat} (left : Vector K leftSize) :
    ∀ {rightSize : Nat} (right : Vector K rightSize)
      (sizeEqual : leftSize = rightSize),
      (∀ index : Fin leftSize,
        left index = right ⟨index.val, sizeEqual ▸ index.isLt⟩) → HEq left right := by
  induction left with
  | nil =>
      intro rightSize right sizeEqual equal
      cases right with
      | nil => rfl
      | cons => exact Nat.noConfusion sizeEqual
  | @cons leftSize leftHead leftTail ih =>
      intro rightSize right sizeEqual equal
      cases right with
      | nil => exact Nat.noConfusion sizeEqual
      | @cons rightSize rightHead rightTail =>
          have tailSizeEqual : leftSize = rightSize := Nat.succ.inj sizeEqual
          cases tailSizeEqual
          have headEqual : leftHead = rightHead := equal 0
          have tailEqual : leftTail = rightTail :=
            eq_of_heq (ih rightTail rfl (fun index => equal index.succ))
          cases headEqual
          cases tailEqual
          rfl

/-- Pointwise equality proves structural equality of a finite vector.

The proof compares the retained head and tail entries recursively, preserving
the original dimension and coefficient carrier. -/
theorem vector_ext {n : Nat} {left right : Vector K n}
    (equal : ∀ index, left index = right index) : left = right := by
  exact eq_of_heq (Basic.vector_heq_of_entries left right rfl equal)

open Purelib.Data.Vector in
/-- Equality of structural vectors transports lookup equality at every retained finite
index. -/
theorem vector_eq_at {n : Nat} {left right : Vector K n}
    (equal : left = right) (index : Fin n) : left index = right index :=
  congrArg (fun vector : Vector K n => vector index) equal

end Vector.Basic
end Purelib.Data

end
