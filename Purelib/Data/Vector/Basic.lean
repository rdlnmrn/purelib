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
namespace Vector

/-- Transform each retained structural vector entry without rebuilding a function table. -/
def map {K L : Type*} (transform : K → L) : {count : Nat} → Vector K count → Vector L count
  | _, .nil => .nil
  | _, .cons head tail => .cons (transform head) (map transform tail)

/-- Combine corresponding retained vector entries by one structural traversal. -/
def zipWith {K L M : Type*} (combine : K → L → M) :
    {count : Nat} → Vector K count → Vector L count → Vector M count
  | _, .nil, .nil => .nil
  | _, .cons left leftTail, .cons right rightTail =>
      .cons (combine left right) (zipWith combine leftTail rightTail)

namespace Basic

/-- Readback of a structural vector transformation consumes the same original entry. -/
theorem map_apply {K L : Type*} (transform : K → L) {count : Nat}
    (values : Vector K count) (index : Fin count) : map transform values index = transform (values index) := by
  induction values with
  | nil => exact Fin.elim0 index
  | @cons count head tail previous =>
      cases index with
      | mk index bound =>
          cases index with
          | zero => rfl
          | succ index => exact previous ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Readback of a paired structural traversal combines the two original entries. -/
theorem zipWith_apply {K L M : Type*} (combine : K → L → M) {count : Nat}
    (left : Vector K count) (right : Vector L count) (index : Fin count) :
    zipWith combine left right index = combine (left index) (right index) := by
  induction left with
  | nil => exact Fin.elim0 index
  | @cons count head tail previous =>
      cases right with
      | cons rightHead rightTail =>
          cases index with
          | mk index bound =>
              cases index with
              | zero => rfl
              | succ index => exact previous rightTail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

end Basic
end Vector

end Purelib.Data

end

public section

namespace Purelib.Data.Vector.Basic

universe v

/-- Whole dimension transport preserves lookup at the correspondingly transported original bounded index.

Equality elimination forwards the original structural vector, retained
entry and finite bound. No vector table or indexing proof is recomputed.
-/
theorem get_eq_mp {K : Type v} {first last : Nat} (equal : first = last)
    (values : Vector K first) (index : Fin first) :
    (Eq.mp (congrArg (fun size => Vector K size) equal) values) (Fin.cast equal index) = values index := by
  cases equal
  rfl

end Purelib.Data.Vector.Basic

end
