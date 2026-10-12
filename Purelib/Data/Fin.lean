module
public import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Purelib.Algebra.Field.ExplicitField

public import Purelib.Data.Nat.Subtraction

/-!
# Splitting finite indices

Finite coordinates carry their original natural values and bounds. Dependent and
nondependent splitters distinguish the first position, the last position, or the two parts of
a finite sum; their computation laws and proposition eliminators retain those
same coordinates.
-/

namespace Purelib.Data.Fin

open Purelib.Data.Nat

public section

/-- Embed a finite index while skipping one displayed position.

Values below the removed position are retained; all later indices move up by one. The
original finite bound certifies the successor-size output. -/
@[expose] def skipIndex {n : Nat} (removed : Fin (n + 1)) (index : Fin n) :
    Fin (n + 1) :=
  if index.val < removed.val then
    ⟨index.val, index.isLt.trans (Nat.lt_succ_self n)⟩
  else ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩

universe u

/-- Split an index of a sum of finite sizes into one of two nondependent branches.

Compare its natural value with the left size, retaining the original value on the
left and subtracting that size on the right. The result type is constant, so no
dependent transport is needed. -/
@[expose] def addCases {leftSize rightSize : Nat} {Alpha : Sort u}
    (left : Fin leftSize → Alpha) (right : Fin rightSize → Alpha)
    (index : Fin (leftSize + rightSize)) : Alpha :=
  if below : index.val < leftSize then
    left ⟨index.val, below⟩
  else
    right ⟨index.val - leftSize,
      Subtraction.sub_lt_left_of_lt_add (Nat.le_of_not_lt below) index.isLt⟩

/-- The finite-sum splitter returns its left branch on an index embedded by castAdd. -/
theorem addCases_left {leftSize rightSize : Nat} {Alpha : Sort u}
    (left : Fin leftSize → Alpha) (right : Fin rightSize → Alpha)
    (index : Fin leftSize) :
    addCases left right (Fin.castAdd rightSize index) = left index := by
  unfold addCases
  simp only [Fin.val_castAdd]
  rw [dif_pos index.isLt]

/-- The finite-sum splitter returns its right branch on an index embedded by natAdd. -/
theorem addCases_right {leftSize rightSize : Nat} {Alpha : Sort u}
    (left : Fin leftSize → Alpha) (right : Fin rightSize → Alpha)
    (index : Fin rightSize) :
    addCases left right (Fin.natAdd leftSize index) = right index := by
  unfold addCases
  simp only [Fin.val_natAdd]
  have notBelow : ¬leftSize + index.val < leftSize :=
    Nat.not_lt.mpr (Nat.le_add_right leftSize index.val)
  rw [dif_neg notBelow]
  apply congrArg right
  apply Fin.ext
  exact Subtraction.add_sub_cancel_left leftSize index.val

/-- Every bounded sum index comes with an explicit left or right index and its embedding
equality. -/
theorem addCases_split {leftSize rightSize : Nat}
    (index : Fin (leftSize + rightSize)) :
    (∃ left : Fin leftSize, index = Fin.castAdd rightSize left) ∨
      (∃ right : Fin rightSize, index = Fin.natAdd leftSize right) := by
  by_cases below : index.val < leftSize
  · exact Or.inl ⟨⟨index.val, below⟩, by
      apply Fin.ext
      rfl⟩
  · have leftAtMost : leftSize ≤ index.val := Nat.le_of_not_lt below
    have remainderBelow : index.val - leftSize < rightSize :=
      Subtraction.sub_lt_left_of_lt_add leftAtMost index.isLt
    exact Or.inr ⟨⟨index.val - leftSize, remainderBelow⟩, by
      apply Fin.ext
      exact (Subtraction.add_sub_of_le leftAtMost).symm⟩

/-- Split a successor-size finite index into its last position or a retained preceding
index.

A direct decidable comparison supplies the original bound for the preceding branch;
the last branch returns the supplied constant result. -/
@[expose] def lastCases {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha)
    (index : Fin (size + 1)) : Alpha :=
  if before : index.val < size then
    previous ⟨index.val, before⟩
  else
    last

/-- Last-position splitting returns the preceding branch on an embedded earlier index. -/
theorem lastCases_castSucc {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha) (index : Fin size) :
    lastCases last previous index.castSucc = previous index := by
  unfold lastCases
  change (if before : index.val < size then
      previous ⟨index.val, before⟩ else last) = previous index
  rw [dif_pos index.isLt]

/-- Last-position splitting returns the supplied last value at the final index. -/
theorem lastCases_last {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha) :
    lastCases last previous (Fin.last size) = last := by
  unfold lastCases
  change (if before : size < size then
      previous ⟨size, before⟩ else last) = last
  rw [dif_neg]
  exact Nat.lt_irrefl size

/-- Every successor-size index is the last index or the castSucc image of an explicit
preceding index. -/
theorem lastCases_split {size : Nat} (index : Fin (size + 1)) :
    index = Fin.last size \/
      exists previous : Fin size, index = previous.castSucc := by
  by_cases before : index.val < size
  · exact Or.inr ⟨⟨index.val, before⟩, by
      apply Fin.ext
      rfl⟩
  · apply Or.inl
    apply Fin.ext
    change index.val = size
    exact Nat.le_antisymm (Nat.le_of_lt_succ index.isLt)
      (Nat.le_of_not_lt before)

/-- Prove a dependent finite-index proposition from its last case and all preceding
cases.

The exact finite split retains an equality to either the last index or a displayed
castSucc index; ordinary equality transport supplies the corresponding proof. -/
theorem lastCases_induction {size : Nat}
    {motive : Fin (size + 1) -> Prop}
    (last : motive (Fin.last size))
    (previous : forall index : Fin size, motive index.castSucc)
    (index : Fin (size + 1)) : motive index := by
  rcases lastCases_split index with equal | ⟨source, equal⟩
  · subst index
    exact last
  · subst index
    exact previous source

set_option backward.match.sparseCases false in
/-- Split a successor-size finite index into its first position or its predecessor.

The natural coordinate selects the branch. A successor coordinate retains its
predecessor value and the bound obtained from the original successor bound.
The branch result has a constant type, so no dependent data transport is needed. -/
@[expose] def cases {size : Nat} {Alpha : Sort u}
    (first : Alpha) (following : Fin size → Alpha) : Fin (size + 1) → Alpha
  | ⟨0, _⟩ => first
  | ⟨value + 1, bound⟩ =>
      following ⟨value, Nat.lt_of_succ_lt_succ bound⟩

/-- First-position splitting returns the supplied first value at coordinate zero. -/
theorem cases_zero {size : Nat} {Alpha : Sort u}
    (first : Alpha) (following : Fin size → Alpha) :
    cases first following (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = first := rfl

/-- First-position splitting returns the following branch at an embedded successor. -/
theorem cases_succ {size : Nat} {Alpha : Sort u}
    (first : Alpha) (following : Fin size → Alpha) (index : Fin size) :
    cases first following index.succ = following index := rfl

/-- Split a successor-size index while retaining its dependent result type.

The first branch uses the exact zero coordinate and the successor branch receives
its original predecessor and strict bound. Natural constructor elimination keeps
the result indexed by the same supplied finite coordinate. -/
@[expose] def casesDependent {size : Nat} {motive : Fin (size + 1) → Sort u}
    (first : motive ⟨0, Nat.zero_lt_succ size⟩)
    (following : (index : Fin size) → motive index.succ)
    (index : Fin (size + 1)) : motive index :=
  Nat.casesOn (motive := fun value => (bound : value < size + 1) → motive ⟨value, bound⟩)
    index.val (fun _ => first)
    (fun value bound => following ⟨value, Nat.lt_of_succ_lt_succ bound⟩) index.isLt

set_option backward.match.sparseCases false in
/-- Prove a finite-index proposition from its first case and every successor case.

The original coordinate is destructed into its natural value and retained bound.
A positive value supplies the predecessor index with its original successor-bound
certificate; proof irrelevance identifies the corresponding finite constructors. -/
@[elab_as_elim] theorem cases_induction {size : Nat}
    {motive : Fin (size + 1) → Prop}
    (first : motive ⟨0, Nat.zero_lt_succ size⟩)
    (following : ∀ index : Fin size, motive index.succ)
    (index : Fin (size + 1)) : motive index := by
  rcases index with ⟨value, bound⟩
  cases value with
  | zero => exact first
  | succ value => exact following ⟨value, Nat.lt_of_succ_lt_succ bound⟩

/-- A successor finite coordinate differs from the first coordinate.

Applying the natural-value projection reduces an alleged equality to equality
between a successor and zero, which the natural constructors exclude. -/
theorem succ_ne_zero {size : Nat} (index : Fin size) :
    index.succ ≠ (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) := by
  intro equal
  exact Nat.noConfusion (congrArg Fin.val equal)

/-- Prove a fixed-bound finite-index proposition by successive coordinates.

The initial case retains the exact zero coordinate and its bound. Every successor
case receives its original predecessor as a bounded index, together with the
proposition at that predecessor; natural-coordinate induction transports only
bound certificates, leaving the finite size fixed. -/
@[elab_as_elim] theorem induction {size : Nat}
    {motive : Fin (size + 1) → Prop}
    (zero : motive ⟨0, Nat.zero_lt_succ size⟩)
    (succ : ∀ index : Fin size, motive index.castSucc → motive index.succ)
    (index : Fin (size + 1)) : motive index := by
  have entry : ∀ value (bound : value < size + 1), motive ⟨value, bound⟩ := by
    intro value
    induction value with
    | zero =>
        intro bound
        exact zero
    | succ value ih =>
        intro bound
        let previous : Fin size := ⟨value, Nat.lt_of_succ_lt_succ bound⟩
        exact succ previous (ih previous.castSucc.isLt)
  exact entry index.val index.isLt

set_option backward.match.sparseCases false in
/-- Construct a dependent finite-index value from its first value and successive values.

Induction follows the original natural coordinate. Each successor retains the
same predecessor index, its bound, and the already constructed preceding value. -/
@[expose, elab_as_elim] def recursion {size : Nat}
    {motive : Fin (size + 1) → Sort u}
    (first : motive (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)))
    (following : ∀ index : Fin size, motive index.castSucc → motive index.succ) :
    ∀ index : Fin (size + 1), motive index
  | ⟨value, bound⟩ => go value bound
where
  go : ∀ (value : Nat) (bound : value < size + 1), motive ⟨value, bound⟩
  | 0, _ => first
  | value + 1, bound =>
      following ⟨value, Nat.lt_of_succ_lt_succ bound⟩
        (go value (Nat.lt_of_succ_lt bound))

/-- Split a dependent finite-index value through its original finite recursion.

The first branch supplies the value at zero. At each successor, the second branch
receives the original predecessor index; the recursive preceding value is ignored.
The retained recursion keeps the same finite-index evaluation procedure. -/
@[expose, elab_as_elim] def casesByRecursion {size : Nat}
    {motive : Fin (size + 1) → Sort u}
    (first : motive (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)))
    (following : ∀ i : Fin size, motive i.succ) :
    ∀ i : Fin (size + 1), motive i :=
  recursion first (fun i _ => following i)

end

end Purelib.Data.Fin
