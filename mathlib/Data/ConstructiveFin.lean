import Init.Data.Fin.Lemmas

/-!
# Constructive cases for finite sums

The core dependent `Fin.addCases` eliminator and its right computation theorem
currently reach `Quot.sound` through heterogeneous-equality infrastructure.
For the finite matrices in this project, the result type is constant.  This
nondependent splitter computes directly from the displayed natural index and
comes with ordinary finite-index certificates for dependent proofs.
-/

namespace QuotientFreeFin

universe u

/-- Split an index below `leftSize + rightSize` without dependent transport. -/
def addCases {leftSize rightSize : Nat} {Alpha : Sort u}
    (left : Fin leftSize → Alpha) (right : Fin rightSize → Alpha)
    (index : Fin (leftSize + rightSize)) : Alpha :=
  if below : index.val < leftSize then
    left ⟨index.val, below⟩
  else
    right ⟨index.val - leftSize,
      Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt below) index.isLt⟩

/-- The nondependent splitter computes to its left branch on a left index. -/
theorem addCases_left {leftSize rightSize : Nat} {Alpha : Sort u}
    (left : Fin leftSize → Alpha) (right : Fin rightSize → Alpha)
    (index : Fin leftSize) :
    addCases left right (Fin.castAdd rightSize index) = left index := by
  unfold addCases
  simp only [Fin.val_castAdd]
  rw [dif_pos index.isLt]

/-- The nondependent splitter computes to its right branch on a right index. -/
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
  exact Nat.add_sub_cancel_left leftSize index.val

/-- Every finite-sum index carries an explicit left or right source index. -/
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
      Nat.sub_lt_left_of_lt_add leftAtMost index.isLt
    exact Or.inr ⟨⟨index.val - leftSize, remainderBelow⟩, by
      apply Fin.ext
      exact (Nat.add_sub_of_le leftAtMost).symm⟩

/-- Nondependent last-element case analysis for a finite successor.  Unlike
`Fin.lastCases`, this definition performs only a decidable comparison on the
displayed natural index. -/
def lastCases {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha)
    (index : Fin (size + 1)) : Alpha :=
  if before : index.val < size then
    previous ⟨index.val, before⟩
  else
    last

/-- The constructive splitter computes on an embedded preceding index. -/
theorem lastCases_castSucc {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha) (index : Fin size) :
    lastCases last previous index.castSucc = previous index := by
  unfold lastCases
  change (if before : index.val < size then
      previous ⟨index.val, before⟩ else last) = previous index
  rw [dif_pos index.isLt]

/-- The constructive splitter computes on the final index. -/
theorem lastCases_last {size : Nat} {Alpha : Sort u}
    (last : Alpha) (previous : Fin size -> Alpha) :
    lastCases last previous (Fin.last size) = last := by
  unfold lastCases
  change (if before : size < size then
      previous ⟨size, before⟩ else last) = last
  rw [dif_neg]
  exact Nat.lt_irrefl size

/-- Every successor-sized finite index is either the displayed last index or
the embedding of an explicitly displayed preceding index. -/
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

/-- Dependent elimination derived from `lastCases_split` using only explicit
finite witnesses and ordinary equality transport. -/
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

end QuotientFreeFin
