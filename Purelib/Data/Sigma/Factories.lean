module

import Purelib.Data.Sigma

/-! # Retained dependent factory tuples

Ordered factories retain their complete values and exact defining
equalities in the original dependent Sigma/Subtype layout.
-/

public section

namespace Purelib.Data.Sigma

universe u₁ u₂ u₃ u₄

/-- Pair an already retained value with its original dependent tail.

Both arguments are supplied values. The operation only constructs the
original Sigma pair and invokes no factory or entry producer.
-/
@[expose, noinline] def pair {α : Type u₁} {β : α → Type u₂}
    (value : α) (tail : β value) : (first : α) × β first :=
  ⟨value, tail⟩

/-- Value packing returns the complete original Sigma pair. -/
theorem pair_eq {α : Type u₁} {β : α → Type u₂} (value : α) (tail : β value) :
    pair value tail = ⟨value, tail⟩ := rfl

/-- Execute two ordered factories once and retain their equalities before constructing an arbitrary certified tail.

The tail consumes those same retained values and keeps its original type,
including any existing specification or conjunction without an extra wrapper.
-/
@[expose, noinline] def ofSubtypeFactoriesWithTail
    {α : Type u₁} {β : α → Type u₂}
    {γ : (first : α) → β first → Type u₃}
    (firstFactory : Unit → α) (secondFactory : (first : α) → β first)
    (tailFactory : (first : α) → (second : β first) → γ first second) :
    (first : { value : α // value = firstFactory () }) ×
    (second : { value : β first.val // value = secondFactory first.val }) ×
    γ first.val second.val :=
  let first := firstFactory ()
  let second := secondFactory first
  let tail := tailFactory first second
  pair ⟨first, rfl⟩ (pair ⟨second, rfl⟩ tail)

/-- The complete retained prefix and certified tail are their original once-executed ordered factories. -/
theorem ofSubtypeFactoriesWithTail_eq
    {α : Type u₁} {β : α → Type u₂}
    {γ : (first : α) → β first → Type u₃}
    (firstFactory : Unit → α) (secondFactory : (first : α) → β first)
    (tailFactory : (first : α) → (second : β first) → γ first second) :
    ofSubtypeFactoriesWithTail firstFactory secondFactory tailFactory =
    (let first := firstFactory ()
     let second := secondFactory first
     let tail := tailFactory first second
     ⟨⟨first, rfl⟩, ⟨second, rfl⟩, tail⟩) := rfl

/-- Execute four dependent factories once in order and retain each complete factory equality.

The second factory consumes the stored first value, the third consumes the
stored first two values, and the fourth consumes all three. The original
subtype values and dependencies remain in the resulting dependent tuple.
-/
@[expose, noinline] def ofSubtypeFactories
    {α : Type u₁} {β : α → Type u₂}
    {γ : (first : α) → β first → Type u₃}
    {δ : (first : α) → (second : β first) → γ first second → Type u₄}
    (firstFactory : Unit → α) (secondFactory : (first : α) → β first)
    (thirdFactory : (first : α) → (second : β first) → γ first second)
    (fourthFactory : (first : α) → (second : β first) → (third : γ first second) → δ first second third) :
    (first : { value : α // value = firstFactory () }) ×
    (second : { value : β first.val // value = secondFactory first.val }) ×
    (third : { value : γ first.val second.val // value = thirdFactory first.val second.val }) ×
    { value : δ first.val second.val third.val //
      value = fourthFactory first.val second.val third.val } :=
  ofSubtypeFactoriesWithTail firstFactory secondFactory
    (γ := fun first second =>
      (third : { value : γ first second // value = thirdFactory first second }) ×
      { value : δ first second third.val // value = fourthFactory first second third.val })
    (fun first second =>
      let third := thirdFactory first second
      let fourth := fourthFactory first second third
      pair ⟨third, rfl⟩ ⟨fourth, rfl⟩)

/-- The retained tuple is the whole original four-factory execution, with the same order and values. -/
theorem ofSubtypeFactories_eq
    {α : Type u₁} {β : α → Type u₂}
    {γ : (first : α) → β first → Type u₃}
    {δ : (first : α) → (second : β first) → γ first second → Type u₄}
    (firstFactory : Unit → α) (secondFactory : (first : α) → β first)
    (thirdFactory : (first : α) → (second : β first) → γ first second)
    (fourthFactory : (first : α) → (second : β first) → (third : γ first second) → δ first second third) :
    ofSubtypeFactories firstFactory secondFactory thirdFactory fourthFactory =
    (let first := firstFactory ()
     let second := secondFactory first
     let third := thirdFactory first second
     let fourth := fourthFactory first second third
     ⟨⟨first, rfl⟩, ⟨second, rfl⟩, ⟨third, rfl⟩, ⟨fourth, rfl⟩⟩) := rfl

end Purelib.Data.Sigma
