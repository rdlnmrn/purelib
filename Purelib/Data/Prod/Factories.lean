module

/-! # Retained ordered product factories

Four ordered factories have independent runtime carriers. Their certified
ordinary product retains the exact original values and all four defining
equalities, including the dependencies between their factory calls.
-/

public section

namespace Purelib.Data.Prod

universe u₁ u₂ u₃ u₄

/-- Execute four ordered factories once and retain their whole defining equalities.

The carriers are independent. Each later factory consumes the same earlier
stored values, and the resulting product's subtype records those exact
calls without reconstructing any value.
-/
@[expose, noinline] def ofSubtypeFactories
    {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}
    (firstFactory : Unit → α) (secondFactory : α → β)
    (thirdFactory : α → β → γ) (fourthFactory : α → β → γ → δ) :
    { values : α × β × γ × δ //
      values.1 = firstFactory () ∧
      values.2.1 = secondFactory values.1 ∧
      values.2.2.1 = thirdFactory values.1 values.2.1 ∧
      values.2.2.2 = fourthFactory values.1 values.2.1 values.2.2.1 } :=
  let first := firstFactory ()
  let second := secondFactory first
  let third := thirdFactory first second
  let fourth := fourthFactory first second third
  ⟨⟨first, second, third, fourth⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The complete certified product is the same four-factory execution in its original order. -/
theorem ofSubtypeFactories_eq
    {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}
    (firstFactory : Unit → α) (secondFactory : α → β)
    (thirdFactory : α → β → γ) (fourthFactory : α → β → γ → δ) :
    ofSubtypeFactories firstFactory secondFactory thirdFactory fourthFactory =
    (let first := firstFactory ()
     let second := secondFactory first
     let third := thirdFactory first second
     let fourth := fourthFactory first second third
     ⟨⟨first, second, third, fourth⟩, ⟨rfl, rfl, rfl, rfl⟩⟩) := rfl

end Purelib.Data.Prod
