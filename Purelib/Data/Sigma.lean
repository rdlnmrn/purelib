module

/-! # Stored subtype values in dependent tuples

Each retained value may depend on all earlier components. Readers preserve
the original tuple, including any dependent remaining family.
-/

public section

namespace Purelib.Data.Sigma

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : α → Type u₂}
variable {γ : (first : α) → β first → Type u₃}
variable {property : (first : α) → (second : β first) → γ first second → Prop}
variable {rest : (first : α) → (second : β first) →
  { third : γ first second // property first second third } → Type u₄}

/-- Read the literal value of the third subtype in a dependent tuple.

Both earlier choices and the complete remaining family retain their
original indices. This operation only projects the stored value.
-/
@[expose] def thirdSubtypeValue
    (retained : Σ first : α, Σ second : β first,
      Σ third : { value : γ first second // property first second value }, rest first second third) :
    γ retained.1 retained.2.1 :=
  retained.2.2.1.val

/-- The projected value is exactly the original nested subtype projection. -/
theorem thirdSubtypeValue_eq
    (retained : Σ first : α, Σ second : β first,
      Σ third : { value : γ first second // property first second value }, rest first second third) :
    thirdSubtypeValue retained = retained.2.2.1.val :=
  rfl

universe u₅

variable {δ : (first : α) → (second : β first) → γ first second → Type u₄}
variable {fourthProperty : (first : α) → (second : β first) → (third : γ first second) →
  δ first second third → Prop}
variable {fourthRest : (first : α) → (second : β first) → (third : γ first second) →
  { fourth : δ first second third // fourthProperty first second third fourth } → Type u₅}

/-- Read the literal value of the fourth subtype in a dependent tuple.

All three earlier choices and the remaining family retain their original
indices. The complete supplied tuple is consumed without a rebuilt tail.
-/
@[expose] def fourthSubtypeValue
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : { value : δ first second third // fourthProperty first second third value },
        fourthRest first second third fourth) :
    δ retained.1 retained.2.1 retained.2.2.1 :=
  retained.2.2.2.1.val

/-- The fourth value is exactly the original nested subtype projection. -/
theorem fourthSubtypeValue_eq
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : { value : δ first second third // fourthProperty first second third value },
        fourthRest first second third fourth) :
    fourthSubtypeValue retained = retained.2.2.2.1.val :=
  rfl

universe u₆

variable {ε : (first : α) → (second : β first) → (third : γ first second) →
  δ first second third → Type u₅}
variable {fifthProperty : (first : α) → (second : β first) → (third : γ first second) →
  (fourth : δ first second third) → ε first second third fourth → Prop}
variable {fifthRest : (first : α) → (second : β first) → (third : γ first second) →
  (fourth : δ first second third) →
  { fifth : ε first second third fourth // fifthProperty first second third fourth fifth } → Type u₆}

/-- Read the literal value of the fifth subtype in a dependent tuple.

All four earlier choices and the remaining family retain their original
indices. The complete supplied tuple is consumed without a rebuilt tail.
-/
@[expose] def fifthSubtypeValue
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third,
      Σ fifth : { value : ε first second third fourth // fifthProperty first second third fourth value },
        fifthRest first second third fourth fifth) :
    ε retained.1 retained.2.1 retained.2.2.1 retained.2.2.2.1 :=
  retained.2.2.2.2.1.val

/-- The fifth value is exactly the original nested subtype projection. -/
theorem fifthSubtypeValue_eq
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third,
      Σ fifth : { value : ε first second third fourth // fifthProperty first second third fourth value },
        fifthRest first second third fourth fifth) :
    fifthSubtypeValue retained = retained.2.2.2.2.1.val :=
  rfl

/-- The fifth retained value satisfies its original dependent subtype property. -/
theorem fifthSubtypeValue_property
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third,
      Σ fifth : { value : ε first second third fourth // fifthProperty first second third fourth value },
        fifthRest first second third fourth fifth) :
    fifthProperty retained.1 retained.2.1 retained.2.2.1 retained.2.2.2.1
      (fifthSubtypeValue retained) :=
  retained.2.2.2.2.1.property

variable {ζ : (first : α) → (second : β first) → (third : γ first second) →
  (fourth : δ first second third) → ε first second third fourth → Type u₆}
variable {sixthProperty : (first : α) → (second : β first) → (third : γ first second) →
  (fourth : δ first second third) → (fifth : ε first second third fourth) →
  ζ first second third fourth fifth → Prop}

/-- Read the literal value of the terminal sixth subtype in a dependent tuple.

All five earlier choices retain their original indices. The complete supplied
tuple is consumed directly, without reconstructing a tail or its evidence.
-/
@[expose] def sixthSubtypeValue
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third, Σ fifth : ε first second third fourth,
        { value : ζ first second third fourth fifth //
          sixthProperty first second third fourth fifth value }) :
    ζ retained.1 retained.2.1 retained.2.2.1 retained.2.2.2.1 retained.2.2.2.2.1 :=
  retained.2.2.2.2.2.val

/-- The sixth value is exactly the original terminal subtype projection. -/
theorem sixthSubtypeValue_eq
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third, Σ fifth : ε first second third fourth,
        { value : ζ first second third fourth fifth //
          sixthProperty first second third fourth fifth value }) :
    sixthSubtypeValue retained = retained.2.2.2.2.2.val :=
  rfl

/-- The sixth retained value satisfies its original dependent subtype property. -/
theorem sixthSubtypeValue_property
    (retained : Σ first : α, Σ second : β first, Σ third : γ first second,
      Σ fourth : δ first second third, Σ fifth : ε first second third fourth,
        { value : ζ first second third fourth fifth //
          sixthProperty first second third fourth fifth value }) :
    sixthProperty retained.1 retained.2.1 retained.2.2.1 retained.2.2.2.1 retained.2.2.2.2.1
      (sixthSubtypeValue retained) :=
  retained.2.2.2.2.2.property

end Purelib.Data.Sigma
