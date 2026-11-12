module

public import Init.Omega.LinearCombo
public import Purelib.Data.Presentation

namespace Purelib.Tactic.Omega.LinearCombination.Presentation

open Lean.Omega

/-!
# Finite linear-combination displays

A display is an integer constant and the original ordered `Coeffs` list of
integer coefficients. Every typed pair is valid. Readback uses the original
`LinearCombo` constructor, and comparison uses its existing decidable equality.
Equality retains every coefficient, including trailing zeros; equal evaluations
are a separate property. The finite product, integer and list decisions and
their retained proof/runtime dependencies are inherited, not certified by this
presentation alone.
-/

/-- The constant and complete ordered coefficient list of a linear combination. -/
public abbrev Code := Int × Coeffs

/-- Construct the original linear combination from its two displayed fields. -/
@[expose] public def read (code : Code) : LinearCombo := ⟨code.1, code.2⟩

/-- Project the two original fields, preserving all retained coefficients. -/
@[expose] public def quote (combination : LinearCombo) : Code :=
  (combination.const, combination.coeffs)

/-- Reading an original combination's fields returns that combination. -/
public theorem read_quote (combination : LinearCombo) : read (quote combination) = combination := by
  cases combination
  rfl

/-- Quoting an input returns the original pair of fields. -/
public theorem quote_read (code : Code) : quote (read code) = code := by
  cases code
  rfl

/-- Every typed finite pair is an admissible linear-combination display. -/
@[expose] public def Valid (_ : Code) : Prop := True

/-- An admissible pair with its trivial recognition evidence. -/
public abbrev Display := {code : Code // Valid code}

/-- Two displays agree when their original linear-combination readbacks agree. -/
@[expose] public def Same (first second : Display) : Prop := read first.val = read second.val

/-- Compare readbacks using the original `LinearCombo` equality decision. -/
@[expose] public def compare (first second : Display) : Decidable (Same first second) :=
  inferInstanceAs (Decidable (read first.val = read second.val))

/-- Readback equality is exactly equality of both retained fields. -/
public theorem same_iff_fields (first second : Display) :
    Same first second ↔ first.val.1 = second.val.1 ∧ first.val.2 = second.val.2 := by
  constructor
  · intro equal
    exact ⟨congrArg LinearCombo.const equal, congrArg LinearCombo.coeffs equal⟩
  · rintro ⟨constant, coefficients⟩
    cases first with
    | mk first _ =>
      cases second with
      | mk second _ =>
        cases first with
        | mk firstConstant firstCoefficients =>
          cases second with
          | mk secondConstant secondCoefficients =>
            cases constant
            cases coefficients
            rfl

/-- The explicit finite presentation of the original linear-combination owner. -/
@[expose] public def presentation : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := fun _ => .isTrue True.intro
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun equal => equal.symm, fun first second => first.trans second⟩

end Purelib.Tactic.Omega.LinearCombination.Presentation
