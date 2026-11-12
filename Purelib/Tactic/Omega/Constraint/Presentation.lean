module

public import Init.Omega.Constraint
public import Purelib.Data.Presentation

namespace Purelib.Tactic.Omega.Constraint.Presentation

open Lean.Omega

/-!
# Finite constraint displays

A display contains the original optional integer lower and upper bounds. Every
typed pair is valid, including inconsistent bounds. Readback uses the original
`Lean.Omega.Constraint` constructor, and comparison uses its existing equality
decision. Equality of the two retained fields is separate from satisfaction of
the constraint at an integer. The finite product, option and integer decisions
and their proof/runtime dependencies are inherited by this presentation.
-/

/-- The original optional lower and upper bounds of a constraint. -/
public abbrev Code := LowerBound × UpperBound

/-- Construct the original constraint with its two displayed bounds. -/
@[expose] public def read (code : Code) : Lean.Omega.Constraint := ⟨code.1, code.2⟩

/-- Project both original optional bounds of a constraint. -/
@[expose] public def quote (constraint : Lean.Omega.Constraint) : Code :=
  (constraint.lowerBound, constraint.upperBound)

/-- Reading the quotation recovers the original constraint. -/
public theorem read_quote (constraint : Lean.Omega.Constraint) : read (quote constraint) = constraint := by
  cases constraint
  rfl

/-- Quoting a readback recovers both original optional bounds. -/
public theorem quote_read (code : Code) : quote (read code) = code := by
  cases code
  rfl

/-- Every typed pair of optional integer bounds is valid constraint data. -/
@[expose] public def Valid (_ : Code) : Prop := True

/-- An admissible pair with its recognition evidence. -/
public abbrev Display := {code : Code // Valid code}

/-- Two displays agree when their original constraint readbacks agree. -/
@[expose] public def Same (first second : Display) : Prop := read first.val = read second.val

/-- Compare readbacks using the original constraint equality decision. -/
@[expose] public def compare (first second : Display) : Decidable (Same first second) :=
  inferInstanceAs (Decidable (read first.val = read second.val))

/-- Readback equality is exactly equality of both original optional bounds. -/
public theorem same_iff_fields (first second : Display) :
    Same first second ↔ first.val.1 = second.val.1 ∧ first.val.2 = second.val.2 := by
  constructor
  · intro equal
    exact ⟨congrArg Lean.Omega.Constraint.lowerBound equal, congrArg Lean.Omega.Constraint.upperBound equal⟩
  · rintro ⟨lower, upper⟩
    cases first with
    | mk first _ =>
      cases second with
      | mk second _ =>
        cases first with
        | mk firstLower firstUpper =>
          cases second with
          | mk secondLower secondUpper =>
            cases lower
            cases upper
            rfl

/-- The finite presentation of the original optional-bound constraint. -/
@[expose] public def presentation : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := fun _ => .isTrue True.intro
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun equal => equal.symm, fun first second => first.trans second⟩

end Purelib.Tactic.Omega.Constraint.Presentation
