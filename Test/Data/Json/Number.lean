module

import Purelib.Data.Json.Number

/-!
# Retained JSON scalar conventions

Integer decoding accepts exponent-zero representations only. These checks
retain sign, decimal scale, original error labels and representation equality.
-/

namespace Test.Data.Json.Number

open Purelib.Data.Json.Number (beq getNat? getInt?)

/-- An exponent-zero nonnegative scalar decodes as a natural number.

The retained mantissa supplies the displayed natural value directly. -/
private theorem natural_value : getNat? ⟨12, 0⟩ = .ok 12 := rfl

/-- A negative exponent-zero scalar decodes as the original signed integer.

The signed decoder retains the negative mantissa without normalization. -/
private theorem negative_integer : getInt? ⟨-12, 0⟩ = .ok (-12) := rfl

/-- Natural decoding rejects a negative mantissa with its original error label.

The rejected scalar has exponent zero; its sign is the violated natural shape. -/
private theorem negative_natural :
    getNat? ⟨-12, 0⟩ = .error "Natural number expected" := rfl

/-- Natural decoding rejects a positive decimal scale even for an integral value.

The retained representation denotes one, but its exponent is not zero. -/
private theorem scaled_natural :
    getNat? ⟨10, 1⟩ = .error "Natural number expected" := rfl

/-- Integer decoding rejects a positive decimal scale with its original error label.

The retained representation denotes an integer; decoding still requires the
original exponent-zero shape. -/
private theorem scaled_integer :
    getInt? ⟨120, 1⟩ = .error "Integer expected" := rfl

/-- Representation equality distinguishes differently scaled equal values.

Both records denote the same rational value, while their original mantissas
and exponents differ. -/
private theorem distinct_scale : beq ⟨12, 1⟩ ⟨120, 2⟩ = false := by
  apply decide_eq_false
  intro equal
  have unequal : (12 : Int) ≠ 120 := by decide
  exact unequal (congrArg Lean.JsonNumber.mantissa equal)

end Test.Data.Json.Number
