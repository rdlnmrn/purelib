module

import Init.Prelude

public section

namespace Except

universe u v

variable {Error : Type u} {Value : Type v}

/-- Retain the actual successful value when every error payload is refuted.

The returned equation identifies the supplied complete outcome with that
same success constructor. The match is generic in both payload types.
-/
def requireSuccess (outcome : Except Error Value) (reject : Error → False) :
    { value : Value // outcome = .ok value } :=
  match outcome with
  | .ok value => ⟨value, rfl⟩
  | .error failure => False.elim (reject failure)

/-- The retained value belongs to the original successful outcome. -/
theorem requireSuccess_eq (outcome : Except Error Value) (reject : Error → False) :
    outcome = .ok (requireSuccess outcome reject).val :=
  (requireSuccess outcome reject).property

/-- Extracting an existing success preserves its whole value and constructor equation. -/
private theorem packaged_requireSuccess_ok (value : Value) (reject : Error → False) :
    requireSuccess (.ok value) reject = ⟨value, rfl⟩ := rfl

/-- Extracting an existing success preserves its whole value and constructor equation. -/
theorem requireSuccess_ok (value : Value) (reject : Error → False) :
    requireSuccess (.ok value) reject = ⟨value, rfl⟩ :=
  packaged_requireSuccess_ok value reject

end Except

end
