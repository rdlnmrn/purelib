module

section
@[expose] public section

/-! Executable Boolean exclusive-or and its direct scalar laws. -/

namespace Purelib.Data.Bool.Xor

/-- Compute exclusive-or of two Boolean values.

A false first argument leaves the second unchanged; a true first argument complements
it. -/
def bitXor : Bool → Bool → Bool
  | false, value => value
  | true, value => !value

/-- Exclusive-or is commutative. -/
theorem bitXor_comm_direct (left right : Bool) :
    bitXor left right = bitXor right left := by
  cases left <;> cases right <;> rfl

/-- Exclusive-or is associative. -/
theorem bitXor_assoc_direct (first second third : Bool) :
    bitXor (bitXor first second) third =
      bitXor first (bitXor second third) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- Exclusive-or of a bit with itself is false. -/
theorem bitXor_self_direct (value : Bool) :
    bitXor value value = false := by
  cases value <;> rfl
end Purelib.Data.Bool.Xor

end
