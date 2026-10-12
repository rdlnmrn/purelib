module

-- Public iteration retains the original nominal range and membership fields.
public import Init.Data.Range.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Remainder
import Purelib.Tactic.QuotientFreeOmega

/-!
# Iteration over an original bounded natural range

The retained range supplies its original start, exclusive stop, positive step
and congruence condition. Iteration advances by that same step and preserves
early returns, yielded accumulators and the original monad's effects.
-/

namespace Purelib.Data.Range

open Purelib.Data.Nat

set_option backward.match.sparseCases false

/-- Advancing an original range index preserves its step congruence.

The retained lower bound allows ordinary subtraction to reconstruct the offset.
Adding exactly one original step leaves that offset's remainder unchanged. -/
private theorem advance_congruence (range : Std.Legacy.Range) (index : Nat)
    (lower : range.start ≤ index)
    (congruent : (index - range.start) % range.step = 0) :
    (index + range.step - range.start) % range.step = 0 := by
  have reconstructed := Subtraction.add_sub_of_le lower
  have shifted : index + range.step - range.start =
      range.step + (index - range.start) := by omega0
  rewrite [shifted]
  have addStep := Remainder.mul_add_mod range.step 1 (index - range.start)
  rewrite [Nat.mul_one] at addStep
  exact addStep.trans congruent

/-- Iterate through the original indices of a retained positive-step range.

Every callback receives the original bounds and step-congruence certificate.
The loop adds the supplied step exactly once after a yield and leaves early
returns and monadic failures unchanged. -/
@[inline] public def forIn' [Monad m] (range : Std.Legacy.Range) (initial : Beta)
    (visit : (index : Nat) → index ∈ range → Beta → m (ForInStep Beta)) : m Beta :=
  let rec @[specialize] loop (accumulator : Beta) (index : Nat)
      (congruent : (index - range.start) % range.step = 0)
      (lower : range.start ≤ index) : m Beta := do
    if upper : index < range.stop then
      match (← visit index ⟨lower, upper, congruent⟩ accumulator) with
      | .done result => pure result
      | .yield result =>
          loop result (index + range.step)
            (advance_congruence range index lower congruent)
            (Nat.le_trans lower (Nat.le_add_right index range.step))
    else pure accumulator
  termination_by range.stop - index
  decreasing_by
    have positive := range.step_pos
    omega0
  loop initial range.start (by
    rewrite [Subtraction.sub_eq_zero_of_le (Nat.le_refl range.start)]
    exact Remainder.mod_eq_of_lt range.step_pos) (Nat.le_refl range.start)

/-- Select iteration over the same nominal bounded natural range.

Opening this scope retains the original membership relation and callback type.
The original start, stop, positive step and supplied monad determine all effects. -/
public scoped instance (priority := 1001) [Monad m] :
    ForIn' m Std.Legacy.Range Nat inferInstance where
  forIn' := forIn'

end Purelib.Data.Range
