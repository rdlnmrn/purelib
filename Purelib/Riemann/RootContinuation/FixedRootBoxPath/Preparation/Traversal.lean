module

public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation

/-!
# Traversal of retained actual root preparations

The advance count reads the existing finite tree. Each original step retains
one actual accepted owner advance, while a join adds the counts of its stored
halves. The computation neither rebuilds a preparation nor runs a root-name
comparison.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation

open Purelib
open Purelib.Riemann.RootContinuation.FixedRootBoxBudget

variable {firstSource secondSource : Gaussian} {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
variable {first : Budget firstOwner} {second : Budget secondOwner} {path : PathData first second}

namespace Prepared

/-- Count the actual accepted owner advances already retained by the original preparation. -/
@[expose] def advanceCount : ∀ {left right leftInside rightInside source target},
    Prepared path left right leftInside rightInside source target → Nat
  | _, _, _, _, _, _, .step _ => 1
  | _, _, _, _, _, _, .join _ firstHalf secondHalf => firstHalf.advanceCount + secondHalf.advanceCount

/-- One original retained leaf has precisely its single cached actual accepted owner advance. -/
theorem advanceCount_step {left right leftInside rightInside source target}
    (step : Step path left right leftInside rightInside source target) :
    (Prepared.step step).advanceCount = 1 := rfl

/-- An original join reads the sum of the actual advance counts of its identical stored halves. -/
theorem advanceCount_join {left middle right leftInside middleInside rightInside source center target}
    (middle_eq : middle = (left + right) / 2)
    (firstHalf : Prepared path left middle leftInside middleInside source center)
    (secondHalf : Prepared path middle right middleInside rightInside center target) :
    (Prepared.join middle_eq firstHalf secondHalf).advanceCount =
      firstHalf.advanceCount + secondHalf.advanceCount := rfl

/-- Every actual original preparation retains at least one accepted owner advance. -/
theorem advanceCount_positive : ∀ {left right leftInside rightInside source target}
    (prepared : Prepared path left right leftInside rightInside source target), 0 < prepared.advanceCount
  | _, _, _, _, _, _, .step _ => (by decide +kernel : 0 < (1 : Nat))
  | _, _, _, _, _, _, .join _ firstHalf secondHalf =>
      Nat.lt_of_lt_of_le firstHalf.advanceCount_positive (Nat.le_add_right _ secondHalf.advanceCount)

end Prepared

namespace Result

/-- Read the exact number of actual accepted advances from the identical stored complete preparation. -/
@[expose] def advanceCount (result : Result path) : Nat := result.prepared.advanceCount

/-- The complete preparation's reported advance count is positive on its actual retained tree. -/
theorem advanceCount_positive (result : Result path) : 0 < result.advanceCount := result.prepared.advanceCount_positive

end Result

end Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
