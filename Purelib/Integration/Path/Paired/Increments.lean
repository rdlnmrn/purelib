module
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# The ordered paired-increment identity with physical terminal terms

Each pair consists of its actual outward and returning increments. The B
entry uses the outward increment, a shared reference return, and all earlier
A totals. No cancellation between the two sheets is assumed. The remaining
reference double-loop and exterior total occur explicitly in both formulas.
-/

namespace Purelib.Integration.Path.Paired.Increments

open Purelib.Integration.Path.IncrementArea

section
open Purelib.Integration.Path
/-- Flatten the original increment pairs, retaining each first-then-second occurrence and pair order. -/
def values : List (IncrementArea.Gaussian × IncrementArea.Gaussian) → List IncrementArea.Gaussian
  | [] => []
  | pair :: rest => pair.1 :: pair.2 :: Purelib.Integration.Path.Paired.Increments.values rest

/-- Sum the original increment pairs in order, adding each pair before its retained tail total. -/
def total : List (IncrementArea.Gaussian × IncrementArea.Gaussian) → IncrementArea.Gaussian
  | [] => 0
  | pair :: rest => (pair.1 + pair.2) + Purelib.Integration.Path.Paired.Increments.total rest

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The flattened original increments have the same total as the retained pairwise sum.

Finite induction retains both entries of every ordered pair and uses the same Gaussian addition for the accumulated
total. -/
theorem values_total (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
  Data.Gaussian.Norm.Sum.Basic.gaussianSum
  (Paired.Increments.values pairs) = Paired.Increments.total pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [Paired.Increments.values, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Paired.Increments.total, ih,
        add_assoc,
        -eq_self, -iff_self]
      rfl

section
open Purelib.Integration.Path
/-- Accumulate the original paired cross-area corrections against a fixed return and evolving prior total.

Each recursive step uses the exact original pair and advances the prior by that pair's sum, preserving all signed cross
terms. -/
def correctedArea (referenceReturn prior : IncrementArea.Gaussian) : List (IncrementArea.Gaussian ×
  IncrementArea.Gaussian) → IncrementArea.Gaussian
  | [] => 0
  | pair :: rest => BoundaryRibbon.area (pair.1 + pair.2) (pair.1 + referenceReturn + prior) +
      Purelib.Integration.Path.Paired.Increments.correctedArea referenceReturn (prior + (pair.1 + pair.2)) rest

/-- Swapping the two original Gaussian displacements negates their signed cross area. -/
private theorem skew (first last : IncrementArea.Gaussian) : BoundaryRibbon.area first last = -BoundaryRibbon.area last
  first := by
  unfold BoundaryRibbon.area
  ring1

end

open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- The original flattened path area plus paired correction equals the total's cross area with reference return and
prior.

The recursive correction follows the same ordered pair list and retains the supplied reference and initial accumulated
displacement. -/
theorem formula (referenceReturn prior : IncrementArea.Gaussian) (pairs : List (IncrementArea.Gaussian ×
  IncrementArea.Gaussian)) :
    IncrementArea.pathArea (Paired.Increments.values pairs) + Paired.Increments.correctedArea referenceReturn prior
      pairs = BoundaryRibbon.area (Paired.Increments.total pairs) (referenceReturn + prior) := by
  induction pairs generalizing prior with
  | nil =>
      simp only [Paired.Increments.values, IncrementArea.pathArea, IncrementArea.traceArea,
        Paired.Increments.correctedArea, Paired.Increments.total, IncrementArea.area_zero_left, add_zero, -eq_self,
        -iff_self]
      rfl
  | cons pair rest ih =>
      have tail := ih (prior + (pair.1 + pair.2))
      calc
        _ = (IncrementArea.pathArea (Paired.Increments.values rest) + Paired.Increments.correctedArea referenceReturn
          (prior + (pair.1 + pair.2)) rest) +
            BoundaryRibbon.area pair.2 (Paired.Increments.total rest) + BoundaryRibbon.area pair.1 (pair.2 +
              Paired.Increments.total rest) +
            BoundaryRibbon.area (pair.1 + pair.2) (pair.1 + referenceReturn + prior) := by
          simp only [Paired.Increments.values, IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
            Paired.Increments.values_total, Paired.Increments.correctedArea]
          ring1
        _ = BoundaryRibbon.area (Paired.Increments.total rest) (referenceReturn + (prior + (pair.1 + pair.2))) +
            BoundaryRibbon.area pair.2 (Paired.Increments.total rest) + BoundaryRibbon.area pair.1 (pair.2 +
              Paired.Increments.total rest) +
            BoundaryRibbon.area (pair.1 + pair.2) (pair.1 + referenceReturn + prior) := by rw [tail]
        _ = _ := by
          simp only [Paired.Increments.total, IncrementArea.area_add_left, IncrementArea.area_add_right,
            IncrementArea.area_self]
          rw [Paired.Increments.skew (Paired.Increments.total rest) pair.1, Paired.Increments.skew
            (Paired.Increments.total rest) pair.2, Paired.Increments.skew pair.2 pair.1]
          ring1

/-- Appending the original forward reference gives the exact odd-length paired area formula. -/
theorem odd (referenceReturn referenceForward : IncrementArea.Gaussian) (pairs : List (IncrementArea.Gaussian ×
  IncrementArea.Gaussian)) :
    IncrementArea.pathArea (Paired.Increments.values pairs ++ [referenceForward]) + Paired.Increments.correctedArea
      referenceReturn 0 pairs =
      BoundaryRibbon.area (Paired.Increments.total pairs) (referenceForward + referenceReturn) := by
  have paired := Paired.Increments.formula referenceReturn 0 pairs
  rw [add_zero] at paired
  rw [IncrementArea.pathArea_append, Paired.Increments.values_total]
  simp only [IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, show IncrementArea.pathArea [] = 0
    from rfl,
    IncrementArea.area_zero_right, add_zero]
  calc
    _ = (IncrementArea.pathArea (Paired.Increments.values pairs) + Paired.Increments.correctedArea referenceReturn 0
      pairs) + BoundaryRibbon.area (Paired.Increments.total pairs) referenceForward := by
      ring1
    _ = _ := by rw [paired, IncrementArea.area_add_right]; ring1

/-- Appending the original forward and final-return increments gives the exact even-length paired area formula.

The terminal cross term retains both references, the original paired total and the separate final return displacement.
-/
theorem even (referenceReturn referenceForward finalReturn : IncrementArea.Gaussian) (pairs : List
  (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    IncrementArea.pathArea (Paired.Increments.values pairs ++ [referenceForward, finalReturn]) +
      Paired.Increments.correctedArea referenceReturn 0 pairs =
      BoundaryRibbon.area (Paired.Increments.total pairs) (referenceForward + referenceReturn) +
        BoundaryRibbon.area (referenceForward + Paired.Increments.total pairs) (Paired.Increments.total pairs +
          (referenceForward + finalReturn)) := by
  have paired := Paired.Increments.formula referenceReturn 0 pairs
  rw [add_zero] at paired
  rw [IncrementArea.pathArea_append, Paired.Increments.values_total]
  simp only [IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, show IncrementArea.pathArea [] = 0
    from rfl,
    IncrementArea.area_zero_right, add_zero, zero_add]
  change IncrementArea.pathArea (Paired.Increments.values pairs) + BoundaryRibbon.area referenceForward finalReturn +
    BoundaryRibbon.area (Paired.Increments.total pairs) (referenceForward + finalReturn) + _ = _
  calc
    _ = (IncrementArea.pathArea (Paired.Increments.values pairs) + Paired.Increments.correctedArea referenceReturn 0
      pairs) + BoundaryRibbon.area referenceForward finalReturn +
        BoundaryRibbon.area (Paired.Increments.total pairs) (referenceForward + finalReturn) := by ring1
    _ = _ := by
      rw [paired]
      simp only [IncrementArea.area_add_left, IncrementArea.area_add_right, IncrementArea.area_self]
      rw [Paired.Increments.skew referenceForward (Paired.Increments.total pairs)]
      ring1

end Purelib.Integration.Path.Paired.Increments
