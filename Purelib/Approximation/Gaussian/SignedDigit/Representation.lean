module
public import Purelib.Approximation.Gaussian.Representation.Ball
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.SignedDigit.Cell
public import Purelib.Approximation.Gaussian.SignedDigit.Geometry
public import Purelib.Approximation.Gaussian.Translation.Observation
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.SignedDigit (Cell)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.SignedDigit

open Purelib.Approximation.Gaussian.SignedDigit.Cell

open Purelib.Approximation.Gaussian.Translation

section
@[expose] public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Approximation.Gaussian.SignedDigit.Representation

/-- Represent signed-digit observations by their original closed cells and pointwise refinements.

The observation retains its exact centre witness, squared precision gauge and redundant boundary convention. -/
def representation :
  Approximation.Gaussian.Representation where
  Observation := Cell
  Possible cell value := cell.Contains value
  witness cell := cell.center
  witness_possible cell := cell.contains_center
  Refines inner outer := inner.Refines outer
  refines_refl := Cell.refines_refl
  refines_trans := Cell.refines_trans
  possible_persists refines possible := refines possible
  precisionSq cell := cell.precisionSq
  precisionSq_nonneg cell := cell.precisionSq_nonneg
  boundary := .redundant

/-- Forget signed syntax while retaining its exact closed-square enclosure as a Gaussian-rational ball. -/
def toBall : Observation.ObservationMap
  representation
    Ball.ballRepresentation where
  map cell := cell.toBall
  covers inside := Cell.toBall_contains inside
  coherent := by
    intro inner outer refines
    refine ⟨inner.center, ?_, ?_⟩
    · exact inner.toBall.contains_center
    · exact Cell.toBall_contains (refines inner.contains_center)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le cell := by
    change 2 * cell.tail ^ 2 ≤ cell.precisionSq + 0
    rw [cell.precisionSq_eq_two_tailSq]
    exact le_of_eq (by ring1)
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 2 }
  costBound _ := 2
  cost_le _ := Nat.le_refl 2
end Purelib.Approximation.Gaussian.SignedDigit.Representation

end
