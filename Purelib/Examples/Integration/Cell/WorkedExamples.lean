module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Rat.Interval.Basic
import Purelib.Integration.Cell.Basic
import Purelib.Integration.Cell.Process
public import Purelib.Integration.Cell.Refinement

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Split
import Purelib.Data.List.Event
public import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Refinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Integration.Cell.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Measure
open Purelib.Examples

/-! ## Finite lower and upper integration -/

/-- Two equally weighted integration cells with value ranges [0,1/4] and [1/2,3/4]. -/
def rangedCells : List (IntegrationCell Nat) :=
  [⟨0, 1 / 2, by decide, 0, 1 / 4, by decide⟩,
    ⟨1, 1 / 2, by decide, 1 / 2, 3 / 4, by decide⟩]

/-- The displayed two-cell lower integral is one quarter. -/
example : (Purelib.Integration.integralBound rangedCells).lower = 1 / 4 := by
  decide

/-- The displayed two-cell upper integral is one half. -/
example : (Purelib.Integration.integralBound rangedCells).upper = 1 / 2 := by
  decide

/-- The displayed integral enclosure has width one quarter. -/
example : (Purelib.Integration.integralBound rangedCells).width = 1 / 4 := by
  decide

/-- The displayed cell reading, one eighth at index zero and five eighths elsewhere. -/
def sampledValue (index : Nat) : Rational :=
  if index == 0 then 1 / 8 else 5 / 8

/-- The exact weighted sample lies inside the retained two-cell integral enclosure. -/
example : (Purelib.Integration.integralBound rangedCells).Contains
    (Purelib.Integration.weightedEvaluation sampledValue
      rangedCells) := by
  apply weightedEvaluation_mem_integralBound
  intro cell member
  simp only [-eq_self, -iff_self, rangedCells] at member
  have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
    (fun equal => Or.inl equal)
    (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
  rcases member with rfl | rfl <;> decide

/-- The unit-weight integration cell with value range [0,1]. -/
def integrationParent : IntegrationCell Unit :=
  ⟨(), 1, by decide, 0, 1, by decide⟩

/-- The two half-weight child cells with ranges [0,1/4] and [3/4,1]. -/
def integrationChildren : List (IntegrationCell Unit) :=
  [⟨(), 1 / 2, by decide, 0, 1 / 4, by decide⟩,
    ⟨(), 1 / 2, by decide, 3 / 4, 1, by decide⟩]

/-- The retained split of the unit integration cell into two half-weight children.

The children conserve weight and refine both endpoints of the parent value interval. -/
def integrationResolution : IntegrationSplit
  integrationParent where
  children := integrationChildren
  weight_conserved := by decide
  lower_refines := by
    intro child member
    simp only [-eq_self, -iff_self, integrationChildren] at member
    have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
      (fun equal => Or.inl equal)
      (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
    rcases member with rfl | rfl <;> decide
  upper_refines := by
    intro child member
    simp only [-eq_self, -iff_self, integrationChildren] at member
    have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
      (fun equal => Or.inl equal)
      (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
    rcases member with rfl | rfl <;> decide

/-- The child-cell integral enclosure refines the singleton parent enclosure. -/
example : Purelib.Data.Rat.Interval.Refines (Purelib.Integration.integralBound
  integrationChildren)
    (Purelib.Integration.integralBound [integrationParent]) :=
  integrationResolution.integralBound_refines

/-- The displayed two-child integration frontier refines the singleton parent frontier. -/
theorem integrationFrontierRefinement :
    IntegrationFrontierRefines integrationChildren
      [integrationParent] := by
  change IntegrationFrontierRefines integrationResolution.children
    [integrationParent]
  simpa only [List.nil_append, Purelib.Data.List.Append.append_nil] using
    (IntegrationFrontierRefines.split [] [] integrationParent
      integrationResolution)

/-- The retained split does not increase the integration frontier oscillation. -/
example : Purelib.Integration.integralOscillation integrationChildren ≤
    Purelib.Integration.integralOscillation [integrationParent] :=
  integrationFrontierRefinement.oscillation_le

/-- The retained split preserves the integration frontier total weight. -/
example : integrationWeight integrationChildren =
    integrationWeight [integrationParent] :=
  integrationFrontierRefinement.weight_conserved

/-- The displayed child frontier has exact integral bounds three eighths and five eighths. -/
example : (Purelib.Integration.integralBound integrationChildren).lower = 3 / 8 ∧
    (Purelib.Integration.integralBound integrationChildren).upper = 5 / 8 := by
  decide

/-- The equally weighted Boolean entries with exact values one quarter and three quarters. -/
def exactSimpleEntries : List (Weighted (Bool ×
  Rational)) :=
  [⟨(false, 1 / 4), 1 / 2, by decide⟩,
    ⟨(true, 3 / 4), 1 / 2, by decide⟩]

/-- The exact simple integration process meets every retained request tolerance after running the finite request list.
-/
example (request : Purelib.Approximation.AccuracyRequest) (requests : List Purelib.Approximation.AccuracyRequest)
    (member : request ∈ requests) :
    Purelib.Integration.integralOscillation
      ((Purelib.Integration.IntegrationProcess.exactSimple exactSimpleEntries).frontier
        ((Purelib.Integration.IntegrationProcess.exactSimple
          exactSimpleEntries).runRequests
          () requests)) < request.tolerance :=
  IntegrationProcess.runRequests_oscillation_lt_of_mem
    (Purelib.Integration.IntegrationProcess.exactSimple exactSimpleEntries)
      () requests request member

end Purelib.Examples.Integration.Cell.WorkedExamples

end
