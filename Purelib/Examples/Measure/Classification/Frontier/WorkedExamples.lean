module
import Purelib.Data.Rat.Interval.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Refinement
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Split
import Purelib.Data.List.Event
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Classification.Frontier.WorkedExamples

open Purelib.Measure
open Purelib.Examples

/-! ## Unresolved event mass and certified refinement -/

/-- The three-entry event frontier with inside mass one quarter, unresolved mass one half and outside mass one quarter.
-/
def unresolvedFrontier : List (Classified Nat) :=
  [⟨⟨0, 1 / 4, by decide⟩, .inside⟩,
    ⟨⟨1, 1 / 2, by decide⟩, .unresolved⟩,
    ⟨⟨2, 1 / 4, by decide⟩, .outside⟩]

/-- The displayed unresolved frontier has lower event bound one quarter. -/
example : (Purelib.Measure.eventBound unresolvedFrontier).lower = 1 / 4
  := by
  decide

/-- The displayed unresolved frontier has upper event bound three quarters. -/
example : (Purelib.Measure.eventBound unresolvedFrontier).upper = 3 / 4
  := by
  decide

/-- The displayed unresolved frontier has enclosure width one half. -/
example : (Purelib.Measure.eventBound unresolvedFrontier).width = 1 / 2
  := by
  decide

/-- The unit-weight unresolved parent event entry. -/
def unresolvedParent : Classified Unit :=
  ⟨⟨(), 1, by decide⟩, .unresolved⟩

/-- The two equally weighted Boolean children with inside and outside statuses. -/
def resolvedChildren : List (Classified Bool) :=
  [⟨⟨false, 1 / 2, by decide⟩, .inside⟩,
    ⟨⟨true, 1 / 2, by decide⟩, .outside⟩]

/-- The retained conservative split of the unresolved parent into the displayed Boolean children. -/
def binaryResolution : Split (β := Bool)
  unresolvedParent where
  children := resolvedChildren
  conserved := by decide
  statuses := by
    intro child member
    trivial

/-- The resolved child event enclosure refines the unresolved parent enclosure. -/
example : Purelib.Data.Rat.Interval.Refines (Purelib.Measure.eventBound
  resolvedChildren)
    (Purelib.Measure.eventBound [unresolvedParent]) :=
  binaryResolution.eventBound_refines

/-- The resolved children give the exact event enclosure [1/2,1/2]. -/
example : (Purelib.Measure.eventBound resolvedChildren).lower = 1 / 2 ∧
    (Purelib.Measure.eventBound resolvedChildren).upper = 1 / 2 := by
  decide

/-- The singleton unresolved unit-weight frontier. -/
def coarseFrontier : List (Classified Unit) :=
  [unresolvedParent]

/-- The two resolved half-weight unit entries replacing the unresolved parent. -/
def refinedFrontier : List (Classified Unit) :=
  [⟨⟨(), 1 / 2, by decide⟩, .inside⟩,
    ⟨⟨(), 1 / 2, by decide⟩, .outside⟩]

/-- The retained conservative split into the displayed unit-valued child frontier. -/
def unitResolution : Split (β := Unit)
  unresolvedParent where
  children := refinedFrontier
  conserved := by decide
  statuses := by
    intro child member
    trivial

/-- The displayed child frontier refines the singleton parent frontier. -/
example : Purelib.Measure.FrontierRefines refinedFrontier
  coarseFrontier := by
  change Purelib.Measure.FrontierRefines unitResolution.children
    [unresolvedParent]
  simpa only [List.nil_append, List.append_nil] using
    (FrontierRefines.split [] [] unresolvedParent
      unitResolution)

/-- The retained frontier refinement does not increase unresolved weight. -/
example : Purelib.Measure.unresolvedWeight refinedFrontier ≤
    Purelib.Measure.unresolvedWeight coarseFrontier := by
  have relation : FrontierRefines unitResolution.children
    [unresolvedParent] :=
    by
      simpa only [List.nil_append, List.append_nil] using
        (FrontierRefines.split [] [] unresolvedParent
          unitResolution)
  exact relation.unresolved_le

end Purelib.Examples.Measure.Classification.Frontier.WorkedExamples

end
