module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Cell.Basic
public import Purelib.Integration.Cell.Refinement

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Integration.Box.Cell
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Subdivision

/-!
# Finite rational box integration

Displayed RFAP boxes supply exact nonnegative cell weights for the generic
finite integration layer.  Vertical and horizontal rational cuts become
certified integration subdivisions by exact finite area conservation.
-/

@[expose] public section

namespace Purelib.Integration.Box.Refinement
namespace BoxIntegrationCell
end BoxIntegrationCell

set_option genInjectivity false in
open Purelib.Geometry.Rational in
open Purelib.Integration in
/-- A retained box cell split into content-conserving children with tighter value enclosures.

The certificate preserves the original parent and ordered child list, bounding every child range inside the original
range. -/
structure BoxIntegrationSplit (parent : Box.Cell.BoxIntegrationCell) where
  /-- The ordered original child box-cell list. -/ children : List Box.Cell.BoxIntegrationCell
  /-- The child box contents sum to the exact parent box content. -/ content_conserved :
    (children.map fun child => Box.Content.boxContent child.box).sum =
      Box.Content.boxContent parent.box
  /-- Each retained child's lower range endpoint is at least the parent's. -/ lower_refines : ∀ child, child ∈ children
    → parent.lower ≤ child.lower
  /-- Each retained child's upper range endpoint is at most the parent's. -/ upper_refines : ∀ child, child ∈ children →
    child.upper ≤ parent.upper

constructive_injectivity BoxIntegrationSplit

namespace BoxIntegrationSplit

open Purelib in
open Purelib.Data.List in
open Purelib.Integration in
/-- Convert the exact box split into its weight-conserving integration-cell split. -/
def toIntegrationSplit {parent :
  Box.Cell.BoxIntegrationCell}
    (split : Box.Refinement.BoxIntegrationSplit parent) :
    Integration.IntegrationSplit parent.toIntegrationCell where
  children := Box.Cell.boxIntegrationCells split.children
  weight_conserved := by
    rw [Box.Cell.integrationWeight_boxIntegrationCells, split.content_conserved]
    rfl
  lower_refines := by
    intro child member
    unfold Box.Cell.boxIntegrationCells at member
    rcases Map.mem_map.mp member with ⟨boxChild, boxChildMember, rfl⟩
    exact split.lower_refines boxChild boxChildMember
  upper_refines := by
    intro child member
    unfold Box.Cell.boxIntegrationCells at member
    rcases Map.mem_map.mp member with ⟨boxChild, boxChildMember, rfl⟩
    exact split.upper_refines boxChild boxChildMember

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- The converted child boxes' integral enclosure refines the original singleton cell enclosure. -/
theorem integralBound_refines {parent :
  Box.Cell.BoxIntegrationCell}
    (split : Box.Refinement.BoxIntegrationSplit parent) :
    Interval.Refines
      (Integration.integralBound
        (Box.Cell.boxIntegrationCells split.children))
      (Integration.integralBound [parent.toIntegrationCell]) :=
  split.toIntegrationSplit.integralBound_refines

end BoxIntegrationSplit

open Purelib.Geometry.Rational in
open Purelib.Integration in
/-- Attaching the parent's range to the retained boxes leaves their exact content list unchanged. -/
theorem boxContent_sameRange_cells (parent : Box.Cell.BoxIntegrationCell) :
    ∀ boxes : List Box,
      (boxes.map parent.sameRange).map
          (fun child => Box.Content.boxContent child.box) =
        boxes.map Box.Content.boxContent
  | [] => rfl
  | box :: remaining => by
      simp only [List.map_cons, Box.Cell.BoxIntegrationCell.sameRange]
      rw [boxContent_sameRange_cells parent remaining]

open Purelib.Data.List in
open Purelib.Geometry.Rational in
open Purelib.Integration in
/-- Construct a box split from the retained content-conserving box list using the original parent range throughout. -/
def sameRangeSplit (parent : Box.Cell.BoxIntegrationCell) (boxes : List
  Box)
    (conserved : (boxes.map Box.Content.boxContent).sum = Box.Content.boxContent parent.box) :
    BoxIntegrationSplit parent where
  children := boxes.map parent.sameRange
  content_conserved := by
    rw [boxContent_sameRange_cells]
    exact conserved
  lower_refines := by
    intro child member
    rcases Map.mem_map.mp member with ⟨box, boxMember, rfl⟩
    exact le_rfl
  upper_refines := by
    intro child member
    rcases Map.mem_map.mp member with ⟨box, boxMember, rfl⟩
    exact le_rfl

section
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration
/-- Split the original box vertically at the retained in-bounds cut while preserving its value range. -/
def verticalSameRangeSplit (parent : Box.Cell.BoxIntegrationCell)
    (cut : Fraction.Rational)
    (inside : parent.box.xLower ≤ cut ∧ cut ≤ parent.box.xUpper) :
    BoxIntegrationSplit parent :=
  sameRangeSplit parent
    [parent.box.verticalLeft cut inside, parent.box.verticalRight cut inside]
    (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact Box.Content.vertical_content_add parent.box cut inside)

/-- Split the original box horizontally at the retained in-bounds cut while preserving its value range. -/
def horizontalSameRangeSplit (parent : Box.Cell.BoxIntegrationCell)
    (cut : Fraction.Rational)
    (inside : parent.box.yLower ≤ cut ∧ cut ≤ parent.box.yUpper) :
    BoxIntegrationSplit parent :=
  sameRangeSplit parent
    [parent.box.horizontalLower cut inside,
      parent.box.horizontalUpper cut inside]
    (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact Box.Content.horizontal_content_add parent.box cut inside)

end

section
open Purelib
open Purelib.Data.Rat
open Purelib.Integration
/-- The retained vertical same-range split refines the original integral enclosure. -/
theorem verticalSameRange_integralBound_refines
    (parent : Box.Cell.BoxIntegrationCell) (cut : Fraction.Rational)
    (inside : parent.box.xLower ≤ cut ∧ cut ≤ parent.box.xUpper) :
    Interval.Refines
      (Integration.integralBound
        (Box.Cell.boxIntegrationCells
          (verticalSameRangeSplit parent cut inside).children))
      (Integration.integralBound [parent.toIntegrationCell]) :=
  (verticalSameRangeSplit parent cut inside).integralBound_refines

/-- The retained horizontal same-range split refines the original integral enclosure. -/
theorem horizontalSameRange_integralBound_refines
    (parent : Box.Cell.BoxIntegrationCell) (cut : Fraction.Rational)
    (inside : parent.box.yLower ≤ cut ∧ cut ≤ parent.box.yUpper) :
    Interval.Refines
      (Integration.integralBound
        (Box.Cell.boxIntegrationCells
          (horizontalSameRangeSplit parent cut inside).children))
      (Integration.integralBound [parent.toIntegrationCell]) :=
  (horizontalSameRangeSplit parent cut inside).integralBound_refines
end

namespace EffectiveNull
end EffectiveNull

end Purelib.Integration.Box.Refinement

end
