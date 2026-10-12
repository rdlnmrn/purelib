module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
public import Purelib.Integration.Cell.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.IntervalIntegration
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Finite rational box integration

Displayed RFAP boxes supply exact nonnegative cell weights for the generic
finite integration layer.  Vertical and horizontal rational cuts become
certified integration subdivisions by exact finite area conservation.
-/

public section

namespace Purelib.Integration.Box.Cell

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- A rational box with ordered lower and upper integrand readings.

The box's exact content supplies its integration weight, separately from the retained value enclosure. -/
structure BoxIntegrationCell where
  /-- The exact rational box forming the cell domain. -/ box : Box
  /-- The retained lower integrand reading. -/ lower : Fraction.Rational
  /-- The retained upper integrand reading. -/ upper : Fraction.Rational
  /-- The lower integrand reading does not exceed the upper reading. -/ range_valid : lower ≤ upper

constructive_injectivity BoxIntegrationCell

namespace BoxIntegrationCell

open Purelib in
open Purelib.Geometry.Rational in
open Purelib.Integration in
/-- Use the original box and its nonnegative content as the payload and weight of the retained range enclosure. -/
@[expose] def toIntegrationCell (cell :
  Box.Cell.BoxIntegrationCell) :
    Integration.IntegrationCell Box where
  item := cell.box
  weight := Box.Content.boxContent cell.box
  weight_nonnegative := Box.Content.boxContent_nonneg cell.box
  lower := cell.lower
  upper := cell.upper
  range_valid := cell.range_valid

open Purelib.Geometry.Rational in
open Purelib.Integration in
/-- Replace the box while retaining both original range endpoints and their order certificate. -/
@[expose] def sameRange (parent : Box.Cell.BoxIntegrationCell)
  (box : Box) :
    Box.Cell.BoxIntegrationCell :=
  ⟨box, parent.lower, parent.upper, parent.range_valid⟩

end BoxIntegrationCell

section
open Purelib
open Purelib.Geometry.Rational
open Purelib.Integration
/-- Convert the original ordered box cells into weighted integration cells without changing occurrences. -/
@[expose] def boxIntegrationCells (cells : List BoxIntegrationCell) :
    List (Integration.IntegrationCell Box) :=
  cells.map BoxIntegrationCell.toIntegrationCell

/-- The converted frontier's weight is the exact sum of the original box contents. -/
theorem integrationWeight_boxIntegrationCells :
    ∀ cells : List BoxIntegrationCell,
      Integration.integrationWeight (boxIntegrationCells cells) =
        (cells.map fun cell => Box.Content.boxContent cell.box).sum
  | [] => rfl
  | cell :: remaining => by
      simp only [boxIntegrationCells, List.map_cons,
        Integration.integrationWeight,
        BoxIntegrationCell.toIntegrationCell, List.sum_cons]
      change Box.Content.boxContent cell.box +
          Integration.integrationWeight
            (boxIntegrationCells remaining) =
        Box.Content.boxContent cell.box +
          (remaining.map fun candidate => Box.Content.boxContent candidate.box).sum
      rw [integrationWeight_boxIntegrationCells remaining]

end

section
open Purelib
open Purelib.Integration
/-- Enclose the weighted integral of the retained box-cell frontier. -/
@[expose] def boxIntegralBound (cells : List BoxIntegrationCell) :
    Data.Rat.Interval :=
  Integration.integralBound (boxIntegrationCells cells)

/-- The box integral enclosure's width is the converted cells' weighted oscillation. -/
theorem boxIntegralBound_width (cells : List BoxIntegrationCell) :
    (boxIntegralBound cells).width =
      Integration.integralOscillation
        (boxIntegrationCells cells) :=
  Integration.integralBound_width _
end

namespace BoxIntegrationSplit
end BoxIntegrationSplit
namespace EffectiveNull
end EffectiveNull

end Purelib.Integration.Box.Cell

end
