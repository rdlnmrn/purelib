module
import Purelib.Data.Vector.Basic

import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Tactic.Ring

@[expose] public section

/-! Translate retained offsets and readings without rebuilding primitive polynomials. -/
namespace Purelib.Riemann.Integration.RectangularPrimitiveTranslation.Offsets
open _root_.Purelib.LinearAlgebra.Grid (Offsets)
open _root_.Purelib.LinearAlgebra.Grid.Offsets (Gaussian)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
variable {columns rows : Nat} {edges : Offsets.Edges columns rows}

open Purelib.Data
open Purelib.LinearAlgebra
/-- Translate every retained grid offset by one Gaussian constant.

The same horizontal and initial vertical edge equations remain valid after the common translation. -/
def translate (offsets : LinearAlgebra.Grid.Offsets edges) (shift : Grid.Offsets.Gaussian) : LinearAlgebra.Grid.Offsets
  edges where
  values := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => offsets.values column row + shift
  horizontal := by
    intro column row
    simp only [Vector.Basic.vectorOfFn_apply]
    rw [offsets.horizontal column row]
    ring1
  firstVertical := by
    intro row
    simp only [Vector.Basic.vectorOfFn_apply]
    rw [offsets.firstVertical row]
    ring1

/-- The translated offset cache adds the same constant at every grid cell.

Both retained cell indices read the original offset cache before adding the supplied Gaussian shift. -/
theorem translate_value (offsets : LinearAlgebra.Grid.Offsets edges) (shift : Grid.Offsets.Gaussian)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (translate offsets shift).values column row = offsets.values column row + shift := by
  simp only [translate, Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self]
  rfl

end Purelib.Riemann.Integration.RectangularPrimitiveTranslation.Offsets

namespace Purelib.Riemann.Integration.RectangularPrimitiveTranslation.RectangularInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
variable {polynomial numerator : Polynomial} {columns rows count : Nat} {geometry : Geometry columns rows}
  {models : Bank polynomial geometry} {primitives : Primitives models numerator}
  {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
  {points : Fin count → Gaussian}

open Purelib.Riemann in
open Purelib.LinearAlgebra in
/-- Translating the offsets adds the same constant to each aligned primitive value. -/
theorem PrimitiveAnchors.alignedValue_translate (anchors : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (shift : Gaussian)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : Gaussian) :
    anchors.alignedValue (Integration.RectangularPrimitiveTranslation.Offsets.translate offsets shift) column row point
      =
      anchors.alignedValue offsets column row point + shift := by
  simp only [PrimitiveAnchors.alignedValue, Integration.RectangularPrimitiveTranslation.Offsets.translate_value]
  ring1

open Purelib.Riemann in
open Purelib.Data in
/-- Translate cached point readings while preserving their exact owners.

Each value receives the same Gaussian shift and remains tied to the translated offsets and original primitive anchors.
-/
def PointReadings.translate (readings : PointReadings anchors offsets points) (shift : Gaussian) :
    PointReadings anchors (Integration.RectangularPrimitiveTranslation.Offsets.translate offsets shift) points where
  owners := readings.owners
  point_eq := readings.point_eq
  values := Vector.Basic.vectorOfFn fun vertex => readings.values vertex + shift
  value_eq := by
    intro vertex
    rw [Vector.Basic.vectorOfFn_apply, readings.value_eq, PrimitiveAnchors.alignedValue_translate anchors]

open Purelib.Data in
/-- A translated point reading is its original cached value plus the common shift. -/
theorem PointReadings.translate_value (readings : PointReadings anchors offsets points) (shift : Gaussian)
    (vertex : Fin count) : (PointReadings.translate readings shift).values vertex = readings.values vertex + shift :=
  Vector.Basic.vectorOfFn_apply _ _

/-- A common translation preserves every difference of retained point readings. -/
theorem PointReadings.translate_increment (readings : PointReadings anchors offsets points) (shift : Gaussian)
    (first last : Fin count) :
    (PointReadings.translate readings shift).values last - (PointReadings.translate readings shift).values first =
      readings.values last - readings.values first := by
  rw [PointReadings.translate_value readings, PointReadings.translate_value readings]
  ring1

end Purelib.Riemann.Integration.RectangularPrimitiveTranslation.RectangularInverseModels
