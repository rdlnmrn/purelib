module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Segment

import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Paths.RectangularPairedSegments
public import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-! One finite physical trace supplies both retained model owners.
Coordinates and their containment certificates are shared by both banks. -/
namespace Purelib.Riemann.Integration.RectangularPairedPointBanks

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_zero line_one)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}

open Purelib.Data in
open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- A cached finite parameter and point trace on the original doubly owned segment piece.

Every parameter lies in the unit interval, its first and last entries retain the original endpoints, and every point
cache keeps its exact affine readback. -/
structure Trace (piece : PairedSegmentPiece leftGeometry rightGeometry) (count : Nat) where
  /-- The retained original finite parameter vector. -/ parameters : Data.Vector Coordinate (count + 1)
  /-- Every retained parameter belongs to the original unit interval. -/ within : ∀ vertex, 0 ≤ parameters vertex ∧
    parameters vertex ≤ 1
  /-- The retained first parameter is exactly zero. -/ first_eq : parameters 0 = 0
  /-- The retained final parameter is exactly one. -/ last_eq : parameters (Fin.last count) = 1
  /-- The cached original affine trace-point vector. -/ points : Data.Vector Gaussian (count + 1)
  /-- Every cached point equals the original segment's affine readback at its retained parameter. -/ points_eq : ∀
    vertex, points vertex = Affine.line piece.first (piece.last - piece.first) (parameters vertex)

constructive_injectivity Trace

namespace Trace

variable {piece : PairedSegmentPiece leftGeometry rightGeometry} {count : Nat}

open Purelib.Data in
open Purelib.Geometry.Rational in
/-- Cache the original paired piece's points at the supplied retained parameter vector. -/
def build (piece : PairedSegmentPiece leftGeometry rightGeometry)
    (parameters : Data.Vector Coordinate (count + 1))
    (within : ∀ vertex, 0 ≤ parameters vertex ∧ parameters vertex ≤ 1)
    (first_eq : parameters 0 = 0) (last_eq : parameters (Fin.last count) = 1) : Trace piece count :=
  ⟨parameters, within, first_eq, last_eq,
    Vector.Basic.vectorOfFn (fun vertex => Affine.line piece.first (piece.last - piece.first) (parameters vertex)),
    fun vertex => Vector.Basic.vectorOfFn_apply _ vertex⟩

/-- The retained trace starts at the original paired piece's first point. -/
theorem first_point (trace : Trace piece count) : trace.points 0 = piece.first := by
  rw [trace.points_eq, trace.first_eq, line_zero]

/-- The retained trace ends at the original paired piece's last point. -/
theorem last_point (trace : Trace piece count) : trace.points (Fin.last count) = piece.last := by
  rw [trace.points_eq, trace.last_eq, line_one]

section
open Purelib.Geometry.Rational
/-- Every retained trace point belongs to the original left-grid owner cell. -/
theorem left_contains (trace : Trace piece count) (vertex : Fin (count + 1)) :
    (leftGeometry.box piece.leftColumn piece.leftRow).Contains (trace.points vertex) := by
  rw [trace.points_eq]
  exact Box.contains_line piece.leftFirst piece.leftLast (trace.within vertex)

/-- Every retained trace point belongs to the original right-grid owner cell. -/
theorem right_contains (trace : Trace piece count) (vertex : Fin (count + 1)) :
    (rightGeometry.box piece.rightColumn piece.rightRow).Contains (trace.points vertex) := by
  rw [trace.points_eq]
  exact Box.contains_line piece.rightFirst piece.rightLast (trace.within vertex)

end

open Purelib
open Purelib.Data
/-- Cache the retained trace's primitive readings through its exact original left cell owner. -/
def leftReadings (trace : Trace piece count) {polynomial numerator : Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => trace.points vertex) :=
  let owners := Vector.Basic.vectorOfFn fun vertex =>
    (⟨piece.leftColumn, piece.leftRow, trace.points vertex, trace.left_contains vertex⟩ : OwnedVertex leftGeometry)
  PointReadings.build anchors offsets (fun vertex => trace.points vertex) owners
    (fun vertex => by dsimp only [owners]; rw [Vector.Basic.vectorOfFn_apply])

/-- Cache the retained trace's primitive readings through its exact original right cell owner. -/
def rightReadings (trace : Trace piece count) {polynomial numerator : Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => trace.points vertex) :=
  let owners := Vector.Basic.vectorOfFn fun vertex =>
    (⟨piece.rightColumn, piece.rightRow, trace.points vertex, trace.right_contains vertex⟩ : OwnedVertex rightGeometry)
  PointReadings.build anchors offsets (fun vertex => trace.points vertex) owners
    (fun vertex => by dsimp only [owners]; rw [Vector.Basic.vectorOfFn_apply])

/-- The left reading cache equals the aligned primitive at the exact original left owner and trace point. -/
theorem leftReadings_value (trace : Trace piece count) {polynomial numerator : Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (vertex : Fin
      (count + 1)) :
    (trace.leftReadings anchors offsets).values vertex =
      anchors.alignedValue offsets piece.leftColumn piece.leftRow (trace.points vertex) := by
  rw [(trace.leftReadings anchors offsets).value_eq]
  dsimp only [leftReadings, PointReadings.build]
  rw [Vector.Basic.vectorOfFn_apply]

/-- The right reading cache equals the aligned primitive at the exact original right owner and trace point. -/
theorem rightReadings_value (trace : Trace piece count) {polynomial numerator : Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (vertex : Fin
      (count + 1)) :
    (trace.rightReadings anchors offsets).values vertex =
      anchors.alignedValue offsets piece.rightColumn piece.rightRow (trace.points vertex) := by
  rw [(trace.rightReadings anchors offsets).value_eq]
  dsimp only [rightReadings, PointReadings.build]
  rw [Vector.Basic.vectorOfFn_apply]

end Trace
end Purelib.Riemann.Integration.RectangularPairedPointBanks
