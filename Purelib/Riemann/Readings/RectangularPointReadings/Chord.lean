module

public import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Riemann.Paths.ClearBoxPaths.Chord
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Tactic.Ring

/-! # Actual chord readings on an unchanged rectangular primitive bank

One supplied bank, geometry, primitive family, anchor cache and offset grid
remain the original numerical owners. Only a three-slot same-cell reader
is constructed. The actual supplied triangle bank keeps all its original
locations and values. Both endpoints and every signed route occurrence
remain literal; no root, domain or primitive bank is transported.
-/

public section

namespace Purelib.Riemann.Readings.RectangularPointReadings.Chord

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Geometry.Rational (Box)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {target : Rational}
    (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    {first last : Canonical}
    (targetReadings : PointReadings anchors offsets (ClearBoxPaths.Chord.coordinate first last))
    (refines : ∀ column row, (geometry.box column row).Refines ambient)

/-- Compare one unchanged cell's raw primitive increment with the actual same-bank signed chord route.

The two cached endpoint locations are independently paid by the original
increment comparison. The same-cell offset cancels exactly. The supplied
three-slot triangle values telescope along the original oriented chord
incidence, preserving all repeated and stationary slot occurrences.
-/
def compareCell (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (firstCell : (geometry.box column row).Contains first)
    (lastCell : (geometry.box column row).Contains last) :
    {fixed : PointReadings anchors offsets (ClearBoxPaths.Chord.coordinate first last) //
      fixed = PointReadings.inCell anchors offsets column row
        (ClearBoxPaths.Chord.coordinate first last) (ClearBoxPaths.Chord.coordinate_inside firstCell lastCell) ∧
      Norm.Basic.normSq
        (((primitives.dense column row).value.eval last - (primitives.dense column row).value.eval first) -
          SewingRetraction.wordValue
            (fun edge : OrientedEdge 3 => targetReadings.values edge.finish - targetReadings.values edge.start)
            ClearBoxPaths.Chord.incidence.path) ≤ 16 * request.globalBound} := by
  let fixed := PointReadings.inCell anchors offsets column row (ClearBoxPaths.Chord.coordinate first last)
    (ClearBoxPaths.Chord.coordinate_inside firstCell lastCell)
  have raw := PointReadings.inCell_increment anchors offsets column row
    (ClearBoxPaths.Chord.coordinate first last) (ClearBoxPaths.Chord.coordinate_inside firstCell lastCell) 1 2
  have endpoints := ClearBoxPaths.Chord.coordinate_values first last
  have rawEndpoints : fixed.values 2 - fixed.values 1 =
      (primitives.dense column row).value.eval last - (primitives.dense column row).value.eval first :=
    raw.trans (congrArg₂ (fun last first : Canonical =>
      (primitives.dense column row).value.eval last - (primitives.dense column row).value.eval first)
      endpoints.2.2 endpoints.2.1)
  let values := fun edge : OrientedEdge 3 =>
    targetReadings.values edge.finish - targetReadings.values edge.start
  have route : SewingRetraction.wordValue values ClearBoxPaths.Chord.incidence.path =
      targetReadings.values 2 - targetReadings.values 1 := by
    rewrite [ClearBoxPaths.Chord.incidence_path]
    change (targetReadings.values 0 - targetReadings.values 1) +
      ((targetReadings.values 2 - targetReadings.values 0) + 0) = _
    ring1
  have paid := RectangularPointReadings.GridPrimitiveAccuracy.increment_comparison_bound
    (bank := bank) (transitions := transitions) (gauge := gauge)
    (primitives := primitives) (anchors := anchors) (offsets := offsets)
    request fixed targetReadings refines 1 2 1 2 rfl rfl
  have scalar := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    rawEndpoints route.symm
  exact ⟨fixed, rfl, scalar.symm.trans_le paid⟩

end Purelib.Riemann.Readings.RectangularPointReadings.Chord

end
