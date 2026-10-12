module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Integration.Path.Dyadic.DyadicTrace
public import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
public import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
public import Purelib.Riemann.Integration.RectangularCenteredPerimeter
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Readings.PrimitiveAreaBounds

public section

/-! Exact geometric length caches for all four retained perimeter traces.
The full centered-area bound uses the rectangle width or height directly. -/
namespace Purelib.Riemann.Integration.RectangularPerimeterLengths
open Purelib.Data.Gaussian
open Purelib.Riemann.Integration
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Paths
open Purelib.Integration.Path
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box}

set_option genInjectivity false in
/-- The four retained coordinate-length banks of one original perimeter trace family.

Horizontal lengths use the exact bottom and top traces, while vertical lengths use the original left and right traces;
every bank preserves its own ordered vertices. -/
structure Lengths (traces : PerimeterTraces mesh) where
  /-- The exact bottom trace's retained horizontal edge lengths. -/ bottom : TraceLengths.VertexTrace.Lengths
    traces.bottom.vertices (fun vertex => (traces.bottom.point vertex).re)
  /-- The exact top trace's retained horizontal edge lengths. -/ top : TraceLengths.VertexTrace.Lengths
    traces.top.vertices (fun vertex => (traces.top.point vertex).re)
  /-- The exact left trace's retained vertical edge lengths. -/ left : TraceLengths.VertexTrace.Lengths
    traces.left.vertices (fun vertex => (traces.left.point vertex).im)
  /-- The exact right trace's retained vertical edge lengths. -/ right : TraceLengths.VertexTrace.Lengths
    traces.right.vertices (fun vertex => (traces.right.point vertex).im)

constructive_injectivity Lengths

namespace Lengths
variable {traces : PerimeterTraces mesh}

/-- Cache all four original perimeter traces' nonnegative coordinate-length banks. -/
@[expose] def build (traces : PerimeterTraces mesh) : Lengths traces :=
  ⟨RectangularHorizontalTraceLengths.lengths traces.bottom,
    RectangularHorizontalTraceLengths.lengths traces.top,
    RectangularVerticalTraceLengths.lengths traces.left,
    RectangularVerticalTraceLengths.lengths traces.right⟩

/-- The retained bottom-trace length equals the original box's horizontal width. -/
theorem bottom_total (lengths : Lengths traces) : lengths.bottom.total = box.xUpper - box.xLower := by
  rw [lengths.bottom.endpoints]
  have lastEq : traces.bottom.vertices.indexed (Fin.last traces.bottom.vertices.rest.length) =
    traces.bottom.vertices.last :=
    DyadicTrace.indexed_last traces.bottom.vertices.first traces.bottom.vertices.rest
  have firstEq : traces.bottom.vertices.indexed 0 = traces.bottom.vertices.first := rfl
  rw [← lastEq, ← firstEq,
    RectangularCenteredPerimeter.bottom_last_point traces,
    RectangularCenteredPerimeter.bottom_first_point traces]

/-- The retained top-trace length equals the original box's horizontal width. -/
theorem top_total (lengths : Lengths traces) : lengths.top.total = box.xUpper - box.xLower := by
  rw [lengths.top.endpoints]
  have lastEq : traces.top.vertices.indexed (Fin.last traces.top.vertices.rest.length) = traces.top.vertices.last :=
    DyadicTrace.indexed_last traces.top.vertices.first traces.top.vertices.rest
  have firstEq : traces.top.vertices.indexed 0 = traces.top.vertices.first := rfl
  rw [← lastEq, ← firstEq,
    RectangularCenteredPerimeter.top_last_point traces,
    RectangularCenteredPerimeter.top_first_point traces]

/-- The retained left-trace length equals the original box's vertical height. -/
theorem left_total (lengths : Lengths traces) : lengths.left.total = box.yUpper - box.yLower := by
  rw [lengths.left.endpoints]
  have lastEq : traces.left.vertices.indexed (Fin.last traces.left.vertices.rest.length) = traces.left.vertices.last :=
    DyadicTrace.indexed_last traces.left.vertices.first traces.left.vertices.rest
  have firstEq : traces.left.vertices.indexed 0 = traces.left.vertices.first := rfl
  rw [← lastEq, ← firstEq,
    RectangularCenteredPerimeter.left_last_point traces,
    RectangularCenteredPerimeter.left_first_point traces]

/-- The retained right-trace length equals the original box's vertical height. -/
theorem right_total (lengths : Lengths traces) : lengths.right.total = box.yUpper - box.yLower := by
  rw [lengths.right.endpoints]
  have lastEq : traces.right.vertices.indexed (Fin.last traces.right.vertices.rest.length) = traces.right.vertices.last
    :=
    DyadicTrace.indexed_last traces.right.vertices.first traces.right.vertices.rest
  have firstEq : traces.right.vertices.indexed 0 = traces.right.vertices.first := rfl
  rw [← lastEq, ← firstEq,
    RectangularCenteredPerimeter.right_last_point traces,
    RectangularCenteredPerimeter.right_first_point traces]

end Lengths
namespace Centered
variable {traces : PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Canonical → PrimitivePoint}

/-- The retained bottom centered area is bounded using the original box's horizontal width.

The exact side-length bank and error budget accompany nonnegative magnitude and density bounds on the same samples and
increments; the squared estimate is four times magnitude times the density factor times the square of the sum of length
and allowance. -/
theorem bottom_geometric_area_bound (samples : Centered traces values) (lengths : Lengths traces)
    {allowance magnitude density : Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget traces.bottom.vertices.rest.length allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, Bounded (samples.bottom.centered vertex) magnitude)
    (increments : ∀ edge : Fin traces.bottom.vertices.rest.length,
      Bounded ((traces.bottom.leftValue values (traces.bottom.vertices.indexed edge.succ)).sub
        (traces.bottom.leftValue values (traces.bottom.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.bottom.point (traces.bottom.vertices.indexed edge.succ) -
            traces.bottom.point (traces.bottom.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq samples.bottom.centeredArea ≤
      4 * magnitude * (4 * density + 3) * (box.xUpper - box.xLower + allowance)^2 := by
  have estimate := budget.centered_area_bound samples.bottom lengths.bottom.values
    magnitudeNonnegative densityNonnegative lengths.bottom.nonnegative bounded (fun edge => by
      have bound := increments edge
      rw [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement
        traces.bottom lengths.bottom edge] at bound
      exact bound)
  rw [← lengths.bottom.total_eq, lengths.bottom_total] at estimate
  exact estimate

/-- The retained top centered area is bounded using the original box's horizontal width.

The exact side-length bank and error budget accompany nonnegative magnitude and density bounds on the same samples and
increments; the squared estimate is four times magnitude times the density factor times the square of the sum of length
and allowance. -/
theorem top_geometric_area_bound (samples : Centered traces values) (lengths : Lengths traces)
    {allowance magnitude density : Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget traces.top.vertices.rest.length allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, Bounded (samples.top.centered vertex) magnitude)
    (increments : ∀ edge : Fin traces.top.vertices.rest.length,
      Bounded ((traces.top.leftValue values (traces.top.vertices.indexed edge.succ)).sub
        (traces.top.leftValue values (traces.top.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.top.point (traces.top.vertices.indexed edge.succ) -
            traces.top.point (traces.top.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq samples.top.centeredArea ≤
      4 * magnitude * (4 * density + 3) * (box.xUpper - box.xLower + allowance)^2 := by
  have estimate := budget.centered_area_bound samples.top lengths.top.values
    magnitudeNonnegative densityNonnegative lengths.top.nonnegative bounded (fun edge => by
      have bound := increments edge
      rw [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement
        traces.top lengths.top edge] at bound
      exact bound)
  rw [← lengths.top.total_eq, lengths.top_total] at estimate
  exact estimate

/-- The retained left centered area is bounded using the original box's vertical height.

The exact side-length bank and error budget accompany nonnegative magnitude and density bounds on the same samples and
increments; the squared estimate is four times magnitude times the density factor times the square of the sum of length
and allowance. -/
theorem left_geometric_area_bound (samples : Centered traces values) (lengths : Lengths traces)
    {allowance magnitude density : Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget traces.left.vertices.rest.length allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, Bounded (samples.left.centered vertex) magnitude)
    (increments : ∀ edge : Fin traces.left.vertices.rest.length,
      Bounded ((traces.left.leftValue values (traces.left.vertices.indexed edge.succ)).sub
        (traces.left.leftValue values (traces.left.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.left.point (traces.left.vertices.indexed edge.succ) -
            traces.left.point (traces.left.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq samples.left.centeredArea ≤
      4 * magnitude * (4 * density + 3) * (box.yUpper - box.yLower + allowance)^2 := by
  have estimate := budget.centered_area_bound samples.left lengths.left.values
    magnitudeNonnegative densityNonnegative lengths.left.nonnegative bounded (fun edge => by
      have bound := increments edge
      rw [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement
        traces.left lengths.left edge] at bound
      exact bound)
  rw [← lengths.left.total_eq, lengths.left_total] at estimate
  exact estimate

/-- The retained right centered area is bounded using the original box's vertical height.

The exact side-length bank and error budget accompany nonnegative magnitude and density bounds on the same samples and
increments; the squared estimate is four times magnitude times the density factor times the square of the sum of length
and allowance. -/
theorem right_geometric_area_bound (samples : Centered traces values) (lengths : Lengths traces)
    {allowance magnitude density : Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget traces.right.vertices.rest.length allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, Bounded (samples.right.centered vertex) magnitude)
    (increments : ∀ edge : Fin traces.right.vertices.rest.length,
      Bounded ((traces.right.leftValue values (traces.right.vertices.indexed edge.succ)).sub
        (traces.right.leftValue values (traces.right.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.right.point (traces.right.vertices.indexed edge.succ) -
            traces.right.point (traces.right.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq samples.right.centeredArea ≤
      4 * magnitude * (4 * density + 3) * (box.yUpper - box.yLower + allowance)^2 := by
  have estimate := budget.centered_area_bound samples.right lengths.right.values
    magnitudeNonnegative densityNonnegative lengths.right.nonnegative bounded (fun edge => by
      have bound := increments edge
      rw [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement
        traces.right lengths.right edge] at bound
      exact bound)
  rw [← lengths.right.total_eq, lengths.right_total] at estimate
  exact estimate

end Centered
end Purelib.Riemann.Integration.RectangularPerimeterLengths

end
