module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Integration.Path.NoisyPathArea
public import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Integration.Path.JoinedTrace
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Integration.RectangularCenteredPerimeter

@[expose] public section

/-! Full source-area comparisons on the actual retained perimeter traces.
Geometric length and zero-length owner junctions use their existing caches.
The endpoint discrepancy is paid from the same increment bounds, without
assuming coordinate or root closure. -/
namespace Purelib.Riemann.Comparison.RectangularPerimeterComparison
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Integration.RectangularPerimeterLengths (Lengths)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate Sample)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}
  {mesh : ObservationMesh cuts box} {traces : PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Canonical → PrimitivePoint}

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
/-- The retained bottom centered area approximates the supplied source area using the original box's horizontal width.

Pointwise centered accuracy and separate increment bounds for both exact sample words use the same retained lengths and
error budget. The squared difference is bounded by forty times error, the density factor and the square of the sum of
length and allowance. -/
theorem bottom_geometric_comparison (samples : Centered traces values) (lengths : Lengths traces)
    {sourceValues : Fin (traces.bottom.vertices.rest.length + 1) → PrimitivePoint} (source : Sample sourceValues)
    {allowance error density : Coordinate} (budget : NoisyPathArea.LengthErrorBudget traces.bottom.vertices.rest.length
      allowance)
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (accurate : ∀ vertex, PrimitiveAreaBounds.PrimitivePoint.Bounded ((samples.bottom.centered vertex).sub
      (source.centered vertex)) error)
    (increments : ∀ edge : Fin traces.bottom.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((traces.bottom.leftValue values (traces.bottom.vertices.indexed
        edge.succ)).sub
        (traces.bottom.leftValue values (traces.bottom.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.bottom.point (traces.bottom.vertices.indexed edge.succ) -
            traces.bottom.point (traces.bottom.vertices.indexed edge.castSucc))))
    (sourceIncrements : ∀ edge : Fin traces.bottom.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((sourceValues edge.succ).sub (sourceValues edge.castSucc))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.bottom.point (traces.bottom.vertices.indexed edge.succ) -
            traces.bottom.point (traces.bottom.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (samples.bottom.centeredArea - source.centeredArea) ≤
      40 * error * (4 * density + 3) * (box.xUpper - box.xLower + allowance)^2 := by
  have estimate := WeightedPathComparison.LengthErrorBudget.centered_full_comparison budget samples.bottom source
    lengths.bottom.values
    errorNonnegative densityNonnegative lengths.bottom.nonnegative accurate
    (fun edge => by
      have bound := increments edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement traces.bottom lengths.bottom edge] at bound
      exact bound)
    (fun edge => by
      have bound := sourceIncrements edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement traces.bottom lengths.bottom edge] at bound
      exact bound)
  rw [← lengths.bottom.total_eq, RectangularPerimeterLengths.Lengths.bottom_total lengths] at estimate
  exact estimate

/-- The retained top centered area approximates the supplied source area using the original box's horizontal width.

Pointwise centered accuracy and separate increment bounds for both exact sample words use the same retained lengths and
error budget. The squared difference is bounded by forty times error, the density factor and the square of the sum of
length and allowance. -/
theorem top_geometric_comparison (samples : Centered traces values) (lengths : Lengths traces)
    {sourceValues : Fin (traces.top.vertices.rest.length + 1) → PrimitivePoint} (source : Sample sourceValues)
    {allowance error density : Coordinate} (budget : NoisyPathArea.LengthErrorBudget traces.top.vertices.rest.length
      allowance)
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (accurate : ∀ vertex, PrimitiveAreaBounds.PrimitivePoint.Bounded ((samples.top.centered vertex).sub (source.centered
      vertex)) error)
    (increments : ∀ edge : Fin traces.top.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((traces.top.leftValue values (traces.top.vertices.indexed
        edge.succ)).sub
        (traces.top.leftValue values (traces.top.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.top.point (traces.top.vertices.indexed edge.succ) -
            traces.top.point (traces.top.vertices.indexed edge.castSucc))))
    (sourceIncrements : ∀ edge : Fin traces.top.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((sourceValues edge.succ).sub (sourceValues edge.castSucc))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.top.point (traces.top.vertices.indexed edge.succ) -
            traces.top.point (traces.top.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (samples.top.centeredArea - source.centeredArea) ≤
      40 * error * (4 * density + 3) * (box.xUpper - box.xLower + allowance)^2 := by
  have estimate := WeightedPathComparison.LengthErrorBudget.centered_full_comparison budget samples.top source
    lengths.top.values
    errorNonnegative densityNonnegative lengths.top.nonnegative accurate
    (fun edge => by
      have bound := increments edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement traces.top lengths.top edge] at bound
      exact bound)
    (fun edge => by
      have bound := sourceIncrements edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularHorizontalTraceLengths.length_movement traces.top lengths.top edge] at bound
      exact bound)
  rw [← lengths.top.total_eq, RectangularPerimeterLengths.Lengths.top_total lengths] at estimate
  exact estimate

/-- The retained left centered area approximates the supplied source area using the original box's vertical height.

Pointwise centered accuracy and separate increment bounds for both exact sample words use the same retained lengths and
error budget. The squared difference is bounded by forty times error, the density factor and the square of the sum of
length and allowance. -/
theorem left_geometric_comparison (samples : Centered traces values) (lengths : Lengths traces)
    {sourceValues : Fin (traces.left.vertices.rest.length + 1) → PrimitivePoint} (source : Sample sourceValues)
    {allowance error density : Coordinate} (budget : NoisyPathArea.LengthErrorBudget traces.left.vertices.rest.length
      allowance)
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (accurate : ∀ vertex, PrimitiveAreaBounds.PrimitivePoint.Bounded ((samples.left.centered vertex).sub
      (source.centered vertex)) error)
    (increments : ∀ edge : Fin traces.left.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((traces.left.leftValue values (traces.left.vertices.indexed
        edge.succ)).sub
        (traces.left.leftValue values (traces.left.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.left.point (traces.left.vertices.indexed edge.succ) -
            traces.left.point (traces.left.vertices.indexed edge.castSucc))))
    (sourceIncrements : ∀ edge : Fin traces.left.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((sourceValues edge.succ).sub (sourceValues edge.castSucc))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.left.point (traces.left.vertices.indexed edge.succ) -
            traces.left.point (traces.left.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (samples.left.centeredArea - source.centeredArea) ≤
      40 * error * (4 * density + 3) * (box.yUpper - box.yLower + allowance)^2 := by
  have estimate := WeightedPathComparison.LengthErrorBudget.centered_full_comparison budget samples.left source
    lengths.left.values
    errorNonnegative densityNonnegative lengths.left.nonnegative accurate
    (fun edge => by
      have bound := increments edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement traces.left lengths.left edge] at bound
      exact bound)
    (fun edge => by
      have bound := sourceIncrements edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement traces.left lengths.left edge] at bound
      exact bound)
  rw [← lengths.left.total_eq, RectangularPerimeterLengths.Lengths.left_total lengths] at estimate
  exact estimate

/-- The retained right centered area approximates the supplied source area using the original box's vertical height.

Pointwise centered accuracy and separate increment bounds for both exact sample words use the same retained lengths and
error budget. The squared difference is bounded by forty times error, the density factor and the square of the sum of
length and allowance. -/
theorem right_geometric_comparison (samples : Centered traces values) (lengths : Lengths traces)
    {sourceValues : Fin (traces.right.vertices.rest.length + 1) → PrimitivePoint} (source : Sample sourceValues)
    {allowance error density : Coordinate} (budget : NoisyPathArea.LengthErrorBudget traces.right.vertices.rest.length
      allowance)
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (accurate : ∀ vertex, PrimitiveAreaBounds.PrimitivePoint.Bounded ((samples.right.centered vertex).sub
      (source.centered vertex)) error)
    (increments : ∀ edge : Fin traces.right.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((traces.right.leftValue values (traces.right.vertices.indexed
        edge.succ)).sub
        (traces.right.leftValue values (traces.right.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.right.point (traces.right.vertices.indexed edge.succ) -
            traces.right.point (traces.right.vertices.indexed edge.castSucc))))
    (sourceIncrements : ∀ edge : Fin traces.right.vertices.rest.length,
      PrimitiveAreaBounds.PrimitivePoint.Bounded ((sourceValues edge.succ).sub (sourceValues edge.castSucc))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (traces.right.point (traces.right.vertices.indexed edge.succ) -
            traces.right.point (traces.right.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (samples.right.centeredArea - source.centeredArea) ≤
      40 * error * (4 * density + 3) * (box.yUpper - box.yLower + allowance)^2 := by
  have estimate := WeightedPathComparison.LengthErrorBudget.centered_full_comparison budget samples.right source
    lengths.right.values
    errorNonnegative densityNonnegative lengths.right.nonnegative accurate
    (fun edge => by
      have bound := increments edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement traces.right lengths.right edge] at bound
      exact bound)
    (fun edge => by
      have bound := sourceIncrements edge
      simp only [Norm.Basic.normSq_eq_canonical] at bound
      rw [RectangularVerticalTraceLengths.length_movement traces.right lengths.right edge] at bound
      exact bound)
  rw [← lengths.right.total_eq, RectangularPerimeterLengths.Lengths.right_total lengths] at estimate
  exact estimate

end

end Purelib.Riemann.Comparison.RectangularPerimeterComparison
