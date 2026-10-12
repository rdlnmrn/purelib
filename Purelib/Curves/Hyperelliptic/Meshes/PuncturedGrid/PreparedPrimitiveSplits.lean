module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

public section

/-!
# Original period primitives split on the actual cut grid

Only the rational parameters are subdivided. Each fragment keeps its original
parent and requested primitive; no child integration model or replacement
owner is prepared. Exact telescoping identifies the sum with the original
request. Every crossing of an actual grid line is a partition endpoint.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits

open Purelib

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents LocalRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid
    curve.polynomial ambient}

set_option genInjectivity false in
/-- Extract the actual retained axes once for the whole parent bank. -/
structure PrimitiveAxes (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) where
  /-- The retained coordinates of the actual vertical grid lines. -/ vertical : List Fraction.Rational
  /-- The cached vertical coordinates are exactly the coordinates of the retained grid lines. -/ vertical_eq : vertical
    = grid.vertical.map VerticalLine.coordinate
  /-- The retained coordinates of the actual horizontal grid lines. -/ horizontal : List Fraction.Rational
  /-- The cached horizontal coordinates are exactly the coordinates of the retained grid lines. -/ horizontal_eq :
    horizontal = grid.horizontal.map HorizontalLine.coordinate

constructive_injectivity PrimitiveAxes

namespace PrimitiveAxes

/-- Extract and cache both coordinate lists from the actual retained grid. -/
@[expose] def build (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid :=
  ⟨grid.vertical.map VerticalLine.coordinate, rfl, grid.horizontal.map HorizontalLine.coordinate, rfl⟩

/-- Compute the real- and imaginary-coordinate crossing parameters of an original parent edge against the retained grid
axes. -/
@[expose] def parameters (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid)
  (parent : PreparedSubdivisionModelCore.CenteredEdge curve source) : List Fraction.Rational :=
  PreparedSegmentCuts.crossings (parent.edge.point 0).re ((parent.edge.point 1).re - (parent.edge.point 0).re)
    axes.vertical ++
    PreparedSegmentCuts.crossings (parent.edge.point 0).im ((parent.edge.point 1).im - (parent.edge.point 0).im)
      axes.horizontal

/-- The number of crossing parameters is bounded by the total number of retained axis lines. -/
theorem parameters_length (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid)
  (parent : PreparedSubdivisionModelCore.CenteredEdge curve source) :
    (axes.parameters parent).length ≤ axes.vertical.length + axes.horizontal.length := by
  rw [parameters,
    Data.List.Append.length_append]
  exact Nat.add_le_add (PreparedSegmentCuts.crossings_length _ _ _) (PreparedSegmentCuts.crossings_length _ _ _)

/-- A moving coordinate cannot cross an actual grid line inside a emitted fragment. Stationary coordinates need no cut
and remain on their fixed line. -/
theorem vertical_outside (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid)
  (parent : PreparedSubdivisionModelCore.CenteredEdge curve source)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) {interval :
      PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) {line : ClearGrid.VerticalLine curve.polynomial ambient} (present : line ∈
      grid.vertical)
    (moving : (parent.edge.point 1).re - (parent.edge.point 0).re ≠ 0) :
    (line.coordinate - (parent.edge.point 0).re) / ((parent.edge.point 1).re - (parent.edge.point 0).re) ≤
      interval.lower ∨
      interval.upper ≤ (line.coordinate - (parent.edge.point 0).re) / ((parent.edge.point 1).re - (parent.edge.point
        0).re) := by
  apply partition.cut_outside member
  apply List.mem_append_left
  rw [PreparedSegmentCuts.crossings, if_neg moving]
  apply Map.mem_map.mpr
  refine ⟨line.coordinate, ?_, rfl⟩
  rw [axes.vertical_eq]
  exact Map.mem_map.mpr ⟨line, present, rfl⟩

/-- For a moving imaginary coordinate, every actual horizontal grid crossing lies outside the interior of each emitted
fragment. -/
theorem horizontal_outside (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid)
  (parent : PreparedSubdivisionModelCore.CenteredEdge curve source)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) {interval :
      PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) {line : ClearGrid.HorizontalLine curve.polynomial ambient} (present : line
      ∈ grid.horizontal)
    (moving : (parent.edge.point 1).im - (parent.edge.point 0).im ≠ 0) :
    (line.coordinate - (parent.edge.point 0).im) / ((parent.edge.point 1).im - (parent.edge.point 0).im) ≤
      interval.lower ∨
      interval.upper ≤ (line.coordinate - (parent.edge.point 0).im) / ((parent.edge.point 1).im - (parent.edge.point
        0).im) := by
  apply partition.cut_outside member
  apply List.mem_append_right
  rw [PreparedSegmentCuts.crossings, if_neg moving]
  apply Map.mem_map.mpr
  refine ⟨line.coordinate, ?_, rfl⟩
  rw [axes.horizontal_eq]
  exact Map.mem_map.mpr ⟨line, present, rfl⟩

end PrimitiveAxes

set_option genInjectivity false in
/-- An ordered splitting spine indexed by the exact original parents. -/
inductive PrimitiveSplits (axes : PrimitiveAxes grid)
  : List (PreparedSubdivisionModelCore.CenteredEdge curve source) → Type
  /-- The empty original parent list has no splitting data. -/ | nil :
    PrimitiveSplits axes []
  /-- Retain the head parent partition and the ordered splitting data for its exact tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve source} {parents : List (PreparedSubdivisionModelCore.CenteredEdge
    curve source)}
      (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) (tail :
        PrimitiveSplits axes parents) :
      PrimitiveSplits axes (parent :: parents)

constructive_injectivity PrimitiveSplits

namespace PrimitiveSplits

variable {axes : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid}

/-- Partition each original parent parameter interval at all retained grid-axis crossings. -/
@[expose] def build (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid) :
  (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)) →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents
  | [] => .nil
  | parent :: parents => .cons (Partition.build 0 1 (by decide) (axes.parameters parent))
    (build axes parents)

/-- Count all fragments in the ordered original-parent splitting spine. -/
@[expose] def count : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents → Nat
  | _, .nil => 0
  | _, .cons partition tail => partition.count + tail.count

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits
/-- Each original parent contributes at most one more fragment than the total number of retained grid axes. -/
theorem count_le : ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (splits :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents),
    splits.count ≤ parents.length * (axes.vertical.length + axes.horizontal.length + 1)
  | _, .nil => Nat.zero_le _
  | _, .cons (parent := parent) partition tail => by
      have head := partition.count_le.trans (Nat.add_le_add_right (axes.parameters_length parent) 1)
      have total := Nat.add_le_add head tail.count_le
      simpa only [count, List.length_cons, Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm] using total

/-- Evaluate each original requested primitive on its retained parameter fragments, preserving parent order. -/
@[expose] def increments {count : Nat} {target : Fraction.Rational} :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents →
      UniformPreparedRequests.RequestedParents count target parents → List Data.Gaussian.Basic.Canonical
  | _, .nil, .nil => []
  | _, .cons (parent := parent) partition tail, .cons request requests =>
      partition.intervals.map (fun interval =>
        request.request.model.primitive.value.eval (parent.edge.point interval.upper) -
          request.request.model.primitive.value.eval (parent.edge.point interval.lower)) ++ tail.increments requests

end

/-- Primitive increments telescope along an increasing finite interval walk. -/
private theorem telescope (value : Fraction.Rational → Data.Gaussian.Basic.Canonical) {intervals : List
  PreparedAxisPartitions.Interval} :
    {first last : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk intervals first last) →
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (walk.edges.map fun interval => value interval.upper - value
        interval.lower) = value last - value first
  | _, _, .nil _ => by change (0 : Data.Gaussian.Basic.Canonical) = _ - _; ring1
  | _, _, .cons interval _ tail => by
      change (value interval.upper - value interval.lower) + Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [telescope value
        tail]
      simp only [id_eq]
      ring1

/-- The Gaussian sum of two concatenated lists is the sum of their separate finite sums. -/
private theorem sum_append (first last : List Data.Gaussian.Basic.Canonical) :
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first +
  Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
      ring1
  | cons head tail ih =>
    change head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail ++ last) = (head +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum tail) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last; rw [ih];
      ring1

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits
/-- Summing all retained fragment increments equals the original parent-request increment sum. -/
theorem sum_eq {count : Nat} {target : Fraction.Rational} :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (splits :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents) (requests :
      UniformPreparedRequests.RequestedParents count target parents),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (splits.increments requests) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments
  | _, .nil, .nil => rfl
  | _, .cons (parent := parent) partition tail, .cons request requests => by
      rw [increments, sum_append, ←
        partition.walk_edges,
        telescope (fun parameter =>
          request.request.model.primitive.value.eval (parent.edge.point parameter)) partition.walk,
        sum_eq tail requests]
      rfl

/-- There is one primitive increment for each retained fragment. -/
theorem increments_length {count : Nat} {target : Fraction.Rational} :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (splits :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents) (requests :
      UniformPreparedRequests.RequestedParents count target parents),
      (splits.increments requests).length = splits.count
  | _, .nil, .nil => rfl
  | _, .cons partition tail, .cons request requests => by
      rw [increments, Data.List.Append.length_append, Data.List.Map.length_map,
        increments_length tail
        requests, ← partition.count_eq]
      rfl

/-- Each emitted fragment endpoint lies in its original parent primitive neighborhood.

The retained partition bounds and endpoint cover certify containment using the same parent root and primitive patch. -/
theorem endpoints_inside {parent : PreparedSubdivisionModelCore.CenteredEdge curve source} (partition :
  Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent))
    {interval : PreparedAxisPartitions.Interval} (member : interval ∈ partition.intervals)
    {count : Nat} {target : Fraction.Rational} (request : UniformPreparedRequests.LocalRequest parent count target) :
    request.neighborhood.box.Contains (parent.edge.point interval.lower) ∧
      request.neighborhood.box.Contains (parent.edge.point interval.upper) := by
  have ends := partition.interval_bounds member
  have firstInside : request.neighborhood.box.Contains (parent.edge.point 0) := by
    rw [request.neighborhood_eq]
    exact request.patch.start_inside count
  exact ⟨PreparedPrimitivePaths.point_inside_of_endpoints parent _ firstInside request.finishInside
      ⟨ends.1, interval.ordered.le.trans ends.2⟩,
    PreparedPrimitivePaths.point_inside_of_endpoints parent _ firstInside request.finishInside
      ⟨ends.1.trans interval.ordered.le, ends.2⟩⟩

end PrimitiveSplits

set_option genInjectivity false in
/-- Cache the original primitive evaluations on actual grid fragments. There is no new integrator or numerical root
selection in this construction. -/
structure SplitPrimitiveRequest (axes : PrimitiveAxes
  grid) {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)}
    {count : Nat} {target : Fraction.Rational} (request : PreparedControlledPrimitiveRequests.ControlledSumRequest
      parents count target) where
  /-- The ordered parameter partitions indexed by the original integration parents. -/ splits :
    PrimitiveSplits axes parents
  /-- The cached original-primitive evaluations on all retained fragments. -/ increments : List
    Data.Gaussian.Basic.Canonical
  /-- The cached increments are the exact original-primitive evaluations on those fragments. -/ increments_eq :
    increments = splits.increments request.requests
  /-- The cached number of retained parameter fragments. -/ count : Nat
  /-- The cached fragment count equals the retained splitting count. -/ count_eq : count = splits.count
  /-- The cached Gaussian sum of all retained fragment increments. -/ sum : Data.Gaussian.Basic.Canonical
  /-- The cached total equals the finite Gaussian sum of the retained increments. -/ sum_eq : sum =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum increments

constructive_injectivity SplitPrimitiveRequest

namespace SplitPrimitiveRequest

variable {axes : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid} {parents
  : List (CenteredEdge curve source)} {count : Nat} {target :
  Rational}
  {request : ControlledSumRequest parents count target}

/-- Cache the original primitive requests on their actual grid fragments.

Each parent partition, fragment increment and final sum is computed once and retained with its exact defining equality.
-/
@[expose] def build (axes : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes grid)
  (request : PreparedControlledPrimitiveRequests.ControlledSumRequest parents count target) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.SplitPrimitiveRequest axes request :=
  let splits := Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits.build axes parents
  let increments := splits.increments request.requests
  ⟨splits, increments, rfl, splits.count, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum increments, rfl⟩

/-- The cached split total equals the original controlled primitive request sum. -/
theorem original_sum (split : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.SplitPrimitiveRequest
  axes request) : split.sum = request.primitiveSum := by
  rw [split.sum_eq, split.increments_eq, split.splits.sum_eq, request.primitiveSum_eq, request.increments_eq]

/-- The cached increment list has exactly the retained fragment count. -/
theorem length_eq (split : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.SplitPrimitiveRequest axes
  request) : split.increments.length = split.count := by
  rw [split.increments_eq, split.splits.increments_length, split.count_eq]

/-- The cached fragment count is bounded by the original parent count times one plus the number of grid axes. -/
theorem count_le (split : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.SplitPrimitiveRequest axes
  request) :
    split.count ≤ parents.length * (axes.vertical.length + axes.horizontal.length + 1) := by
  rw [split.count_eq]
  exact split.splits.count_le

end SplitPrimitiveRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
