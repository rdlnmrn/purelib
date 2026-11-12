module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# The complete polygon of cached cap-chart vertex readings

Each midpoint is sampled once and passed to both children. The returned
segments retain the actual coordinates, source and chart values. Their
source increments are exactly the original arc's dyadic increments.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint midpoint_between)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared Reading Chart)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree ChartTree Mesh ChartMesh)
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    UniformReciprocalRootChannels.RootModel cell}
  {target : Coordinate} {floor index : Nat} {box :
    Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {comparison : Data regular cell}
  {sample : Sample comparison capSample} {stage : Nat}

set_option genInjectivity false in
/-- A segment between two cached cap-chart readings at a common stage.

The ordered parameters, actual endpoint readings and both source and chart increments are retained together with their
exact difference equations. -/
structure Segment (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    {comparison : Data regular cell}
    (sample : Sample comparison capSample) (target : Coordinate) (floor stage : Nat)
      where
  /-- The retained parameter of the first endpoint. -/ firstParameter : Coordinate
  /-- The retained parameter of the last endpoint. -/ lastParameter : Coordinate
  /-- The cached first endpoint reading at the shared stage. -/ first : Reading regular model sample
    firstParameter target floor stage
  /-- The cached last endpoint reading at the shared stage. -/ last : Reading regular model sample
    lastParameter target floor stage
  /-- The first parameter does not exceed the last parameter. -/ ordered : firstParameter ≤ lastParameter
  /-- The cached difference of the two source readings. -/ sourceIncrement : Gaussian
  /-- The source increment is exactly the retained last value minus the first. -/ source_eq : sourceIncrement =
    last.sourceValue - first.sourceValue
  /-- The cached difference of the two chart readings. -/ chartIncrement : Gaussian
  /-- The chart increment is exactly the retained last value minus the first. -/ chart_eq : chartIncrement =
    last.chartValue - first.chartValue

constructive_injectivity Segment

namespace Segment

/-- Cache both increments from the supplied ordered endpoint readings without evaluating either endpoint again. -/
@[expose] def build {first last : Coordinate} (before : Reading regular model
  sample first target floor stage)
    (after : Reading regular model sample last target floor stage) (ordered : first ≤ last) :
      Segment regular model sample target floor stage :=
  ⟨first, last, before, after, ordered, after.sourceValue - before.sourceValue, rfl,
    after.chartValue - before.chartValue, rfl⟩

/-- Consecutive segments share their actual root coordinates from the supplied first coordinate to the supplied last
coordinate. -/
@[expose] def From (first : Gaussian) : List
  (Segment regular model sample target floor stage) →
  Gaussian → Prop
  | [], last => first = last
  | segment :: remaining, last => first = segment.first.root.coordinate ∧
    Segment.From segment.last.root.coordinate remaining
    last

/-- Concatenation preserves the actual endpoint chain when its middle root coordinate agrees. -/
theorem from_append {first middle last : Gaussian} {before after : List
  (Segment regular model sample target floor stage)}
    (left : From first before middle) (right :
      From middle after last) :
      From first (before ++ after) last := by
  induction before generalizing first with
  | nil => exact left ▸ right
  | cons head tail ih => exact ⟨left.1, ih left.2⟩

end Segment

set_option genInjectivity false in
/-- A complete dyadic polygon built from cached cap-chart endpoint readings.

The segment chain retains both increment paths and their summaries, their exact dyadic source readback, the telescoping
chart total and every segment width. -/
structure Path (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    {comparison : Data regular cell}
    (sample : Sample comparison capSample) (target : Coordinate) (floor stage depth :
      Nat)
    {first last : Coordinate} (before : Reading regular model sample first target
      floor stage)
    (after : Reading regular model sample last target floor stage) where
  /-- The cached ordered list of actual endpoint segments. -/ segments : List
    (Segment regular model sample target floor stage)
  /-- There are exactly two to the retained depth segments. -/ count_eq : segments.length = 2 ^ depth
  /-- The actual root coordinates connect from the supplied first reading to the last. -/ chain :
    Segment.From (regular := regular) (model := model) (sample
    := sample)
    before.root.coordinate segments after.root.coordinate
  /-- The cached list of source increments. -/ sourcePath : List Gaussian
  /-- The source path is exactly the source-increment projection of the retained segments. -/ sourcePath_eq : sourcePath
    = segments.map Segment.sourceIncrement
  /-- The cached list of chart increments. -/ chartPath : List Gaussian
  /-- The chart path is exactly the chart-increment projection of the retained segments. -/ chartPath_eq : chartPath =
    segments.map Segment.chartIncrement
  /-- The cached source-path summary including all area cross terms. -/ source : Summary sourcePath
  /-- The cached chart-path summary including all area cross terms. -/ chart : Summary chartPath
  /-- The retained source path is exactly the dyadic primitive increment list at this depth. -/ source_dyadic :
    sourcePath = dyadicIncrements (ArcArea.Sample.capValue sample) depth first last
  /-- The retained chart total is the actual last chart reading minus the first. -/ chart_total : chart.total =
    after.chartValue - before.chartValue
  /-- Every retained segment has the original interval width divided by two to the depth. -/ width_eq : ∀ segment ∈
    segments, ((2 ^ depth : Nat) : Coordinate) *
    (segment.lastParameter - segment.firstParameter) = last - first

constructive_injectivity Path

namespace Path

/-- Build the single-segment polygon from the supplied cached endpoint readings. -/
@[expose] def leaf {first last : Coordinate} (before : Reading regular model sample
  first target floor stage)
    (after : Reading regular model sample last target floor stage) (ordered : first ≤ last) :
    Path regular model sample target floor stage 0 before after
      := by
  let segment := Segment.build before after ordered
  let sourcePath := [segment.sourceIncrement]
  let chartPath := [segment.chartIncrement]
  let source := Summary.build sourcePath
  let chart := Summary.build chartPath
  refine ⟨[segment], rfl, ⟨rfl, rfl⟩, sourcePath, rfl, chartPath, rfl, source, chart, ?_, ?_, ?_⟩
  · change [after.sourceValue - before.sourceValue] = [_]
    rw [after.source_eq, before.source_eq]
    apply congrArg (fun value => [value])
    unfold ArcArea.Sample.capValue
    ring1
  · change (after.chartValue - before.chartValue) + 0 = _
    ring1
  · intro segment member
    rcases Data.List.Membership.mem_cons.mp member with same | impossible
    · subst segment
      change (1 : Coordinate) * (last - first) = last - first
      exact Fraction.Field.one_mul _
    · exact False.elim (List.not_mem_nil impossible)

/-- Concatenate two cached half-interval polygons at their shared midpoint reading.

Both increment lists and summaries are reused, and the equal-width certificate is transported to the doubled segment
count. -/
@[expose] def join {depth : Nat} {first last : Coordinate}
    {before : Reading regular model sample first target floor stage}
    {middle : Reading regular model sample
      (midpoint first last) target floor stage}
    {after : Reading regular model sample last target floor stage}
    (left : Path regular model sample target floor stage depth
      before middle)
    (right : Path regular model sample target floor stage depth
      middle after) :
    Path regular model sample target floor stage (depth + 1)
      before after := by
  refine ⟨left.segments ++ right.segments, ?_,
    Segment.from_append left.chain right.chain,
    left.sourcePath ++ right.sourcePath, ?_, left.chartPath ++ right.chartPath, ?_,
    left.source.append right.source, left.chart.append right.chart, ?_, ?_, ?_⟩
  · rw [Data.List.Append.length_append, left.count_eq, right.count_eq, Nat.pow_succ, Nat.mul_two]
  · rw [Data.List.Map.map_append, ← left.sourcePath_eq, ← right.sourcePath_eq]
  · rw [Data.List.Map.map_append, ← left.chartPath_eq, ← right.chartPath_eq]
  · rw [left.source_dyadic, right.source_dyadic]
    rfl
  · change left.chart.total + right.chart.total = _
    rw [left.chart_total, right.chart_total]
    ring1
  · intro segment member
    rw [Nat.pow_succ, Algebra.NatCast.mul]
    have scaled : ((2 ^ depth : Nat) : Coordinate) * (2 : Coordinate) *
      (segment.lastParameter - segment.firstParameter) =
        (((2 ^ depth : Nat) : Coordinate) * (segment.lastParameter - segment.firstParameter)) * 2
          := by ring1
    change ((2 ^ depth : Nat) : Coordinate) * (2 : Coordinate) *
      (segment.lastParameter - segment.firstParameter) = _
    rw [scaled]
    rcases Data.List.Membership.mem_append.mp member with member | member
    · rw [left.width_eq segment member]
      calc
        _ = ((last - first) / 2) * 2 := by
          unfold midpoint;
          ring1
        _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    · rw [right.width_eq segment member]
      have twiceHalf := Fraction.Field.div_mul_cancel_of_ne (last - first) 2 (by decide)
      calc
        _ = (last - first) * 2 - ((last - first) / 2) * 2 := by
          unfold midpoint;
          ring1
        _ = _ := by rw [twiceHalf]; ring1

end Path

set_option genInjectivity false in
/-- An actual midpoint reading with its original prepared owner. -/
structure OwnedReading (prepared : Prepared regular model parameter target floor)
    (sample : Sample comparison capSample) (stage : Nat) where
  /-- The cached midpoint reading with its actual prepared owner. -/ reading : Reading regular model
    sample parameter target floor stage
  /-- The reading retains exactly the supplied prepared midpoint request. -/ owner : reading.prepared = prepared

constructive_injectivity OwnedReading

/-- Retained midpoint readings in the original dyadic tree order. -/
@[expose] def TreeReadings (sample : Sample comparison capSample) (stage : Nat) :
    {depth : Nat} → {first last : Coordinate} → Tree regular model target floor depth
      first last → Type 1
  | _, _, _, .leaf _ _ => PUnit
  | _, _, _, .node middle left right => OwnedReading middle
    sample stage × VertexPaths.TreeReadings sample stage left ×
    VertexPaths.TreeReadings sample stage right

namespace TreeReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.TreeReadings in
/-- The cached complete polygon built from these endpoint and midpoint readings. -/
@[expose] def path : {depth : Nat} → {first last : Coordinate} → {tree : Tree regular
  model target floor depth first last} →
    TreeReadings sample stage tree → (before :
      Reading regular model sample first target floor stage) →
    (after : Reading regular model sample last target floor stage) → first ≤ last →
    Path regular model sample target floor stage depth before
      after
  | _, _, _, .leaf _ _, _, before, after, ordered => Path.leaf
    before after ordered
  | _, _, _, .node _ _ _, readings, before, after, ordered =>
      let between := midpoint_between ordered
      Path.join (path readings.2.1 before readings.1.reading
        between.1)
        (path readings.2.2 readings.1.reading after between.2)

end TreeReadings

namespace ChartTree

variable {minimum : Nat}

/-- Sample each midpoint once and preserve its owner for subsequent basis comparisons. The path builder consumes these
same readings. -/
@[expose] def read (sample : Sample comparison capSample) (stage : Nat) :
    {depth : Nat} → {first last : Coordinate} → {tree : Tree regular model target floor
      depth first last} →
    (charts : ChartTree capSample minimum tree) → tree.index ≤ index → charts.stage ≤ stage →
    TreeReadings sample stage tree
  | _, _, _, _, .leaf _ _, _, _ => ⟨⟩
  | _, _, _, _, .node middle left right, modelLater, readingLater => by
      have modelIndices : max _ (max _ _) ≤ index := modelLater
      have readingIndices : max _ (max _ _) ≤ stage := readingLater
      let value := middle.evaluate sample ((Data.Nat.Order.le_max_left _ _).trans modelIndices) stage
        ((Data.Nat.Order.le_max_left _ _).trans readingIndices)
      exact ⟨⟨value, rfl⟩,
        ChartTree.read sample stage left
          ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans modelIndices))
          ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans readingIndices)),
        ChartTree.read sample stage right
          ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans modelIndices))
          ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans readingIndices))⟩

end ChartTree

namespace ChartMesh

variable {minimum depth : Nat} {mesh : Mesh regular model
  depth target floor}

set_option genInjectivity false in
/-- Cached endpoint and midpoint readings with their complete dyadic polygon.

The endpoint owners match the prepared mesh, and the retained polygon is built from these exact readings without a
second root evaluation. -/
structure Evaluation (charts : ChartMesh mesh capSample minimum) (sample : Sample comparison
  capSample) (stage : Nat) where
  /-- The cached first endpoint reading at the shared stage. -/ first : Reading regular model sample
    edge.left.parameter target floor stage
  /-- The cached last endpoint reading at the shared stage. -/ last : Reading regular model sample
    edge.right.parameter target floor stage
  /-- The first reading retains exactly the mesh's first prepared request. -/ first_prepared : first.prepared =
    mesh.first
  /-- The last reading retains exactly the mesh's last prepared request. -/ last_prepared : last.prepared = mesh.last
  /-- The cached midpoint readings in their original dyadic tree order. -/ readings :
    TreeReadings sample stage mesh.tree
  /-- The cached complete polygon built from these endpoint and midpoint readings. -/ path :
    Path regular model sample target floor stage depth first
    last
  /-- The retained polygon is exactly the construction from the cached reading tree. -/ path_eq : path =
    TreeReadings.path readings first last cell.ordered.le

constructive_injectivity Evaluation

/-- One read per vertex at the same stage; endpoints and all midpoints are retained in the exact original dyadic edge
order. -/
@[expose] def evaluate (charts : ChartMesh mesh capSample minimum) (sample : Sample comparison
  capSample)
    (modelLater : mesh.index ≤ index) (stage : Nat) (readingLater : charts.stage ≤ stage) :
      Evaluation charts sample stage := by
  have modelIndices := mesh.index_eq ▸ modelLater
  have readingIndices := charts.stage_eq ▸ readingLater
  let first := charts.first.evaluate sample ((Data.Nat.Order.le_max_left _ _).trans modelIndices) stage
    ((Data.Nat.Order.le_max_left _ _).trans readingIndices)
  let last := charts.last.evaluate sample ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans modelIndices)) stage
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans readingIndices))
  let readings := ChartTree.read sample stage charts.tree
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans modelIndices))
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans readingIndices))
  let path := TreeReadings.path readings first last
    cell.ordered.le
  exact ⟨first, last, rfl, rfl, readings, path, rfl⟩

end ChartMesh
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
