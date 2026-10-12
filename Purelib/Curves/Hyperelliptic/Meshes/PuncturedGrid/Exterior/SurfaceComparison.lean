module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-!
# Full exterior surface/cap comparison at one shared stage

Every actual exterior occurrence consumes the same face bank and cap
polynomial sample. The complete source and cap increment paths retain all
cross-segment area terms. Cached component summaries assemble their totals
and areas without recomputing primitive paths or reading another stage.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
  (Entry SampledEntry Samples Request sourceMaximum sourceMaximum_nonnegative)
open Purelib.Riemann.Normalization
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Coordinate}
    {floor : Nat}
  {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

namespace SampledEntry

variable {localTarget localArea : Coordinate}

/-- The complete retained cap summary total is the sum of the actual component totals. -/
theorem rightSummary_total (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth
  readingIndex localTarget localArea floor)) :
    (SampledEntry.rightSummary values).total = Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value =>
      value.evaluated.right.total)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (head.evaluated.right.total + ·) ih

/-- The complete cap path area retains both the original internal areas and the area of the ordered component totals. -/
theorem rightSummary_area (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth
  readingIndex localTarget localArea floor)) :
    (SampledEntry.rightSummary values).area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value =>
      value.evaluated.right.area)) +
      IncrementArea.pathArea (values.map (fun value => value.evaluated.right.total)) := by
  induction values with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 + 0; ring1
  | cons head tail ih =>
      change head.evaluated.right.area + (SampledEntry.rightSummary tail).area +
        BoundaryRibbon.area head.evaluated.right.total (SampledEntry.rightSummary tail).total =
          head.evaluated.right.area + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun value =>
            value.evaluated.right.area)) +
            IncrementArea.pathArea (head.evaluated.right.total :: tail.map (fun value => value.evaluated.right.total))
      rw [ih,
        rightSummary_total,
        IncrementArea.pathArea_cons]
      ring1

/-- Every retained surface increment reads the same original source edge from the supplied shared triangle bank. -/
theorem increment_list_eq (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth
  readingIndex localTarget localArea floor))
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    values.map SampledEntry.increment =
      (values.map SampledEntry.entry).map (fun entry => entry.occurrence.placement.location.sourceEdge.increment
        readings.values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      exact congrArg₂ List.cons (head.increment_eq.trans (readings.route_increment _).symm) ih

end SampledEntry

namespace Request

/-- The retained count, slope and local allowances pay the complete source/cap area target. -/
theorem area_paid (request : AllSurfacePreparation.Request prepared target areaTarget floor) :
    2 * ((request.count : InverseRootPolynomial.Coordinate) ^ 2 * request.budget.areaTarget +
      16 * (request.count : InverseRootPolynomial.Coordinate) ^ 4 * request.localTarget * (2 * (request.slope + 1))) <
        areaTarget := by
  have slopeNonnegative : 0 ≤ request.slope := request.slope_eq ▸ AllSurfacePreparation.sourceMaximum_nonnegative
    prepared.occurrences
  have countNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le request.count)) 4)
  have boundNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg slopeNonnegative (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.local_le countNonnegative) boundNonnegative))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_lt request.budget.paid

/-- The retained local allowance pays the original endpoint-total polygon discrepancy. -/
theorem polygon_paid (request : AllSurfacePreparation.Request prepared target areaTarget floor) :
    16 * (request.count : InverseRootPolynomial.Coordinate) ^ 4 * request.localTarget * (2 * (request.slope + 1)) <
      areaTarget := by
  have slopeNonnegative : 0 ≤ request.slope := request.slope_eq ▸ AllSurfacePreparation.sourceMaximum_nonnegative
    prepared.occurrences
  have internalNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct (request.count : InverseRootPolynomial.Coordinate))
      request.budget.area_positive.le
  have polygonNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le request.count))
          4)) request.positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) (add_nonneg
      slopeNonnegative (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)))
  exact ((le_add_of_nonneg_left internalNonnegative).trans
    ((le_add_of_nonneg_right (add_nonneg internalNonnegative polygonNonnegative)).trans_eq (by ring1))).trans_lt
      request.area_paid

set_option genInjectivity false in
/-- The complete exterior surface/cap comparison on the same original polynomial banks.

Cached local summaries assemble the actual paths, totals and areas, retaining the internal-area correction separately
from the polygon of source increments. -/
structure Evaluation (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) (shared : PrimitiveData.FacePrimitiveBank differential index
      domains)
    (depth readingIndex : Nat) where
  /-- The actual original occurrence samples sharing the supplied cap and face primitive banks. -/ samples :
    AllSurfacePreparation.Samples request.entries sample shared depth readingIndex
  /-- The retained ordered list of complete original source and cap increment paths. -/ pairs : List (List
    InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The paired paths are exactly those of the cached original occurrence samples. -/ pairs_eq : pairs =
    samples.values.map SampledEntry.pair
  /-- The actual pair count equals the original request's retained count. -/ count_eq : pairs.length = request.count
  /-- The complete cached source-path summary including all cross-component area terms. -/ source :
    IncrementArea.Summary (pairs.map Prod.fst).flatten
  /-- The complete cached cap-path summary including all cross-component area terms. -/ cap : IncrementArea.Summary
    (pairs.map Prod.snd).flatten
  /-- The cached sum of the original actual source increments. -/ integral : InverseRootPolynomial.Gaussian
  /-- The integral cache equals the sum of the retained samples' actual increments. -/ integral_eq : integral =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map SampledEntry.increment)
  /-- The actual source integral and cap total satisfy the original total target. -/ integral_close :
    Data.Gaussian.Norm.Basic.normSq (integral - cap.total) < target
  /-- The actual complete source and cap areas satisfy the original area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (source.area - cap.area) < areaTarget
  /-- The cached polygon summary of the original source increments. -/ surface : IncrementArea.Summary
    (samples.values.map SampledEntry.increment)
  /-- The cached sum of internal areas of the original cap component paths. -/ internalArea :
    InverseRootPolynomial.Gaussian
  /-- The internal-area cache is exactly the sum of the retained original cap component areas. -/ internalArea_eq :
    internalArea = Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value =>
    value.evaluated.right.area))
  /-- The source-increment polygon plus the retained internal-area correction approximates the complete cap area. -/
    surface_area_close : Data.Gaussian.Norm.Basic.normSq (surface.area + internalArea - cap.area) < areaTarget

constructive_injectivity Evaluation

/-- Every local request uses these exact shared polynomial banks. The complete path areas are assembled from the already
cached local summaries. -/
@[expose] def evaluateWithSamples (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (samples : AllSurfacePreparation.Samples request.entries sample shared depth readingIndex) :
    Evaluation request
      sample shared depth readingIndex := by
  let pairs := samples.values.map SampledEntry.pair
  let source := SampledEntry.leftSummary samples.values
  let cap := SampledEntry.rightSummary samples.values
  let integral := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map SampledEntry.increment)
  have countEq : samples.values.length = request.count := by
    rw [← Data.List.Map.length_map (values := samples.values) SampledEntry.entry, samples.entries_eq,
      request.count_entries]
  have pairCount : pairs.length = request.count := (Data.List.Map.length_map ..).trans countEq
  have integralClose : Data.Gaussian.Norm.Basic.normSq (integral - cap.total) < target := by
    have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
      (samples.values.map (fun value => value.increment - value.evaluated.right.total)) request.localTarget (by
        intro value member
        obtain ⟨original, member, equal⟩ := Map.mem_map.mp member
        rw [← equal]
        exact original.integral_close.le)
    rw [Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub, Data.List.Map.length_map, countEq, ←
      SampledEntry.rightSummary_total]
      at estimate
    exact estimate.trans_lt request.total_paid
  have slopeNonnegative : 0 ≤ request.slope := request.slope_eq ▸ AllSurfacePreparation.sourceMaximum_nonnegative
    prepared.occurrences
  have bounds : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤
        request.budget.areaTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ request.localTarget ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 *
        (request.slope + 1) ∧ Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        pair.2) ≤ 2 * (request.slope + 1) := by
    intro pair member
    obtain ⟨value, member, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact value.pair_bounds slopeNonnegative
      (request.entry_bound value.entry (samples.entries_eq ▸ Map.mem_map.mpr ⟨value, member, rfl⟩))
      (request.local_le.trans request.budget.total_le_one)
  have areaClose : Data.Gaussian.Norm.Basic.normSq (source.area - cap.area) < areaTarget := by
    have estimate := IncrementAreaComparison.blocks_area_difference_bound pairs request.positive.le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg slopeNonnegative (by decide)))
      (fun pair member => (bounds pair member).1) (fun pair member => (bounds pair member).2.1)
      (fun pair member => (bounds pair member).2.2.1) (fun pair member => (bounds pair member).2.2.2)
    rw [pairCount, ← source.area_eq, ← cap.area_eq] at estimate
    exact estimate.trans_lt request.area_paid
  let surface := IncrementArea.Summary.build (samples.values.map SampledEntry.increment)
  let internalArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value =>
    value.evaluated.right.area))
  have surfaceClose : Data.Gaussian.Norm.Basic.normSq (surface.area + internalArea - cap.area) < areaTarget :=
    by
    let totals := samples.values.map (fun value => (value.increment, value.evaluated.right.total))
    have totalBounds : ∀ pair ∈ totals, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ request.localTarget
      ∧
        Data.Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (request.slope + 1) ∧
          Data.Gaussian.Norm.Basic.normSq pair.2 ≤ 2 * (request.slope + 1) := by
      intro pair member
      obtain ⟨value, member, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      have sourceLe := request.entry_bound value.entry (samples.entries_eq ▸ Map.mem_map.mpr ⟨value, member, rfl⟩)
      have small := request.local_le.trans request.budget.total_le_one
      have right := (value.pair_bounds slopeNonnegative sourceLe small).2.2.2
      change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        value.evaluated.capPath) ≤ _ at right
      rw [← value.evaluated.right.total_eq] at right
      exact ⟨value.integral_close.le, value.increment_bound sourceLe small, right⟩
    have estimate := IncrementAreaComparison.pathArea_difference_bound totals request.positive.le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg slopeNonnegative (by decide)))
      (fun pair member => (totalBounds pair member).1) (fun pair member => (totalBounds pair member).2.1)
      (fun pair member => (totalBounds pair member).2.2)
    change Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea ((samples.values.map _).map Prod.fst) -
      IncrementArea.pathArea ((samples.values.map _).map Prod.snd)) ≤ _ at estimate
    simp only [Data.List.Map.map_map, Function.comp_def] at estimate
    have totalCount : totals.length = request.count := (Data.List.Map.length_map ..).trans countEq
    rw [totalCount] at estimate
    have capAreaEq : cap.area = internalArea + IncrementArea.pathArea (samples.values.map (fun value =>
      value.evaluated.right.total)) :=

        SampledEntry.rightSummary_area
        samples.values
    have equal : surface.area + internalArea - cap.area =
        IncrementArea.pathArea (samples.values.map SampledEntry.increment) -
          IncrementArea.pathArea (samples.values.map (fun value => value.evaluated.right.total)) := by
      rw [capAreaEq, surface.area_eq]
      ring1
    rw [equal]
    exact estimate.trans_lt request.polygon_paid
  exact ⟨samples, pairs, rfl, pairCount, source, cap, integral, rfl, integralClose, areaClose,
    surface, internalArea, rfl, surfaceClose⟩

/-- Ordinary acquisition delegates to the retained-samples constructor. -/
@[expose] def evaluate (request : AllSurfacePreparation.Request prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) (shared : PrimitiveData.FacePrimitiveBank differential index
      domains)
    (depth readingIndex : Nat) (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
    Evaluation request
      sample shared depth readingIndex :=
  request.evaluateWithSamples (Samples.build request.entries
    (request.index_eq ▸ later) (request.readingIndex_eq ▸ readingLater))

/-- The displayed integral consists of the actual source edges consumed by sewing, in the exterior occurrence order
certified by `Request.indexed_eq`. -/
theorem Evaluation.triangle_integral {request : AllSurfacePreparation.Request prepared target areaTarget floor}
    (evaluated :
      Evaluation
      request sample shared depth readingIndex)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    evaluated.integral = Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.entries.map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values)) := by
  rw [evaluated.integral_eq,
    SampledEntry.increment_list_eq
    evaluated.samples.values readings, evaluated.samples.entries_eq]

/-- The area comparison uses the polygon of the actual shared triangle increments. Its internal cap-area correction
remains in `surface_area_close`. -/
theorem Evaluation.triangle_area {request : AllSurfacePreparation.Request prepared target areaTarget floor}
    (evaluated :
      Evaluation
      request sample shared depth readingIndex) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh) :
    evaluated.surface.area = IncrementArea.pathArea (request.entries.map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values)) := by
  rw [evaluated.surface.area_eq,
    SampledEntry.increment_list_eq
    evaluated.samples.values readings, evaluated.samples.entries_eq]

set_option genInjectivity false in
/-- The shared original cap and face primitive banks with their complete evaluated exterior comparison. -/
structure Acquisition (request : AllSurfacePreparation.Request prepared target areaTarget floor) (depth : Nat) where
  /-- The retained cap primitive sample at the original request stage and collar box. -/ sample : Primitives.Sample cap
    differential request.index collar.box
  /-- The retained face primitive bank at that same original request stage. -/ shared : PrimitiveData.FacePrimitiveBank
    differential request.index domains
  /-- The actual complete evaluation using these exact cached banks and original reading stage. -/ evaluated :
    Evaluation request
    sample shared depth request.readingIndex

constructive_injectivity Acquisition

/-- Build the shared original cap and face banks once, then cache their complete exterior comparison at the requested
depth. -/
@[expose] def acquire (request : AllSurfacePreparation.Request prepared target areaTarget floor) (depth : Nat) :
  Acquisition request
  depth :=
  let sample := Primitives.Sample.build cap differential request.index collar.box
  let shared := FacePrimitiveBank.build differential request.index domains
  ⟨sample, shared, request.evaluate sample shared depth request.readingIndex le_rfl le_rfl⟩

end Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
