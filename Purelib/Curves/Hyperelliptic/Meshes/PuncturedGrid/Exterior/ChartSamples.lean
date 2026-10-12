module
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

public section

/-!
# Shared chart samples in the original exterior occurrence order

All spatial requests precede the common cap and face samples. Chart plans
then select one reading stage. Every returned surface sample consumes the
source evaluation retained by its own chart acquisition.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Entry
  SampledEntry Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapRequest
  ChartRequest)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace ChartSamples

set_option genInjectivity false in
/-- The ordered chart requests on the exact original exterior occurrence list. -/
inductive ChartRequests (chartTarget : InverseRootPolynomial.Coordinate) : List (AllSurfacePreparation.Entry regular
  domains differential localTarget localArea floor) → Type 2
  /-- The empty chart request spine on the original empty occurrence list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget []
  /-- Prepend the actual original occurrence's chart request to its retained request tail. -/ | cons {entry :
    AllSurfacePreparation.Entry regular domains differential localTarget localArea floor} {remaining : List
    (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)}
      (head : SegmentComparison.ChartRequest entry.request chartTarget) (tail :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget remaining) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget (entry ::
        remaining)

constructive_injectivity ChartRequests

end ChartSamples

namespace ChartSamples.ChartRequests

/-- Prepare a positive chart request for every original occurrence in its retained order. -/
@[expose] def build (chartTarget : InverseRootPolynomial.Coordinate) (positive : 0 < chartTarget) :
    (entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries
  | [] => .nil
  | entry :: remaining => .cons (ChartRequest.build entry.request chartTarget positive)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests.build chartTarget positive
    remaining)

variable {entries : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular
  domains differential localTarget localArea floor)}

/-- The maximum original source stage, retaining the supplied floor for an empty request list. -/
@[expose] def maximum : {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea
  floor)} → Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries → Nat
  | _, .nil => floor
  | _, .cons head tail => max head.index tail.maximum

/-- The maximum subdivision depth of the original retained chart requests, with zero for an empty list. -/
@[expose] def depthMaximum : {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget
  localArea floor)} → Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries
  → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.depth tail.depthMaximum

end ChartSamples.ChartRequests

variable {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

namespace ChartSamples

set_option genInjectivity false in
/-- The dependent chart plan spine using one exact original cap sample. -/
inductive ChartPlans (sample : Primitives.Sample cap differential index box) :
    {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries → Type 2
  /-- The empty chart plan spine on the original empty request list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample .nil
  /-- Prepend the original occurrence's plan on the exact shared cap sample. -/ | cons {entry :
    AllSurfacePreparation.Entry regular domains differential localTarget localArea floor} {remaining : List
    (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)}
      {head : SegmentComparison.ChartRequest entry.request chartTarget} {tail :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget remaining}
      (plan : ChartRequest.Plan head sample) (plans :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample tail) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample (.cons head tail)

constructive_injectivity ChartPlans

set_option genInjectivity false in
/-- An original exterior occurrence and its retained chart evaluation on the shared cap and face banks.

The source sample is built from that exact chart acquisition's original evaluation, with the original face-stage proof.
-/
structure ChartedEntry (sample : Primitives.Sample cap differential index box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (depth readingIndex : Nat)
    (localTarget localArea chartTarget : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original retained exterior surface occurrence request. -/ entry : AllSurfacePreparation.Entry regular domains
    differential localTarget localArea floor
  /-- The actual chart request bound to that exact original occurrence. -/ request : SegmentComparison.ChartRequest
    entry.request chartTarget
  /-- The retained chart plan on the original shared cap sample. -/ plan : ChartRequest.Plan request sample
  /-- The actual chart evaluation at the common subdivision and reading stages. -/ chart : Plan.Evaluation plan depth
    readingIndex
  /-- The common source stage pays the original face reference request. -/ face_later : entry.request.budget.grid.index
    ≤ index
  /-- The actual original surface sample on the shared face bank. -/ value : AllSurfacePreparation.SampledEntry sample
    shared depth readingIndex localTarget localArea floor
  /-- The surface sample is exactly the one constructed from the retained chart's original evaluation. -/ value_eq :
    value = SampledEntry.ofEvaluation entry chart.original face_later

constructive_injectivity ChartedEntry

end ChartSamples

namespace ChartSamples.ChartedEntry

/-- Evaluate the original chart plan and reuse its source evaluation in the exact shared surface sample. -/
@[expose] def build (entry : AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)
    (request : SegmentComparison.ChartRequest entry.request chartTarget) (plan : ChartRequest.Plan request sample)
    (positive : 0 < chartTarget) (later : request.index ≤ index) (fineLater : request.depth ≤ depth) (readingLater :
      plan.stage ≤ readingIndex) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample shared
      depth readingIndex localTarget localArea chartTarget floor :=
  let chart := plan.evaluate positive depth readingIndex later fineLater readingLater
  let faceLater := (Data.Nat.Order.le_max_right _ _).trans (request.source_le.trans later)
  let value := SampledEntry.ofEvaluation entry chart.original faceLater
  ⟨entry, request, plan, chart, faceLater, value, rfl⟩

variable (entry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea chartTarget floor)

/-- The retained surface sample refers to exactly the original charted occurrence. -/
theorem value_entry : entry.value.entry = entry.entry := by rw [entry.value_eq]; rfl

/-- The actual chart replacement preserves the original retained surface sample's cap total. -/
theorem total_preserved : entry.chart.summary.total = entry.value.evaluated.right.total := by
  rw [entry.value_eq]
  exact entry.chart.total_preserved

/-- The actual chart replacement area satisfies the original chart allowance against the retained surface sample. -/
theorem area_error : Data.Gaussian.Norm.Basic.normSq (entry.chart.summary.area -
  entry.value.evaluated.right.area) < chartTarget := by
  rw [entry.value_eq]
  exact entry.chart.area_error

end ChartSamples.ChartedEntry

set_option genInjectivity false in
/-- The complete ordered charted exterior sample bank with exact original occurrence readback. -/
structure ChartSamples (entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea
  floor))
    (sample : Primitives.Sample cap differential index box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (depth readingIndex : Nat) (chartTarget :
      InverseRootPolynomial.Coordinate) where
  /-- The ordered charted entries sharing the original cap and face primitive banks. -/ values : List
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample shared
    depth readingIndex localTarget localArea chartTarget floor)
  /-- The charted samples project to exactly the retained original exterior occurrence list. -/ entries_eq : values.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.entry = entries

constructive_injectivity ChartSamples

namespace ChartSamples

/-- The original surface samples preserve the exact ordered charted occurrence owners. -/
theorem source_entries (values : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry
  (regular := regular) sample shared depth readingIndex localTarget localArea chartTarget floor)) :
    (values.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value).map
      SampledEntry.entry = values.map ChartedEntry.entry := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg₂ List.cons head.value_entry ih

variable {entries : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular
  domains differential localTarget localArea floor)}

/-- Read the original surface sample bank directly from the retained charted entries. -/
@[expose] def original (samples : ChartSamples entries
  sample shared depth readingIndex chartTarget) : AllSurfacePreparation.Samples entries sample shared depth readingIndex
  :=
  ⟨samples.values.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.value,
    (source_entries samples.values).trans
    samples.entries_eq⟩

/-- The actual charted sample count equals the original occurrence count. -/
theorem count_eq (samples : ChartSamples entries sample
  shared depth readingIndex chartTarget) : samples.values.length = entries.length := by
  have same := congrArg List.length samples.entries_eq
  simpa only [Data.List.Map.length_map] using same

end ChartSamples

namespace ChartSamples.ChartPlans

/-- Prepare each original request's chart plan on the exact same retained cap sample. -/
@[expose] def build (sample : Primitives.Sample cap differential index box) :
    {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)} → (requests
      : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (Plan.build head sample)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans.build sample tail)

/-- The maximum actual chart reading stage, retaining the supplied floor for an empty plan list. -/
@[expose] def maximum : {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea
  floor)} →
    {requests : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample requests → Nat
  | _, _, .nil => floor
  | _, _, .cons head tail => max head.stage tail.maximum

/-- Evaluate every original chart plan at the paid common source, subdivision and reading stages, preserving occurrence
order. -/
@[expose] def evaluate (positive : 0 < chartTarget) :
    {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)} →
    {requests : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartRequests chartTarget entries} →
      (plans : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartPlans sample requests) →
    requests.maximum ≤ index → requests.depthMaximum ≤ depth → plans.maximum ≤ readingIndex →
    ChartSamples entries sample shared depth
      readingIndex chartTarget
  | _, _, .nil, _, _, _ => ⟨[], rfl⟩
  | _, _, .cons (entry := entry) (head := request) head tail, later, fineLater, readingLater =>
      let first := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.build entry request head
        positive ((Data.Nat.Order.le_max_left _ _).trans later)
        ((Data.Nat.Order.le_max_left _ _).trans fineLater) ((Data.Nat.Order.le_max_left _ _).trans readingLater)
      let rest := tail.evaluate positive ((Data.Nat.Order.le_max_right _ _).trans later)
        ((Data.Nat.Order.le_max_right _ _).trans fineLater) ((Data.Nat.Order.le_max_right _ _).trans readingLater)
      ⟨first :: rest.values, congrArg (List.cons entry) rest.entries_eq⟩

end ChartSamples.ChartPlans
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
