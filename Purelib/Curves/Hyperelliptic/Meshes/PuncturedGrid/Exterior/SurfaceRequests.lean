module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-!
# Shared surface/cap requests across every exterior occurrence

One request pays the full occurrence count before choosing the common cap
and face index. Area concatenation retains every internal excursion and all
cross terms between segment totals. The retained source paths, shared
triangle edges and cap paths are consumed without a second preparation.
-/

section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapRequest)
open Purelib.Riemann.Normalization
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive count_mul_perTerm_lt)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

/-- Read the maximum of zero and all actual exterior occurrence source bounds. -/
@[expose] def sourceMaximum : List (ExteriorProgram.SurfaceOccurrence regular domains differential) →
  InverseRootPolynomial.Coordinate
  | [] => 0
  | head :: tail => max head.cap.sourceBound
    (sourceMaximum
    tail)

/-- The retained exterior source-bound maximum is nonnegative. -/
theorem sourceMaximum_nonnegative (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
  : 0 ≤ sourceMaximum
  occurrences := by
  cases occurrences with
  | nil => exact le_rfl
  | cons head tail => exact head.cap.sourceBound_nonnegative.trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _)

/-- Every actual original exterior occurrence source bound is below the retained maximum. -/
theorem sourceBound_le (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential)) :
    ∀ item ∈ occurrences, item.cap.sourceBound ≤
      sourceMaximum occurrences
      := by
  induction occurrences with
  | nil => intro item member; cases member
  | cons head tail ih =>
      intro item member
      rcases Membership.mem_cons.mp member with rfl | member
      · exact Data.Rat.Fraction.Order.Basic.le_max_left _ _
      · exact (ih item member).trans (Data.Rat.Fraction.Order.Basic.le_max_right _ _)

set_option genInjectivity false in
/-- One actual exterior surface occurrence and its paid source/cap comparison request. -/
structure Entry (regular : RegularBounds.Data cap) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) (target areaTarget : InverseRootPolynomial.Coordinate)
      (floor : Nat) where
  /-- The exact original surface occurrence retained by this request. -/ occurrence : ExteriorProgram.SurfaceOccurrence
    regular domains differential
  /-- The actual cap comparison request on this occurrence's existing preparation. -/ request :
    SegmentComparison.CapRequest occurrence.cap target areaTarget floor

constructive_injectivity Entry

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry

/-- Prepare the supplied original exterior occurrence's cap comparison at the requested positive total and area targets.
-/
@[expose] def build (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) (target areaTarget :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
      differential target areaTarget floor :=
  ⟨occurrence, CapRequest.build occurrence.cap target areaTarget positive areaPositive floor⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry

variable {target areaTarget : Coordinate} {floor : Nat}

/-- Read the common model stage paying every actual occurrence request and the caller floor. -/
@[expose] def maximum : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential target areaTarget floor) → Nat
  | [] => floor
  | head :: tail => max head.request.index
    (maximum
    tail)

/-- Read the common reading stage paying every actual occurrence request and the caller floor. -/
@[expose] def readingMaximum : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential target areaTarget floor) → Nat
  | [] => floor
  | head :: tail => max head.request.readingIndex
    (readingMaximum
    tail)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

set_option genInjectivity false in
/-- The complete count-paid source/cap request on the original exterior occurrence bank.

One common allowance pays total, area and retained period obligations before model and reading stages are selected. -/
structure Request (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) (target areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached actual exterior occurrence count. -/ count : Nat
  /-- The count cache is exactly the original preparation's occurrence-list length. -/ count_eq : count =
    prepared.occurrences.length
  /-- The cached common source bound across all original exterior occurrences. -/ slope :
    InverseRootPolynomial.Coordinate
  /-- The slope cache is exactly the maximum of the original occurrence source bounds. -/ slope_eq : slope =
    sourceMaximum
    prepared.occurrences
  /-- The retained full-side area budget on this exact occurrence count and source bound. -/ budget :
    ReciprocalSideArea.SideAreaBudget slope count areaTarget
  /-- The cached period plans on the original exterior components. -/ periods : PeriodPlans.ComponentPeriodPlans target
    prepared.components
  /-- The cached minimum local allowance required by the original period plans. -/ periodLocal :
    InverseRootPolynomial.Coordinate
  /-- The local period allowance is exactly the retained plans' minimum. -/ periodLocal_eq : periodLocal =
    periods.localMinimum
  /-- The cached minimum coefficient allowance required by the original period plans. -/ periodCoefficient :
    InverseRootPolynomial.Coordinate
  /-- The coefficient allowance is exactly the retained plans' minimum. -/ periodCoefficient_eq : periodCoefficient =
    periods.coefficientMinimum
  /-- The cached positive allowance simultaneously paying original count, area and period obligations. -/ localTarget :
    InverseRootPolynomial.Coordinate
  /-- The allowance is exactly the minimum of the count-paid total, side-area, local-period and coefficient budgets. -/
    localTarget_eq : localTarget = min (min (Aggregate.perTerm target count) budget.totalTarget) (min periodLocal
    periodCoefficient)
  /-- The retained common local allowance is strictly positive. -/ positive : 0 < localTarget
  /-- The actual occurrence count squared times the retained allowance is below the original total target. -/ total_paid
    : (count : InverseRootPolynomial.Coordinate) * ((count : InverseRootPolynomial.Coordinate) * localTarget) < target
  /-- The complete ordered request bank on the original surface occurrences. -/ entries : List
    (Entry regular domains
    differential localTarget budget.areaTarget floor)
  /-- The request entries project to exactly the original occurrence list. -/ occurrences_eq : entries.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.occurrence =
    prepared.occurrences
  /-- The number of actual request entries equals the cached occurrence count. -/ count_entries : entries.length = count
  /-- The cached common model stage for all original occurrence requests. -/ index : Nat
  /-- The model stage is exactly the retained entry maximum. -/ index_eq : index =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.maximum entries
  /-- The cached common reading stage for all original occurrence requests. -/ readingIndex : Nat
  /-- The reading stage is exactly the retained entry reading maximum. -/ readingIndex_eq : readingIndex =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.readingMaximum
    entries

constructive_injectivity Request

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}
  {floor : Nat}

/-- Allocate one positive count-paid allowance across the original occurrence and period obligations, then cache all
requests and common stages. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) (target areaTarget :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
      areaTarget floor := by
  let count := prepared.occurrences.length
  let slope := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum
    prepared.occurrences
  let budget := SideAreaBudget.build slope
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum_nonnegative
    _) count areaTarget areaPositive
  let periods := ComponentPeriodPlans.build target positive prepared.components
  let periodLocal := periods.localMinimum
  let periodCoefficient := periods.coefficientMinimum
  let localTarget := min (min (Aggregate.perTerm target count) budget.totalTarget) (min periodLocal periodCoefficient)
  have localPositive : 0 < localTarget := Fraction.Order.Basic.lt_min (Fraction.Order.Basic.lt_min
    (Aggregate.perTerm_positive positive _) budget.total_positive)
    (Fraction.Order.Basic.lt_min periods.local_positive periods.coefficient_positive)
  let entries := prepared.occurrences.map (fun occurrence =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.build occurrence
    localTarget budget.areaTarget localPositive budget.area_positive floor)
  have occurrencesEq : entries.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.occurrence =
    prepared.occurrences := by
    change (prepared.occurrences.map _).map _ = _
    rw [Map.map_map]
    change prepared.occurrences.map (fun item => item) = prepared.occurrences
    induction prepared.occurrences with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  have paid : (count : InverseRootPolynomial.Coordinate) * ((count : InverseRootPolynomial.Coordinate) * localTarget) <
    target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ((Data.Rat.Fraction.Order.Basic.min_le_left _ _).trans
        (Data.Rat.Fraction.Order.Basic.min_le_left _ _))
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))).trans_lt (Aggregate.count_mul_perTerm_lt positive
        count)
  exact ⟨count, rfl, slope, rfl, budget, periods, periodLocal, rfl, periodCoefficient, rfl, localTarget, rfl,
    localPositive, paid, entries, occurrencesEq,
    Map.length_map ..,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.maximum entries,
      rfl, Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.readingMaximum
      entries, rfl⟩

/-- The retained local allowance pays the original side-area total-error obligation. -/
theorem local_le (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) : request.localTarget ≤ request.budget.totalTarget := by
  rw [request.localTarget_eq]
  exact (Data.Rat.Fraction.Order.Basic.min_le_left _ _).trans (Data.Rat.Fraction.Order.Basic.min_le_right _ _)

/-- The retained local allowance pays every original component period's local obligation. -/
theorem local_period_le (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) : request.localTarget ≤ request.periods.localMinimum := by
  rw [request.localTarget_eq, ← request.periodLocal_eq]
  exact (Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Data.Rat.Fraction.Order.Basic.min_le_left _ _)

/-- The retained local allowance pays every original component period's coefficient obligation. -/
theorem coefficient_period_le (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) : request.localTarget ≤ request.periods.coefficientMinimum := by
  rw [request.localTarget_eq, ← request.periodCoefficient_eq]
  exact (Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Data.Rat.Fraction.Order.Basic.min_le_right _ _)

/-- Every actual member occurrence satisfies the request's cached common source bound. -/
theorem entry_bound (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) (entry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential request.localTarget request.budget.areaTarget floor)
    (member : entry ∈ request.entries) : entry.occurrence.cap.sourceBound ≤ request.slope := by
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceBound_le _ _
    (request.occurrences_eq ▸ Map.mem_map.mpr ⟨entry, member, rfl⟩)).trans_eq request.slope_eq.symm

/-- The retained request occurrences read exactly the complete original exterior boundary edges in order. -/
theorem indexed_eq (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
  areaTarget floor) :
    request.entries.map (fun entry => entry.occurrence.placement.indexed) = lifted.exteriorBoundaries.flatten := by
  have equal := congrArg (List.map (fun occurrence => occurrence.placement.indexed)) request.occurrences_eq
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at equal
  exact equal.trans prepared.indexed_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request

variable {localTarget localArea : Coordinate} {floor index depth
  readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : FacePrimitiveBank differential index
    domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

set_option genInjectivity false in
/-- One original exterior occurrence evaluated on the shared cap and face banks.

The actual shared face increment retains separate comparisons to the cached source and cap totals. -/
structure SampledEntry (sample : Primitives.Sample cap differential index box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (depth readingIndex : Nat)
    (localTarget localArea : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The exact original exterior request consumed by this numerical entry. -/ entry :
    Entry regular domains
    differential localTarget localArea floor
  /-- The actual retained cap comparison at the supplied common depth and reading stage. -/ evaluated :
    CapRequest.Evaluation entry.request sample depth readingIndex
  /-- The cached shared face-bank increment at this exact original occurrence placement. -/ increment :
    InverseRootPolynomial.Gaussian
  /-- The increment cache equals the original shared bank's exact edge increment. -/ increment_eq : increment =
    shared.edgeIncrement entry.occurrence.placement.location
  /-- The actual face increment and retained source total satisfy the prescribed local source allowance. -/ source_close
    : Data.Gaussian.Norm.Basic.normSq (increment - evaluated.left.total) < (localTarget / 4) / 4
  /-- The actual face increment and retained cap total satisfy the original local target. -/ integral_close :
    Data.Gaussian.Norm.Basic.normSq (increment - evaluated.right.total) < localTarget

constructive_injectivity SampledEntry

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry

/-- Consume the supplied retained cap evaluation and its exact shared face reference. Chart acquisition and ordinary
acquisition use this same path. -/
@[expose] def ofEvaluation (entry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential localTarget localArea floor)
    (evaluated : CapRequest.Evaluation entry.request sample depth readingIndex)
    (later : entry.request.budget.grid.index ≤ index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor :=
  ⟨entry, evaluated, shared.edgeIncrement entry.occurrence.placement.location, rfl,
    evaluated.corner_source_error entry.occurrence.aligned later shared,
    evaluated.corner_error entry.occurrence.aligned later shared⟩

/-- Evaluate the original occurrence request and retain its exact shared face increment at the supplied paid stages. -/
@[expose] def build (entry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential localTarget localArea floor)
    (later : entry.request.index ≤ index) (readingLater : entry.request.readingIndex ≤ readingIndex) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor :=
  ofEvaluation
    entry (entry.request.evaluate sample depth readingIndex later readingLater) ((Data.Nat.Order.le_max_right _ _).trans
    later)

/-- Read the actual original source and cap paths already retained by this evaluated occurrence. -/
@[expose] def pair (value :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor) : List InverseRootPolynomial.Gaussian × List
  Gaussian :=
  (value.evaluated.sourcePath,
    value.evaluated.capPath)

/-- Concatenate the actual retained source summaries, preserving all original path totals and area cross terms. -/
@[expose] def leftSummary : (values : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor)) →
    IncrementArea.Summary (((values.map
      pair).map
      Prod.fst).flatten)
  | [] => IncrementArea.Summary.build []
  | head :: tail => head.evaluated.left.append
    (leftSummary
    tail)

/-- Concatenate the actual retained cap summaries, preserving all original path totals and area cross terms. -/
@[expose] def rightSummary : (values : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor)) →
    IncrementArea.Summary (((values.map
      pair).map
      Prod.snd).flatten)
  | [] => IncrementArea.Summary.build []
  | head :: tail => head.evaluated.right.append
    (rightSummary
    tail)

/-- The actual shared face increment satisfies the original source-slope magnitude bound when the local target is at
most one. -/
theorem increment_bound (value :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor)
    {slope : InverseRootPolynomial.Coordinate} (sourceLe : value.entry.occurrence.cap.sourceBound ≤ slope) (small :
      localTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq value.increment ≤ 2 * (slope + 1) := by
  have positive := value.entry.request.positive.le
  have quarterNonnegative := Fraction.Order.Field.div_nonneg_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  have error := value.source_close.le.trans ((Fraction.Order.Field.divide_le_self quarterNonnegative (by decide)).trans
    ((Fraction.Order.Field.divide_le_self positive (by decide)).trans small))
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two value.evaluated.left.total
    (value.increment - value.evaluated.left.total)
  rw [show value.evaluated.left.total + (value.increment - value.evaluated.left.total) =
    value.increment by ring1] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (value.evaluated.source_bounded.trans sourceLe) error) (by decide))

/-- The actual retained source/cap paths satisfy their local area and total-error bounds and common source-slope
magnitude bounds. -/
theorem pair_bounds (value :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
  regular) sample shared depth readingIndex localTarget localArea floor)
    {slope : InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope) (sourceLe :
      value.entry.occurrence.cap.sourceBound ≤ slope)
    (small : localTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea value.pair.1 - IncrementArea.pathArea value.pair.2)
      ≤ localArea ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum value.pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum value.pair.2) ≤ localTarget ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum value.pair.1) ≤ 2 * (slope +
      1) ∧ Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum value.pair.2) ≤ 2 *
      (slope + 1) := by
  dsimp only
    [pair]
  rw [← value.evaluated.left.area_eq, ← value.evaluated.right.area_eq,
    ← value.evaluated.left.total_eq, ← value.evaluated.right.total_eq]
  have sourceBound := value.evaluated.source_bounded.trans sourceLe
  have totalBound := value.evaluated.total_close.le.trans (Fraction.Order.Field.divide_le_self
    value.entry.request.positive.le (by decide))
  have expanded : slope ≤ 2 * (slope + 1) :=
    (le_add_of_nonneg_right (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by decide)).trans
      ((le_add_of_nonneg_right (add_nonneg slopeNonnegative (show (0 : InverseRootPolynomial.Coordinate) ≤ 1 by
        decide))).trans_eq (by ring1))
  refine ⟨value.evaluated.area_close.le, totalBound, sourceBound.trans expanded, ?_⟩
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two value.evaluated.left.total
    (-(value.evaluated.left.total - value.evaluated.right.total))
  rw [show value.evaluated.left.total + -(value.evaluated.left.total - value.evaluated.right.total) =
    value.evaluated.right.total by ring1, Data.Gaussian.Norm.Basic.normSq_neg] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add sourceBound (totalBound.trans small)) (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

set_option genInjectivity false in
/-- The complete evaluated exterior occurrence bank retaining its exact original request ordering. -/
structure Samples (entries : List
  (Entry regular domains
  differential localTarget localArea floor))
    (sample : Primitives.Sample cap differential index box) (shared : PrimitiveData.FacePrimitiveBank differential index
      domains)
    (depth readingIndex : Nat) where
  /-- The cached actual occurrence evaluations on the shared cap and face samples. -/ values : List
    (SampledEntry (regular :=
    regular) sample shared depth readingIndex localTarget localArea floor)
  /-- The evaluated occurrence bank projects to exactly the original request list. -/ entries_eq : values.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.entry =
    entries

constructive_injectivity Samples

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

/-- Evaluate every original occurrence request in order on the same retained cap and face samples. -/
@[expose] def build : (entries : List
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry regular domains
  differential localTarget localArea floor)) →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.maximum entries ≤
      index →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Entry.readingMaximum
      entries ≤ readingIndex →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples entries sample
      shared depth readingIndex
  | [], _, _ => ⟨[], rfl⟩
  | head :: tail, later, readingLater =>
      let value :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.build head
        ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans readingLater)
      let rest :=
        build
        tail ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans readingLater)
      ⟨value :: rest.values, congrArg (List.cons head) rest.entries_eq⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

end
