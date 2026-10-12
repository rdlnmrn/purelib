module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Riemann.Paths.SegmentGapArea

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergyData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartEnergy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SegmentNonempty

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# The actual shared energy boundary and the polygon of retained endpoint gaps

Group endpoint packets by the original nonempty surface occurrences. Their
cached local energy boundaries sum to the root residual minus the sewn
endpoint polygon, with no omitted cross-occurrence connector.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index depth readingIndex : Nat} {box :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

namespace ChartSamples.ChartedEntry.EnergyData

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- Only the retained endpoints of each original occurrence are read. -/
@[expose] def
  segments
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth entries → List (Gaussian × Gaussian)
  | [], _ => []
  | _ :: tail, energies =>
      let ends := energies.1.endBank branch
      (ends.firstValue, ends.lastValue ends.firstValue) ::
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.segments branch
        tail energies.2

/-- There is exactly one retained endpoint segment per original occurrence. -/
theorem
  segments_length
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries) :
    (energies.segments branch entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih energies.2)

/-- The retained endpoint displacements equal the actual original chart summary totals when the source parents are
nonempty. -/
theorem
  segments_totals
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (nonempty : ∀ entry ∈ entries, entry.entry.occurrence.compared.entered.cache.parents ≠ []) :
    (energies.segments branch entries).map (fun segment => segment.2 - segment.1) =
      entries.map (fun entry => entry.chart.summary.total) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change ((_ - _) :: _) = (head.chart.summary.total :: _)
      rw [← energies.1.endBank_total branch (nonempty head (List.mem_cons_self ..)), ← head.chart.data_total]
      exact congrArg (List.cons _) (ih energies.2 (fun entry member => nonempty entry (List.mem_cons_of_mem head
        member)))

/-- The actual concatenated endpoint bank starts at the first original retained segment value. -/
theorem
  segments_first
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (nonempty : ∀ entry ∈ entries, entry.entry.occurrence.compared.entered.cache.parents ≠ []) :
    (energies.endBank branch entries).firstValue = Paths.SegmentGapArea.first (energies.segments branch entries) 0 := by
  cases entries with
  | nil => rfl
  | cons head tail =>
    exact Charts.Reciprocal.Disk.EnergyEndBank.append_firstValue
      _ _ (nonempty head (List.mem_cons_self ..))

/-- The actual concatenated boundary equals the local boundary sum with every original sewn connector and its endpoint
correction. -/
theorem
  boundary_sewn
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (nonempty : ∀ entry ∈ entries, entry.entry.occurrence.compared.entered.cache.parents ≠ []) (previous finish :
      Gaussian) :
    (energies.endBank branch entries).boundary previous + Path.BoundaryRibbon.area ((energies.endBank branch
      entries).lastValue previous) finish =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.boundaries entries) + Paths.SegmentGapArea.sewnAreas
        (energies.segments branch entries) finish +
        Path.BoundaryRibbon.area previous (Paths.SegmentGapArea.first (energies.segments branch entries) finish) := by
  induction entries generalizing previous with
  | nil =>
    change (0 : Gaussian) + Path.BoundaryRibbon.area previous finish =
      0 + 0 + Path.BoundaryRibbon.area previous finish; ring1
  | cons head tail ih =>
      have present := nonempty head (List.mem_cons_self ..)
      have remaining := fun entry member => nonempty entry (List.mem_cons_of_mem head member)
      let left := energies.1.endBank branch
      let right := energies.2.endBank branch tail
      change (left.append right).boundary previous + Path.BoundaryRibbon.area ((left.append right).lastValue previous)
        finish = _
      rw [Charts.Reciprocal.Disk.EnergyEndBank.append_boundary,
        Charts.Reciprocal.Disk.EnergyEndBank.append_lastValue,
        left.lastValue_independent present previous left.firstValue,
        left.boundary_translate previous left.firstValue]
      have tailEq := ih energies.2 remaining (left.lastValue left.firstValue)
      change right.boundary (left.lastValue left.firstValue) + Path.BoundaryRibbon.area (right.lastValue (left.lastValue
        left.firstValue)) finish = _ at tailEq
      rw [show left.boundary left.firstValue + Path.BoundaryRibbon.area (previous - left.firstValue) left.firstValue +
          right.boundary (left.lastValue left.firstValue) + Path.BoundaryRibbon.area (right.lastValue (left.lastValue
            left.firstValue)) finish =
        left.boundary left.firstValue + Path.BoundaryRibbon.area (previous - left.firstValue) left.firstValue +
          (right.boundary (left.lastValue left.firstValue) + Path.BoundaryRibbon.area (right.lastValue (left.lastValue
            left.firstValue)) finish) by ring1,
        tailEq]
      change _ = (energies.1.boundary + Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.2.boundaries tail)) +
        (Path.BoundaryRibbon.area left.firstValue (left.lastValue left.firstValue) +
          Path.BoundaryRibbon.area (left.lastValue left.firstValue) (Paths.SegmentGapArea.first (energies.2.segments
            branch tail) finish) +
            Paths.SegmentGapArea.sewnAreas (energies.2.segments branch tail) finish) + Path.BoundaryRibbon.area previous
              left.firstValue
      rw [energies.1.endBank_boundary branch present]
      have origin : Path.BoundaryRibbon.area (previous - left.firstValue) left.firstValue = Path.BoundaryRibbon.area
        previous left.firstValue := by
        apply Gaussian.Basic.ext <;> simp only [Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
          Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
      rw [origin]
      dsimp only [left]
      ring1

/-- The actual concatenated endpoint residual equals the original local boundary sum plus the closed sewn endpoint
polygon. -/
theorem
  residual_sewn
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (nonempty : ∀ entry ∈ entries, entry.entry.occurrence.compared.entered.cache.parents ≠ []) :
    (energies.endBank branch entries).residual = Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.boundaries entries)
      +
      Paths.SegmentGapArea.sewnAreas (energies.segments branch entries) (Paths.SegmentGapArea.first (energies.segments
        branch entries) 0) := by
  rw [Charts.Reciprocal.Disk.EnergyEndBank.residual_eq, energies.segments_first
    branch entries nonempty,
    energies.boundary_sewn branch entries nonempty]
  have same : Paths.SegmentGapArea.first (energies.segments branch entries)
      (Paths.SegmentGapArea.first (energies.segments branch entries) 0) = Paths.SegmentGapArea.first (energies.segments
        branch entries) 0 := by
    cases energies.segments branch entries <;> rfl
  rw [same, Path.IncrementArea.area_self, Gaussian.Basic.add_zero]

end ChartSamples.ChartedEntry.EnergyData

namespace SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan.SharedEnergy

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor} {charts :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest request
    chartTarget}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan
    charts sample} {evaluated :
    Evaluation
    plan shared depth readingIndex}
  {energyTarget : Coordinate} {energyFloor : Nat}

/-- Every actual retained energy occurrence has a nonempty original source parent list. -/
theorem
  occurrences_nonempty
  (_energy :
  Plan.SharedEnergy
  evaluated energyTarget energyFloor) :
    ∀ entry ∈ evaluated.samples.values, entry.entry.occurrence.compared.entered.cache.parents ≠ [] := open Purelib in by
  intro entry member
  have entryMember : entry.entry ∈ request.entries :=
    evaluated.samples.entries_eq ▸ Data.List.Map.mem_map.mpr ⟨entry, member, rfl⟩
  have occurrenceMember : entry.entry.occurrence ∈ prepared.occurrences :=
    request.occurrences_eq ▸ Data.List.Map.mem_map.mpr ⟨entry.entry, entryMember, rfl⟩
  exact prepared.occurrence_nonempty entry.entry.occurrence occurrenceMember

/-- This is the missing correction between the shared boundary and the
residual of its actual concatenated endpoint bank. -/
theorem
  boundary_residual_eq
  (energy :
  Plan.SharedEnergy
  evaluated energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    energy.boundary - (energy.data.endBank branch evaluated.samples.values).residual =
      Path.IncrementArea.pathArea ((energy.data.segments branch evaluated.samples.values).map (fun segment => segment.2
        - segment.1)) -
        Paths.SegmentGapArea.sewnAreas (energy.data.segments branch evaluated.samples.values)
          (Paths.SegmentGapArea.first (energy.data.segments branch evaluated.samples.values) 0) := by
  rw [energy.boundary_eq, energy.endpointTerms_eq, energy.coarse.area_eq,
    energy.data.residual_sewn branch evaluated.samples.values energy.occurrences_nonempty,
    energy.data.segments_totals branch evaluated.samples.values energy.occurrences_nonempty]
  ring1

/-- Segment displacement bounds come from the original surface request. -/
theorem
  segments_bounded
  (energy :
  Plan.SharedEnergy
  evaluated energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    ∀ segment ∈ energy.data.segments branch evaluated.samples.values,
      normSq (segment.2 - segment.1) ≤ 2 * (request.slope + 1) := open Purelib in by
  intro segment member
  have belongs : segment.2 - segment.1 ∈ evaluated.samples.values.map (fun entry => entry.chart.summary.total) :=
    energy.data.segments_totals branch evaluated.samples.values energy.occurrences_nonempty ▸
      Data.List.Map.mem_map.mpr ⟨segment, member, rfl⟩
  obtain ⟨entry, inEntries, equal⟩ := Data.List.Map.mem_map.mp belongs
  rw [← equal, entry.total_preserved, entry.value.evaluated.right.total_eq]
  have sourceLe := request.entry_bound entry.entry
    (evaluated.samples.entries_eq ▸ Data.List.Map.mem_map.mpr ⟨entry, inEntries, rfl⟩)
  have bound := entry.value.pair_bounds (request.slope_eq ▸
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum_nonnegative
    prepared.occurrences)
    (entry.value_entry.symm ▸ sourceLe) (request.local_le.trans request.budget.total_le_one)
  have scalar := bound.2.2.2
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- Small gaps between the retained endpoint segments bound the actual shared boundary-minus-residual correction using
the original count and slope. -/
theorem
  boundary_residual_bound
  (energy :
  Plan.SharedEnergy
  evaluated energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) {error : Coordinate}
      (nonnegative : 0 ≤ error)
    (gaps : Paths.SegmentGapArea.GapsSmall (energy.data.segments branch evaluated.samples.values)
      (Paths.SegmentGapArea.first (energy.data.segments branch evaluated.samples.values) 0) error) :
    normSq (energy.boundary - (energy.data.endBank branch evaluated.samples.values).residual) ≤
      2 * (16 * (request.count : Coordinate) ^ 4 * error * (2 * (2 * (request.slope + 1) + error)) +
        (request.count : Coordinate) ^ 2 * (4 * (2 * (request.slope + 1)) * error)) := open Purelib.Data.Rat in by
  rw [energy.boundary_residual_eq branch]
  have estimate := Paths.SegmentGapArea.correction_bound (energy.data.segments branch evaluated.samples.values)
    nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2)
      (add_nonneg (request.slope_eq ▸
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum_nonnegative
        prepared.occurrences) (by decide : (0 : Coordinate) ≤ 1)))
    gaps (by
      intro segment member
      have scalar := energy.segments_bounded branch segment member
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)
  rw [energy.data.segments_length, evaluated.samples.count_eq, request.count_entries] at estimate
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

end SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan.SharedEnergy
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
