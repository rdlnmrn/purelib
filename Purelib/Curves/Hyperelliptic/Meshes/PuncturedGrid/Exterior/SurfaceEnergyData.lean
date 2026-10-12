module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.RootRadialGeometry

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ParentOrientation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Energy on the exact retained exterior occurrences

One shared bound and one radial mesh serve every original surface segment.
The list of signed endpoint terms stays in the original boundary order.
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapRequest
  ChartRequest)

/-- Angular orientation comes from the original component program. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.parents_oriented
  (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential) (parentMember : parent ∈
      occurrence.compared.entered.cache.parents) :
    0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) := open Purelib in by
  rw [prepared.occurrences_eq] at member
  obtain ⟨component, _, belongs⟩ := Data.List.Flatten.mem_flatMap.mp member
  have combined : parent ∈ (component.prepared.occurrences.map (fun item =>
    item.compared.entered.cache.parents)).flatten :=
    Data.List.Flatten.mem_flatMap.mpr ⟨occurrence, belongs, parentMember⟩
  rw [component.prepared.parents_eq] at combined
  exact component.program.parents_oriented parent combined

namespace ChartSamples.ChartedEntry

/-- The coarse polygon retains every cross-occurrence term. -/
theorem summary_area (values
  : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample shared depth
  readingIndex localTarget localArea chartTarget floor)) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary values).area =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.chart.summary.area)) +
      Path.IncrementArea.pathArea (values.map (fun value => value.chart.summary.total)) := by
  have total : ∀ values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular :=
    regular) sample shared depth readingIndex localTarget localArea chartTarget floor),
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary values).total =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.chart.summary.total)) := by
    intro values
    induction values with
    | nil => rfl
    | cons head tail ih => exact congrArg (head.chart.summary.total + ·) ih
  induction values with
  | nil => change (0 : Gaussian) = 0 + 0; ring1
  | cons head tail ih =>
      change head.chart.summary.area + (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary
        tail).area + Path.BoundaryRibbon.area head.chart.summary.total
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary tail).total = _
      rw [ih, total]
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Path.IncrementArea.pathArea_cons]
      ring1

/-- The ordered energy preparations for the exact retained exterior chart entries. -/
@[expose] def
  EnergyPreparations
  (energyTarget : Coordinate) (energyFloor : Nat) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample shared depth
      readingIndex localTarget localArea chartTarget floor) → Type 1
  | [] => PUnit
  | head :: tail =>
    Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data.EnergyPreparation
    head.chart.data energyTarget energyFloor ×
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyPreparations energyTarget
    energyFloor tail

/-- Prepare every original chart entry using the same cap bound, positive target and stage floor. -/
@[expose] def prepareEnergy
  (bounds : Charts.Reciprocal.Cap.EnergyBounds sample
  RootContinuation.RootRadialGeometry.domain)
    (energyTarget : Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyPreparations energyTarget energyFloor
      values
  | [] => ⟨⟩
  | head :: tail => ⟨ChartRequest.Plan.Data.prepareEnergy head.chart.data bounds energyTarget positive energyFloor,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.prepareEnergy bounds
        energyTarget positive energyFloor tail⟩

/-- The ordered evaluated energy data on the exact original chart entries at one shared depth. -/
@[expose] def EnergyData
  (energyTarget : Coordinate) (energyFloor energyDepth : Nat) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample shared depth
      readingIndex localTarget localArea chartTarget floor) → Type 1
  | [] => PUnit
  | head :: tail =>
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data.EnergyData
    head.chart.data energyTarget energyFloor energyDepth ×
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
    energyFloor energyDepth tail

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- The maximum sufficient depth retained by the original chart preparations, including the supplied floor. -/
@[expose] def
  EnergyPreparations.maximum
  :
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyPreparations energyTarget energyFloor
      values → Nat
  | [], _ => energyFloor
  | _ :: tail, preparations => max preparations.1.minimum (maximum tail preparations.2)

/-- Evaluate the retained preparations on one radial mesh and common sufficient depth using their original
parent-orientation certificates. -/
@[expose] def
  EnergyPreparations.evaluate
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth) :
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
    (preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyPreparations
      energyTarget energyFloor values) →
    (∀ entry ∈ values, ∀ parent ∈ entry.entry.occurrence.compared.entered.cache.parents,
      0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) →
    preparations.maximum values ≤ energyDepth →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth values
  | [], _, _, _ => ⟨⟩
  | head :: tail, preparations, oriented, later =>
      ⟨preparations.1.evaluate branch (oriented head (List.mem_cons_self)) parameters ((Data.Nat.Order.le_max_left _
        _).trans later),
        evaluate branch parameters tail preparations.2 (fun entry member => oriented entry (List.mem_cons_of_mem _
          member))
          ((Data.Nat.Order.le_max_right _ _).trans later)⟩

namespace EnergyData

/-- The actual energy readings in the original exterior occurrence order. -/
@[expose] def
  values :
  (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth entries → List Gaussian
  | [], _ => []
  | _ :: tail, energies => energies.1.value ::
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.values tail
    energies.2

/-- The actual signed boundary-potential readings in the original exterior occurrence order. -/
@[expose] def
  boundaries :
  (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth entries → List Gaussian
  | [], _ => []
  | _ :: tail, energies => energies.1.boundary ::
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.boundaries tail
    energies.2

/-- The energy-minus-boundary comparison errors retaining each original chart area and boundary potential. -/
@[expose] def
  errors :
  (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth entries → List Gaussian
  | [], _ => []
  | head :: tail, energies => (energies.1.value - (-head.chart.summary.area + energies.1.boundary)) ::
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.errors tail
    energies.2

/-- There is one retained comparison error per original exterior chart entry. -/
theorem
  errors_count :
  (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries) → (energies.errors entries).length = entries.length
  | [], _ => rfl
  | _ :: tail, energies => congrArg Nat.succ
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.errors_count tail
    energies.2)

/-- The sum of the original comparison errors is total energy plus chart area minus boundary potential. -/
theorem
  errors_sum :
  (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
  shared depth readingIndex localTarget localArea chartTarget floor)) →
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries) →
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.errors entries) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (energies.values entries) +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.chart.summary.area)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.boundaries entries)
  | [], _ => by change (0 : Gaussian) = 0 + 0 - 0; ring1
  | head :: tail, energies => by
      change (energies.1.value - (-head.chart.summary.area + energies.1.boundary)) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.2.errors tail) =
        (energies.1.value + Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.2.values tail)) +
          (head.chart.summary.area + Data.Gaussian.Norm.Sum.Basic.gaussianSum _) -
          (energies.1.boundary + Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.2.boundaries tail))
      rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.errors_sum
        tail energies.2]
      ring1

/-- Every retained ramified-chart error satisfies the original chart and local target bound. -/
theorem
  errors_bounded
  (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (positive : 0 < chartTarget)
  :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries) →
    ∀ error ∈ energies.errors entries, normSq error ≤ 256 * (4 * chartTarget + localTarget)
  | [], _, _, member => by cases member
  | head :: tail, energies, error, member => by
      rcases Data.List.Membership.mem_cons.mp member with equal | member
      · subst error
        rw [head.chart.data_area]
        have scalar := (energies.1.boundary_close branch positive).le
        rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar
      · exact
          Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.errors_bounded
          branch positive tail energies.2 error member

/-- The total retained chart energy is bounded below by minus the original occurrence count times the energy target. -/
theorem lower
  (positive : 0 < energyTarget) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries) →
    -((entries.length : Coordinate) * energyTarget) ≤ (Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.values
      entries)).im / 4
  | [], _ => by
    change -((0 : Coordinate) * energyTarget) ≤ (0 : Coordinate) / 4; rw [show -((0 : Coordinate) * energyTarget) = 0 by
      ring1]; decide
  | head :: tail, energies => by
      have combined := Fraction.Order.Arithmetic.add_le_add_direct (energies.1.lower positive).le
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData.lower positive
        tail energies.2)
      simp only [List.length_cons, Nat.cast_succ]
      change -(((tail.length : Coordinate) + 1) * energyTarget) ≤ (energies.1.value +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (energies.2.values tail)).im / 4
      exact (show -(((tail.length : Coordinate) + 1) * energyTarget) = -energyTarget + -((tail.length : Coordinate) *
        energyTarget) by ring1).trans_le
        (combined.trans_eq (by simp only [Gaussian.Basic.add_im, Fraction.Field.div_eq_mul_inv_direct]; ring1))

end EnergyData
end ChartSamples.ChartedEntry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
