module
import Purelib.Data.List.Membership
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalRegularPeriods
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Data.List.Flatten
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Each retained exterior component is read on its own original canonical
word. The component partition reuses the full request's sampled values. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl
open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request
  SampledEntry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples (SampledComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (RegularBoundaryControl)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary (canonical_physical_source)
open Purelib.Topology.Mesh.RetracingWords (sum_map_eq_wordValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (exteriorPrograms
  exteriorPrograms_indexed)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Coordinate} {floor : Nat}
  {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared
    target areaTarget floor}

namespace Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation

/-- The canonical edge valuation reads each actual retained exterior component word as its original sampled surface
total. -/
theorem
  canonical_component_integral
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (grouped : ComponentSamples sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor
      prepared.components evaluated.samples.values)
    (group : ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor)
    (member : group ∈ grouped.groups) (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      group.component.program.indexed = group.surface.total := by
  have indexed : group.values.map (fun entry => entry.entry.occurrence.placement.indexed) =
    group.component.program.indexed := by
    have equal := congrArg (List.map (fun occurrence => occurrence.placement.indexed)) group.occurrences_eq
    simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at equal
    exact equal.trans group.component.prepared.occurrences_eq
  have valueEq (entry : AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth readingIndex
    request.localTarget request.budget.areaTarget floor)
      (retained : entry ∈ group.values) :
      CanonicalEdgeValues.edgeValuation lifted.mesh readings.values entry.entry.occurrence.placement.indexed =
        entry.entry.occurrence.placement.location.sourceEdge.increment readings.values := by
    have inValues : entry ∈ evaluated.samples.values := grouped.values_eq ▸
      (Data.List.mem_flatten_of_mem (Map.mem_map_of_mem member) retained)
    have inEntries : entry.entry ∈ request.entries := evaluated.samples.entries_eq ▸ Map.mem_map_of_mem inValues
    have exterior : entry.entry.occurrence.placement.indexed ∈ lifted.exteriorBoundaries.flatten :=
      request.indexed_eq ▸ Map.mem_map_of_mem inEntries
    have physical : entry.entry.occurrence.placement.indexed ∈ lifted.boundaryLoops.flatten := by
      change _ ∈ (lifted.exteriorBoundaries ++ _).flatten
      rw [Data.List.Flatten.flatten_append]
      exact Data.List.Membership.mem_append.mpr (Or.inl exterior)
    have canonical := CanonicalPhysicalBoundary.canonical_physical_source
      entry.entry.occurrence.placement.location.sourceEdge
      (entry.entry.occurrence.placement.location.sourceEdge_project.symm ▸ physical) readings.values
    exact (congrArg (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      entry.entry.occurrence.placement.location.sourceEdge_project).symm.trans canonical
  calc
    _ = SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (group.values.map (fun entry => entry.entry.occurrence.placement.indexed)) := congrArg _ indexed.symm
    _ = Data.Gaussian.Norm.Sum.Basic.gaussianSum ((group.values.map (fun entry =>
      entry.entry.occurrence.placement.indexed)).map
        (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) := (RetracingWords.sum_map_eq_wordValue _
          _).symm
    _ = Data.Gaussian.Norm.Sum.Basic.gaussianSum ((group.values.map SampledEntry.entry).map
        (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values)) := by
      simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self]
      exact congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (Map.map_congr_left valueEq)
    _ = group.surface.total := (group.triangle_integral readings).symm

/-- The original even-degree exterior preparation bounds each retained canonical component word separately by the
requested target. -/
theorem
  canonical_component_small
  (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (grouped : ComponentSamples sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor
      prepared.components evaluated.samples.values)
    (group : ComponentSamples.SampledComponent (regular := regular) sample shared depth readingIndex request.localTarget
      request.budget.areaTarget floor)
    (member : group ∈ grouped.groups) (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.values) group.component.program.indexed) < target :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (evaluated.canonical_component_integral grouped group member
    readings)).trans_lt
    (evaluated.component_integral_small degree grouped group member)

end Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation
namespace RegularBoundaryControl

variable {loss : Coordinate}

/-- Each original canonical component is small separately. -/
theorem
  canonical_components_small
  (control : RegularBoundaryControl prepared target loss floor)
    (readings : TrianglePrimitiveReadings.TriangleReadings control.acquired.shared lifted.mesh) :
    ∀ group ∈ control.components.groups,
      Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
        lifted.mesh readings.values) group.component.program.indexed) < target := by
  intro group member
  exact (congrArg Data.Gaussian.Norm.Basic.normSq
    (control.acquired.evaluated.source.canonical_component_integral
    control.components group member readings)).trans_lt (control.component_integrals_small group member)

/-- Canonical preparation retains exactly the original exterior loop list, not merely an equality of flattened
occurrence lists. -/
theorem
  component_words
    (control : RegularBoundaryControl (AllSurfacePreparation.build regular domains differential)
      target loss floor) :
    control.components.groups.map (fun group => group.component.program.indexed) = lifted.exteriorBoundaries := by
  have equal := congrArg (List.map (fun component => component.program.indexed)) control.components.components_eq
  simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at equal
  have canonical : (AllSurfacePreparation.build regular domains differential).components.map
      (fun component => component.program.indexed) = lifted.exteriorBoundaries := by
    change ((PeriodPrograms.exteriorPrograms lifted differential).map (SurfaceComponent.build regular domains)).map
      (fun component => component.program.indexed) = _
    rw [Data.List.Map.map_map]
    exact PeriodPrograms.exteriorPrograms_indexed lifted differential
  exact equal.trans canonical

/-- Every loop used by the physical correction has its own period bound. -/
theorem
  boundary_words_small
    (control : RegularBoundaryControl (AllSurfacePreparation.build regular domains differential)
      target loss floor)
    (readings : TrianglePrimitiveReadings.TriangleReadings control.acquired.shared lifted.mesh) :
    ∀ word ∈ lifted.exteriorBoundaries,
      Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
        lifted.mesh readings.values) word) < target := by
  intro word member
  have retained : word ∈ control.components.groups.map (fun group => group.component.program.indexed) :=
    control.component_words.symm ▸ member
  obtain ⟨group, present, equal⟩ := Map.mem_map.mp retained
  exact (congrArg (fun boundary => Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) boundary)) equal).symm.trans_lt
    (control.canonical_components_small readings group present)

end RegularBoundaryControl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
