module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
public import Purelib.Integration.Path.PairedIncrementArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-! Paired area on the literal shared-grid source word of annular excision.
Both differential banks use the same retained source occurrences. The coarse
source count remains in the bound and must be paid by the global allocator. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedSources

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted : Meshes.LiftedPuncturedGrid
    grid.punctured}

namespace Lifted.OuterPreparation.Comparison

variable {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted} {prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region}
  {differential : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars}
  {tolerance : Fraction.Rational}

/-- Each paired differential reading on the same retained source occurrence satisfies the common scalar magnitude bound.
-/
theorem paired_source_bound (first :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance)
    {other : Fin genus} (second :
      Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance)
    {stage : Nat} (firstLater : first.reference.index ≤ stage) (secondLater : second.reference.index ≤ stage)
    {firstBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    {secondBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential other) stage domains}
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank
      lifted.mesh) :
    ∀ point ∈ prepared.sources.map (fun source =>
      (⟨Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
        Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)),
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded point (3 * tolerance + 4 * (target / 16)) := by
  intro point member
  rcases Data.List.Map.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  rw [prepared.sources_eq] at sourceMember
  have firstScalar := first.reference.source_bound first.shared firstLater firstReadings
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values)
    (Data.List.Map.mem_map.mpr ⟨source, sourceMember, rfl⟩)
  have secondScalar := second.reference.source_bound second.shared secondLater secondReadings
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values)
    (Data.List.Map.mem_map.mpr ⟨source, sourceMember, rfl⟩)
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
  exact ⟨firstScalar, secondScalar⟩

/-- The full ordered polygon, including every repeated source occurrence. -/
theorem paired_source_area_bound (first :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance)
    {other : Fin genus} (second :
      Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance)
    {stage : Nat} (firstLater : first.reference.index ≤ stage) (secondLater : second.reference.index ≤ stage)
    {firstBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    {secondBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential other) stage domains}
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (prepared.sources.map (fun source =>
      (⟨Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
        Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))) ≤
      4 * ((region.outer.length : Fraction.Rational)^2 * (3 * tolerance + 4 * (target / 16)))^2 := by
  have bounded := Path.PairedIncrementArea.area_bound _ first.reference.bound_nonnegative
    (Hyperelliptic.Meshes.Newton.Annulus.PairedSources.Lifted.OuterPreparation.Comparison.paired_source_bound first
      second firstLater secondLater firstReadings secondReadings)
  have count := congrArg List.length prepared.sources_project
  rw [List.Map.length_map] at count
  rw [List.Map.length_map, count] at bounded
  exact bounded

/-- Endpoint increments are bounded, not erased by sheet return. -/
theorem paired_source_total_bound (first :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance)
    {other : Fin genus} (second :
      Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance)
    {stage : Nat} (firstLater : first.reference.index ≤ stage) (secondLater : second.reference.index ≤ stage)
    {firstBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    {secondBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential other) stage domains}
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank
      lifted.mesh) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total (prepared.sources.map (fun source =>
        (⟨Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
          Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))))
      ((region.outer.length : Fraction.Rational)^2 * (3 * tolerance + 4 * (target / 16))) := by
  have count := congrArg List.length prepared.sources_project
  rw [List.Map.length_map] at count
  exact Path.PairedIncrementArea.total_bound first.reference.bound_nonnegative
    (Hyperelliptic.Meshes.Newton.Annulus.PairedSources.Lifted.OuterPreparation.Comparison.paired_source_bound first
      second firstLater secondLater firstReadings secondReadings)
    (by rw [List.Map.length_map, count])

/-- Translation retains the determinant against the actual endpoint total. -/
theorem paired_source_trace_bound (first :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance)
    {other : Fin genus} (second :
      Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared other domains
      tolerance)
    {stage : Nat} (firstLater : first.reference.index ≤ stage) (secondLater : second.reference.index ≤ stage)
    {firstBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    {secondBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential other) stage domains}
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank
      lifted.mesh)
    (anchor : Topology.Polygon.Stokes.PrimitivePoint) {magnitude : Fraction.Rational} (anchorBound :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded anchor magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.traceArea anchor (prepared.sources.map (fun source =>
      (⟨Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source firstReadings.values,
        Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment source secondReadings.values⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))) ≤
      8 * ((region.outer.length : Fraction.Rational)^2 * (3 * tolerance + 4 * (target / 16)))^2 +
        8 * magnitude * ((region.outer.length : Fraction.Rational)^2 * (3 * tolerance + 4 * (target / 16))) := by
  have endpoint := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound anchorBound
    (Hyperelliptic.Meshes.Newton.Annulus.PairedSources.Lifted.OuterPreparation.Comparison.paired_source_total_bound
      first second firstLater secondLater firstReadings secondReadings)
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at endpoint
  rw [Path.PairedIncrementArea.traceArea_eq]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add
        (Hyperelliptic.Meshes.Newton.Annulus.PairedSources.Lifted.OuterPreparation.Comparison.paired_source_area_bound
        first second firstLater secondLater firstReadings secondReadings)
        endpoint) (by decide)).trans_eq (by ring1))

end Lifted.OuterPreparation.Comparison
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedSources
