module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly
public import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds
import Purelib.Riemann.Readings.RectangularClippedSeamBounds
import Purelib.Integration.Polynomial.Rectangle.ClippedCornerCombination
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Readings.RectangularClippedCornerBounds

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Topology.Polygon

@[expose] public section

/-! Paired grid boundary assembly from the supplied domain numerical bank.
The common model index is selected before these side readings are acquired. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly (BilinearBoundaryAssembly)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {stage : Nat}

/-- Reuse precisely the two entries supplied by the all-differential cache. -/
def DomainBilinearAssembly.bilinearAssembly
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus) (depth : Nat) :
    RectangularBilinearBoundaryAssembly.BilinearBoundaryAssembly (cached first).anchors (cached first).offsets
      (cached second).anchors (cached second).offsets depth :=
  BilinearBoundaryAssembly.build (cached first).anchors (cached first).offsets
    (cached second).anchors (cached second).offsets depth

/-- Apply the clipped-box identity to the very same cached primitive pair. The local model owner is retained, including
on boundary vertices. -/
theorem DomainBilinearAssembly.bilinear_clipped_boundary
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus) {box : Rational.Box}
    (mesh : RectangularObservationMesh.ObservationMesh domain.cuts box) :
    let values := fun column row point =>
      (⟨(cached first).anchors.alignedValue (cached first).offsets column row point,
        (cached second).anchors.alignedValue (cached second).offsets column row point⟩ :
          Stokes.PrimitivePoint)
    RectangularClippedLocalBoundary.localWedges values mesh.triangles =
      mesh.pieces.localBoundary values mesh.depth :=
  mesh.localWedges_eq_boundary _

section EnergyPreflight.Request

variable {preflight : EnergyPreflight domain}
  {target : Coordinate}

/-- Transport the retained basis-row accuracy request to the supplied later common polynomial stage. -/
def DomainBasisBounds.EnergyPreflight.Request.rowAtStage
  (request : EnergyPreflight.Request preflight target)
    (stage : Nat) (later : request.index ≤ stage) (row : Fin genus) :=
  GridPrimitiveAccuracy.atIndex
    (request.rows.get row) stage ((request.index_eq row).trans_le later)

/-- The actual observation mesh may include cuts from other faces. Its corner polygons use the supplied numerical bank
and the retained request at that stage. -/
theorem
  DomainBasisBounds.EnergyPreflight.Request.clipped_cornerTotal_bound
  (request : EnergyPreflight.Request preflight target)
    (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus) {box : Rational.Box}
    {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (assembly : ObservationMesh.ClippedAssembly mesh
      (fun column row point =>
        ⟨(cached first).anchors.alignedValue (cached first).offsets column row point,
          (cached second).anchors.alignedValue (cached second).offsets column row point⟩)) :
    Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
      256 * ((mesh.boundaryColumns : InverseRootPolynomial.Coordinate) * (mesh.boundaryRows :
        InverseRootPolynomial.Coordinate)) ^ 2 *
        (max (request.rowAtStage stage later first).globalBound
          (request.rowAtStage stage later second).globalBound) ^ 2 := by
  exact assembly.cornerTotal_bound
    (request.rowAtStage stage later first) (request.rowAtStage stage later second)
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
    domain.patch.cell_refines

/-- All corrected seams and corners of the actual observation mesh are paid using the same supplied domain bank and
synchronized request index. -/
theorem DomainBilinearAssembly.EnergyPreflight.Request.clipped_local_sub_exterior_bound (request :
  EnergyPreflight.Request preflight target)
    (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus) {box : Rational.Box}
    {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (assembly : ObservationMesh.ClippedAssembly mesh
      (fun column row point =>
        ⟨(cached first).anchors.alignedValue (cached first).offsets column row point,
          (cached second).anchors.alignedValue (cached second).offsets column row point⟩)) :
    let left := request.rowAtStage stage later first
    let right := request.rowAtStage stage later second
    let seam := 8 * max (4 * left.globalBound) (4 * right.globalBound) *
      (4 * max (RectangularSeamBounds.boundarySlope (preflight.overlaps.get first)) (RectangularSeamBounds.boundarySlope
        (preflight.overlaps.get second)) +
        max (4 * RectangularSeamBounds.boundarySlope (preflight.overlaps.get first)) (4 *
          RectangularSeamBounds.boundarySlope (preflight.overlaps.get second)))
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      4 * ((mesh.boundaryColumns : InverseRootPolynomial.Coordinate) ^ 2 * ((mesh.boundaryRows + 1 : Nat) :
        InverseRootPolynomial.Coordinate) ^ 2 +
        ((mesh.boundaryColumns + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (mesh.boundaryRows :
          InverseRootPolynomial.Coordinate) ^ 2) * seam +
      512 * ((mesh.boundaryColumns : InverseRootPolynomial.Coordinate) * (mesh.boundaryRows :
        InverseRootPolynomial.Coordinate)) ^ 2 *
        (max left.globalBound right.globalBound) ^ 2 := by
  exact assembly.local_sub_exterior_bound
    (request.rowAtStage stage later first) (request.rowAtStage stage later second)
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
    domain.patch.cell_refines

/-- Every basis pair is paid for when bounding a coefficient-weighted corner sum; the request target is common to all
rows. -/
theorem DomainBilinearAssembly.EnergyPreflight.Request.weighted_clipped_cornerTotal_bound (request :
  EnergyPreflight.Request preflight target)
    (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (left right : Fin genus → Data.Gaussian.Basic.Canonical) {box : Rational.Box}
    {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box}
    (assembly : ObservationMesh.ClippedAssembly mesh
      (fun column row point =>
        ⟨FiniteSum.Fin.sumFin (fun i => left i *
            (cached i).anchors.alignedValue (cached i).offsets column row point),
          FiniteSum.Fin.sumFin (fun j => right j *
            (cached j).anchors.alignedValue (cached j).offsets column row point)⟩)) :
    Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
      ((genus : InverseRootPolynomial.Coordinate) * (genus : InverseRootPolynomial.Coordinate)) *
        FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq (left i)) *
        FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Norm.Basic.normSq (right j)) *
        (256 * ((mesh.boundaryColumns : InverseRootPolynomial.Coordinate) * (mesh.boundaryRows :
          InverseRootPolynomial.Coordinate)) ^ 2 * target ^ 2) := by
  rw [assembly.cornerTotal_eq_values, ClippedCornerCombination.cornerSum_combination]
  apply BilinearCombination.combination_bound
  intro first second
  let paired := ClippedAssembly.build mesh
    (fun column row point =>
      ⟨(cached first).anchors.alignedValue (cached first).offsets column row point,
        (cached second).anchors.alignedValue (cached second).offsets column row point⟩)
  have estimate := request.clipped_cornerTotal_bound later cached first second paired
  rw [paired.cornerTotal_eq_values] at estimate
  apply estimate.trans
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · apply Fraction.Order.Arithmetic.pow_le_pow_direct _ _ 2
    · exact ((request.rowAtStage stage later first).edgeBound_nonnegative.trans
        (request.rowAtStage stage later first).edgeBound_le_globalBound).trans (Fraction.Order.Basic.le_max_left _ _)
    · exact Fraction.Order.Basic.max_le (request.rowAtStage stage later first).accurate.le
        (request.rowAtStage stage later second).accurate.le
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The original synchronized row requests bound all corrected seams and corners of the actual retained full-domain
bilinear assembly. -/
theorem DomainBilinearAssembly.EnergyPreflight.Request.bilinear_assembly_bound (request : EnergyPreflight.Request
  preflight target)
    (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus) {depth : Nat}
    (assembly : RectangularBilinearBoundaryAssembly.BilinearBoundaryAssembly (cached first).anchors (cached
      first).offsets
      (cached second).anchors (cached second).offsets depth) :
    let left := request.rowAtStage stage later first
    let right := request.rowAtStage stage later second
    let seam := 8 * max left.globalBound right.globalBound *
      (4 * max (RectangularSeamBounds.boundarySlope (preflight.overlaps.get first)) (RectangularSeamBounds.boundarySlope
        (preflight.overlaps.get second)) +
        max left.edgeBound right.edgeBound)
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      4 * ((domain.steps : InverseRootPolynomial.Coordinate) ^ 2 * ((domain.steps + 1 : Nat) :
        InverseRootPolynomial.Coordinate) ^ 2 +
        ((domain.steps + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (domain.steps :
          InverseRootPolynomial.Coordinate) ^ 2) * seam +
      128 * ((domain.steps : InverseRootPolynomial.Coordinate) * (domain.steps : InverseRootPolynomial.Coordinate)) ^ 2
        *
        (max left.globalBound right.globalBound) ^ 2 := by
  exact assembly.local_sub_exterior_bound
    (request.rowAtStage stage later first) (request.rowAtStage stage later second)
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
    domain.patch.cell_refines

end EnergyPreflight.Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
