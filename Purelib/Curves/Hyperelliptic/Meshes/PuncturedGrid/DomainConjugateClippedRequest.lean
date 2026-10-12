module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest
import Purelib.Riemann.Integration.RectangularSharedConjugateError
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.ClippedBilinearBudget
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularClippedLocalBoundary

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Requested conjugate/value comparisons with clipped local boundaries

The existing pair request's finite counts and reading allowances also pay
for the conjugate/value pair. The same numerical rows, meshes and primitive
owners are used; no conjugate holomorphic differential is postulated.
-/

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateClippedRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest (ClippedPairRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest (ClippedBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {box :
    Box} {preflight :
    EnergyPreflight domain}
  {mesh : ObservationMesh domain.cuts box} {first second : Fin genus}
    {target : Rational}

/-- The actual conjugate/value boundary readings satisfy the original clipped local-boundary target using the same
retained numerical rows and mesh. -/
theorem
  ClippedPairRequest.conjugate_accurate
    (request : DomainClippedRequest.ClippedPairRequest preflight mesh first second target)
    {stage : Nat} (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length =>
          ⟨conj ((readings.rows.get first).values vertex), (readings.rows.get second).values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨conj ((cached first).primitives.value column row point),
          (cached second).primitives.value column row point⟩) mesh.depth) < target := by
  let left := request.models.rowAtStage stage later first
  let right := request.models.rowAtStage stage later second
  have leftLe := left.accurate.le
  have rightLe := right.accurate.le
  have estimate := RectangularSharedConjugateError.shared_boundary_conjugate_error left right
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
    domain.patch.cell_refines (readings.rows.get first) (readings.rows.get second)
    (request.budget.small leftLe rightLe)
  let values := fun column row point =>
    (⟨conj ((cached first).primitives.value column row point),
      (cached second).primitives.value column row point⟩ : Stokes.PrimitivePoint)
  have readback := OwnedTriangulation.localWedges_eq_indexed mesh.surface values
  rw [mesh.localWedges_eq_boundary] at readback
  have transported := congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
    (fun vertex : Fin mesh.surface.mesh.vertices.length =>
      ⟨conj ((readings.rows.get first).values vertex), (readings.rows.get second).values vertex⟩)
    mesh.surface.mesh.triangulation.boundary - area)) readback
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at transported ⊢
  exact (transported.trans_le estimate).trans_lt (request.budget.paid leftLe rightLe)

/-- The actual conjugate/value boundary readings satisfy the original clipped local-boundary target using the same
retained numerical rows and mesh. -/
theorem
  ClippedBasisRequest.conjugate_accurate
    (request : DomainClippedRequest.ClippedBasisRequest preflight mesh target)
    {stage : Nat} (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (first second : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length =>
          ⟨conj ((readings.rows.get first).values vertex), (readings.rows.get second).values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨conj ((cached first).primitives.value column row point),
          (cached second).primitives.value column row point⟩) mesh.depth) < target :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateClippedRequest.ClippedPairRequest.conjugate_accurate
    ((request.pairs.get first).get second) ((request.index_ge first second).trans later) cached readings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateClippedRequest
