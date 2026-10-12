module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Periods.ClippedBilinearBudget
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularRequestedClippedBoundary
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation

public section

/-! Ownership requests selected before constructing a shared domain bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann
open Purelib.Riemann.Integration.RectangularOwnedTriangulation
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Box)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Periods (ClippedBilinearBudget)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest (EnergyRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {box :
    Box}

set_option genInjectivity false in
/-- A paid clipped-boundary comparison for one original basis pair on the actual observation mesh.

The two original clipped side realizations retain their source intervals and paid bounds. The request consumes the
displayed maximum allowance without replacing either input owner. -/
structure ClippedPairRequest (preflight : DomainBasisBounds.EnergyPreflight domain) (mesh :
  RectangularObservationMesh.ObservationMesh domain.cuts box)
    (first second : Fin genus) (target : InverseRootPolynomial.Coordinate) where
  /-- The retained bilinear clipping budget uses the actual triangle count and both original row slope bounds. -/ budget
    : Periods.ClippedBilinearBudget (mesh.triangles.map ModelTriangle.triangle).length
    (max (RectangularSeamBounds.boundarySlope (preflight.overlaps.get first)) (RectangularSeamBounds.boundarySlope
      (preflight.overlaps.get second))) target
  /-- The cached synchronized basis-model request at the budget's exact reading target. -/ models :
    EnergyPreflight.Request preflight budget.readingTarget

constructive_injectivity ClippedPairRequest

namespace ClippedPairRequest

variable {preflight : EnergyPreflight domain} {mesh
  : ObservationMesh domain.cuts box}
  {first second : Fin genus} {target : Coordinate}

/-- Pay the actual mesh face count and paired slope ceiling, then acquire the original basis requests at the resulting
reading target. -/
@[expose] def build (preflight : DomainBasisBounds.EnergyPreflight domain) (mesh :
  RectangularObservationMesh.ObservationMesh domain.cuts box)
    (first second : Fin genus) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedPairRequest preflight mesh first second target
      := by
  have nonnegative : 0 ≤ RectangularSeamBounds.boundarySlope (preflight.overlaps.get first) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (preflight.overlaps.get first).numeratorUpper_nonnegative
        (preflight.overlaps.get first).inverseUpper_positive.le)) face.cell.box.diagonalSq_nonneg
  let budget := ClippedBilinearBudget.build (mesh.triangles.map ModelTriangle.triangle).length
    (max (RectangularSeamBounds.boundarySlope (preflight.overlaps.get first)) (RectangularSeamBounds.boundarySlope
      (preflight.overlaps.get second)))
    target (nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)) positive
  exact ⟨budget, EnergyPreflight.Request.build preflight budget.readingTarget budget.readingTarget_positive⟩

/-- The actual shared pair boundary differs from the original clipped local primitive boundary by less than its paid
target. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedPairRequest preflight
  mesh first second target) {stage : Nat}
    (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length =>
          ⟨(readings.rows.get first).values vertex, (readings.rows.get second).values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨(cached first).primitives.value column row point,
          (cached second).primitives.value column row point⟩) mesh.depth) < target := by
  exact RectangularRequestedClippedBoundary.requested_shared_clipped_boundary
    (request.models.rowAtStage stage later first) (request.models.rowAtStage stage later second)
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
    domain.patch.cell_refines mesh request.budget le_rfl le_rfl
    (readings.rows.get first) (readings.rows.get second)

end ClippedPairRequest
set_option genInjectivity false in
/-- All basis pairs select scalar requests before the shared numerical bank. No row or primitive is sampled by this
finite index selection.

The retained basis realizations determine the cached request and its bounds. Both sides retain their original domain and
clipped source data. -/
structure ClippedBasisRequest (preflight : DomainBasisBounds.EnergyPreflight domain) (mesh :
  RectangularObservationMesh.ObservationMesh domain.cuts box)
    (target : InverseRootPolynomial.Coordinate) where
  /-- The complete retained matrix of clipped requests for every actual ordered basis pair. -/ pairs :
    Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector
    (fun second : Fin genus => ClippedPairRequest
      preflight mesh first second target))
  /-- The cached common sufficient model stage for all retained basis-pair requests. -/ index : Nat
  /-- Every retained pair's model request is bounded by the common stage. -/ index_ge : ∀ first second, ((pairs.get
    first).get second).models.index ≤ index

constructive_injectivity ClippedBasisRequest

namespace ClippedBasisRequest

variable {preflight : EnergyPreflight domain} {mesh
  : ObservationMesh domain.cuts box} {target :
  Coordinate}

/-- Cache every original ordered pair request and select their exact finite maximum model stage. -/
@[expose] def build (preflight : DomainBasisBounds.EnergyPreflight domain) (mesh :
  RectangularObservationMesh.ObservationMesh domain.cuts box)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest preflight mesh target :=
  let pairs := DependentVector.ofFn fun first : Fin genus =>
    DependentVector.ofFn fun second : Fin genus =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedPairRequest.build preflight mesh first
      second target positive
  let index := pairs.maximum (fun _ row => row.maximum (fun _ request => request.models.index))
  ⟨pairs, index, fun first second =>
    ((pairs.get first).get_le_maximum (fun _ request => request.models.index) second).trans
      (pairs.get_le_maximum (fun _ row => row.maximum (fun _ request => request.models.index)) first)⟩

/-- Every actual ordered basis pair satisfies the original clipped-boundary target on the same sufficiently refined
shared numerical bank. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest preflight
  mesh target) {stage : Nat}
    (later : request.index ≤ stage)
    (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row) stage)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (first second : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length =>
          ⟨(readings.rows.get first).values vertex, (readings.rows.get second).values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨(cached first).primitives.value column row point,
          (cached second).primitives.value column row point⟩) mesh.depth) < target :=
  ((request.pairs.get first).get second).accurate ((request.index_ge first second).trans later) cached readings

end ClippedBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest

end
