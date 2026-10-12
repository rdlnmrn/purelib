module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Topology.NewtonObservationSurfaceBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateClippedRequest
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Conjugate boundary requests on every regular-surface piece

The complete retained geometry and common spatial depth are unchanged.
Nested finite error allowances pay for every face and every piece, and one
later numerical index satisfies the energy and all ownership comparisons.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open _root_.Purelib.Data.Gaussian.Basic (conj)

open Purelib.Data.Nat

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars} {sheet : Fin
    2}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Fraction.Rational}

namespace ConjugateRequest

/-- Dependent clipped conjugate-basis requests for every original piece of one retained surface face. -/
@[expose] def ConjugatePieces (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget)
    (perFace : Fraction.Rational) (position : Fin grid.faces.regulars.length) :=
  Data.Vector.DependentVector (fun piece : Fin (partitions.get position).cuts.boxes.length =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest (fixed.get position).get
      ((energy.meshes.get position).entries.get piece)
      (Rational.Budget.Aggregate.perTerm perFace (partitions.get position).cuts.boxes.length))

end ConjugateRequest

set_option genInjectivity false in
/-- A shared-stage conjugate-boundary request over every retained face and piece.

Nested finite budgets pay for both counts while retaining the original energy request and all local owners. -/
structure ConjugateRequest (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget) (error : Fraction.Rational) where
  /-- The requested total squared-norm error is strictly positive. -/ positive : 0 < error
  /-- The retained count-paid error allowance for each original regular face. -/ perFace : Fraction.Rational
  /-- The per-face allowance is exactly the original request divided by its finite aggregate payment. -/ perFace_eq :
    perFace = Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length
  /-- The original dependent bank of clipped requests for every retained face and piece. -/ entries :
    Data.Vector.DependentVector (Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest.ConjugatePieces energy perFace)
  /-- The shared sufficient stage for energy and all retained piece comparisons. -/ index : Nat
  /-- The shared stage is at least the original energy-request stage. -/ energy_le : energy.index ≤ index
  /-- Every original retained piece request is ready by the shared stage. -/ index_ge : ∀ position piece, ((entries.get
    position).get piece).index ≤ index

constructive_injectivity ConjugateRequest

namespace ConjugateRequest

variable {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {error :
  Fraction.Rational}

/-- Prepare all original piece comparisons and take one stage satisfying both the retained energy request and every
local request. -/
@[expose] def build (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget)
  (error : Fraction.Rational) (positive : 0 < error) :
    ConjugateRequest energy error :=
  let perFace := Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length
  let entries : Data.Vector.DependentVector (Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest.ConjugatePieces energy
    perFace) :=
    Data.Vector.DependentVector.ofFn fun position => Data.Vector.DependentVector.ofFn fun piece =>
      Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest.ClippedBasisRequest.build (fixed.get position).get
        ((energy.meshes.get position).entries.get piece)
        (Rational.Budget.Aggregate.perTerm perFace (partitions.get position).cuts.boxes.length)
        (Rational.Budget.Aggregate.perTerm_positive
          (Rational.Budget.Aggregate.perTerm_positive positive _) _)
  let floor := entries.maximum fun _ row => row.maximum fun _ request => request.index
  ⟨positive, perFace, rfl, entries, max energy.index floor, Order.le_max_left _ _, fun position piece =>
    (((entries.get position).get_le_maximum (fun _ request => request.index) piece).trans
      (entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) position)).trans
        (Order.le_max_right _ _)⟩

variable {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

/-- The shared conjugate/value area minus the same clipped sides evaluated
in their retained local owners. No seams between domains are removed. -/
@[expose] def pairError (samples : energy.Readings cache) (first second : Fin genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) : Gaussian :=
  let mesh := (energy.meshes.get position).entries.get piece
  let readings := (samples.get position).readings.get piece
  Topology.Polygon.Stokes.edgeListArea (fun vertex : Fin mesh.surface.mesh.vertices.length =>
    ⟨conj ((readings.rows.get first).values vertex), (readings.rows.get second).values vertex⟩)
    mesh.surface.mesh.triangulation.boundary -
  mesh.pieces.localBoundary (fun column row point =>
    ⟨conj ((cache.atDomain position sheet first).primitives.value column row point),
      (cache.atDomain position sheet second).primitives.value column row point⟩) mesh.depth

/-- Each original piece's conjugate-boundary discrepancy satisfies its retained nested comparison budget. -/
theorem pairError_bound (request : ConjugateRequest energy error)
  (later : request.index ≤ stage)
    (samples : energy.Readings cache) (first second : Fin genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    Data.Gaussian.Norm.Basic.normSq (pairError
      samples first second position piece) <
      Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length :=
  Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateClippedRequest.ClippedBasisRequest.conjugate_accurate
    ((request.entries.get position).get piece) ((request.index_ge position piece).trans later)
    (cache.atDomain position sheet) ((samples.get position).readings.get piece) first second

/-- The complete double finite sum of original face-piece discrepancies has squared norm below the requested error. -/
theorem total_pairError_bound (request : ConjugateRequest energy
  error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (first second : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      pairError samples first second position
      piece))) < error := by
  have perFacePositive : 0 < request.perFace := by
    rw [request.perFace_eq]
    exact Rational.Budget.Aggregate.perTerm_positive request.positive _
  have faceBound (position : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun piece =>
        pairError samples first second position
        piece)) ≤ request.perFace := by
    have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _
      (Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length)
      (fun piece => (pairError_bound request later
        samples first second position piece).le)
    have payment := Rational.Budget.Aggregate.count_mul_perTerm_lt perFacePositive (partitions.get
      position).cuts.boxes.length
    have equal : ((partitions.get position).cuts.boxes.length : Fraction.Rational) ^ 2 *
        Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length =
        ((partitions.get position).cuts.boxes.length : Fraction.Rational) *
          (((partitions.get position).cuts.boxes.length : Fraction.Rational) *
            Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length) := by ring1
    exact (estimate.trans_lt (equal.trans_lt payment)).le
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ request.perFace faceBound
  have payment := Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive grid.faces.regulars.length
  have equal : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace =
      (grid.faces.regulars.length : Fraction.Rational) * ((grid.faces.regulars.length : Fraction.Rational) *
        Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length) := by rw [request.perFace_eq]; ring1
  exact estimate.trans_lt (equal.trans_lt payment)

end ConjugateRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
