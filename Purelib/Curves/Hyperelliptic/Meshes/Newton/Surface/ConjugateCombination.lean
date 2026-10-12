module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
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
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Homogeneous ownership error for complete regular-surface energy

Expand the actual energy sample into all conjugated basis pairs, then pay
all piece and face errors with one coefficient-independent request. The
local side sum retains its model owners, spatial cuts and common depth.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

attribute [local congr] FiniteSum.Fin.sumFin_congr

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
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget error :
    Fraction.Rational}
  {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {stage : Nat}
    {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

/-- The actual coefficient-combined energy boundary minus the retained local-owner side sum for one original surface
piece. -/
@[expose] def combinedError (samples : energy.Readings cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) : Gaussian :=
  let mesh := (energy.meshes.get position).entries.get piece
  let readings := (samples.get position).readings.get piece
  Topology.Polygon.Stokes.edgeListArea (fun vertex : Fin mesh.surface.mesh.vertices.length =>
    Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun row => coefficients row * (readings.rows.get
      row).values vertex)))
    mesh.surface.mesh.triangulation.boundary -
  mesh.pieces.localBoundary (fun column row point => Energy.Polygon.energyPrimitivePoint
    (FiniteSum.Fin.sumFin (fun rowIndex => coefficients rowIndex * (cache.atDomain position sheet
      rowIndex).primitives.value column row point))) mesh.depth

/-- The original piece discrepancy equals its complete conjugated basis-pair expansion. -/
theorem combinedError_eq (samples : energy.Readings cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        ConjugateRequest.pairError samples first second position
          piece)) := by
  unfold Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError
  dsimp only
  rw [Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes.edgeListArea_energy_combination,
    Polynomial.Rectangle.ClippedEnergyCombination.ObservationPieces.localBoundary_energy_combination]
  simp only [ConjugateRequest.pairError, mul_sub,
    FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rfl

/-- The complete original face-piece discrepancy sum equals the basis-pair combination of the retained paired errors. -/
theorem total_combinedError_eq (samples : energy.Readings cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece)) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
          ConjugateRequest.pairError samples first second position
          piece)))) := by
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece =>
    Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError_eq samples coefficients position piece))]
  rw [FiniteSum.Fin.sumFin_congr (fun position => Periods.BilinearCombination.sumFin_combination
    (fun row => Data.Gaussian.Basic.conj (coefficients row)) coefficients (fun piece first second =>
      ConjugateRequest.pairError samples first second position
      piece))]
  exact Periods.BilinearCombination.sumFin_combination (fun row => Data.Gaussian.Basic.conj (coefficients row))
    coefficients _

/-- The original complete combined discrepancy has squared norm at most genus squared times coefficient norm squared
times the retained request error. -/
theorem combinedError_bound (request : ConjugateRequest energy
  error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece))) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        error := by
  rw [Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.total_combinedError_eq]
  have estimate := Periods.BilinearCombination.combination_bound (fun row => Data.Gaussian.Basic.conj (coefficients
    row)) coefficients
    (fun first second => FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      ConjugateRequest.pairError samples first second position
      piece)))
    (fun first second => (ConjugateRequest.total_pairError_bound
      request later samples first second).le)
  rw [FiniteSum.Fin.sumFin_congr (fun row => Gaussian.Norm.Basic.normSq_conj (coefficients row))] at estimate
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [coefficientNorm] at estimate
  exact estimate.trans_eq (by unfold Readings.PreparedObservationCoercivity.coefficientNormSq; ring1)

/-- Pointwise equal primitive values give equal original finite boundary edge-list areas. -/
private theorem edgeListArea_pointwise {vertices : Nat}
    (first last : Fin vertices → Topology.Polygon.Stokes.PrimitivePoint) (equal : ∀ vertex, first vertex = last vertex)
    (word : List (Topology.Polygon.Stokes.OrientedEdge vertices)) :
    Topology.Polygon.Stokes.edgeListArea first word = Topology.Polygon.Stokes.edgeListArea last word := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Topology.Polygon.Stokes.edgeArea (first edge.start) (first edge.finish) + _ = _
      rw [equal, equal, ih]
      rfl

/-- The coefficient expansion reads the actual cached energy sample, not a
separately integrated linear combination or a replacement mesh. -/
theorem sample_error_eq (samples : energy.Readings cache) (budget :
  Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest.Budget energy samples)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (position : Fin
      grid.faces.regulars.length)
    (piece : Fin (partitions.get position).cuts.boxes.length) :
    (((budget.entries.get position).get piece).sample coefficients).boundaryArea -
      ((energy.meshes.get position).entries.get piece).pieces.localBoundary
        (fun column row point => Energy.Polygon.energyPrimitivePoint
          (FiniteSum.Fin.sumFin (fun rowIndex => coefficients rowIndex * (cache.atDomain position sheet
            rowIndex).primitives.value column row point)))
        ((energy.meshes.get position).entries.get piece).depth =
          Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece :=
          by
  apply congrArg (fun boundary => boundary - _)
  change Topology.Polygon.Stokes.edgeListArea
    (fun vertex => Energy.Polygon.energyPrimitivePoint ((((budget.entries.get position).get piece).sample
      coefficients).primitiveValue vertex))
    ((energy.meshes.get position).entries.get piece).surface.mesh.triangulation.boundary = _
  apply Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.edgeListArea_pointwise
  intro vertex
  apply congrArg Energy.Polygon.energyPrimitivePoint
  rw [Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget.sample_value]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [((samples.get position).readings.get piece).values_eq]

/-- The actual retained energy-sample boundaries satisfy the coefficient-homogeneous comparison bound against their
original local side sums. -/
theorem boundary_error_bound (request : ConjugateRequest energy
  error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (budget : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest.Budget energy
      samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      (((budget.entries.get position).get piece).sample coefficients).boundaryArea -
        ((energy.meshes.get position).entries.get piece).pieces.localBoundary
          (fun column row point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun rowIndex =>
            coefficients rowIndex * (cache.atDomain position sheet rowIndex).primitives.value column row point)))
          ((energy.meshes.get position).entries.get piece).depth))) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        error := by
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece =>
    Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.sample_error_eq samples budget coefficients position
    piece))]
  exact Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError_bound request later samples coefficients

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination
