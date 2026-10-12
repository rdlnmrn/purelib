module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Integration.Polynomial.Rectangle.ClippedBoundaryCombination
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
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
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Meshes.RectangularObservationMesh
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon

/-! Homogeneous coefficient bound on the actual all-face ownership errors. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest (ClippedRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest (pairError pairError_bound
  total_pairError_bound)
open Purelib.Riemann.Periods.BilinearCombination (edgeListArea_combination)
open Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces (localBoundary_combination)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (RegularFace bank)} {domains :
    FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {energyTarget target : Rational}
  {energy : TwoSheetRequest coarse fixed
    energyTarget}

/-- The actual face ownership discrepancy for two supplied coefficient combinations on the retained common mesh. -/
@[expose] def combinedError {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples :
  TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin faces.length) :
      Data.Gaussian.Basic.Canonical :=
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let readings := (samples.get sheet).readings.get position
  Stokes.edgeListArea
    (fun vertex : Fin mesh.surface.mesh.vertices.length =>
      ⟨sumFin (fun row => left row * (readings.rows.get row).values vertex),
        FiniteSum.Fin.sumFin (fun row => right row * (readings.rows.get row).values vertex)⟩)
    mesh.surface.mesh.triangulation.boundary -
  mesh.pieces.localBoundary (fun column row point =>
    ⟨sumFin (fun i => left i * (cache.atDomain position sheet i).primitives.value column row point),
      FiniteSum.Fin.sumFin (fun j => right j * (cache.atDomain position sheet j).primitives.value column row point)⟩)
        mesh.depth

/-- The actual combined ownership discrepancy equals the finite coefficient-weighted sum of original basis-pair
discrepancies. -/
theorem combinedError_eq {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples : TwoSheetRequest.Samples
  energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin faces.length) :
    combinedError samples left right sheet
      position =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => left first * right second *
        ClippedRequest.pairError samples first second sheet position)) := by
  unfold combinedError
  dsimp only
  rw [BilinearCombination.edgeListArea_combination, ObservationPieces.localBoundary_combination]
  simp only [ClippedRequest.pairError, mul_sub, FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rfl

/-- Summing actual ownership discrepancies over both sheets and all faces preserves their exact original coefficient
combination. -/
theorem total_combinedError_eq {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples :
  TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
      combinedError samples left right sheet
      position)) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => left first * right second *
        FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
          ClippedRequest.pairError samples first second sheet position)))) := by
  have perFace := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 =>
    FiniteSum.Fin.sumFin_congr (fun position : Fin faces.length =>
      combinedError_eq samples left right sheet
      position))
  rw [perFace]
  have perSheet := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 =>
    BilinearCombination.sumFin_combination left right (fun position first second => ClippedRequest.pairError samples
      first second sheet position))
  rw [perSheet]
  exact BilinearCombination.sumFin_combination left right _

/-- The actual complete basis-pair discrepancy combination satisfies the original genus and coefficient-norm bound. -/
theorem weighted_pairError_bound (request : RegularClippedRequest.ClippedRequest energy target) {stage : Nat} {cache :
  RegularMeshes.Numerics domains stage}
    (later : request.index ≤ stage) (samples : TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun first : Fin genus => FiniteSum.Fin.sumFin (fun
      second : Fin genus => left first * right second *
      FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
        ClippedRequest.pairError samples first second sheet position))))) ≤
      (genus : Fraction.Rational) ^ 2 * Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq right * target := by
  have estimate := BilinearCombination.combination_bound left right
    (fun first second => FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin
      faces.length =>
      ClippedRequest.pairError samples first second sheet position)))
    (fun first second => (request.total_pairError_bound later samples first second).le)
  have leftNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (left row))
  have rightNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (right row))
  rw [leftNorm, rightNorm] at estimate
  exact estimate.trans_eq (by
    unfold PreparedObservationCoercivity.coefficientNormSq
    ring1)

/-- The full actual two-sheet ownership discrepancy of the supplied coefficient combinations satisfies the retained
homogeneous target bound. -/
theorem combinedError_bound (request : RegularClippedRequest.ClippedRequest energy target) {stage : Nat} {cache :
  RegularMeshes.Numerics domains stage}
    (later : request.index ≤ stage) (samples : TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun
      position : Fin faces.length => combinedError
      samples left right sheet position))) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq left *
        PreparedObservationCoercivity.coefficientNormSq right * target := by
  rw [total_combinedError_eq]
  exact weighted_pairError_bound request later
    samples left right

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination
