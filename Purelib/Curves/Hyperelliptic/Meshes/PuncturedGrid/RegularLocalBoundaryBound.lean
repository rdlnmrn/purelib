module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
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

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

open Purelib.Topology.Polygon

public section

/-! Actual local clipped boundaries inherit the shared mesh energy bound
and the independently paid ownership perturbation on the same bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination (combinedError combinedError_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest (ClippedRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)

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

/-- The actual shared-mesh boundary area of the retained two affine basis combinations. -/
@[expose] def sharedBoundary {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples :
  TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin faces.length) :
      Data.Gaussian.Basic.Canonical :=
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let readings := (samples.get sheet).readings.get position
  Stokes.edgeListArea (fun vertex : Fin mesh.surface.mesh.vertices.length =>
    ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩) mesh.surface.mesh.triangulation.boundary

/-- The actual owner-local boundary area on the same retained face position, sheet and depth. -/
@[expose] def localBoundary {stage : Nat} (cache : RegularMeshes.Numerics domains stage)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin faces.length) :
      Data.Gaussian.Basic.Canonical :=
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  mesh.pieces.localBoundary (fun column row point =>
    ⟨sumFin (fun i => left i * (cache.atDomain position sheet i).primitives.value column row point),
      FiniteSum.Fin.sumFin (fun j => right j * (cache.atDomain position sheet j).primitives.value column row point)⟩)
        mesh.depth

/-- The retained combined ownership error equals the actual shared boundary area minus its original local boundary area.
-/
theorem combinedError_eq_shared_sub_local {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples :
  TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin faces.length) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination.combinedError samples left right sheet
      position = sharedBoundary samples left
      right sheet position -
      localBoundary (energy := energy) cache
        left right sheet position := by
  unfold RegularClippedCombination.combinedError
    sharedBoundary
    localBoundary
  dsimp only
  apply congrArg (fun area : Data.Gaussian.Basic.Canonical => area - _)
  induction ((energy.entries.get sheet).meshes.entries.get position).surface.mesh.triangulation.boundary with
  | nil => rfl
  | cons edge edges ih =>
      rw [Stokes.edgeListArea, Stokes.edgeListArea]
      apply congrArg₂ (fun first rest : Data.Gaussian.Basic.Canonical => first + rest)
      · apply congrArg₂ Stokes.edgeArea
        · simp only [-eq_self, -iff_self, AffineBasis.value, BasisReadings.values_eq]
          rfl
        · simp only [-eq_self, -iff_self, AffineBasis.value, BasisReadings.values_eq]
          rfl
      · exact ih

/-- The complete original local boundary sum is the shared boundary sum minus the retained combined errors. -/
theorem total_localBoundary_eq {stage : Nat} {cache : RegularMeshes.Numerics domains stage} (samples :
  TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
      localBoundary (energy := energy) cache left
      right sheet position)) =
      FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
        sharedBoundary samples left right sheet
        position)) -
        FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
          RegularClippedCombination.combinedError samples left right sheet position)) := by
  have equal := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 =>
    FiniteSum.Fin.sumFin_congr (fun position : Fin faces.length =>
      combinedError_eq_shared_sub_local samples left
        right sheet position))
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_sub] at equal
  rw [equal]
  ring1

/-- The original local clipped boundary sum satisfies the shared energy estimate plus the independently paid ownership
perturbation.

Both use the same retained numerical bank and actual coefficient vectors at the paid common stage. -/
theorem localBoundary_bound (request : RegularClippedRequest.ClippedRequest energy target) {stage : Nat} {cache :
  RegularMeshes.Numerics domains stage}
    (later : request.index ≤ stage) (samples : TwoSheetRequest.Samples energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun
      position : Fin faces.length =>
      localBoundary (energy := energy) cache left
        right sheet position))) ≤
      PreparedObservationCoercivity.coefficientNormSq left * PreparedObservationCoercivity.coefficientNormSq right *
        (128 * energyTarget ^ 2 + 2 * (genus : Fraction.Rational) ^ 2 * target) := by
  have shared := TwoSheetRequest.bilinear_bound
    energy (request.energy_le.trans later) samples left right
  have error := RegularClippedCombination.combinedError_bound request later samples left right
  rw [total_localBoundary_eq samples left right]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add shared error) (by decide)).trans_eq (by
      ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound
