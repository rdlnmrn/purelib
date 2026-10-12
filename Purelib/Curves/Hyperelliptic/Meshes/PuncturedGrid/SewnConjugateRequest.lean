module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.Bilinear.Coverage
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Topology.Surface.Sewing.SewnConjugateRequests
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewnConjugateSamples

public section

/-! The retained grid sewing request controls conjugate energy pairs on
all actual lifted triangles, at every later common numerical stage. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (sourceContacts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh
    vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {i j : Fin genus} {polygon : Topology.Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest}
  {prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation polygon domains i j}
    {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- All contact and magnitude premises are discharged at the shared later stage. Coverage reads every actual mesh
triangle exactly once. -/
theorem conjugate_accurate (request : BilinearPreparation.Request prepared target floor) {stage : Nat} (later :
  request.index ≤ stage)
    {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun source =>
      Stokes.triangleWedgeArea
      ⟨conj (left.values source 0), right.values source 0⟩
      ⟨conj (left.values source 1), right.values source 1⟩
      ⟨conj (left.values source 2), right.values source 2⟩)) < target := by
  have coverage : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts polygon.patch.assembly, contact ∈
    prepared.contacts.entries := by
    intro contact member
    rw [prepared.contacts.entries_eq]
    exact member
  have leftAccuracy := request.left.localAccuracy_of_coverage coverage le_rfl
    (request.left_le.trans later) left leftSurface.sewn.readings
  have rightAccuracy := request.right.localAccuracy_of_coverage coverage le_rfl
    (request.right_le.trans later) right rightSurface.sewn.readings
  have bounded (source : Fin mesh.triangles.length) (which : Fin 3) :
      PrimitivePoint.Bounded
        (⟨conj (left.values source which) - Data.Gaussian.Basic.conj (left.values source 0),
          right.values source which - right.values source 0⟩ : Stokes.PrimitivePoint)
        (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) := by
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (Data.Gaussian.Basic.conj (left.values source which) -
        Data.Gaussian.Basic.conj (left.values source 0)) ≤ _
      rw [← ConjugatePair.conj_sub, ← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
        Data.Gaussian.Norm.Basic.normSq_conj]
      exact (prepared.leftMagnitude.triangle_bounded
        ((Data.Nat.Order.le_max_right _ _).trans (request.left.floor_le.trans (request.left_le.trans later))) left
          source which).trans
        (le_add_of_nonneg_right prepared.rightMagnitude.nonnegative)
    · have scalar := (prepared.rightMagnitude.triangle_bounded
        ((Data.Nat.Order.le_max_right _ _).trans (request.right.floor_le.trans (request.right_le.trans later))) right
          source which).trans
        (le_add_of_nonneg_left prepared.leftMagnitude.nonnegative)
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar
  have estimate := SewnConjugateRequests.accurate request.budget sample leftAccuracy rightAccuracy
    (fun position => bounded (Errors.traceAt leftSurface position).source)
  have sourceSum := Coverage.source_sum polygon leftSurface (fun source => Stokes.triangleWedgeArea
    ⟨conj (left.values source 0), right.values source 0⟩
    ⟨conj (left.values source 1), right.values source 1⟩
    ⟨conj (left.values source 2), right.values source 2⟩)
  rw [sourceSum] at estimate
  exact estimate

/-- The actual retained sewn energy area agrees with the complete original local conjugate-triangle sum within the paid
target. -/
theorem diagonal_energy_accurate
    {prepared : SewnBilinearRequest.BilinearPreparation polygon domains i i} (request : BilinearPreparation.Request
      prepared target floor)
    {stage : Nat} (later : request.index ≤ stage) {cache : RegularMeshes.Numerics domains stage}
    (readings : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (surface :
      SewnPrimitiveSamples.CachedSample polygon.patch readings.values) :
    Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - FiniteSum.Fin.sumFin (fun source =>
      Stokes.triangleWedgeArea
      ⟨conj (readings.values source 0), readings.values source 0⟩
      ⟨conj (readings.values source 1), readings.values source 1⟩
      ⟨conj (readings.values source 2), readings.values source 2⟩)) < target := by
  let paired := ConjugatePair.build surface surface
  have estimate := request.conjugate_accurate later readings readings paired
  rw [paired.diagonal_boundary] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request
