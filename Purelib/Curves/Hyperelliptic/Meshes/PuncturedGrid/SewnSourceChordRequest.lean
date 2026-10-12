module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Topology.Surface.Sewing.SewnSourceChordReadback
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The existing shared grid request pays actual source-chord transport,
retaining the sewn origin contribution of every oriented cut owner. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
open Purelib.Data.List
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources OrientedOwner)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation (Request)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings (sourceChord)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    FaceDomainBank frames faces.regulars}
  {i j : Fin genus}

namespace BilinearPreparation.Request
variable {polygon : SinglePolygon forest} {prepared :
  BilinearPreparation polygon domains i j}
  {target : Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- The actual cut-edge area minus its retained sewn-origin term approximates the original source chord.

The shared request pays both local primitive comparisons and uses the original triangle magnitude banks on the supplied
sewn samples. -/
theorem source_chord_accurate (request : BilinearPreparation.Request prepared target floor) {stage : Nat} (later :
  request.index ≤ stage)
    {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) (route :
      SewnPrimitiveFaces.OrientedOwner polygon.patch.cut) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (sample.values route.cutEdge.start) (sample.values
      route.cutEdge.finish) -
      Stokes.edgeArea (sample.values polygon.patch.cut.triangles[route.owner.position.val].first)
        ((sample.values route.cutEdge.finish).sub (sample.values route.cutEdge.start)) -
      TriangleReadings.sourceChord left right route.sourceEdge) ≤ request.budget.weight * request.budget.error := by
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
      PrimitivePoint.Bounded (⟨left.values source which - left.values source 0,
        right.values source which - right.values source 0⟩ : Stokes.PrimitivePoint)
          (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) := by
    constructor
    · have scalar := prepared.leftMagnitude.triangle_bounded
        ((Data.Nat.Order.le_max_right _ _).trans (request.left.floor_le.trans (request.left_le.trans later))) left
          source which
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans (le_add_of_nonneg_right prepared.rightMagnitude.nonnegative)
    · have scalar := prepared.rightMagnitude.triangle_bounded
        ((Data.Nat.Order.le_max_right _ _).trans (request.right.floor_le.trans (request.right_le.trans later))) right
          source which
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans (le_add_of_nonneg_left prepared.leftMagnitude.nonnegative)
  have small : request.budget.error ≤ 1 := by
    rw [request.budget.error_eq]
    exact Fraction.Order.Basic.min_le_left _ _
  rw [request.budget.weight_eq]
  exact SewnSourceChordReadback.owner_source_chord_error sample route
    (add_nonneg prepared.leftMagnitude.nonnegative prepared.rightMagnitude.nonnegative)
    request.budget.error_positive.le small
    (request.budget.trace_bound leftSurface leftAccuracy route.owner.position)
    (request.budget.trace_bound rightSurface rightAccuracy route.owner.position)
    (bounded route.sourceEdge.source)

/-- The actual path source cache supplies all occurrences, including repeats. Its raw edge area retains every
sewn-origin contribution. -/
theorem path_source_chord_accurate (request : BilinearPreparation.Request prepared target floor) {stage : Nat}
    (later : request.index ≤ stage) {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    {edges : List (Stokes.OrientedEdge polygon.patch.cut.count)} (sources : SewnPrimitiveFaces.PathSources
      polygon.patch.cut edges) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea sample.values edges -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.entries.map (fun route =>
        Stokes.edgeArea (sample.values polygon.patch.cut.triangles[route.owner.position.val].first)
          ((sample.values route.cutEdge.finish).sub (sample.values route.cutEdge.start)))) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.sources.map (TriangleReadings.sourceChord left right))) ≤
      (edges.length : SewnPrimitiveFaces.Coordinate) * ((edges.length : SewnPrimitiveFaces.Coordinate) *
        (request.budget.weight * request.budget.error)) := by
  let origin := fun route : SewnPrimitiveFaces.OrientedOwner polygon.patch.cut =>
    Stokes.edgeArea (sample.values polygon.patch.cut.triangles[route.owner.position.val].first)
      ((sample.values route.cutEdge.finish).sub (sample.values route.cutEdge.start))
  let error := fun route : SewnPrimitiveFaces.OrientedOwner polygon.patch.cut =>
    Stokes.edgeArea (sample.values route.cutEdge.start) (sample.values route.cutEdge.finish) -
      origin route - TriangleReadings.sourceChord left right route.sourceEdge
  have bounds : ∀ value ∈ sources.entries.map error, Data.Gaussian.Norm.Basic.normSq value ≤
    request.budget.weight * request.budget.error := by
    intro value member
    obtain ⟨route, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact
      source_chord_accurate
      request later left right sample route
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounds
  have count := congrArg List.length sources.edges_eq
  simp only [Data.List.Map.length_map, -eq_self, -iff_self] at count estimate
  rw [count] at estimate
  have balance : Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.entries.map error) =
      Stokes.edgeListArea sample.values edges - Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.entries.map
        origin) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.sources.map (TriangleReadings.sourceChord left right)) :=
          by
    rw [← congrArg (Stokes.edgeListArea sample.values) sources.edges_eq, sources.sources_eq, Data.List.Map.map_map]
    induction sources.entries with
    | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 - 0 - 0; ring1
    | cons route tail ih =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Stokes.edgeListArea, -eq_self, -iff_self]
      rw [ih]
      dsimp only [error, Function.comp_def, -eq_self, -iff_self]
      ring1
  rw [balance] at estimate
  exact estimate

/-- Raw paired values are exactly those cached by the annular samples. Both the edge areas and all owner-origin terms
use these same values. -/
theorem raw_path_source_chord_accurate (request : BilinearPreparation.Request prepared target floor) {stage : Nat}
    (later : request.index ≤ stage) {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    {edges : List (Stokes.OrientedEdge polygon.patch.cut.count)} (sources : SewnPrimitiveFaces.PathSources
      polygon.patch.cut edges) :
    let raw := fun vertex => (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea raw edges -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.entries.map (fun route =>
        Stokes.edgeArea (raw polygon.patch.cut.triangles[route.owner.position.val].first)
          ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.sources.map (TriangleReadings.sourceChord left right))) ≤
      (edges.length : SewnPrimitiveFaces.Coordinate) * ((edges.length : SewnPrimitiveFaces.Coordinate) *
        (request.budget.weight * request.budget.error)) := by
  intro raw
  have estimate :=
    path_source_chord_accurate
    request later left right sample sources
  rw [SewnSourceChordReadback.path_origin_area_eq_raw sample sources] at estimate
  exact estimate

end BilinearPreparation.Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest
