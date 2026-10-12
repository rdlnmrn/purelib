module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Riemann.RootContinuation.NewtonBandWindowHole
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ConjugateLapAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowSelectedRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateHolePolygonRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! The selected fine annular area cancels the positive physical-hole
polygons, with all errors paid by the actual outer Newton-band budget. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateTriangleHoleRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation target radius}
  {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
    Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index}
  {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured} {region :
    Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
  {prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.grid.faces.regulars} {i j : Fin genus}

/-- Prepare a common threshold bounding the selected conjugate annular triangles plus both positive physical-hole
polygons.

The retained outer-lap, selected-triangle and hole-polygon requests share the original magnitude banks and pay the
fortyfold outer target on every later cache. -/
@[expose] def conjugateTriangleHoleRequest (comparison :
  Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation.AreaRequest.PairedComparison request prepared
  i j domains)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j)) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
        (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
          (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j)
          lifted.mesh),
        threshold ≤ stage →
        let value := fun edge => (⟨Data.Gaussian.Basic.conj
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh left.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh right.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint)
        let physical := fun sheet => Path.PairedIncrementArea.area
          ((lifted.edges.indexedEdges lifted.vertices (RootContinuation.NewtonBandWindowHole.fineHole (current :=
            lifted) annulus).hole.boundary sheet).map value)
        Data.Gaussian.Norm.Basic.normSq
          (Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
          position =>
          decide ((request.grid.faces.regulars[position.val]'position.isLt).cell.box.Refines
            (request.grid.bands.box index))) + (physical 0 + physical 1)) ≤ 40 * target } := by
  let outer := Hyperelliptic.Meshes.Newton.Annulus.ConjugateLapAreaRequest.conjugateLapAreaRequest comparison first
    second floor
  let triangles := Hyperelliptic.Meshes.Newton.BandConjugateWindowSelectedRequest.selectedConjugateTriangleRequest
    annulus first second target request.budget.positive floor
  let hole := Hyperelliptic.Meshes.Newton.BandConjugateHolePolygonRequest.conjugateHolePolygonRequest annulus first
    second target request.budget.positive floor
  refine ⟨max outer.val (max triangles.val hole.val), outer.property.1.trans (Data.Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right later value physical
  have outerBound := outer.property.2 stage cache left right ((Data.Nat.Order.le_max_left _ _).trans later)
  have triangleBound := triangles.property.2 stage cache left right
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later))
  have holeBound := hole.property.2 stage cache left right
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later))
  let lap := fun sheet => Path.PairedIncrementArea.area
    ((lifted.edges.indexedEdges lifted.vertices annulus.boundary sheet).map value)
  let kept := fun sheet => Path.PairedIncrementArea.area
    ((RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := lifted) annulus sheet).word.map value)
  let selected := Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right
    (fun position =>
    decide ((request.grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (request.grid.bands.box index)))
  have readback (sheet : Fin 2) :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        lifted.edges.chainArea lifted.vertices
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          left.values edge)) (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          right.values) coefficient)
        annulus.boundary sheet - Topology.Mesh.RetracingWords.wordArea
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
            Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            lifted.mesh left.values edge)) (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            lifted.mesh right.values) coefficient)
          (RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := lifted) annulus sheet).word) = lap sheet -
            kept sheet := by
    have distribute (a b : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) :
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient => a
          coefficient - b coefficient) =
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract a -
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract b := by
      unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
      ring1
    exact (distribute _ _).trans (congrArg₂ (· - ·)
      (Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix _ _ _)
        (Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix _ _ _))
  dsimp only at triangleBound
  rw [readback 0, readback 1] at triangleBound
  change Data.Gaussian.Norm.Basic.normSq ((lap 0 - kept 0) + (lap 1 - kept 1) - selected) < target at triangleBound
  change Data.Gaussian.Norm.Basic.normSq ((kept 0 + kept 1) - (physical 0 + physical 1)) ≤ target at holeBound
  change Data.Gaussian.Norm.Basic.normSq (lap 0 + lap 1) ≤ 16 * target at outerBound
  have defects := (Gaussian.Norm.Bounds.normSq_add_le_two
      ((lap 0 - kept 0) + (lap 1 - kept 1) - selected)
      ((kept 0 + kept 1) - (physical 0 + physical 1))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      triangleBound.le holeBound) (by decide))
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two (lap 0 + lap 1)
      (((lap 0 - kept 0) + (lap 1 - kept 1) - selected) +
        ((kept 0 + kept 1) - (physical 0 + physical 1)))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct outerBound
      defects) (by decide))
  rw [show (lap 0 + lap 1) - (((lap 0 - kept 0) + (lap 1 - kept 1) - selected) +
      ((kept 0 + kept 1) - (physical 0 + physical 1))) = selected + (physical 0 + physical 1) by ring1] at estimate
  exact estimate.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateTriangleHoleRequest
