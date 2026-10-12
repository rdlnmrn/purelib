module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowSelectedRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandHolePolygonRequest
import Batteries.Logic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

public section

open Purelib.Data

/-! The selected fine annular area cancels the positive physical-hole
polygons, with all errors paid by the actual outer Newton-band budget. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandTriangleHoleRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (mix extract)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation.AreaRequest
  (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapAreaRequest (lapAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowSelectedRequest (selectedTriangleRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.BandHolePolygonRequest (holePolygonRequest)
open Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits (fineCompiler)
open Purelib.Riemann.RootContinuation.NewtonBandWindowHole (fineHole)
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization (extract_wordArea_mix)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {request : AreaRequest preparation
    target radius}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
    AnnularFaces request.grid index}
  {lifted : LiftedPuncturedGrid request.grid.punctured} {region :
    Lifted annulus lifted}
  {prepared : OuterPreparation region}
  {domains : FaceDomainBank lifted.frames
    request.grid.faces.regulars} {i j : Fin genus}

/-- Choose a common stage bounding the selected Newton-band triangles plus both physical-hole polygons.

The original outer-lap, selected-triangle and hole-polygon requests share the supplied magnitude banks and pay the bound
of forty times the outer target. -/
@[expose] def triangleHoleRequest (comparison : AreaRequest.PairedComparison request prepared i j domains)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j)) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh),
        threshold ≤ stage →
        let value := fun edge => (⟨edgeValuation lifted.mesh left.values edge,
          CanonicalEdgeValues.edgeValuation lifted.mesh right.values edge⟩ : Stokes.PrimitivePoint)
        let physical := fun sheet => PairedIncrementArea.area
          ((lifted.edges.indexedEdges lifted.vertices (NewtonBandWindowHole.fineHole annulus (current :=
            lifted)).hole.boundary sheet).map value)
        Data.Gaussian.Norm.Basic.normSq (SelectedTrianglePartition.selectedFullTriangleArea left right (fun
          position =>
          decide ((request.grid.faces.regulars[position.val]'position.isLt).cell.box.Refines
            (request.grid.bands.box index))) + (physical 0 + physical 1)) ≤ 40 * target } := by
  let outer := LapAreaRequest.lapAreaRequest comparison first second floor
  let triangles := BandWindowSelectedRequest.selectedTriangleRequest annulus first second target request.budget.positive
    floor
  let hole := BandHolePolygonRequest.holePolygonRequest annulus first second target request.budget.positive floor
  refine ⟨max outer.val (max triangles.val hole.val), outer.property.1.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right later value physical
  have outerBound := outer.property.2 stage cache left right ((Nat.Order.le_max_left _ _).trans later)
  have triangleBound := triangles.property.2 stage cache left right
    ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans later))
  have holeBound := hole.property.2 stage cache left right
    ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans later))
  let lap := fun sheet => PairedIncrementArea.area
    ((lifted.edges.indexedEdges lifted.vertices annulus.boundary sheet).map value)
  let kept := fun sheet => PairedIncrementArea.area
    ((NewtonBandWindowCircuits.fineCompiler annulus (current := lifted) sheet).word.map value)
  let selected := SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
    decide ((request.grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (request.grid.bands.box index)))
  have readback (sheet : Fin 2) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient => lifted.edges.chainArea lifted.vertices
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation lifted.mesh left.values)
          (CanonicalEdgeValues.edgeValuation lifted.mesh right.values) coefficient)
        annulus.boundary sheet - RetracingWords.wordArea
          (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation lifted.mesh left.values)
            (CanonicalEdgeValues.edgeValuation lifted.mesh right.values) coefficient)
          (NewtonBandWindowCircuits.fineCompiler annulus (current := lifted) sheet).word) = lap sheet - kept sheet := by
    have distribute (a b : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
          coefficient => a coefficient - b coefficient) =
          Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract a -
          Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract b := by
      unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
      ring1
    exact (distribute _ _).trans (congrArg₂ (· - ·)
      (BilinearPolarization.extract_wordArea_mix _ _ _) (BilinearPolarization.extract_wordArea_mix _ _ _))
  dsimp only at triangleBound
  rw [readback 0, readback 1] at triangleBound
  change Data.Gaussian.Norm.Basic.normSq ((lap 0 - kept 0) + (lap 1 - kept 1) - selected) < target at triangleBound
  change Data.Gaussian.Norm.Basic.normSq ((kept 0 + kept 1) - (physical 0 + physical 1)) ≤ target at holeBound
  change Data.Gaussian.Norm.Basic.normSq (lap 0 + lap 1) ≤ 16 * target at outerBound
  have defects := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
      ((lap 0 - kept 0) + (lap 1 - kept 1) - selected)
      ((kept 0 + kept 1) - (physical 0 + physical 1))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      triangleBound.le holeBound) (by decide))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (lap 0 + lap 1)
      (((lap 0 - kept 0) + (lap 1 - kept 1) - selected) +
        ((kept 0 + kept 1) - (physical 0 + physical 1)))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct outerBound
      defects) (by decide))
  rw [show (lap 0 + lap 1) - (((lap 0 - kept 0) + (lap 1 - kept 1) - selected) +
      ((kept 0 + kept 1) - (physical 0 + physical 1))) = selected + (physical 0 + physical 1) by ring1] at estimate
  exact estimate.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandTriangleHoleRequest
