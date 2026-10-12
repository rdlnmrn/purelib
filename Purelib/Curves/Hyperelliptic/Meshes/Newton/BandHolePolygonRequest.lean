module
public import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Nat.Order
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Riemann.RootContinuation.NewtonBandWindowHole
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleStemRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleStemRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

public section

open Purelib.Data

/-! Remove the actual compiler stem from both retained fine-hole polygons.
The positive boundary polygons of the shrunken physical hole remain. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandHolePolygonRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (mix mix_reverse
  extract extract_congr)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.RootContinuation.NewtonBandWindowHole (fineHole fineCompiler_hole_area)
open Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits (fineCompiler)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}

/-- The threshold pays the two actual stem defects. Its conclusion retains the complete positive physical-hole polygons,
not just endpoint chords. -/
@[expose] def holePolygonRequest (region : Faces.AnnularFaces grid index)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh),
        threshold ≤ stage →
        let value := fun edge => (⟨edgeValuation current.mesh left.values edge,
          CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
        let retained := fun sheet => PairedIncrementArea.area
          (((NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).word).map value)
        let physical := fun sheet => PairedIncrementArea.area
          ((current.edges.indexedEdges current.vertices (NewtonBandWindowHole.fineHole (current := current)
            region).hole.boundary sheet).map value)
        Data.Gaussian.Norm.Basic.normSq ((retained 0 + retained 1) - (physical 0 + physical 1)) ≤ error } := by
  let found := NewtonBandWindowHole.fineHole (current := current) region
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let zero := PairedStemRequest.build found.hole found.stem first second 0 (error / 4) partPositive
  let one := PairedStemRequest.build found.hole found.stem first second 1 (error / 4) partPositive
  let threshold := max floor (max zero.index one.index)
  refine ⟨threshold, Nat.Order.le_max_left _ _, ?_⟩
  intro stage cache left right later value retained physical
  let member := LiftedBoundary.anchor_onGrid region
  let loop := fun sheet => PairedIncrementArea.area
    ((current.edges.indexedEdges current.vertices (found.stem.based found.hole.boundary) sheet).map value)
  have readback (sheet : Fin 2) : retained sheet = loop sheet := by
    have equal := BilinearPolarization.extract_congr (fun coefficient => NewtonBandWindowHole.fineCompiler_hole_area
      region sheet
      (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
      (BilinearPolarization.mix_reverse _ _ (CanonicalEdgeValues.edgeValuation_reverse current.mesh left.values)
        (CanonicalEdgeValues.edgeValuation_reverse current.mesh right.values) coefficient))
    change BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
      (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
      (NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).word) =
      BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh left.values)
          (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
        (current.edges.indexedEdges current.vertices (found.stem.based found.hole.boundary) sheet)) at equal
    rw [BilinearPolarization.extract_wordArea_mix, BilinearPolarization.extract_wordArea_mix] at equal
    exact equal
  have zeroBound := zero.accurate member left right ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _
    _).trans later))
  have oneBound := one.accurate member left right ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _
    _).trans later))
  change Data.Gaussian.Norm.Basic.normSq (loop 0 - physical (RootEdgeBank.target current.edges found.stem 0)) ≤
    error / 4 at zeroBound
  change Data.Gaussian.Norm.Basic.normSq (loop 1 - physical (RootEdgeBank.target current.edges found.stem 1)) ≤
    error / 4 at oneBound
  have distinct : RootEdgeBank.target current.edges found.stem 0 ≠ RootEdgeBank.target current.edges found.stem 1 := by
    intro equal
    have same := current.edges.target_injective
      (fun point present => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point present).toLoop)
        found.stem equal
    exact (by decide : (0 : Fin 2) ≠ 1) same
  have allSheets := Algebra.FiniteSum.Gaussian.two_sheets physical _ _ distinct
  rw [readback 0, readback 1, ← allSheets]
  rw [show (loop 0 + loop 1) -
      (physical (RootEdgeBank.target current.edges found.stem 0) + physical (RootEdgeBank.target current.edges
        found.stem 1)) =
      (loop 0 - physical (RootEdgeBank.target current.edges found.stem 0)) +
      (loop 1 - physical (RootEdgeBank.target current.edges found.stem 1)) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct zeroBound
      oneBound) (by decide)).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandHolePolygonRequest
