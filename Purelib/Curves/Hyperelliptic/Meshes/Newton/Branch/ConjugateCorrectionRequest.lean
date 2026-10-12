module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSelectedConjugateSewing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateWindowSelectedRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateLapSum
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Topology.NewtonSelectedConjugateSewing

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

open Purelib.Topology.Surface.Sewing

public section

/-! The original branch-region correction is compared to its retained fine
hole polygons. No smallness of those remaining hole polygons is assumed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateCorrectionRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Integration.Path (PairedOccurrenceArea)

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests (BilinearStemRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests (BilinearHoleRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization (extract_wordArea_mix)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits (fineCompiler)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {entry : AnnularEntry grid current} {sheet : Fin 2}
  {leftFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)}
  {rightFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)}
  {error : Rational} {floor : Nat}

/-- These are the actual fine compiler's retained hole words, on both initial sheets, evaluated at the same two
numerical readings. -/
@[expose] def retainedConjugateHoleArea (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed
  rightFixed error floor)
    {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) : Gaussian :=
  let hole := fun initial => BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
    (WindowCircuits.fineCompiler (current := current) request.outer initial).word)
  hole 0 + hole 1

/-- The original receipt, its sewn annulus, both outer laps, and the fine hole polygons are all compared on a
constructed common later stage. -/
@[expose] def conjugateCorrectionRequest (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed
  rightFixed error floor)
    (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j)
    (bound : Rational) (positive : 0 < bound) (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
        (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
        (sample : PairedBranchRequest.ConjugateSample request left right leftSurface rightSurface pair), threshold ≤
          stage →
        Data.Gaussian.Norm.Basic.normSq (sample.cut.correction +
          retainedConjugateHoleArea request left
          right) ≤ bound} := by
  let part := bound / 16
  have partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 16)
  have lapPositive : 0 < part / 4 := Fraction.Order.Field.div_pos_direct partPositive (by decide : (0 : Rational) < 4)
  let geometry := ConjugateWindowSelectedRequest.selectedConjugateTriangleRequest request.outer prepared.leftMagnitude
    prepared.rightMagnitude part partPositive minimum
  let sewing := BilinearPreparation.Request.build prepared part partPositive minimum
  let canonical := PairedRequest.build request.geometry prepared.leftMagnitude prepared.rightMagnitude
    part partPositive minimum
  let laps := BilinearHoleRequest.build bank grid.shrunk.included prepared.leftMagnitude prepared.rightMagnitude
    entry.hole.index (part / 4) lapPositive
  let threshold := max (max geometry.val sewing.index) (max canonical.index laps.index)
  refine ⟨threshold, geometry.property.1.trans ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)), ?_⟩
  intro stage cache left right leftSurface rightSurface pair sample later
  have geometryLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have sewingLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have canonicalLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans later)
  have lapsLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans later)
  let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    left.values edge),
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  let walk :=
    BilinearHoleRequest.boundary (next
    := grid.punctured) bank grid.shrunk.included entry.hole.index
  let polygon := fun initial => PairedIncrementArea.area ((current.edges.indexedEdges current.vertices walk initial).map
    value)
  let double := PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map value)
  let triangles := ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun position =>
    decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell entry.hole.index).box))
  let hole := fun initial =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient => RetracingWords.wordArea
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
    (WindowCircuits.fineCompiler (current := current) request.outer initial).word)
  let outer := fun initial =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient => current.edges.chainArea current.vertices
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
    (grid.shrunk.included.resplit (CellBoundary.Cell.boundaryWalk (base.bank.cell entry.hole.index) (base.bank.cell_mem
      entry.hole.index))
      (ClearGrid.Cell.anchor_mem (base.bank.cell entry.hole.index) (base.bank.cell_mem entry.hole.index))) initial)
  have polygonEq (initial : Fin 2) : outer initial = polygon initial := by
    have boundary := (bank.rows.get entry.hole.index).boundary_eq
    unfold outer polygon walk
      BilinearHoleRequest.boundary
    rw [boundary]
    exact BilinearPolarization.extract_wordArea_mix _ _ _
  have geometryBound := geometry.property.2 stage cache left right geometryLater
  have extraction (initial : Fin 2) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient => current.edges.chainArea current.vertices
        (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
          current.mesh left.values edge))
          (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
        (grid.shrunk.included.resplit (CellBoundary.Cell.boundaryWalk (base.bank.cell entry.hole.index)
          (base.bank.cell_mem entry.hole.index))
          (ClearGrid.Cell.anchor_mem (base.bank.cell entry.hole.index) (base.bank.cell_mem entry.hole.index))) initial -
        RetracingWords.wordArea (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj
          (CanonicalEdgeValues.edgeValuation current.mesh left.values edge))
          (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
          (WindowCircuits.fineCompiler (current := current) request.outer initial).word) = outer initial - hole initial
            := by
    dsimp only [outer, hole]
    unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  dsimp only at geometryBound
  rw [extraction 0, extraction 1, polygonEq 0, polygonEq 1] at geometryBound
  change Data.Gaussian.Norm.Basic.normSq ((polygon 0 - hole 0) + (polygon 1 - hole 1) - triangles) < part
    at geometryBound
  have areaBound := ConjugateSample.selected_accurate left right sample.cut sewing sewingLater
  change Data.Gaussian.Norm.Basic.normSq (sample.cut.area - triangles) < part at areaBound
  have corrected := ConjugateSample.canonical_accurate canonical left right leftSurface rightSurface pair sample.cut
    canonicalLater
  change Data.Gaussian.Norm.Basic.normSq (sample.cut.area - sample.cut.correction - double) ≤ part at corrected
  have lapBound := ConjugateLapSum.conjugate_sum_accurate laps left right lapsLater
  have lapPaid : Data.Gaussian.Norm.Basic.normSq (polygon 0 + polygon 1 - double) ≤ part :=
    lapBound.trans_eq ((Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  have first := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (sample.cut.area - triangles)
    (sample.cut.area - sample.cut.correction - double)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      areaBound.le corrected) (by decide))
  have second := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (polygon 0 + polygon 1 - double)
    ((polygon 0 - hole 0) + (polygon 1 - hole 1) - triangles)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct lapPaid
      geometryBound.le) (by decide))
  have equal : sample.cut.correction +
    retainedConjugateHoleArea request left right =
      ((sample.cut.area - triangles) - (sample.cut.area - sample.cut.correction - double)) +
      ((polygon 0 + polygon 1 - double) - ((polygon 0 - hole 0) + (polygon 1 - hole 1) - triangles)) := by
    change sample.cut.correction + (hole 0 + hole 1) = _
    ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
      second) (by decide)).trans_eq
      ((by ring1 : 2 * (2 * (part + part) + 2 * (part + part)) = bound / 16 * 16).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateCorrectionRequest
