module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowHole
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateCorrectionRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateHolePolygonRequest
import Purelib.Data.Gaussian.Basic
import Batteries.Logic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

open Purelib.Topology.Surface.Sewing

public section

/-! Replace the remaining compiler hole polygons by the actual positive
boundary polygons of the shrunken hole, with both stem errors paid. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest

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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing (PairedRequest)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
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

/-- Both positive laps around the retained shrunken hole, with the actual shared edge readings. Its cell identity is
certified by `fineHole_cell`. -/
@[expose] def
  conjugatePhysicalHoleArea
  (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed rightFixed error floor)
    {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) : Gaussian :=
  let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    left.values edge),
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  let physical := fun initial => PairedIncrementArea.area
    ((current.edges.indexedEdges current.vertices (WindowHole.fineHole (current := current) request.outer).hole.boundary
      initial).map value)
  physical 0 + physical 1

/-- The exact original cut correction plus the positive physical-hole polygon sum is small at every later shared
numerical stage. -/
@[expose] def
  conjugatePhysicalCorrectionRequest
  (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed rightFixed error floor)
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
        Data.Gaussian.Norm.Basic.normSq (sample.cut.correction + request.conjugatePhysicalHoleArea left right)
          ≤ bound} := by
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
  let correction := ConjugateCorrectionRequest.conjugateCorrectionRequest request prepared (bound / 4) partPositive
    minimum
  let hole := ConjugateHolePolygonRequest.conjugateHolePolygonRequest request.outer prepared.leftMagnitude
    prepared.rightMagnitude (bound / 4) partPositive minimum
  refine ⟨max correction.val hole.val, correction.property.1.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right leftSurface rightSurface pair sample later
  have correctionBound := correction.property.2 stage cache left right leftSurface rightSurface pair sample
    ((Nat.Order.le_max_left _ _).trans later)
  have holeBound := hole.property.2 stage cache left right ((Nat.Order.le_max_right _ _).trans later)
  let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    left.values edge),
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  let retained := fun initial => PairedIncrementArea.area
    (((WindowCircuits.fineCompiler (current := current) request.outer initial).word).map value)
  have readback : ConjugateCorrectionRequest.retainedConjugateHoleArea request left right = retained 0 + retained 1 :=
    by
    exact congrArg₂ (· + ·) (BilinearPolarization.extract_wordArea_mix _ _ _) (BilinearPolarization.extract_wordArea_mix
      _ _ _)
  change Data.Gaussian.Norm.Basic.normSq ((retained 0 + retained 1) - request.conjugatePhysicalHoleArea left
    right) ≤ bound / 4 at holeBound
  rw [← readback] at holeBound
  have equal : sample.cut.correction + request.conjugatePhysicalHoleArea left right =
      (sample.cut.correction + ConjugateCorrectionRequest.retainedConjugateHoleArea request left right) -
        (ConjugateCorrectionRequest.retainedConjugateHoleArea request left right - request.conjugatePhysicalHoleArea
          left right) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      correctionBound holeBound) (by decide)).trans_eq
      ((by ring1 : 2 * (bound / 4 + bound / 4) = bound / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest
