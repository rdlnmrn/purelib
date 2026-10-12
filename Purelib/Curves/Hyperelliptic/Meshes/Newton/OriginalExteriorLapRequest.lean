module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
public import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.ExteriorBoundary
public import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
public import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Batteries.Logic
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

public section

open Purelib.Data

/-! Identify the actual original exterior with the requested closed
component polygons, preserving each incoming sheet under grid refinement. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalExteriorLapRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation (atDepth)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (mix extract
  extract_congr mix_reverse)
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization (extract_wordArea_mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (exteriorPrograms
  exteriorPrograms_indexed)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest (ExteriorLapRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {first second : Fin genus}
  {target radius : Rational} {floor : Nat}

/-- The automatic constructor retains the literal canonical component list. -/
theorem build_exterior_components (preparation : BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (first second : Fin genus) (target radius : Fraction.Rational) (positive : 0 < target) (radiusPositive : 0 < radius)
      (floor : Nat) :
    let prepared := BoundaryPreparation.build preparation first second target radius positive radiusPositive floor
    prepared.exterior.prepared.components.map (fun component => component.program.indexed) =
      prepared.lifted.exteriorBoundaries := by
  intro prepared
  change (((PeriodPrograms.exteriorPrograms prepared.lifted (PeriodMatrix.standardDifferential first)).map
    (SurfaceComponent.build prepared.exterior.regular prepared.domains)).map _) = _
  rw [List.Map.map_map]
  exact PeriodPrograms.exteriorPrograms_indexed prepared.lifted _

/-- Only numerical surface depth changes; the canonical components survive. -/
theorem atDepth_exterior_components (prepared : NewtonRequestedBoundary.BoundaryPreparation preparation first second
  target radius floor)
    (canonical : prepared.exterior.prepared.components.map (fun component => component.program.indexed) =
      prepared.lifted.exteriorBoundaries)
    (depth : Nat) :
    (BoundaryPreparation.atDepth prepared depth).exterior.prepared.components.map (fun component =>
      component.program.indexed) =
      (BoundaryPreparation.atDepth prepared depth).lifted.exteriorBoundaries := canonical

open Purelib.Integration.Path.PairedIncrementArea (area) in
/-- Both parities compare twice the original exterior polygon with the actual closed component sum. The caller supplies
only retained ownership. -/
@[expose] def originalExteriorLapRequest (prepared : NewtonRequestedBoundary.BoundaryPreparation preparation first
  second target radius floor)
    (canonical : prepared.exterior.prepared.components.map (fun component => component.program.indexed) =
      prepared.lifted.exteriorBoundaries)
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics prepared.domains stage)
        (readings : CutPairingRequest.Readings prepared.paid.cut cache), threshold ≤ stage →
        ∀ sheet : Fin 2,
        let value := fun coefficient => BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
          readings.left.values)
          (CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values) coefficient
        let lap := BilinearPolarization.extract (fun coefficient => prepared.lifted.edges.chainArea
          prepared.lifted.vertices (value coefficient)
          (prepared.fine.family.single.grid.shrunk.included.resplit base.bank.exterior
            (FramedBranchCellBank.baseMember base.bank)) sheet)
        Data.Gaussian.Norm.Basic.normSq (lap + lap - Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (prepared.exterior.prepared.components.map (fun component =>
          area (component.program.indexed.map (fun edge =>
            (⟨edgeValuation prepared.lifted.mesh readings.left.values edge,
              CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
                Stokes.PrimitivePoint)))))) ≤ error} := by
  let left := FaceMagnitudeBank.build prepared.domains (PeriodMatrix.standardDifferential first)
  let right := FaceMagnitudeBank.build prepared.domains (PeriodMatrix.standardDifferential second)
  let request := ExteriorLapRequest.build left right error positive
  refine ⟨max minimum request.index, Nat.Order.le_max_left _ _, ?_⟩
  intro stage cache readings later sheet value lap
  let pairs := fun edge => (⟨edgeValuation prepared.lifted.mesh readings.left.values edge,
    CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ : Stokes.PrimitivePoint)
  let area := fun word => PairedIncrementArea.area (List.map pairs word)
  have comparison := prepared.fine.family.single.grid.shrunk.included.exterior_comparison base.bank.frame
    prepared.fine.family.single.grid.punctured.bank.frame prepared.lifted.edges prepared.lifted.vertices
    (fun point member => (BranchCellBank.referenceAt
      prepared.fine.family.single.grid.punctured.bank.toBranchCellBank point member).toLoop)
  have readback : lap = area (prepared.lifted.edges.indexedEdges prepared.lifted.vertices
      prepared.fine.family.single.grid.punctured.bank.exterior sheet) := by
    have equal := BilinearPolarization.extract_congr (fun coefficient => comparison.areas (value coefficient)
      (BilinearPolarization.mix_reverse _ _ (CanonicalEdgeValues.edgeValuation_reverse prepared.lifted.mesh
        readings.left.values)
        (CanonicalEdgeValues.edgeValuation_reverse prepared.lifted.mesh readings.right.values) coefficient) sheet)
    exact equal.trans (BilinearPolarization.extract_wordArea_mix _ _ _)
  have bounded := request.accurate readings.left readings.right ((Nat.Order.le_max_right _ _).trans later) sheet
  have words := congrArg (List.map area) canonical
  rw [List.Map.map_map] at words
  have sum := congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum words
  have equal := congrArg₂ (fun polygon components => Data.Gaussian.Norm.Basic.normSq (polygon + polygon -
    components)) readback sum
  exact equal.trans_le bounded

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalExteriorLapRequest
