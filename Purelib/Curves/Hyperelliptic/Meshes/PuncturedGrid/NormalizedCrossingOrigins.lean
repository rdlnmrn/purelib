module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings

@[expose] public section

/-! The actual normalized destination readings have a uniform origin bound. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCrossingOrigins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual normalized destination reading at a retained horizontal crossing origin has squared norm at most four. -/
theorem normalized_right_origin_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps 1)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.normalize.anchors cached.normalize.offsets).values 0) ≤ 4 := by
  apply cached.normalized_reading_anchor_le_four gridRequest
  change trace.point (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [HorizontalCrossing.origin_eq joined trace,
    first.lifted.coordinates.2.2.2]
  exact (HorizontalCrossing.next_anchor joined).symm

/-- A zero retained destination anchor gives squared norm at most four for the actual horizontal crossing origin
reading. -/
theorem right_origin_bound_of_zero
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps 1)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) (originZero : cached.corners.values 0 = 0) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.anchors cached.offsets).values 0) ≤ 4 := by
  apply cached.reading_anchor_le_four_of_zero gridRequest originZero
  change trace.point (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [HorizontalCrossing.origin_eq joined trace,
    first.lifted.coordinates.2.2.2]
  exact (HorizontalCrossing.next_anchor joined).symm

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual normalized destination reading at a retained vertical crossing origin has squared norm at most four. -/
theorem normalized_right_origin_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps 1)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.normalize.anchors cached.normalize.offsets).values 0) ≤ 4 := by
  apply cached.normalized_reading_anchor_le_four gridRequest
  change trace.point (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [VerticalCrossing.origin_eq joined trace,
    first.lifted.coordinates.2.1]
  exact (VerticalCrossing.next_anchor joined).symm

/-- A zero retained destination anchor gives squared norm at most four for the actual vertical crossing origin reading.
-/
theorem right_origin_bound_of_zero
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps 1)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) (originZero : cached.corners.values 0 = 0) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.anchors cached.offsets).values 0) ≤ 4 := by
  apply cached.reading_anchor_le_four_of_zero gridRequest originZero
  change trace.point (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [VerticalCrossing.origin_eq joined trace,
    first.lifted.coordinates.2.1]
  exact (VerticalCrossing.next_anchor joined).symm

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCrossingOrigins
