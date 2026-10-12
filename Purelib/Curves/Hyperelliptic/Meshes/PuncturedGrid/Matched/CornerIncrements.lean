module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
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
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
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
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness

open Purelib.Data.Rat

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Matched trace increments use the fixed face corners of the period bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerIncrements

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
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

/-- The actual left horizontal crossing increment differs from its retained corner increment by at most sixteen times
the original grid error in squared norm. -/
theorem left_corner_increment_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      (((trace.leftReadings cached.anchors cached.offsets).values (Fin.last trace.vertices.rest.length) -
        (trace.leftReadings cached.anchors cached.offsets).values 0) -
        (cached.corners.values 2 - cached.corners.values 3)) ≤ 16 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_increment_bound gridRequest cached
  · change Trace.point trace (trace.vertices.indexed 0) = FaceCorners.point _ 3
    rw [HorizontalCrossing.origin_eq joined trace, first.lifted.coordinates.2.2.2]
    rfl
  · change Trace.point trace (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) = FaceCorners.point _ 2
    rw [HorizontalCrossing.terminal_eq joined trace, first.lifted.coordinates.2.2.1]
    rfl

/-- The actual right horizontal crossing increment differs from its retained corner increment by at most sixteen times
the original grid error in squared norm. -/
theorem right_corner_increment_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      (((trace.rightReadings cached.anchors cached.offsets).values (Fin.last trace.vertices.rest.length) -
        (trace.rightReadings cached.anchors cached.offsets).values 0) -
        (cached.corners.values 1 - cached.corners.values 0)) ≤ 16 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_increment_bound gridRequest cached
  · change Trace.point trace (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
    rw [HorizontalCrossing.origin_eq joined trace, first.lifted.coordinates.2.2.2]
    exact (HorizontalCrossing.next_anchor joined).symm
  · change Trace.point trace (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) = FaceCorners.point _ 1
    rw [HorizontalCrossing.terminal_eq joined trace]
    have endpoint : joined.crossing.next.located.lifted.quad.second = first.lifted.quad.third :=
      congrArg (fun edge => edge.finish) joined.reversed
    rw [← endpoint, joined.crossing.next.located.lifted.coordinates.2.1]
    rfl

/-- The actual left horizontal crossing origin differs from its retained corner value by at most four times the original
grid error in squared norm. -/
theorem left_corner_origin_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.leftReadings cached.anchors cached.offsets).values 0 - cached.corners.values 3) ≤
      4 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_bound gridRequest cached
  change Trace.point trace (trace.vertices.indexed 0) = FaceCorners.point _ 3
  rw [HorizontalCrossing.origin_eq joined trace, first.lifted.coordinates.2.2.2]
  rfl

/-- The actual right horizontal crossing origin differs from its retained corner value by at most four times the
original grid error in squared norm. -/
theorem right_corner_origin_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.anchors cached.offsets).values 0 - cached.corners.values 0) ≤
      4 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_bound gridRequest cached
  change Trace.point trace (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [HorizontalCrossing.origin_eq joined trace, first.lifted.coordinates.2.2.2]
  exact (HorizontalCrossing.next_anchor joined).symm

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual left vertical crossing increment differs from its retained corner increment by at most sixteen times the
original grid error in squared norm. -/
theorem left_corner_increment_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      (((trace.leftReadings cached.anchors cached.offsets).values (Fin.last trace.vertices.rest.length) -
        (trace.leftReadings cached.anchors cached.offsets).values 0) -
        (cached.corners.values 2 - cached.corners.values 1)) ≤ 16 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_increment_bound gridRequest cached
  · change Trace.point trace (trace.vertices.indexed 0) = FaceCorners.point _ 1
    rw [VerticalCrossing.origin_eq joined trace, first.lifted.coordinates.2.1]
    rfl
  · change Trace.point trace (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) = FaceCorners.point _ 2
    rw [VerticalCrossing.terminal_eq joined trace, first.lifted.coordinates.2.2.1]
    rfl

/-- The actual right vertical crossing increment differs from its retained corner increment by at most sixteen times the
original grid error in squared norm. -/
theorem right_corner_increment_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      (((trace.rightReadings cached.anchors cached.offsets).values (Fin.last trace.vertices.rest.length) -
        (trace.rightReadings cached.anchors cached.offsets).values 0) -
        (cached.corners.values 3 - cached.corners.values 0)) ≤ 16 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_increment_bound gridRequest cached
  · change Trace.point trace (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
    rw [VerticalCrossing.origin_eq joined trace, first.lifted.coordinates.2.1]
    exact (VerticalCrossing.next_anchor joined).symm
  · change Trace.point trace (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) = FaceCorners.point _ 3
    rw [VerticalCrossing.terminal_eq joined trace]
    have endpoint : joined.crossing.next.located.lifted.quad.fourth = first.lifted.quad.third :=
      congrArg (fun edge => edge.start) joined.reversed
    rw [← endpoint, joined.crossing.next.located.lifted.coordinates.2.2.2]
    rfl

/-- The actual left vertical crossing origin differs from its retained corner value by at most four times the original
grid error in squared norm. -/
theorem left_corner_origin_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.leftReadings cached.anchors cached.offsets).values 0 - cached.corners.values 1) ≤
      4 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_bound gridRequest cached
  change Trace.point trace (trace.vertices.indexed 0) = FaceCorners.point _ 1
  rw [VerticalCrossing.origin_eq joined trace, first.lifted.coordinates.2.1]
  rfl

/-- The actual right vertical crossing origin differs from its retained corner value by at most four times the original
grid error in squared norm. -/
theorem right_corner_origin_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {tolerance : Fraction.Rational}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance)
    (cached : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet) differential
      gridRequest.index) :
    Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings cached.anchors cached.offsets).values 0 - cached.corners.values 0) ≤
      4 * gridRequest.globalBound := by
  apply DomainPrimitives.reading_corner_bound gridRequest cached
  change Trace.point trace (trace.vertices.indexed 0) = faces.regulars[nextPosition.val].cell.box.anchor
  rw [VerticalCrossing.origin_eq joined trace, first.lifted.coordinates.2.1]
  exact (VerticalCrossing.next_anchor joined).symm

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerIncrements
