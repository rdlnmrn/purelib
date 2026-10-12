module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

@[expose] public section

/-! Pay the actual change of owner at a common physical point. No source
resampling or zero-increment assertion is used for an owner junction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.OwnerRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount
  pieceIndex junction junction_eq junction_point)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece (trace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {tolerance : Coordinate}

/-- The first differential's two original owner readings at the same geometric junction differ by at most one quarter of
the target once the owner request is paid. -/
theorem first_jump (request : PairedOwnerRequest.OwnerRequest occurrence other tolerance) {index leftCount rightCount :
  Nat}
    (later : request.index ≤ index) (data : PairedFragmentValues.FirstData occurrence index)
    {leftPoints : Fin leftCount → InverseRootPolynomial.Gaussian} {rightPoints : Fin rightCount →
      InverseRootPolynomial.Gaussian}
    (left : RectangularPointReadings.PointReadings data.anchors data.offsets leftPoints)
    (right : RectangularPointReadings.PointReadings data.anchors data.offsets rightPoints)
    (first : Fin leftCount) (last : Fin rightCount) (equal : rightPoints last = leftPoints first) :
    Data.Gaussian.Norm.Basic.normSq (right.values last - left.values first) ≤ tolerance / 4 := by
  have inside := (left.point_eq first).trans equal.symm ▸ (left.owners first).contains
  have bounded := request.first_bound later data right last (left.owners first).column (left.owners first).row inside
  have evaluated : data.anchors.alignedValue data.offsets (left.owners first).column (left.owners first).row
      (rightPoints last) = left.values first := by
    rw [equal, ← left.point_eq first]
    exact (left.value_eq first).symm
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (right.values last - value))
    evaluated).symm.trans_le bounded

/-- The second differential's two original owner readings at the same geometric junction differ by at most one quarter
of the target once the owner request is paid. -/
theorem second_jump (request : PairedOwnerRequest.OwnerRequest occurrence other tolerance) {index leftCount rightCount :
  Nat}
    (later : request.index ≤ index) (data : PairedFragmentValues.SecondData occurrence other index)
    {leftPoints : Fin leftCount → InverseRootPolynomial.Gaussian} {rightPoints : Fin rightCount →
      InverseRootPolynomial.Gaussian}
    (left : RectangularPointReadings.PointReadings data.anchors data.offsets leftPoints)
    (right : RectangularPointReadings.PointReadings data.anchors data.offsets rightPoints)
    (first : Fin leftCount) (last : Fin rightCount) (equal : rightPoints last = leftPoints first) :
    Data.Gaussian.Norm.Basic.normSq (right.values last - left.values first) ≤ tolerance / 4 := by
  have inside := (left.point_eq first).trans equal.symm ▸ (left.owners first).contains
  have bounded := request.second_bound later data right last (left.owners first).column (left.owners first).row inside
  have evaluated : data.anchors.alignedValue data.offsets (left.owners first).column (left.owners first).row
      (rightPoints last) = left.values first := by
    rw [equal, ← left.point_eq first]
    exact (left.value_eq first).symm
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (right.values last - value))
    evaluated).symm.trans_le bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.OwnerRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.SurfaceOccurrence
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount
  pieceIndex junction junction_eq junction_point)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece (trace)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

/-- Read both original aligned face-bank values at the retained occurrence's column, row, point and sheet. -/
def JunctionValues (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) {index : Nat}
    (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) (secondBank :
      PrimitiveData.FacePrimitiveBank other index domains) :=
  let first := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let second := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  fun column row point => (⟨first.anchors.alignedValue first.offsets column row point,
    second.anchors.alignedValue second.offsets column row point⟩ : Stokes.PrimitivePoint)

/-- Transport an actual junction norm bound through the two exact scalar readback equalities. -/
private theorem jump_readback {a b c d : InverseRootPolynomial.Gaussian} {bound : InverseRootPolynomial.Coordinate}
    (first : a = c) (last : b = d) (bounded : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ bound) :
      Data.Gaussian.Norm.Basic.normSq (c - d) ≤ bound :=
  (congrArg₂ (fun x y => Data.Gaussian.Norm.Basic.normSq (x - y)) first last).symm.trans_le bounded

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece in
/-- Retain the original trace reading list with its exact aligned face-bank value at every original trace point. -/
private theorem trace_readings {lc lr rc rr count : Nat} {lg : RectangularInverseModels.Geometry lc lr} {rg :
  RectangularInverseModels.Geometry rc rr}
    {piece : RectangularPairedSegments.PairedSegmentPiece lg rg} (trace : RectangularPairedPointBanks.Trace piece count)
    {polynomial numerator : InverseRootPolynomial.Polynomial} {models : RectangularInverseModels.Bank polynomial lg}
    {primitives : RectangularPrimitiveModels.Primitives models numerator} (anchors :
      RectangularPrimitiveGluing.PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    ∃ readings : RectangularPointReadings.PointReadings anchors offsets (fun vertex => trace.points vertex),
      ∀ vertex, readings.values vertex = anchors.alignedValue offsets
        piece.leftColumn piece.leftRow (trace.points vertex) :=
  ⟨trace.leftReadings anchors offsets, trace.leftReadings_value anchors offsets⟩

/-- The original cached whole-perimeter sample satisfies the paid owner-junction bound.

Both differential readings use the same original shared face banks and actual adjoining trace endpoints; the bound is
one quarter of the requested tolerance. -/
theorem retained_junction_bound (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {cuts : RectangularSegmentSplitting.GridCuts ((domains.get occurrence.sideOccurrence.position).domain
      occurrence.sideOccurrence.sheet).geometry}
    {box : Rational.Box} {mesh : RectangularObservationMesh.ObservationMesh cuts box} (perimeter :
      RectangularPerimeterTraces.PerimeterTraces mesh)
    {index : Nat} (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (secondBank : PrimitiveData.FacePrimitiveBank other index domains)
    (samples : RectangularCenteredPerimeter.Centered perimeter
      (JunctionValues
      occurrence firstBank secondBank))
    (side : GridLiftedDualSteps.GridSide) (junctionIndex : Fin (RetainedPerimeterPiece.junctionCount mesh side))
    {tolerance : InverseRootPolynomial.Coordinate} (owners : PairedOwnerRequest.OwnerRequest occurrence other tolerance)
    (later : owners.index ≤ index) :
    PrimitivePoint.Bounded (RetainedPerimeterPiece.junction samples side junctionIndex) (tolerance / 4) := by
  let before := RetainedPerimeterPiece.pieceIndex mesh side junctionIndex.castSucc
  let after := RetainedPerimeterPiece.pieceIndex mesh side junctionIndex.succ
  let beforeTrace := RetainedPerimeterPiece.trace perimeter side before
  let afterTrace := RetainedPerimeterPiece.trace perimeter side after
  let last := Fin.last (RectangularDyadicPairedTrace.dyadicCount mesh.depth)
  let firstData := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let secondData := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  obtain ⟨firstBefore, firstBeforeValues⟩ :=
    trace_readings beforeTrace
    firstData.anchors firstData.offsets
  obtain ⟨firstAfter, firstAfterValues⟩ :=
    trace_readings afterTrace
    firstData.anchors firstData.offsets
  obtain ⟨secondBefore, secondBeforeValues⟩ :=
    trace_readings beforeTrace
    secondData.anchors secondData.offsets
  obtain ⟨secondAfter, secondAfterValues⟩ :=
    trace_readings afterTrace
    secondData.anchors secondData.offsets
  obtain ⟨sharedFirstBefore, firstBeforeEq⟩ := occurrence.compared.sharedReadings firstBank occurrence.aligned
    firstBefore
  obtain ⟨sharedFirstAfter, firstAfterEq⟩ := occurrence.compared.sharedReadings firstBank occurrence.aligned firstAfter
  let recast := occurrence.recastComparison other
  let aligned := occurrence.recastComparison_aligned other
  obtain ⟨sharedSecondBefore, secondBeforeEq⟩ := recast.sharedReadings secondBank aligned secondBefore
  obtain ⟨sharedSecondAfter, secondAfterEq⟩ := recast.sharedReadings secondBank aligned secondAfter
  have equal := RetainedPerimeterPiece.junction_point perimeter side junctionIndex
  have leftBound := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.OwnerRequest.first_jump
    owners later (occurrence.compared.sharedData firstBank occurrence.aligned)
    sharedFirstBefore sharedFirstAfter last 0 equal
  have rightBound := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.OwnerRequest.second_jump
    owners later (recast.sharedData secondBank aligned)
    sharedSecondBefore sharedSecondAfter last 0 equal
  have left := jump_readback
    (a := sharedFirstAfter.values 0) (b := sharedFirstBefore.values last)
    (bound := tolerance / 4)
    ((congrArg (fun values => values 0) firstAfterEq).trans
      (firstAfterValues 0))
    ((congrArg (fun values => values last) firstBeforeEq).trans
      (firstBeforeValues last)) leftBound
  have right := jump_readback
    (a := sharedSecondAfter.values 0) (b := sharedSecondBefore.values last)
    (bound := tolerance / 4)
    ((congrArg (fun values => values 0) secondAfterEq).trans
      (secondAfterValues 0))
    ((congrArg (fun values => values last) secondBeforeEq).trans
      (secondBeforeValues last)) rightBound
  apply Eq.mp (congrArg (fun value => PrimitivePoint.Bounded value (tolerance / 4))
    (RetainedPerimeterPiece.junction_eq samples side junctionIndex).symm)
  constructor
  · change Fraction.Order.Basic.LessEqual _ _ at left ⊢
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact left
  · change Fraction.Order.Basic.LessEqual _ _ at right ⊢
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact right

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.SurfaceOccurrence
