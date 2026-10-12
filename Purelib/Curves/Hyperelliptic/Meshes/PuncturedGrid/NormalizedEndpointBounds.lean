module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Integration.Polynomial.Rectangle.ClippedEndpointBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCrossingOrigins
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
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
import Purelib.Integration.Path.EndpointJump
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.ClippedBilinearBudget
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCrossingOrigins

open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

@[expose] public section

/-! The computed contact error bounds actual normalized endpoint corrections. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.HorizontalCrossing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.VerticalCrossing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
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
  {faces : PuncturedFaces bank} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool} {joined :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.HorizontalCrossing request first nextPosition
    firstUpper lastUpper}
  {firstDifferential secondDifferential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
    {firstParent secondParent : Fin 2}
  {tolerance : Purelib.Data.Rat.Fraction.Rational} {floor : Nat}

/-- The exact retained left horizontal endpoint sample on the original normalized primitive bank. -/
def
  AreaRequest.NormalizedLeftSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings firstLeft.normalize.anchors firstLeft.normalize.offsets).values vertex,
        (allocated.trace.leftReadings secondLeft.normalize.anchors secondLeft.normalize.offsets).values vertex⟩)

/-- The exact retained right horizontal endpoint sample on the original normalized primitive bank. -/
def
  AreaRequest.NormalizedRightSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings firstRight.normalize.anchors firstRight.normalize.offsets).values vertex,
        (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets).values vertex⟩)

/-- The exact retained left horizontal endpoint sample on the original primitive bank. -/
def
  AreaRequest.LeftSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings firstLeft.anchors firstLeft.offsets).values vertex,
        (allocated.trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩)

/-- The exact retained right horizontal endpoint sample on the original primitive bank. -/
def
  AreaRequest.RightSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings firstRight.anchors firstRight.offsets).values vertex,
        (allocated.trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)

/-- The actual normalized endpoint-increment error is bounded by sixteen times the original retained contact budget. -/
def
  AreaRequest.NormalizedEndpointErrorBound
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) ≤
      16 * allocated.accuracy.request.budget.error

/-- The paid original request bounds the actual normalized endpoint error using its retained destination-origin
estimate. -/
theorem
  AreaRequest.normalized_endpoint_error_bound
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedEndpointErrorBound firstLeft firstRight secondLeft secondRight left right := by
  dsimp only
    [AreaRequest.NormalizedEndpointErrorBound]
  have origin : PrimitivePoint.Bounded (⟨(allocated.trace.rightReadings firstRight.normalize.anchors
    firstRight.normalize.offsets).values 0,
      (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets).values 0⟩ :
      Topology.Polygon.Stokes.PrimitivePoint) 4 := by
    have firstOrigin := HorizontalCrossing.normalized_right_origin_bound joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.firstGrid stage (allocated.accuracy.first_le.trans later))
        firstRight
    have secondOrigin := HorizontalCrossing.normalized_right_origin_bound joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.secondGrid stage (allocated.accuracy.second_le.trans later))
        secondRight
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstOrigin secondOrigin
    exact ⟨firstOrigin, secondOrigin⟩
  have estimate := allocated.accuracy.request.endpointIncrementError_bound (allocated.accuracy.request_le.trans later)
    firstLeft.normalize firstRight.normalize secondLeft.normalize secondRight.normalize
    (allocated.trace.leftReadings firstLeft.normalize.anchors firstLeft.normalize.offsets)
    (allocated.trace.rightReadings firstRight.normalize.anchors firstRight.normalize.offsets)
    (allocated.trace.leftReadings secondLeft.normalize.anchors secondLeft.normalize.offsets)
    (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets) left right origin
  exact estimate.trans_eq (by ring1)

/-- The actual normalized endpoint-increment error satisfies the original strict requested tolerance. -/
def
  AreaRequest.NormalizedEndpointErrorAccurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) < tolerance

/-- The original contact budget pays the actual normalized endpoint error at every retained later stage. -/
theorem
  AreaRequest.normalized_endpoint_error_accurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedEndpointErrorAccurate firstLeft firstRight secondLeft secondRight left right :=
  allocated.accuracy.request.budget.endpoint_paid left right
    (allocated.normalized_endpoint_error_bound later firstLeft firstRight secondLeft secondRight left right)

/-- The actual normalized area difference after its retained endpoint jump satisfies four times the original requested
tolerance. -/
def
  AreaRequest.NormalizedJumpAccurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq
      ((left.originalArea - right.originalArea) - left.endpointJump right) < 4 * tolerance

/-- The original normalized area comparison and paid endpoint error bound the actual retained jump discrepancy. -/
theorem
  AreaRequest.normalized_jump_accurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedJumpAccurate firstLeft firstRight secondLeft secondRight left right :=
  left.jump_comparison right
    (allocated.accuracy.accurate later firstLeft.normalize firstRight.normalize secondLeft.normalize
      secondRight.normalize left right)
    (allocated.normalized_endpoint_error_accurate later firstLeft firstRight secondLeft secondRight left right)

/-- The actual endpoint-increment error bound by sixteen times the original retained contact budget. -/
def
  AreaRequest.EndpointErrorBoundOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) ≤
      16 * allocated.accuracy.request.budget.error

/-- Zero original destination anchors give the retained contact-budget bound on the actual endpoint error. -/
theorem
  AreaRequest.endpoint_error_bound_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.EndpointErrorBoundOfZero firstLeft firstRight secondLeft secondRight left right := by
  dsimp only
    [AreaRequest.EndpointErrorBoundOfZero]
  have origin : PrimitivePoint.Bounded (⟨(allocated.trace.rightReadings firstRight.anchors firstRight.offsets).values 0,
      (allocated.trace.rightReadings secondRight.anchors secondRight.offsets).values 0⟩ :
      Topology.Polygon.Stokes.PrimitivePoint) 4 := by
    have firstOrigin := HorizontalCrossing.right_origin_bound_of_zero joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.firstGrid stage (allocated.accuracy.first_le.trans later))
        firstRight firstZero
    have secondOrigin := HorizontalCrossing.right_origin_bound_of_zero joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.secondGrid stage (allocated.accuracy.second_le.trans later))
        secondRight secondZero
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstOrigin secondOrigin
    exact ⟨firstOrigin, secondOrigin⟩
  have estimate := allocated.accuracy.request.endpointIncrementError_bound (allocated.accuracy.request_le.trans later)
    firstLeft firstRight secondLeft secondRight
    (allocated.trace.leftReadings firstLeft.anchors firstLeft.offsets)
    (allocated.trace.rightReadings firstRight.anchors firstRight.offsets)
    (allocated.trace.leftReadings secondLeft.anchors secondLeft.offsets)
    (allocated.trace.rightReadings secondRight.anchors secondRight.offsets) left right origin
  exact estimate.trans_eq (by ring1)

/-- The actual endpoint-increment error satisfies the original strict requested tolerance. -/
def
  AreaRequest.EndpointErrorAccurateOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) < tolerance

/-- The original contact budget pays the actual endpoint error when both retained destination anchors vanish. -/
theorem
  AreaRequest.endpoint_error_accurate_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.EndpointErrorAccurateOfZero firstLeft firstRight secondLeft secondRight left right :=
  allocated.accuracy.request.budget.endpoint_paid left right
    (allocated.endpoint_error_bound_of_zero later firstLeft firstRight secondLeft secondRight firstZero secondZero left
      right)

/-- The actual original area difference after its retained endpoint jump satisfies four times the requested tolerance.
-/
def
  AreaRequest.JumpAccurateOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq
      ((left.originalArea - right.originalArea) - left.endpointJump right) < 4 * tolerance

/-- The original area comparison and paid endpoint error bound the retained jump discrepancy when both destination
anchors vanish. -/
theorem
  AreaRequest.jump_accurate_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.JumpAccurateOfZero firstLeft firstRight secondLeft secondRight left right :=
  left.jump_comparison right
    (allocated.accuracy.accurate later firstLeft firstRight secondLeft secondRight left right)
    (allocated.endpoint_error_accurate_of_zero later firstLeft firstRight secondLeft secondRight firstZero secondZero
      left right)

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool} {joined :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.VerticalCrossing request first nextPosition
    firstUpper lastUpper}
  {firstDifferential secondDifferential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
    {firstParent secondParent : Fin 2}
  {tolerance : Purelib.Data.Rat.Fraction.Rational} {floor : Nat}

/-- The exact retained left vertical endpoint sample on the original normalized primitive bank. -/
def
  AreaRequest.NormalizedLeftSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings firstLeft.normalize.anchors firstLeft.normalize.offsets).values vertex,
        (allocated.trace.leftReadings secondLeft.normalize.anchors secondLeft.normalize.offsets).values vertex⟩)

/-- The exact retained right vertical endpoint sample on the original normalized primitive bank. -/
def
  AreaRequest.NormalizedRightSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings firstRight.normalize.anchors firstRight.normalize.offsets).values vertex,
        (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets).values vertex⟩)

/-- The exact retained left vertical endpoint sample on the original primitive bank. -/
def
  AreaRequest.LeftSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings firstLeft.anchors firstLeft.offsets).values vertex,
        (allocated.trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩)

/-- The exact retained right vertical endpoint sample on the original primitive bank. -/
def
  AreaRequest.RightSample
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage) :=
  CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings firstRight.anchors firstRight.offsets).values vertex,
        (allocated.trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)

/-- The actual normalized endpoint-increment error is bounded by sixteen times the original retained contact budget. -/
def
  AreaRequest.NormalizedEndpointErrorBound
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) ≤
      16 * allocated.accuracy.request.budget.error

/-- The paid original request bounds the actual normalized endpoint error using its retained destination-origin
estimate. -/
theorem
  AreaRequest.normalized_endpoint_error_bound
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedEndpointErrorBound firstLeft firstRight secondLeft secondRight left right := by
  dsimp only
    [AreaRequest.NormalizedEndpointErrorBound]
  have origin : PrimitivePoint.Bounded (⟨(allocated.trace.rightReadings firstRight.normalize.anchors
    firstRight.normalize.offsets).values 0,
      (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets).values 0⟩ :
      Topology.Polygon.Stokes.PrimitivePoint) 4 := by
    have firstOrigin := VerticalCrossing.normalized_right_origin_bound joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.firstGrid stage (allocated.accuracy.first_le.trans later))
        firstRight
    have secondOrigin := VerticalCrossing.normalized_right_origin_bound joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.secondGrid stage (allocated.accuracy.second_le.trans later))
        secondRight
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstOrigin secondOrigin
    exact ⟨firstOrigin, secondOrigin⟩
  have estimate := allocated.accuracy.request.endpointIncrementError_bound (allocated.accuracy.request_le.trans later)
    firstLeft.normalize firstRight.normalize secondLeft.normalize secondRight.normalize
    (allocated.trace.leftReadings firstLeft.normalize.anchors firstLeft.normalize.offsets)
    (allocated.trace.rightReadings firstRight.normalize.anchors firstRight.normalize.offsets)
    (allocated.trace.leftReadings secondLeft.normalize.anchors secondLeft.normalize.offsets)
    (allocated.trace.rightReadings secondRight.normalize.anchors secondRight.normalize.offsets) left right origin
  exact estimate.trans_eq (by ring1)

/-- The actual normalized endpoint-increment error satisfies the original strict requested tolerance. -/
def
  AreaRequest.NormalizedEndpointErrorAccurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) < tolerance

/-- The original contact budget pays the actual normalized endpoint error at every retained later stage. -/
theorem
  AreaRequest.normalized_endpoint_error_accurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedEndpointErrorAccurate firstLeft firstRight secondLeft secondRight left right :=
  allocated.accuracy.request.budget.endpoint_paid left right
    (allocated.normalized_endpoint_error_bound later firstLeft firstRight secondLeft secondRight left right)

/-- The actual normalized area difference after its retained endpoint jump satisfies four times the original requested
tolerance. -/
def
  AreaRequest.NormalizedJumpAccurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq
      ((left.originalArea - right.originalArea) - left.endpointJump right) < 4 * tolerance

/-- The original normalized area comparison and paid endpoint error bound the actual retained jump discrepancy. -/
theorem
  AreaRequest.normalized_jump_accurate
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.NormalizedLeftSample firstLeft secondLeft)
    (right : allocated.NormalizedRightSample firstRight secondRight) :
    allocated.NormalizedJumpAccurate firstLeft firstRight secondLeft secondRight left right :=
  left.jump_comparison right
    (allocated.accuracy.accurate later firstLeft.normalize firstRight.normalize secondLeft.normalize
      secondRight.normalize left right)
    (allocated.normalized_endpoint_error_accurate later firstLeft firstRight secondLeft secondRight left right)

/-- The actual endpoint-increment error bound by sixteen times the original retained contact budget. -/
def
  AreaRequest.EndpointErrorBoundOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) ≤
      16 * allocated.accuracy.request.budget.error

/-- Zero original destination anchors give the retained contact-budget bound on the actual endpoint error. -/
theorem
  AreaRequest.endpoint_error_bound_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.EndpointErrorBoundOfZero firstLeft firstRight secondLeft secondRight left right := by
  dsimp only
    [AreaRequest.EndpointErrorBoundOfZero]
  have origin : PrimitivePoint.Bounded (⟨(allocated.trace.rightReadings firstRight.anchors firstRight.offsets).values 0,
      (allocated.trace.rightReadings secondRight.anchors secondRight.offsets).values 0⟩ :
      Topology.Polygon.Stokes.PrimitivePoint) 4 := by
    have firstOrigin := VerticalCrossing.right_origin_bound_of_zero joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.firstGrid stage (allocated.accuracy.first_le.trans later))
        firstRight firstZero
    have secondOrigin := VerticalCrossing.right_origin_bound_of_zero joined allocated.trace
      (GridPrimitiveAccuracy.atIndex allocated.accuracy.secondGrid stage (allocated.accuracy.second_le.trans later))
        secondRight secondZero
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstOrigin secondOrigin
    exact ⟨firstOrigin, secondOrigin⟩
  have estimate := allocated.accuracy.request.endpointIncrementError_bound (allocated.accuracy.request_le.trans later)
    firstLeft firstRight secondLeft secondRight
    (allocated.trace.leftReadings firstLeft.anchors firstLeft.offsets)
    (allocated.trace.rightReadings firstRight.anchors firstRight.offsets)
    (allocated.trace.leftReadings secondLeft.anchors secondLeft.offsets)
    (allocated.trace.rightReadings secondRight.anchors secondRight.offsets) left right origin
  exact estimate.trans_eq (by ring1)

/-- The actual endpoint-increment error satisfies the original strict requested tolerance. -/
def
  AreaRequest.EndpointErrorAccurateOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) < tolerance

/-- The original contact budget pays the actual endpoint error when both retained destination anchors vanish. -/
theorem
  AreaRequest.endpoint_error_accurate_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.EndpointErrorAccurateOfZero firstLeft firstRight secondLeft secondRight left right :=
  allocated.accuracy.request.budget.endpoint_paid left right
    (allocated.endpoint_error_bound_of_zero later firstLeft firstRight secondLeft secondRight firstZero secondZero left
      right)

/-- The actual original area difference after its retained endpoint jump satisfies four times the requested tolerance.
-/
def
  AreaRequest.JumpAccurateOfZero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat}
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) : Prop :=
    Data.Gaussian.Norm.Basic.normSq
      ((left.originalArea - right.originalArea) - left.endpointJump right) < 4 * tolerance

/-- The original area comparison and paid endpoint error bound the retained jump discrepancy when both destination
anchors vanish. -/
theorem
  AreaRequest.jump_accurate_of_zero
    (allocated : AreaRequest joined firstDifferential secondDifferential firstParent secondParent tolerance floor)
    {stage : Nat} (later : allocated.accuracy.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives ((domains.get firstPosition).domain firstSheet) secondDifferential
      stage)
    (secondRight : PrimitiveData.DomainPrimitives ((domains.get nextPosition).domain joined.crossing.next.sheet)
      secondDifferential stage)
    (firstZero : firstRight.corners.values 0 = 0) (secondZero : secondRight.corners.values 0 = 0)
    (left : allocated.LeftSample firstLeft secondLeft)
    (right : allocated.RightSample firstRight secondRight) :
    allocated.JumpAccurateOfZero firstLeft firstRight secondLeft secondRight left right :=
  left.jump_comparison right
    (allocated.accuracy.accurate later firstLeft firstRight secondLeft secondRight left right)
    (allocated.endpoint_error_accurate_of_zero later firstLeft firstRight secondLeft secondRight firstZero secondZero
      left right)

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
