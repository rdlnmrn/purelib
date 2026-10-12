module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedEndpointBounds
import Purelib.Integration.Path.EndpointJump
public import Purelib.Riemann.Paths.RectangularMatchedChords
public import Purelib.Riemann.Integration.RectangularMatchedJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
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
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Integration.RectangularMatchedPerimeter

public section

/-! Samples retain both actual path areas and endpoint corrections for every
prepared match. Certified nonmatches contribute exactly zero. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.RectangularObservationAssembly
open Purelib.Topology.Polygon

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared VerticalPrepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.HorizontalCrossing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.VerticalCrossing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

namespace HorizontalPrepared

/-- The two actual differential values on the first retained horizontal trace, read from its original anchor and offset
cache. -/
@[expose] def leftValues {joined : LiftedSides.HorizontalCrossing request first nextPosition false false}
    (allocated : HorizontalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor)
    (cache : RegularMeshes.Numerics domains stage) (vertex : Fin (allocated.trace.vertices.rest.length + 1)) :
      PrimitivePoint :=
  ⟨(allocated.trace.leftReadings (cache.atDomain firstPosition (firstSheet) i).anchors
      (cache.atDomain firstPosition (firstSheet) i).offsets).values vertex,
    (allocated.trace.leftReadings (cache.atDomain firstPosition (firstSheet) j).anchors
      (cache.atDomain firstPosition (firstSheet) j).offsets).values vertex⟩

/-- The two actual differential values on the neighboring retained horizontal trace and its arriving sheet. -/
@[expose] def rightValues {joined : LiftedSides.HorizontalCrossing request first nextPosition false false}
    (allocated : HorizontalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor)
    (cache : RegularMeshes.Numerics domains stage) (vertex : Fin (allocated.trace.vertices.rest.length + 1)) :
      PrimitivePoint :=
  ⟨(allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors
      (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets).values vertex,
    (allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors
      (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets).values vertex⟩

/-- The two actual centered path samples for a matched horizontal crossing, or the unit value for certified separation.
-/
@[expose] def Sample {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    (prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome) (cache :
      RegularMeshes.Numerics domains stage) : Type :=
  match prepared with
  | .matched allocated => CenteredBilinearPath.Sample
    (leftValues allocated cache) ×
      CenteredBilinearPath.Sample
        (rightValues allocated
        cache)
  | .separated _ => Unit

/-- Acquire both retained horizontal path samples for a match, preserving the unit result for a certified separation. -/
@[expose] def Sample.build {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    (prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome) (cache :
      RegularMeshes.Numerics domains stage) :
      Sample prepared cache :=
  match prepared with
  | .matched allocated => ⟨CenteredBilinearPath.Sample.build
    (leftValues allocated cache),
      CenteredBilinearPath.Sample.build
        (rightValues allocated
        cache)⟩
  | .separated _ => ()

/-- The actual path-area difference minus its retained endpoint correction, with zero for separation. -/
@[expose] def Sample.residual {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact (sample.1.originalArea - sample.2.originalArea) - (sample.1.endpoint - sample.2.endpoint)
  | separated _ => exact 0

/-- The paid original horizontal request bounds the squared norm of the retained centered residual. -/
theorem Sample.bound {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) (positive : 0 < tolerance)
    (later : HorizontalPrepared.index _ _ _ _ _ _ prepared ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.residual sample) ≤
      tolerance := by
  cases prepared with
  | matched allocated =>
      obtain ⟨left, right⟩ := sample
      exact (allocated.accuracy.accurate later
        (cache.atDomain firstPosition firstSheet i) (cache.atDomain nextPosition _ i)
        (cache.atDomain firstPosition firstSheet j) (cache.atDomain nextPosition _ j) left right).le
  | separated obstruction =>
      simpa only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.residual,
        Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self] using positive.le

/-- The actual area difference of the two retained horizontal paths, with zero for separation. -/
@[expose] def Sample.areaDifference {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.originalArea - sample.2.originalArea
  | separated _ => exact 0

/-- The difference of the two retained endpoint determinants, with zero for separation. -/
@[expose] def Sample.endpointDifference {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpoint - sample.2.endpoint
  | separated _ => exact 0

/-- The retained residual is the actual area difference minus the endpoint determinant difference. -/
theorem Sample.residual_eq {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.residual sample =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.areaDifference sample
      - Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointDifference
      sample := by
  cases prepared with
  | matched allocated => rfl
  | separated _ => exact (sub_self _).symm

/-- The sampled horizontal area difference reads the actual top and bottom perimeter contributions of the retained
clipped assemblies. -/
theorem Sample.areaDifference_eq_perimeters
    {joined : LiftedSides.HorizontalCrossing request first nextPosition false false}
    {allocated : HorizontalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor}
    {cache : RegularMeshes.Numerics domains stage} (sample :
      Sample (.matched allocated)
      cache)
    (leftAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get firstSheet).meshes.entries.get firstPosition)
      (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue (cache.atDomain firstPosition firstSheet
          i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue (cache.atDomain firstPosition firstSheet
            j).offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get (joined.crossing.next.sheet)).meshes.entries.get nextPosition)
      (fun column row point =>
        ⟨(cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors.alignedValue (cache.atDomain nextPosition
          (joined.crossing.next.sheet) i).offsets column row point,
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue (cache.atDomain nextPosition
            (joined.crossing.next.sheet) j).offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.areaDifference sample =
      leftPerimeter.top - rightPerimeter.bottom := by
  let leftValue := fun column row point => (⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
      (cache.atDomain firstPosition firstSheet i).offsets column row point,
    (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
      (cache.atDomain firstPosition firstSheet j).offsets column row point⟩ : Stokes.PrimitivePoint)
  let rightValue := fun column row point => (⟨(cache.atDomain nextPosition (joined.crossing.next.sheet)
    i).anchors.alignedValue
      (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets column row point,
    (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue
      (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets column row point⟩ : Stokes.PrimitivePoint)
  have leftArea : sample.1.originalArea = leftPerimeter.top := by
    rw [sample.1.originalArea_eq]
    have readback := allocated.trace.left_area_eq_top leftValue leftAssembly leftPerimeter
      ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_last.symm
    unfold CenteredBilinearPath.area at readback ⊢
    simp only [leftValues,
      allocated.trace.leftReadings_value, -eq_self, -iff_self]
    exact readback
  have rightArea : sample.2.originalArea = rightPerimeter.bottom := by
    rw [sample.2.originalArea_eq]
    have readback := allocated.trace.right_area rightValue
    have depthEq : ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth =
        ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).depth := by
      rw [request.mesh_depth, request.mesh_depth]
    have depthReadback := congrArg (joined.side.rightArea rightValue) depthEq
    rw [depthReadback, joined.side.right_boundary_eq_bottom rightValue rightAssembly rightPerimeter
      (HorizontalCrossing.adjacent joined |>.trans
        ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).y_first.symm)] at readback
    unfold CenteredBilinearPath.area at readback ⊢
    simp only [rightValues,
      allocated.trace.rightReadings_value, -eq_self, -iff_self]
    exact readback
  change sample.1.originalArea - sample.2.originalArea = _
  rw [leftArea, rightArea]

/-- Canonical endpoint determinant difference; the sample retains the computed value. -/
@[expose] def endpointSpecification {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    (prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome) (cache : RegularMeshes.Numerics domains stage) :
        Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | @matched joined allocated =>
      exact joined.side.leftChord (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet j).offsets column row point⟩) -
        joined.side.rightChord (fun column row point =>
        ⟨(cache.atDomain nextPosition _ i).anchors.alignedValue
            (cache.atDomain nextPosition _ i).offsets column row point,
          (cache.atDomain nextPosition _ j).anchors.alignedValue
            (cache.atDomain nextPosition _ j).offsets column row point⟩)
  | separated _ => exact 0

/-- The retained endpoint determinant difference equals the chord difference of the actual matched side. -/
theorem Sample.endpointDifference_eq_specification {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) :
      Sample.endpointDifference
      sample =
      endpointSpecification
      prepared cache := by
  cases prepared with
  | @matched joined allocated =>
      unfold
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointDifference
        CrossingSamples.HorizontalPrepared.endpointSpecification
      apply congrArg₂ (fun left right : Data.Gaussian.Basic.Canonical => left - right)
      · apply allocated.trace.left_endpoint_eq_chord
        intro vertex
        simp only [leftValues,
          allocated.trace.leftReadings_value, -eq_self, -iff_self]
        rfl
      · apply allocated.trace.right_endpoint_eq_chord
        intro vertex
        simp only [rightValues,
          allocated.trace.rightReadings_value, -eq_self, -iff_self]
        rfl
  | separated obstruction => rfl

/-- The endpoint jump of the two retained path samples, with zero for separation. -/
@[expose] def Sample.endpointJump {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpointJump sample.2
  | separated _ => exact 0

/-- The actual matched horizontal side jump read from the retained anchor and offset caches, with zero for separation.
-/
@[expose] def jumpSpecification {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    (prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome) (cache : RegularMeshes.Numerics domains stage) :
        Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | @matched joined allocated =>
      exact joined.side.jump (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet j).offsets column row point⟩) (fun column row point =>
        ⟨(cache.atDomain nextPosition _ i).anchors.alignedValue
            (cache.atDomain nextPosition _ i).offsets column row point,
          (cache.atDomain nextPosition _ j).anchors.alignedValue
            (cache.atDomain nextPosition _ j).offsets column row point⟩)
  | separated _ => exact 0

/-- The retained sample jump reads the actual matched-side jump specification. -/
theorem Sample.endpointJump_eq_specification {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump
      sample =
      jumpSpecification
      prepared cache := by
  cases prepared with
  | @matched joined allocated =>
      unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump
        CrossingSamples.HorizontalPrepared.jumpSpecification
      apply allocated.trace.endpointJump_eq
      · intro vertex
        simp only [leftValues,
          allocated.trace.leftReadings_value, -eq_self, -iff_self]
        rfl
      · intro vertex
        simp only [rightValues,
          allocated.trace.rightReadings_value, -eq_self, -iff_self]
        rfl
  | separated obstruction => rfl

/-- The retained endpoint increment error between the two actual path samples, with zero for separation. -/
@[expose] def Sample.endpointIncrementError {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpointIncrementError sample.2
  | separated _ => exact 0

/-- The actual endpoint determinant difference splits into the retained jump and endpoint increment error. -/
theorem Sample.endpointDifference_eq_jump {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointDifference
      sample = Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump
      sample +
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointIncrementError
      sample := by
  cases prepared with
  | matched allocated => exact sample.1.endpoint_difference sample.2
  | separated obstruction => exact (add_zero _).symm

/-- At the paid stage, normalized horizontal readings bound the area difference minus the retained endpoint jump by four
times the tolerance. -/
theorem Sample.normalized_jump_bound {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache.normalize) (positive : 0 < tolerance)
    (later : HorizontalPrepared.index _ _ _ _ _ _ prepared ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.areaDifference sample
      - Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump sample)
      ≤ 4 * tolerance := by
  cases prepared with
  | @matched joined allocated =>
      have firstZero : (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).corners.values 0 = 0 := by
        rw [cache.normalize_atDomain]
        exact (cache.atDomain nextPosition joined.crossing.next.sheet i).normalize_origin
      have secondZero : (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).corners.values 0 = 0 := by
        rw [cache.normalize_atDomain]
        exact (cache.atDomain nextPosition joined.crossing.next.sheet j).normalize_origin
      exact (allocated.jump_accurate_of_zero later
        (cache.normalize.atDomain firstPosition firstSheet i) (cache.normalize.atDomain nextPosition
          joined.crossing.next.sheet i)
        (cache.normalize.atDomain firstPosition firstSheet j) (cache.normalize.atDomain nextPosition
          joined.crossing.next.sheet j)
        firstZero secondZero sample.1 sample.2).le
  | separated obstruction =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 4 * tolerance
      rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le

end HorizontalPrepared

namespace VerticalPrepared

/-- The two actual differential values on the first retained vertical trace, read from its original anchor and offset
cache. -/
@[expose] def leftValues {joined : LiftedSides.VerticalCrossing request first nextPosition false false}
    (allocated : VerticalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor)
    (cache : RegularMeshes.Numerics domains stage) (vertex : Fin (allocated.trace.vertices.rest.length + 1)) :
      PrimitivePoint :=
  ⟨(allocated.trace.leftReadings (cache.atDomain firstPosition (firstSheet) i).anchors
      (cache.atDomain firstPosition (firstSheet) i).offsets).values vertex,
    (allocated.trace.leftReadings (cache.atDomain firstPosition (firstSheet) j).anchors
      (cache.atDomain firstPosition (firstSheet) j).offsets).values vertex⟩

/-- The two actual differential values on the neighboring retained vertical trace and its arriving sheet. -/
@[expose] def rightValues {joined : LiftedSides.VerticalCrossing request first nextPosition false false}
    (allocated : VerticalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor)
    (cache : RegularMeshes.Numerics domains stage) (vertex : Fin (allocated.trace.vertices.rest.length + 1)) :
      PrimitivePoint :=
  ⟨(allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors
      (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets).values vertex,
    (allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors
      (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets).values vertex⟩

/-- The two actual centered path samples for a matched vertical crossing, or the unit value for certified separation. -/
@[expose] def Sample {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    (prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome) (cache :
      RegularMeshes.Numerics domains stage) : Type :=
  match prepared with
  | .matched allocated => CenteredBilinearPath.Sample
    (leftValues allocated cache) ×
      CenteredBilinearPath.Sample
        (rightValues allocated cache)
  | .separated _ => Unit

/-- Acquire both retained vertical path samples for a match, preserving the unit result for a certified separation. -/
@[expose] def Sample.build {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    (prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome) (cache :
      RegularMeshes.Numerics domains stage) :
      Sample prepared cache :=
  match prepared with
  | .matched allocated => ⟨CenteredBilinearPath.Sample.build
    (leftValues allocated cache),
      CenteredBilinearPath.Sample.build
        (rightValues allocated
        cache)⟩
  | .separated _ => ()

/-- The actual path-area difference minus its retained endpoint correction, with zero for separation. -/
@[expose] def Sample.residual {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact (sample.1.originalArea - sample.2.originalArea) - (sample.1.endpoint - sample.2.endpoint)
  | separated _ => exact 0

/-- The paid original vertical request bounds the squared norm of the retained centered residual. -/
theorem Sample.bound {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      (positive : 0 < tolerance)
    (later : VerticalPrepared.index _ _ _ _ _ _ prepared ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.residual sample) ≤
      tolerance := by
  cases prepared with
  | matched allocated =>
      obtain ⟨left, right⟩ := sample
      exact (allocated.accuracy.accurate later
        (cache.atDomain firstPosition firstSheet i) (cache.atDomain nextPosition _ i)
        (cache.atDomain firstPosition firstSheet j) (cache.atDomain nextPosition _ j) left right).le
  | separated obstruction =>
      simpa only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.residual,
        Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self] using positive.le

/-- The actual area difference of the two retained vertical paths, with zero for separation. -/
@[expose] def Sample.areaDifference {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.originalArea - sample.2.originalArea
  | separated _ => exact 0

/-- The difference of the two retained endpoint determinants, with zero for separation. -/
@[expose] def Sample.endpointDifference {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpoint - sample.2.endpoint
  | separated _ => exact 0

/-- The retained residual is the actual area difference minus the endpoint determinant difference. -/
theorem Sample.residual_eq {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor outcome} {cache :
      RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.residual sample =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.areaDifference sample -
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointDifference
      sample := by
  cases prepared with
  | matched allocated => rfl
  | separated _ => exact (sub_self _).symm

/-- The sampled vertical area difference reads the actual right and left perimeter contributions of the retained clipped
assemblies. -/
theorem Sample.areaDifference_eq_perimeters
    {joined : LiftedSides.VerticalCrossing request first nextPosition false false}
    {allocated : VerticalCrossing.AreaRequest joined (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor}
    {cache : RegularMeshes.Numerics domains stage} (sample :
      Sample (.matched allocated)
      cache)
    (leftAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get firstSheet).meshes.entries.get firstPosition)
      (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue (cache.atDomain firstPosition firstSheet
          i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue (cache.atDomain firstPosition firstSheet
            j).offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get (joined.crossing.next.sheet)).meshes.entries.get nextPosition)
      (fun column row point =>
        ⟨(cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors.alignedValue (cache.atDomain nextPosition
          (joined.crossing.next.sheet) i).offsets column row point,
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue (cache.atDomain nextPosition
            (joined.crossing.next.sheet) j).offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.areaDifference sample =
      leftPerimeter.right - rightPerimeter.left := by
  let leftValue := fun column row point => (⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
      (cache.atDomain firstPosition firstSheet i).offsets column row point,
    (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
      (cache.atDomain firstPosition firstSheet j).offsets column row point⟩ : Stokes.PrimitivePoint)
  let rightValue := fun column row point => (⟨(cache.atDomain nextPosition (joined.crossing.next.sheet)
    i).anchors.alignedValue
      (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets column row point,
    (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue
      (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets column row point⟩ : Stokes.PrimitivePoint)
  have leftArea : sample.1.originalArea = leftPerimeter.right := by
    rw [sample.1.originalArea_eq]
    have readback := allocated.trace.left_area_eq_right leftValue leftAssembly leftPerimeter
      ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_last.symm
    unfold CenteredBilinearPath.area at readback ⊢
    simp only [leftValues,
      allocated.trace.leftReadings_value, -eq_self, -iff_self]
    exact readback
  have rightArea : sample.2.originalArea = rightPerimeter.left := by
    rw [sample.2.originalArea_eq]
    have readback := allocated.trace.right_area rightValue
    have depthEq : ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth =
        ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).depth := by
      rw [request.mesh_depth, request.mesh_depth]
    have depthReadback := congrArg (joined.side.rightArea rightValue) depthEq
    rw [depthReadback, joined.side.right_boundary_eq_left rightValue rightAssembly rightPerimeter
      (VerticalCrossing.adjacent joined |>.trans
        ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).x_first.symm)] at readback
    unfold CenteredBilinearPath.area at readback ⊢
    simp only [rightValues,
      allocated.trace.rightReadings_value, -eq_self, -iff_self]
    exact readback
  change sample.1.originalArea - sample.2.originalArea = _
  rw [leftArea, rightArea]

/-- Canonical endpoint determinant difference; the sample retains the computed value. -/
@[expose] def endpointSpecification {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    (prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome) (cache : RegularMeshes.Numerics domains stage) :
        Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | @matched joined allocated =>
      exact joined.side.leftChord (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet j).offsets column row point⟩) -
        joined.side.rightChord (fun column row point =>
        ⟨(cache.atDomain nextPosition _ i).anchors.alignedValue
            (cache.atDomain nextPosition _ i).offsets column row point,
          (cache.atDomain nextPosition _ j).anchors.alignedValue
            (cache.atDomain nextPosition _ j).offsets column row point⟩)
  | separated _ => exact 0

/-- The retained endpoint determinant difference equals the chord difference of the actual matched side. -/
theorem Sample.endpointDifference_eq_specification {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      :
      Sample.endpointDifference
      sample =
      endpointSpecification
      prepared cache := by
  cases prepared with
  | @matched joined allocated =>
      unfold
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointDifference
        CrossingSamples.VerticalPrepared.endpointSpecification
      apply congrArg₂ (fun left right : Data.Gaussian.Basic.Canonical => left - right)
      · apply allocated.trace.left_endpoint_eq_chord
        intro vertex
        simp only [leftValues,
          allocated.trace.leftReadings_value, -eq_self, -iff_self]
        rfl
      · apply allocated.trace.right_endpoint_eq_chord
        intro vertex
        simp only [rightValues,
          allocated.trace.rightReadings_value, -eq_self, -iff_self]
        rfl
  | separated obstruction => rfl

/-- The endpoint jump of the two retained path samples, with zero for separation. -/
@[expose] def Sample.endpointJump {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpointJump sample.2
  | separated _ => exact 0

/-- The actual matched vertical side jump read from the retained anchor and offset caches, with zero for separation. -/
@[expose] def jumpSpecification {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    (prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome) (cache : RegularMeshes.Numerics domains stage) :
        Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | @matched joined allocated =>
      exact joined.side.jump (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue
            (cache.atDomain firstPosition firstSheet j).offsets column row point⟩) (fun column row point =>
        ⟨(cache.atDomain nextPosition _ i).anchors.alignedValue
            (cache.atDomain nextPosition _ i).offsets column row point,
          (cache.atDomain nextPosition _ j).anchors.alignedValue
            (cache.atDomain nextPosition _ j).offsets column row point⟩)
  | separated _ => exact 0

/-- The retained sample jump reads the actual matched-side jump specification. -/
theorem Sample.endpointJump_eq_specification {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump
      sample =
      jumpSpecification
      prepared cache := by
  cases prepared with
  | @matched joined allocated =>
      unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump
        CrossingSamples.VerticalPrepared.jumpSpecification
      apply allocated.trace.endpointJump_eq
      · intro vertex
        simp only [leftValues,
          allocated.trace.leftReadings_value, -eq_self, -iff_self]
        rfl
      · intro vertex
        simp only [rightValues,
          allocated.trace.rightReadings_value, -eq_self, -iff_self]
        rfl
  | separated obstruction => rfl

/-- The retained endpoint increment error between the two actual path samples, with zero for separation. -/
@[expose] def Sample.endpointIncrementError {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      : Data.Gaussian.Basic.Canonical := by
  cases prepared with
  | matched allocated => exact sample.1.endpointIncrementError sample.2
  | separated _ => exact 0

/-- The actual endpoint determinant difference splits into the retained jump and endpoint increment error. -/
theorem Sample.endpointDifference_eq_jump {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared cache)
      :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointDifference sample
      = Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump sample +
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointIncrementError
      sample := by
  cases prepared with
  | matched allocated => exact sample.1.endpoint_difference sample.2
  | separated obstruction => exact (add_zero _).symm

/-- At the paid stage, normalized vertical readings bound the area difference minus the retained endpoint jump by four
times the tolerance. -/
theorem Sample.normalized_jump_bound {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome} {cache : RegularMeshes.Numerics domains stage}
    (sample : Sample prepared
      cache.normalize) (positive : 0 < tolerance)
    (later : VerticalPrepared.index _ _ _ _ _ _ prepared ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.areaDifference sample -
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump sample) ≤ 4
      * tolerance := by
  cases prepared with
  | @matched joined allocated =>
      have firstZero : (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).corners.values 0 = 0 := by
        rw [cache.normalize_atDomain]
        exact (cache.atDomain nextPosition joined.crossing.next.sheet i).normalize_origin
      have secondZero : (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).corners.values 0 = 0 := by
        rw [cache.normalize_atDomain]
        exact (cache.atDomain nextPosition joined.crossing.next.sheet j).normalize_origin
      exact (allocated.jump_accurate_of_zero later
        (cache.normalize.atDomain firstPosition firstSheet i) (cache.normalize.atDomain nextPosition
          joined.crossing.next.sheet i)
        (cache.normalize.atDomain firstPosition firstSheet j) (cache.normalize.atDomain nextPosition
          joined.crossing.next.sheet j)
        firstZero secondZero sample.1 sample.2).le
  | separated obstruction =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 4 * tolerance
      rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le

end VerticalPrepared

namespace CrossingRequests
variable {retained : CrossingBank request mesh}
  (allocated : CrossingRequests
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained)
  (cache : Numerics domains stage)

set_option genInjectivity false in
/-- The complete retained horizontal and vertical crossing sample banks.

Every matched pair carries both actual path samples; every certified separation keeps its original zero contribution. -/
structure Samples where
  /-- The actual horizontal samples indexed by original face, sheet and neighboring face. -/ horizontal :
    Data.Vector.DependentVector (fun a : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun b : Fin 2 => Data.Vector.DependentVector (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample
        (((allocated.horizontal.get a).get b).get c) cache)))
  /-- The actual vertical samples indexed by original face, sheet and neighboring face. -/ vertical :
    Data.Vector.DependentVector (fun a : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun b : Fin 2 => Data.Vector.DependentVector (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample
        (((allocated.vertical.get a).get b).get c) cache)))

constructive_injectivity Samples

/-- Acquire the two complete crossing sample banks on the supplied original numerical cache. -/
@[expose] def Samples.build : Samples
  allocated cache :=
  ⟨DependentVector.ofFn (fun a => DependentVector.ofFn (fun b => DependentVector.ofFn (fun c =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.build
        (((allocated.horizontal.get a).get b).get c) cache))),
    DependentVector.ofFn (fun a => DependentVector.ofFn (fun b => DependentVector.ofFn (fun c =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.build
        (((allocated.vertical.get a).get b).get c) cache)))⟩

/-- Every retained horizontal sample satisfies the original tolerance once the common crossing request is paid. -/
theorem Samples.horizontal_bound (samples :
  Samples allocated cache) (positive
  : 0 < tolerance)
    (later : allocated.index ≤ stage) (a : Fin faces.regulars.length) (b : Fin 2) (c : Fin faces.regulars.length) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.residual
      (prepared := (((allocated.horizontal.get a).get b).get c)) (cache := cache)
      (((samples.horizontal.get a).get b).get c)) ≤ tolerance :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.bound _ positive
    ((allocated.horizontal_le a b c).trans later)

/-- Every retained vertical sample satisfies the original tolerance once the common crossing request is paid. -/
theorem Samples.vertical_bound (samples :
  Samples allocated cache) (positive
  : 0 < tolerance)
    (later : allocated.index ≤ stage) (a : Fin faces.regulars.length) (b : Fin 2) (c : Fin faces.regulars.length) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.residual
      (prepared := (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c)) ≤ tolerance :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.bound _ positive
    ((allocated.vertical_le a b c).trans later)

end CrossingRequests

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
