module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerIncrements
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
public import Purelib.Integration.Path.EndpointJump
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
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
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerIncrements

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

@[expose] public section

/-! Actual matched endpoint jumps compare with the fixed shared corner determinant. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
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

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

/-- Two retained endpoint errors bounded by four times a tolerance give a difference error bounded by sixteen times that
tolerance. -/
private theorem difference_error {a b c d : Data.Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
    (left : Data.Gaussian.Norm.Basic.normSq (a - c) ≤ 4 * tolerance) (right :
      Data.Gaussian.Norm.Basic.normSq (b - d) ≤ 4 * tolerance) :
    Data.Gaussian.Norm.Basic.normSq ((a - b) - (c - d)) ≤ 16 * tolerance := by
  have equal : (a - b) - (c - d) = (a - c) - (b - d) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right) (by decide)).trans_eq (by
      ring1))

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual normalized horizontal endpoint jump is close to its retained shared-corner determinant.

The paid four grid requests and both original magnitude references bound the discrepancy by the stated tolerance factor.
-/
theorem corner_jump_bound
    (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {i j : Fin genus} {stage : Nat}
    (firstMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (secondMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {tolerance : Fraction.Rational} (positive : 0 < tolerance) (small : 16 * tolerance ≤ 1)
    {liBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential i))}
    (li : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy liBounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance) (liLater : li.index ≤ stage)
    {riBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential i))}
    (ri : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy riBounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance) (riLater : ri.index ≤ stage)
    {ljBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential j))}
    (lj : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy ljBounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance) (ljLater : lj.index ≤ stage)
    {rjBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential j))}
    (rj : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy rjBounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance) (rjLater : rj.index ≤ stage)
    (cache : RegularMeshes.Numerics domains stage)
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet i).anchors
          (cache.normalize.atDomain firstPosition firstSheet i).offsets).values vertex,
        (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet j).anchors
          (cache.normalize.atDomain firstPosition firstSheet j).offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).anchors
          (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).offsets).values vertex,
        (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).anchors
          (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).offsets).values vertex⟩))
    : Data.Gaussian.Norm.Basic.normSq (left.endpointJump right -
        Numerics.cornerJump cache.normalize i j firstPosition nextPosition firstSheet joined.crossing.next.sheet 3 2) ≤
      512 * (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * tolerance := by
  let liGrid := GridPrimitiveAccuracy.atIndex li stage liLater
  have liPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct liGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have liOrigin := (HorizontalCrossing.left_corner_origin_bound joined trace liGrid
    (cache.normalize.atDomain firstPosition firstSheet i)).trans liPaid
  have liIncrement := (HorizontalCrossing.left_corner_increment_bound joined trace liGrid
    (cache.normalize.atDomain firstPosition firstSheet i)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct liGrid.accurate.le
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
  let riGrid := GridPrimitiveAccuracy.atIndex ri stage riLater
  have riPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct riGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have riOrigin := (HorizontalCrossing.right_corner_origin_bound joined trace riGrid
    (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i)).trans riPaid
  let ljGrid := GridPrimitiveAccuracy.atIndex lj stage ljLater
  have ljPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ljGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have ljOrigin := (HorizontalCrossing.left_corner_origin_bound joined trace ljGrid
    (cache.normalize.atDomain firstPosition firstSheet j)).trans ljPaid
  have ljIncrement := (HorizontalCrossing.left_corner_increment_bound joined trace ljGrid
    (cache.normalize.atDomain firstPosition firstSheet j)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ljGrid.accurate.le
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
  let rjGrid := GridPrimitiveAccuracy.atIndex rj stage rjLater
  have rjPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rjGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have rjOrigin := (HorizontalCrossing.right_corner_origin_bound joined trace rjGrid
    (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j)).trans rjPaid
  have jumpError : PrimitivePoint.Bounded ((⟨
      (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet i).anchors
        (cache.normalize.atDomain firstPosition firstSheet i).offsets).values 0 -
      (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).anchors
        (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).offsets).values 0,
      (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet j).anchors
        (cache.normalize.atDomain firstPosition firstSheet j).offsets).values 0 -
      (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).anchors
        (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).offsets).values 0⟩ :
          Stokes.PrimitivePoint).sub
      ((Numerics.cornerPair cache.normalize i j firstPosition firstSheet 3).sub
        (Numerics.cornerPair cache.normalize i j nextPosition joined.crossing.next.sheet 0))) (16 * tolerance) :=
    ⟨by
      have scalar := difference_error liOrigin riOrigin
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar, by
      have scalar := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds.difference_error ljOrigin
        rjOrigin
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar⟩
  have incrementError : PrimitivePoint.Bounded
      ((left.centered (Fin.last trace.vertices.rest.length)).sub
        ((Numerics.cornerPair cache.normalize i j firstPosition firstSheet 2).sub
          (Numerics.cornerPair cache.normalize i j firstPosition firstSheet 3)))
      (16 * tolerance) := by
    rw [left.centered_eq]
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at liIncrement ljIncrement
    exact ⟨liIncrement, ljIncrement⟩
  have estimate := Numerics.normalized_corner_jump_perturbation
    firstMagnitude secondMagnitude firstLater secondLater cache
    firstPosition nextPosition firstSheet joined.crossing.next.sheet 3 2 _ _
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small jumpError incrementError
  exact estimate.trans_eq (by ring1)

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual normalized vertical endpoint jump is close to its retained shared-corner determinant.

The paid four grid requests and both original magnitude references bound the discrepancy by the stated tolerance factor.
-/
theorem corner_jump_bound
    (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) {i j : Fin genus} {stage : Nat}
    (firstMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (secondMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {tolerance : Fraction.Rational} (positive : 0 < tolerance) (small : 16 * tolerance ≤ 1)
    {liBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential i))}
    (li : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy liBounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance) (liLater : li.index ≤ stage)
    {riBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential i))}
    (ri : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy riBounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance) (riLater : ri.index ≤ stage)
    {ljBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[firstPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential j))}
    (lj : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy ljBounds
      ((domains.get firstPosition).domain firstSheet).steps tolerance) (ljLater : lj.index ≤ stage)
    {rjBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds faces.regulars[nextPosition.val].clearance
      (PreparedPrimitiveSamples.differentialNumerator (PeriodMatrix.standardDifferential j))}
    (rj : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy rjBounds
      ((domains.get nextPosition).domain joined.crossing.next.sheet).steps tolerance) (rjLater : rj.index ≤ stage)
    (cache : RegularMeshes.Numerics domains stage)
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet i).anchors
          (cache.normalize.atDomain firstPosition firstSheet i).offsets).values vertex,
        (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet j).anchors
          (cache.normalize.atDomain firstPosition firstSheet j).offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).anchors
          (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).offsets).values vertex,
        (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).anchors
          (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).offsets).values vertex⟩))
    : Data.Gaussian.Norm.Basic.normSq (left.endpointJump right -
        Numerics.cornerJump cache.normalize i j firstPosition nextPosition firstSheet joined.crossing.next.sheet 1 2) ≤
      512 * (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * tolerance := by
  let liGrid := GridPrimitiveAccuracy.atIndex li stage liLater
  have liPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct liGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have liOrigin := (VerticalCrossing.left_corner_origin_bound joined trace liGrid
    (cache.normalize.atDomain firstPosition firstSheet i)).trans liPaid
  have liIncrement := (VerticalCrossing.left_corner_increment_bound joined trace liGrid
    (cache.normalize.atDomain firstPosition firstSheet i)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct liGrid.accurate.le
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
  let riGrid := GridPrimitiveAccuracy.atIndex ri stage riLater
  have riPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct riGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have riOrigin := (VerticalCrossing.right_corner_origin_bound joined trace riGrid
    (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i)).trans riPaid
  let ljGrid := GridPrimitiveAccuracy.atIndex lj stage ljLater
  have ljPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ljGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have ljOrigin := (VerticalCrossing.left_corner_origin_bound joined trace ljGrid
    (cache.normalize.atDomain firstPosition firstSheet j)).trans ljPaid
  have ljIncrement := (VerticalCrossing.left_corner_increment_bound joined trace ljGrid
    (cache.normalize.atDomain firstPosition firstSheet j)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ljGrid.accurate.le
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
  let rjGrid := GridPrimitiveAccuracy.atIndex rj stage rjLater
  have rjPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rjGrid.accurate.le
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have rjOrigin := (VerticalCrossing.right_corner_origin_bound joined trace rjGrid
    (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j)).trans rjPaid
  have jumpError : PrimitivePoint.Bounded ((⟨
      (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet i).anchors
        (cache.normalize.atDomain firstPosition firstSheet i).offsets).values 0 -
      (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).anchors
        (cache.normalize.atDomain nextPosition joined.crossing.next.sheet i).offsets).values 0,
      (trace.leftReadings (cache.normalize.atDomain firstPosition firstSheet j).anchors
        (cache.normalize.atDomain firstPosition firstSheet j).offsets).values 0 -
      (trace.rightReadings (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).anchors
        (cache.normalize.atDomain nextPosition joined.crossing.next.sheet j).offsets).values 0⟩ :
          Stokes.PrimitivePoint).sub
      ((Numerics.cornerPair cache.normalize i j firstPosition firstSheet 1).sub
        (Numerics.cornerPair cache.normalize i j nextPosition joined.crossing.next.sheet 0))) (16 * tolerance) :=
    ⟨by
      have scalar := difference_error liOrigin riOrigin
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar, by
      have scalar := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds.difference_error ljOrigin
        rjOrigin
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar⟩
  have incrementError : PrimitivePoint.Bounded
      ((left.centered (Fin.last trace.vertices.rest.length)).sub
        ((Numerics.cornerPair cache.normalize i j firstPosition firstSheet 2).sub
          (Numerics.cornerPair cache.normalize i j firstPosition firstSheet 1)))
      (16 * tolerance) := by
    rw [left.centered_eq]
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at liIncrement ljIncrement
    exact ⟨liIncrement, ljIncrement⟩
  have estimate := Numerics.normalized_corner_jump_perturbation
    firstMagnitude secondMagnitude firstLater secondLater cache
    firstPosition nextPosition firstSheet joined.crossing.next.sheet 1 2 _ _
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small jumpError incrementError
  exact estimate.trans_eq (by ring1)

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds
