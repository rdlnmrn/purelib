module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveArea
import Purelib.Riemann.Readings.RectangularPointReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison

@[expose] public section

/-! Newton bounds for a retained face-contained side segment at arbitrary
endpoints. No triangle-edge placement or face-corner assumption is required,
so the reference can serve a prefix ending at a fine boundary vertex. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.PreparedClearPathModels (Owner)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide ParentOnBoundary)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences (Reference)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison (PrimitiveSample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {ambient : Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner}
  {differential : Differential genus} {parentSheet : Fin 2}
  {entered : EnteredPath models piece.path
    differential parentSheet}
  {bandAmbient : Box} {current :
    Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : Purelib.Riemann.RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {fixed : Purelib.Riemann.RootContinuation.NewtonBandDifferentials.DifferentialProfile profile differential.exponent}
  {target tolerance : Rational}

/-- Reuse the fixed reference and its original parent cache. The auxiliary Newton resampling is proof-local; reading a
later face bank does not execute another preparation or integration. Both refinement counts cancel. -/
theorem newton_point_density_bound (reference : PrimitiveReferences.Reference entered tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    {index : Nat} (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = start) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq (readings.values last - readings.values first) ≤ 3 * tolerance + 4 *
      (PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed band.error *
      Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  let sampled := PrimitiveSample.build band reference.request.toPrimitiveSumRequest
    entered.cache.proper (fun _ member => PreparedSegmentBoundaryGeometry.segment_parent_boundary entered.cache
      firstInside lastInside side member)
  have numerical := PrimitiveSample.integral_density_bound sampled (Data.Gaussian.Norm.Basic.normSq (finish -
    start)) piece.mesh.depth
    (PreparedSegmentBoundaryGeometry.segment_parentCount (piece := piece) entered.cache)
    (fun _ member => (PreparedSegmentBoundaryGeometry.segment_parent_movement (piece := piece) entered.cache member).le)
  have referenceBound : Data.Gaussian.Norm.Basic.normSq reference.value ≤
      2 * (tolerance / 4 + PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed band.error *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
    have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
      (reference.request.primitiveSum - sampled.sample.integralSample) sampled.sample.integralSample).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (PrimitiveSample.accurate sampled).le numerical) (by decide))
    rw [sub_add_cancel, ← reference.value_eq] at estimate
    exact estimate
  have accurate := PointReferences.point_accurate reference later data readings first last firstEq lastEq
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((readings.values last - readings.values first) - reference.value) reference.value).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct accurate.le referenceBound) (by decide))
  rw [sub_add_cancel] at estimate
  apply estimate.trans_eq
  calc
    _ = 2 * tolerance + (tolerance / 4) * 4 + 4 * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
      band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
      ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1

/-- Reuse the fixed reference and its original parent cache. The auxiliary Newton resampling is proof-local; reading a
later face bank does not execute another preparation or integration. Both refinement counts cancel. -/
theorem newton_point_bound (reference : PrimitiveReferences.Reference entered tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    {index : Nat} (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = start) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq (readings.values last - readings.values first) ≤ 3 * tolerance + 4 * target
      := by
  have densityNonnegative := PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
    (sample := band.sample) (differential := differential) fixed band.errorPositive.le
  have movement := (band.sample.output.box.normSq_sub_le_diagonalSq lastInside firstInside).trans
    (band.sample.output.band.diagonalSq_le band.sample.output.radiusPositive)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement densityNonnegative).trans
    ((PreparedNewtonBandSamples.Sample.preparedDensity_movement_le band.sample fixed band.error_le_one
      band.radius_le_one).trans band.paid)
  exact (newton_point_density_bound reference band
    firstInside lastInside side later data readings
    first last firstEq lastEq).trans
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid (by decide)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences
