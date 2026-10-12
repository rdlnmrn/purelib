module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
public import Purelib.Integration.Path.NoisyPathArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! The finite request discharges both component bounds for the full area of
one retained side. The estimate depends on total geometric length, not the
number of samples; each distinct owner junction is paid by the error budget. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonSideArea

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {count : Nat} {points : Fin (count + 1) → Gaussian.Basic.Canonical} {geometry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points}
  {sheet : Fin 2} {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {left right :
    Hyperelliptic.Differentials.Basic.Differential genus}
  {allowance : Fraction.Rational}

/-- All prefix and edge references are constructed before selecting the shared
numerical bank. No caller primitive magnitude or increment estimate remains. -/
theorem area_bound (budget : Path.NoisyPathArea.LengthErrorBudget count allowance)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request geometry domain left right
      budget.tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget density : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (points vertex))
    (leftSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box (points first) (points
      last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (points vertex))
    (rightSide : ∀ first last, Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box (points first)
      (points last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    {index : Nat} (later : request.index ≤ index)
    (leftData : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain left index) (rightData :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain right index)
    (leftReadings : Readings.RectangularPointReadings.PointReadings leftData.anchors leftData.offsets points)
    (rightReadings : Readings.RectangularPointReadings.PointReadings rightData.anchors rightData.offsets points)
    {values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint}
    (valuesEq : ∀ vertex, values vertex = ⟨leftReadings.values vertex, rightReadings.values vertex⟩)
    (sample : Periods.CenteredBilinearPath.Sample values) (lengths : Fin count → Fraction.Rational)
    (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (movement : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (points edge.succ - points edge.castSucc) =
      (lengths edge)^2) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) *
        (4 * density + 3) * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have pairBound (first last : Fin (count + 1))
      (pair : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest geometry domain left
        right budget.tolerance first last)
      (pairLater : pair.reference.index ≤ index) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((values last).sub (values first))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq (points last - points first)) := by
    rw [valuesEq last, valuesEq first]
    exact pair.reference.point_density_bound leftBand rightBand
      (leftInside first) (leftInside last) (leftSide first last)
      (rightInside first) (rightInside last) (rightSide first last) leftDensity rightDensity
      pairLater leftData rightData leftReadings rightReadings first last rfl rfl
  have magnitudeNonnegative : 0 ≤ 3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) budget.tolerance_positive.le)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        densityNonnegative)
        (leftBand.sample.output.box.normSq_sub_le_diagonalSq (leftInside 0) (leftInside 0) |>.trans' (by
          exact Gaussian.Norm.Basic.normSq_nonneg _)))
  apply budget.centered_area_bound sample lengths magnitudeNonnegative densityNonnegative nonnegative
  · intro vertex
    rw [sample.centered_eq]
    have bound := pairBound 0 vertex (request.prefixes.get vertex) ((request.prefixes_later vertex).trans later)
    have movementBound := leftBand.sample.output.box.normSq_sub_le_diagonalSq (leftInside vertex) (leftInside 0)
    have paid := Fraction.Order.Arithmetic.add_le_add_direct (le_refl (3 * budget.tolerance))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) densityNonnegative))
    exact ⟨bound.1.trans paid, bound.2.trans paid⟩
  · intro edge
    have bound := pairBound edge.castSucc edge.succ (request.edges.get edge) ((request.edges_later edge).trans later)
    rw [movement edge] at bound
    exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonSideArea
