module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.NoisyPathArea
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonSideArea
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Path

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.State

open Purelib.Topology.Polygon

@[expose] public section

/-! The Newton side-area estimate for a conjugated first component.
Conjugation preserves the pointwise squared-norm bounds; no holomorphic
vanishing assertion is applied to the energy pair. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonConjugateSideArea
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation (SideGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (Request PairRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Rat.Fraction.Compatibility

/-- Gaussian conjugation preserves the difference of the two original values. -/
private theorem conjugate_sub (first last : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.conj (first -
  last) = Data.Gaussian.Basic.conj first - Data.Gaussian.Basic.conj last := by
  apply Data.Gaussian.Basic.ext
  · rfl
  · simp only [Data.Gaussian.Basic.conj, Data.Gaussian.Basic.sub_im]; ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {count : Nat} {points : Fin (count + 1) → Purelib.Data.Gaussian.Basic.Canonical} {geometry :
    SideGeometry models points}
  {sheet : Fin 2} {domain : PeriodDomain models sheet}
    {left right : Differential genus}
  {allowance : Rational}

/-- All prefix and edge references are constructed before selecting the shared numerical bank. No caller primitive
magnitude or increment estimate remains. -/
theorem conjugate_area_bound (budget : NoisyPathArea.LengthErrorBudget count allowance)
    (request : SideGeometry.Request geometry domain left right budget.tolerance)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget density : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (points vertex))
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (points first) (points last))
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (points vertex))
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (points first) (points
      last))
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    {index : Nat} (later : request.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives domain left index) (rightData : PrimitiveData.DomainPrimitives domain
      right index)
    (leftReadings : RectangularPointReadings.PointReadings leftData.anchors leftData.offsets points)
    (rightReadings : RectangularPointReadings.PointReadings rightData.anchors rightData.offsets points)
    {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (valuesEq : ∀ vertex, values vertex = ⟨conj (leftReadings.values vertex), rightReadings.values vertex⟩)
    (sample : CenteredBilinearPath.Sample values) (lengths : Fin count → Fraction.Rational)
    (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (movement : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (points edge.succ - points edge.castSucc) =
      (lengths edge)^2) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) *
        (4 * density + 3) * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have pairBound (first last : Fin (count + 1))
      (pair : SideGeometry.PairRequest geometry domain left right budget.tolerance first last)
      (pairLater : pair.reference.index ≤ index) :
      PrimitivePoint.Bounded ((values last).sub (values first))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq (points last - points first)) :=
          by
    rw [valuesEq last, valuesEq first]
    have bound := pair.reference.point_density_bound leftBand rightBand
      (leftInside first) (leftInside last) (leftSide first last)
      (rightInside first) (rightInside last) (rightSide first last) leftDensity rightDensity
      pairLater leftData rightData leftReadings rightReadings first last rfl rfl
    refine ⟨?_, bound.2⟩
    change Data.Gaussian.Basic.Canonical.normSq (Data.Gaussian.Basic.conj (leftReadings.values last) -
      Data.Gaussian.Basic.conj (leftReadings.values first)) ≤ _
    rw [← conjugate_sub, ←
      Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq_conj,
      Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact bound.1
  have magnitudeNonnegative : 0 ≤ 3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) budget.tolerance_positive.le)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        densityNonnegative)
        leftBand.sample.output.box.diagonalSq_nonneg)
  apply budget.centered_area_bound sample lengths magnitudeNonnegative densityNonnegative nonnegative
  · intro vertex
    rw [sample.centered_eq]
    have bound := pairBound 0 vertex (request.prefixes.get vertex) ((request.prefixes_later vertex).trans later)
    have movementBound := leftBand.sample.output.box.normSq_sub_le_diagonalSq (leftInside vertex) (leftInside 0)
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at movementBound bound
    have paid := Fraction.Order.Arithmetic.add_le_add_direct (le_refl (3 * budget.tolerance))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) densityNonnegative))
    exact ⟨bound.1.trans paid, bound.2.trans paid⟩
  · intro edge
    have bound := pairBound edge.castSucc edge.succ (request.edges.get edge) ((request.edges_later edge).trans later)
    have step := movement edge
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at step bound
    rw [step] at bound
    exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonConjugateSideArea
