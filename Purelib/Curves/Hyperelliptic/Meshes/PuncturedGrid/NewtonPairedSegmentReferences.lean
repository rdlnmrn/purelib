module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.Paths.PreparedBoundarySegments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Tactic.Ring

public section

/-! Both differential bounds use one covered comparison segment and the
specified shared face domain. The request constructs the parent caches and
reference sums; later point readings incur no new preparation or integration. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

open Purelib.Data.Nat

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {sheet : Fin 2} {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
  {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}

set_option genInjectivity false in
/-- Two original differential references sharing one covered segment and retained face domain.

Keep each differential's parent cache and reference request with one stage sufficient for both. -/
structure PairedReference (prepared : Face.SegmentPreparation
  models sheet segment)
    (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet) (left right :
      Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) where
  /-- The original covered-segment parent cache for the first differential. -/ leftParents :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared.piece.path left sheet
  /-- The original covered-segment parent cache for the second differential. -/ rightParents :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared.piece.path right sheet
  /-- The first differential's original reference on the retained entered domain. -/ leftReference :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference (prepared.entered domain left leftParents)
    tolerance
  /-- The second differential's original reference on the same retained entered domain. -/ rightReference :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference (prepared.entered domain right rightParents)
    tolerance
  /-- The common sufficient grid stage of both original reference requests. -/ index : Nat
  /-- The first original reference is ready by the retained common stage. -/ left_later :
    leftReference.budget.grid.index ≤ index
  /-- The second original reference is ready by the retained common stage. -/ right_later :
    rightReference.budget.grid.index ≤ index

constructive_injectivity PairedReference

namespace PairedReference

variable {prepared : Face.SegmentPreparation models sheet segment}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet}
  {left right : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance : Fraction.Rational}

/-- Prepare both differential parent caches and retain their common sufficient stage.

The original covered segment and domain determine both retained references.
Their exact grid stages select the same maximum, sufficient for either reading. -/
@[expose] def build (prepared : Face.SegmentPreparation models
  sheet segment) (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
    (left right : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) (positive : 0 <
      tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences.PairedReference prepared domain left right
      tolerance :=
  let lp := Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build prepared.piece.path left sheet
  let rp := Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build prepared.piece.path right sheet
  let lr := Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.build (prepared.entered domain left
    lp) tolerance positive
  let rr := Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.build (prepared.entered domain right
    rp) tolerance positive
  ⟨lp, rp, lr, rr, max lr.budget.grid.index rr.budget.grid.index,
    (by rw [Order.max_eq_natMax]; exact Order.le_max_left _ _),
    (by rw [Order.max_eq_natMax]; exact Order.le_max_right _ _)⟩

/-- The density is a common upper bound for the two supplied Newton bands.
The readings may retain different local owners at coincident coordinates. -/
theorem point_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences.PairedReference prepared domain left right tolerance)
    {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile left.exponent}
    {rightProfile : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile right.exponent}
    {leftTarget rightTarget density : Fraction.Rational}
    (leftBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget)
    (rightBand : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftFirst : leftBand.sample.output.box.Contains start)
    (leftLast : leftBand.sample.output.box.Contains finish)
    (leftSide : Paths.PreparedBoundarySegments.SameSide leftBand.sample.output.box start finish)
    (rightFirst : rightBand.sample.output.box.Contains start)
    (rightLast : rightBand.sample.output.box.Contains finish)
    (rightSide : Paths.PreparedBoundarySegments.SameSide rightBand.sample.output.box start finish)
    (leftDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile
      leftBand.error ≤ density)
    (rightDensity : RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile
      rightBand.error ≤ density)
    {index : Nat} (later : reference.index ≤ index)
    (leftData : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain left index) (rightData :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain right index)
    {count : Nat} {points : Fin count → Gaussian.Basic.Canonical}
    (leftReadings : Readings.RectangularPointReadings.PointReadings leftData.anchors leftData.offsets points)
    (rightReadings : Readings.RectangularPointReadings.PointReadings rightData.anchors rightData.offsets points)
    (first last : Fin count) (firstEq : points first = start) (lastEq : points last = finish) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Topology.Polygon.Stokes.PrimitivePoint.mk
      (leftReadings.values last - leftReadings.values first)
      (rightReadings.values last - rightReadings.values first))
        (3 * tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  constructor
  · have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound
      reference.leftReference leftBand leftFirst leftLast leftSide
      (reference.left_later.trans later) leftData leftReadings first last firstEq lastEq
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound ⊢
    apply bound.trans
    have h := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftDensity
      (Gaussian.Basic.Canonical.normSq_nonneg (finish - start))
    have h' := Fraction.Order.Arithmetic.add_le_add_direct (first := 3 * tolerance) le_rfl
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct h (by decide : (0 : Fraction.Rational) ≤ 4))
    exact h'.trans_eq (by ring1)
  · have bound := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound
      reference.rightReference rightBand rightFirst rightLast rightSide
      (reference.right_later.trans later) rightData rightReadings first last firstEq lastEq
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound ⊢
    apply bound.trans
    have h := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rightDensity
      (Gaussian.Basic.Canonical.normSq_nonneg (finish - start))
    have h' := Fraction.Order.Arithmetic.add_le_add_direct (first := 3 * tolerance) le_rfl
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct h (by decide : (0 : Fraction.Rational) ≤ 4))
    exact h'.trans_eq (by ring1)

end PairedReference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences
