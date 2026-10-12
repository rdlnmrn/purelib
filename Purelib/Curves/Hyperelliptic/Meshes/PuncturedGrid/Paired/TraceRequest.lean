module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
public import Purelib.Integration.Path.EndpointJump
public import Purelib.Riemann.Periods.ClippedBilinearBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

section

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-! Two actual prefix-contact banks pay the complete paired path-area error.
Endpoint terms remain explicit in the certified result. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat} {points : Fin (count + 1) → Gaussian.Basic.Canonical} {firstDifferential secondDifferential :
    Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet secondSheet : Fin 2}

set_option genInjectivity false in
/-- A paid comparison of the two original differential traces.

Retain the bilinear error allocation, both prefix-contact requests and a stage sufficient for both original banks. -/
structure PairedTraceRequest {start : Gaussian.Basic.Canonical}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
      Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
    {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain
      : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
    {count : Nat}
    {points : Fin (count + 1) → Gaussian.Basic.Canonical}
    {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet
      secondSheet : Fin 2}
    (firstBank : @Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank genus curve branches higher bank
      frames firstFace lastFace firstModels lastModels
      start owner count leftEntry rightEntry leftDomain rightDomain points firstDifferential firstSheet)
    (secondBank : @Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank genus curve branches higher
      bank frames firstFace lastFace firstModels lastModels
      start owner count leftEntry rightEntry leftDomain rightDomain points secondDifferential secondSheet)
    (magnitude target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original count-and-magnitude bilinear error allocation. -/ budget : Periods.ClippedBilinearBudget count
    magnitude target
  /-- The first original differential's prefix-contact request. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request firstBank budget.error floor
  /-- The second original differential's prefix-contact request. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request secondBank budget.error floor
  /-- The retained common stage for both original requests. -/ index : Nat
  /-- The first original request is ready by the retained common stage. -/ first_le : first.index ≤ index
  /-- The second original request is ready by the retained common stage. -/ second_le : second.index ≤ index

constructive_injectivity PairedTraceRequest

namespace PairedTraceRequest

variable {start : Gaussian.Basic.Canonical}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat}
  {points : Fin (count + 1) → Gaussian.Basic.Canonical}
  {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet secondSheet
    : Fin 2}

variable {firstBank : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry
  leftDomain rightDomain points firstDifferential firstSheet}
  {secondBank : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain
    rightDomain points secondDifferential secondSheet}
  {magnitude target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Allocate the bilinear target before preparing both original prefix requests and their common stage. -/
@[expose] def build
    (firstBank : @Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank genus curve branches higher bank
      frames firstFace lastFace firstModels lastModels
      start owner count leftEntry rightEntry leftDomain rightDomain points firstDifferential firstSheet)
    (secondBank : @Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank genus curve branches higher
      bank frames firstFace lastFace firstModels lastModels
      start owner count leftEntry rightEntry leftDomain rightDomain points secondDifferential secondSheet)
    (magnitude target : Normalization.InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ magnitude) (positive : 0 <
      target) (floor : Nat) :
    _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
      magnitude target floor :=
  let budget := Periods.ClippedBilinearBudget.build count magnitude target nonnegative positive
  let first := Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request.build firstBank
    budget.error budget.error_positive floor
  let second := Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request.build secondBank
    budget.error budget.error_positive floor
  ⟨budget, first, second, max first.index second.index, Purelib.Data.Nat.Order.le_max_left _ _,
    Purelib.Data.Nat.Order.le_max_right _ _⟩

/-- The retained common comparison stage meets the original requested floor. -/
theorem floor_le (request :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
  magnitude target floor) : floor ≤ request.index :=
  request.first.floor_le.trans request.first_le

/-- The original centered bilinear readings differ within the retained count-and-magnitude error allowance. -/
theorem centered_accurate (request :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
  magnitude target floor) {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (leftFirst : Readings.RectangularPointReadings.PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : Readings.RectangularPointReadings.PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : Readings.RectangularPointReadings.PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : Readings.RectangularPointReadings.PointReadings secondRight.anchors secondRight.offsets points)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨leftFirst.values vertex, leftSecond.values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨rightFirst.values vertex, rightSecond.values vertex⟩))
    (vertex : Fin (count + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((left.centered vertex).sub (right.centered vertex)) request.budget.error := by
  rw [left.centered_eq, right.centered_eq]
  have firstBound := (request.first.accurate (request.first_le.trans later) firstLeft firstRight leftFirst rightFirst
    vertex).le
  have secondBound := (request.second.accurate (request.second_le.trans later) secondLeft secondRight leftSecond
    rightSecond vertex).le
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstBound secondBound
  exact ⟨firstBound, secondBound⟩

/-- The original endpoint-increment correction is bounded by four times the retained origin magnitude and local error.
-/
theorem endpointIncrementError_bound (request :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
  magnitude target floor) {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (leftFirst : Readings.RectangularPointReadings.PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : Readings.RectangularPointReadings.PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : Readings.RectangularPointReadings.PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : Readings.RectangularPointReadings.PointReadings secondRight.anchors secondRight.offsets points)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨leftFirst.values vertex, leftSecond.values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨rightFirst.values vertex, rightSecond.values vertex⟩))
    {originMagnitude : Normalization.InverseRootPolynomial.Coordinate}
    (origin : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (⟨rightFirst.values 0, rightSecond.values 0⟩ : Topology.Polygon.Stokes.PrimitivePoint) originMagnitude) :
    Data.Gaussian.Norm.Basic.normSq (left.endpointIncrementError right) ≤ 4 * originMagnitude * request.budget.error
      :=
  left.endpointIncrementError_bound right origin
    (request.centered_accurate later firstLeft firstRight secondLeft secondRight
      leftFirst rightFirst leftSecond rightSecond left right (Fin.last count))

/-- After subtracting their actual endpoint corrections, the two original area readings differ by less than the target.
-/
theorem accurate (request :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
  magnitude target floor) {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (leftFirst : Readings.RectangularPointReadings.PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : Readings.RectangularPointReadings.PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : Readings.RectangularPointReadings.PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : Readings.RectangularPointReadings.PointReadings secondRight.anchors secondRight.offsets points)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨leftFirst.values vertex, leftSecond.values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨rightFirst.values vertex, rightSecond.values vertex⟩))
    (bounded : ∀ vertex, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (right.centered vertex) magnitude) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint - right.endpoint)) <
      target := by
  have errors (vertex : Fin (count + 1)) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((left.centered vertex).sub (right.centered vertex)) request.budget.error := by
    exact request.centered_accurate later firstLeft firstRight secondLeft secondRight
      leftFirst rightFirst leftSecond rightSecond left right vertex
  have estimate := left.comparison right request.budget.magnitude_nonnegative request.budget.error_positive.le
    request.budget.error_le_one bounded errors
  have paid := request.budget.error_paid
  rw [request.budget.weight_eq] at paid
  exact estimate.trans_lt ((show (count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (32 * (magnitude + 1) *
    request.budget.error) =
    (count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (32 * (magnitude + 1)) * request.budget.error by
      ring1).trans_lt paid)

end PairedTraceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest

end
