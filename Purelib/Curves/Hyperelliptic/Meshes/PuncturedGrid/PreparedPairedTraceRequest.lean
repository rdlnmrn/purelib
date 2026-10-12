module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceGeometryBound
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
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
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceGeometryBound

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest

open Purelib.Data.Rat

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

@[expose] public section

/-! A complete finite area request from cached common trace preparation.
Bounds and both differential contact banks are retained before numerical evaluation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks (TraceContactBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest (PairedTraceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner
    (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {count : Nat} {firstDifferential secondDifferential : Differential
    genus} {firstSheet secondSheet : Fin 2}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

variable {piece : Purelib.Riemann.Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry
  rightDomain.geometry}
  {trace : Purelib.Riemann.Integration.RectangularPairedPointBanks.Trace piece count}

namespace PairedTracePreparation

set_option genInjectivity false in
/-- A complete paired trace-area request on the original retained preparation.

Both differential bounds and exact contact banks are cached before selecting the common reading stage. -/
structure AreaRequest
    (preparation :
      _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation (leftEntry
      := leftEntry) (rightEntry := rightEntry) trace)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstSheet secondSheet : Fin 2)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached primitive-overlap bounds for the original first differential and terminal face. -/ firstBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    firstDifferential)
  /-- The cached primitive-overlap bounds for the original second differential and terminal face. -/ secondBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    secondDifferential)
  /-- The retained original first-differential contact bank on this exact trace. -/ firstBank :
    TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => trace.points vertex) firstDifferential firstSheet
  /-- The retained original second-differential contact bank on this exact trace. -/ secondBank :
    TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => trace.points vertex) secondDifferential secondSheet
  /-- The first bank is exactly the one produced by the original trace preparation. -/ firstBank_eq : firstBank =
    preparation.contacts firstDifferential firstSheet
  /-- The second bank is exactly the one produced by that same original preparation. -/ secondBank_eq : secondBank =
    preparation.contacts secondDifferential secondSheet
  /-- The retained paired trace request using the maximum of both cached boundary slopes. -/ request :
    TraceRequest.PairedTraceRequest firstBank secondBank
    (max (RectangularSeamBounds.boundarySlope firstBounds) (RectangularSeamBounds.boundarySlope secondBounds)) target
      floor

constructive_injectivity AreaRequest

namespace AreaRequest

variable {preparation :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation (leftEntry :=
  leftEntry) (rightEntry := rightEntry) trace}
  {target : Coordinate} {floor : Nat}

/-- Cache both original differential bounds and contact banks, then prepare their shared paid trace-area request. -/
def build (preparation :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation (leftEntry :=
  leftEntry) (rightEntry := rightEntry) trace)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstSheet secondSheet : Fin 2)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor := by
  let firstBounds := PrimitiveOverlapBounds.build lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    firstDifferential)
  let secondBounds := PrimitiveOverlapBounds.build lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    secondDifferential)
  let firstBank := preparation.contacts firstDifferential firstSheet
  let secondBank := preparation.contacts secondDifferential secondSheet
  have nonnegative : 0 ≤ RectangularSeamBounds.boundarySlope firstBounds :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct firstBounds.numeratorUpper_nonnegative
      firstBounds.inverseUpper_positive.le)) lastFace.cell.box.diagonalSq_nonneg
  exact ⟨firstBounds, secondBounds, firstBank, secondBank, rfl, rfl,
    PairedTraceRequest.build firstBank secondBank
      (@max Fraction.Rational Fraction.Order.Basic.instLinearOrder.toMax
        (RectangularSeamBounds.boundarySlope firstBounds) (RectangularSeamBounds.boundarySlope secondBounds)) target
      (nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)) positive floor⟩

/-- At every stage meeting the retained request, the actual endpoint-corrected paired trace-area discrepancy satisfies
the original target. -/
theorem accurate (assembled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation.AreaRequest
    preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.request.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors firstLeft.offsets).values
      vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint -
      right.endpoint)) < target :=
  PairedTraceRequest.trace_accurate
    assembled.firstBounds assembled.secondBounds assembled.request later
    firstLeft firstRight secondLeft secondRight left right

end AreaRequest
end PairedTracePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
