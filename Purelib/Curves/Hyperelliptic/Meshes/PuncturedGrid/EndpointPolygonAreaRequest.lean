module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest
public import Purelib.Riemann.Integration.RectangularEndpointMagnitude
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
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring

public section

/-! Computed contact requests bound the centered endpoint-polygon energy.
The retained grid tree supplies the magnitude; no numerical bound is an input. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks (TraceContactBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest (PairedTraceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Integration.Path.JoinedCenteredArea (endpointPolygon)
open Purelib.Integration.Path.PairedEndpointPolygon (pairedEndpointPolygon pairedEndpointPolygon_left_centered
  pairedEndpointPolygon_right_centered)

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

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    Riemann.Meshes.PuncturedGridFaces.RegularFace bank}
  {firstModels : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
    firstFace} {lastModels : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels
    frames lastFace}
  {start : Data.Gaussian.Basic.Canonical} {owner : Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  {leftEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner}
    {rightEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPairedEndpointReadings (PairedEndpointReadingsGeometry)

variable {count : Nat}
  {first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (Riemann.Integration.RectangularOwnedTriangulation.OwnedVertex leftDomain.geometry)}
  {last : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (Riemann.Integration.RectangularOwnedTriangulation.OwnedVertex rightDomain.geometry)}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Integration.RectangularEndpointMagnitude (endpointMagnitude)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace EndpointPolygonPreparation

variable {geometry : Riemann.Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first last}

set_option genInjectivity false in
/-- A computed contact request comparing the two original endpoint polygons.

The original differential bounds and contact banks determine a common magnitude from the retained domain steps, with the
requested positive target and stage floor. -/
structure AreaRequest
    (preparation : EndpointPolygonPreparation (leftEntry := leftEntry) (rightEntry :=
      rightEntry) geometry)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstSheet secondSheet : Fin 2)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original last-face primitive overlap bounds for the first differential. -/ firstBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    firstDifferential)
  /-- The original last-face primitive overlap bounds for the second differential. -/ secondBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance (PreparedPrimitiveSamples.differentialNumerator
    secondDifferential)
  /-- The retained endpoint contact bank for the first original differential and sheet. -/ firstBank :
    TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => geometry.points vertex) firstDifferential firstSheet
  /-- The retained endpoint contact bank for the second original differential and sheet. -/ secondBank :
    TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => geometry.points vertex) secondDifferential secondSheet
  /-- The first contact bank is exactly the original endpoint preparation's bank. -/ firstBank_eq : firstBank =
    preparation.contacts firstDifferential firstSheet
  /-- The second contact bank is exactly the original endpoint preparation's bank. -/ secondBank_eq : secondBank =
    preparation.contacts secondDifferential secondSheet
  /-- The paid paired contact request using the maximum of the two computed original endpoint magnitudes. -/ request :
    TraceRequest.PairedTraceRequest firstBank secondBank
    (max (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
      (RectangularSeamBounds.boundarySlope firstBounds))
      (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
        (RectangularSeamBounds.boundarySlope secondBounds))) target floor

constructive_injectivity AreaRequest

namespace AreaRequest

variable {preparation : EndpointPolygonPreparation
  (leftEntry := leftEntry) (rightEntry := rightEntry) geometry}
  {firstDifferential secondDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet
    secondSheet : Fin 2}
  {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Compute both original primitive bounds and endpoint contact banks, then prepare their common positive area request.
-/
@[expose] def build (preparation : EndpointPolygonPreparation (leftEntry := leftEntry)
  (rightEntry := rightEntry) geometry)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstSheet secondSheet : Fin 2)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation.AreaRequest
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
  let request := PairedTraceRequest.build firstBank secondBank
    (max (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
      (RectangularSeamBounds.boundarySlope firstBounds))
      (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
        (RectangularSeamBounds.boundarySlope secondBounds))) target
    ((RectangularEndpointMagnitude.endpointMagnitude_nonnegative _ _ nonnegative).trans
      (Fraction.Order.Basic.le_max_left _ _)) positive floor
  exact ⟨firstBounds, secondBounds, firstBank, secondBank, rfl, rfl, request⟩

/-- The actual retained paired contact request's stage. -/
@[expose] def index (assembled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation.AreaRequest
  preparation firstDifferential secondDifferential firstSheet secondSheet target floor) : Nat :=
  assembled.request.index

/-- The computed paired contact stage is above the supplied original floor. -/
theorem floor_le (assembled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation.AreaRequest
  preparation firstDifferential secondDifferential firstSheet secondSheet target floor) :
    floor ≤ assembled.index := assembled.request.floor_le

/-- At a stage paying the contact request, the two retained conjugate-centered endpoint areas differ by less than the
target. -/
theorem conjugate_accurate (assembled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation.AreaRequest
  preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((geometry.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (geometry.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((geometry.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (geometry.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) < target := by
  have bounded (vertex) : PrimitivePoint.Bounded (right.centered vertex)
      (max (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
        (RectangularSeamBounds.boundarySlope assembled.firstBounds))
        (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps rightDomain.steps
          (RectangularSeamBounds.boundarySlope assembled.secondBounds))) := by
    rw [right.centered_eq]
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq
        (Data.Gaussian.Basic.conj
          ((geometry.rightReadings firstRight.anchors firstRight.offsets).values vertex) -
          Data.Gaussian.Basic.conj
            ((geometry.rightReadings firstRight.anchors firstRight.offsets).values 0)) ≤ _
      have conjugation : Data.Gaussian.Basic.conj ((geometry.rightReadings firstRight.anchors
        firstRight.offsets).values vertex) -
          Data.Gaussian.Basic.conj ((geometry.rightReadings firstRight.anchors firstRight.offsets).values 0) =
          Data.Gaussian.Basic.conj ((geometry.rightReadings firstRight.anchors firstRight.offsets).values
            vertex -
            (geometry.rightReadings firstRight.anchors firstRight.offsets).values 0) := by
        apply Data.Gaussian.Basic.ext
        · rfl
        · simp only [Data.Gaussian.Basic.conj, Data.Gaussian.Basic.sub_im, -eq_self, -iff_self]
          ring1
      rw [conjugation, ← Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq_conj,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (RectangularEndpointMagnitude.endpoint_readings_magnitude firstRight.anchors firstRight.offsets
        assembled.firstBounds rightDomain.patch.cell_refines
        (geometry.rightReadings firstRight.anchors firstRight.offsets) 0 vertex).trans (Fraction.Order.Basic.le_max_left
          _ _)
    · have scalar := (RectangularEndpointMagnitude.endpoint_readings_magnitude secondRight.anchors secondRight.offsets
        assembled.secondBounds rightDomain.patch.cell_refines
        (geometry.rightReadings secondRight.anchors secondRight.offsets) 0 vertex).trans
          (Fraction.Order.Basic.le_max_right (RectangularEndpointMagnitude.endpointMagnitude rightDomain.steps
          rightDomain.steps (RectangularSeamBounds.boundarySlope assembled.firstBounds)) _)
      change Data.Gaussian.Basic.Canonical.normSq ((geometry.rightReadings secondRight.anchors
        secondRight.offsets).values vertex - (geometry.rightReadings secondRight.anchors secondRight.offsets).values 0)
        ≤ _
      exact scalar
  have estimate := PairedTraceRequest.conjugate_accurate assembled.request later firstLeft firstRight secondLeft
    secondRight
    (geometry.leftReadings firstLeft.anchors firstLeft.offsets) (geometry.rightReadings firstRight.anchors
      firstRight.offsets)
    (geometry.leftReadings secondLeft.anchors secondLeft.offsets) (geometry.rightReadings secondRight.anchors
      secondRight.offsets)
    left right bounded
  have equal : (left.originalArea - right.originalArea) - (left.endpoint - right.endpoint) =
      left.centeredArea - right.centeredArea := by
    rw [left.decomposition, right.decomposition]
    ring1
  rw [equal] at estimate
  exact estimate

/-- Values retain each original endpoint's cell owner. -/
@[expose] def energyValues {stage : Nat} (first : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (second : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage) (owner :
      RectangularOwnedTriangulation.OwnedVertex leftDomain.geometry) : PrimitivePoint :=
  ⟨conj (first.anchors.alignedValue first.offsets owner.column owner.row owner.point),
    second.anchors.alignedValue second.offsets owner.column owner.row owner.point⟩

/-- The contact request bounds the original two endpoint polygons, even when those polygons have distinct vertex types
and independent cached samples. -/
theorem original_polygons_accurate
    (assembled :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((geometry.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (geometry.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((geometry.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (geometry.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩))
    (leftPolygon : CenteredBilinearPath.Sample (fun vertex =>
      energyValues
      firstLeft secondLeft ((JoinedCenteredArea.endpointPolygon first).indexed vertex)))
    (rightPolygon : CenteredBilinearPath.Sample (fun vertex =>
      energyValues
      firstRight secondRight ((JoinedCenteredArea.endpointPolygon last).indexed vertex))) :
    Data.Gaussian.Norm.Basic.normSq (leftPolygon.centeredArea - rightPolygon.centeredArea) < target := by
  let pairedLeft := CenteredBilinearPath.Sample.build (fun vertex =>
    energyValues
    firstLeft secondLeft
    ((PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).1)
  let pairedRight := CenteredBilinearPath.Sample.build (fun vertex =>
    energyValues
    firstRight secondRight
    ((PairedEndpointPolygon.pairedEndpointPolygon first last).indexed vertex).2)
  have leftReadback : left.centeredArea = pairedLeft.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    rw [geometry.leftReadings_value, geometry.leftReadings_value]
    rfl
  have rightReadback : right.centeredArea = pairedRight.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    rw [geometry.rightReadings_value, geometry.rightReadings_value]
    rfl
  have leftEq := leftReadback.trans
    (PairedEndpointPolygon.pairedEndpointPolygon_left_centered first last
      (energyValues
      firstLeft secondLeft) pairedLeft leftPolygon)
  have rightEq := rightReadback.trans
    (PairedEndpointPolygon.pairedEndpointPolygon_right_centered first last
      (energyValues
      firstRight secondRight) pairedRight rightPolygon)
  have estimate := assembled.conjugate_accurate later firstLeft firstRight secondLeft secondRight left right
  rw [leftEq, rightEq] at estimate
  exact estimate

end AreaRequest
end EndpointPolygonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest
