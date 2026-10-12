module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
public import Purelib.Integration.Path.IncrementAreaJoins
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib.Integration.Path

open Purelib.Integration.Path.IncrementAreaJoins

open Purelib.Riemann.Normalization

public section

/-!
# Synchronized readings of retained cap endpoints

An operational owner join supplies indices for the actual cached chart
evaluations. Refinement preserves each local polynomial comparison and square
residual, while the returned negative primitive values satisfy the requested
junction bound.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)

set_option genInjectivity false in
/-- Both evaluated occurrences and the certified discrepancy of their selected values are retained. The two local
request types may differ. -/
structure JoinedPoints (First : Type u) (Last : Type v) (firstValue : First → InverseRootPolynomial.Gaussian)
    (lastValue : Last → InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate) where
  /-- The retained first evaluated endpoint occurrence with its original request type. -/ first : First
  /-- The retained second evaluated endpoint occurrence with its original request type. -/ last : Last
  /-- The cached difference of the two actual retained endpoint values. -/ connector : InverseRootPolynomial.Gaussian
  /-- The connector is exactly the last retained value minus the first. -/ connector_eq : connector = lastValue last -
    firstValue first
  /-- The actual retained connector satisfies the original squared-norm target. -/ close :
    Data.Gaussian.Norm.Basic.normSq connector < target

constructive_injectivity JoinedPoints

namespace JoinedPoints

variable {First : Type u} {Last : Type v} {firstValue : First →
  Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {lastValue : Last →
  Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- The connector is attached using the next block's retained summary. -/
@[expose] def connect (joined : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.JoinedPoints First Last firstValue
  lastValue target) {increments : List InverseRootPolynomial.Gaussian}
    (summary : IncrementArea.Summary increments) : IncrementArea.Summary (joined.connector :: increments) :=
  Summary.prepend summary joined.connector

/-- Prepending the retained endpoint connector changes the original next-block area by at most four times its target and
total bound. -/
theorem connection_area_bound (joined : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.JoinedPoints First Last
  firstValue lastValue target) {increments : List InverseRootPolynomial.Gaussian}
    (summary : IncrementArea.Summary increments) {bound : InverseRootPolynomial.Coordinate} (bounded :
      Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq ((joined.connect summary).area - summary.area) ≤ 4 * target * bound :=
  Summary.prepend_area_error summary joined.connector joined.close.le bounded

end JoinedPoints

namespace PointRequest

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {firstCenter lastCenter : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {firstCount lastCount : Nat}
  {firstOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval firstCenter)}
  {lastOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval lastCenter)}
  {firstTerminal : Terminal cap firstOwner firstCount} {lastTerminal : Terminal cap lastOwner lastCount}
  {firstComparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data firstTerminal
    differential}
  {lastComparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data lastTerminal
    differential}
  {firstPoint lastPoint : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {firstTarget lastTarget :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {firstFloor lastFloor index : Nat}
  {firstRequest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest firstComparison firstPoint
    firstTarget firstFloor}
  {lastRequest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest lastComparison lastPoint
    lastTarget lastFloor}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {firstSource : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample firstTerminal.preparation
    capSample}
  {lastSource : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample lastTerminal.preparation
    capSample}

/-- The indices are selected from the certified join of these very channels. The source polynomial samples and their
cached factor readings are reused. -/
@[expose] def synchronize (first : PointRequest.Evaluation firstRequest firstSource) (last : PointRequest.Evaluation
  lastRequest lastSource)
    (join : RootCoordinates.Overlap.Join firstRequest.prepared.coordinates lastRequest.prepared.coordinates)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.JoinedPoints (PointRequest.Evaluation firstRequest
      firstSource) (PointRequest.Evaluation lastRequest lastSource)
      (fun evaluated => evaluated.vertex.value) (fun evaluated => evaluated.vertex.value) target := by
  let comparison := (join.readings capSample).compare first.chart.stage last.chart.stage target positive
  let left := first.refine comparison.leftIndex comparison.left_ge
  let right := last.refine comparison.rightIndex comparison.right_ge
  have close : Data.Gaussian.Norm.Basic.normSq (left.chart.reading.value - right.chart.reading.value) < target
    := by
    rw [left.chart.reading.value_sample, right.chart.reading.value_sample]
    exact comparison.close (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨left, right, right.vertex.value - left.vertex.value, rfl, ?_⟩
  change Data.Gaussian.Norm.Basic.normSq (-right.chart.reading.value - -left.chart.reading.value) < target
  rw [show -right.chart.reading.value - -left.chart.reading.value =
    left.chart.reading.value - right.chart.reading.value by ring1]
  exact close

end PointRequest

namespace ParentBoundary

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {parent next : Parent curve differential}
  {firstData : ParentData cap differential count parent} {lastData : ParentData cap differential count next}
  {firstPoint lastPoint : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {firstTarget lastTarget :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {firstFloor lastFloor : Nat}

/-- Transfer the retained coarse-parent join to the actual requests at the two fine-block endpoints. Each local transfer
uses its original parent query. -/
@[expose] def join (coarse : RootCoordinates.Overlap.Join firstData.data.last.coordinates
  lastData.data.first.coordinates)
    (firstRequest : FineCharts.PointRequest firstData.comparison firstPoint firstTarget firstFloor)
    (lastRequest : FineCharts.PointRequest lastData.comparison lastPoint lastTarget lastFloor)
    (firstEq : parent.edge.point 1 = firstPoint) (lastEq : next.edge.point 0 = lastPoint) :
    RootCoordinates.Overlap.Join firstRequest.prepared.coordinates lastRequest.prepared.coordinates :=
  (firstData.point_join 1 (by decide) firstEq firstData.last_eq.symm firstRequest.prepared firstData.data.last).trans
    (coarse.trans (lastData.point_join 0 (by decide) lastData.first_eq.symm lastEq lastData.data.first
      lastRequest.prepared))

end ParentBoundary
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
