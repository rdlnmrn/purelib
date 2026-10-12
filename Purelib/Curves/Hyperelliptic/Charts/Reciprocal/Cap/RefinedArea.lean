module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CommonReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
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
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

public section

/-!
# Refined cap polygons retaining their source calculations

Replace the chart readings at one common index, retaining the evaluated
source rows and their polynomial summary. The resulting endpoint equations
identify the displayed polygon values with the original requested streams.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest

open Purelib
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Parent curve differential} {count : Nat} {data : ParentData cap differential count parent}
  {integrationTarget totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor
    index : Nat} {box : Purelib.Geometry.Rational.Box}
  {base : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data integrationTarget floor}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget areaTarget}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {retained : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Sample base capSample}

/-- Transport the original cached path summary along exact equality of its retained increment list. -/
@[expose] public def castSummary {first last : List InverseRootPolynomial.Gaussian} (equal : first = last) (summary :
  IncrementArea.Summary first) : IncrementArea.Summary last := by
  cases equal
  exact summary

/-- Equal original data give equal applications when the remaining argument is only a proof of its property. -/
private theorem apply_proof_congr {α : Type u} {β : Type v} {property : α → Prop} {first last : α}
    (equal : first = last) (apply : (value : α) → property value → β)
    (firstProof : property first) (lastProof : property last) : apply first firstProof = apply last lastProof := by
  cases equal
  rfl

namespace Evaluation

/-- Read the original first retained endpoint's chart approximation stream. -/
@[expose] public def firstStream (evaluated : AreaRequest.Evaluation request retained) :
  ApproximationData :=
  (evaluated.first.request.prepared.coordinates.chartApproximation capSample).toApproximation

/-- Read the original last retained endpoint's chart approximation stream. -/
@[expose] public def lastStream (evaluated : AreaRequest.Evaluation request retained) :
  ApproximationData :=
  (evaluated.last.request.prepared.coordinates.chartApproximation capSample).toApproximation

/-- The original first endpoint reading stage is bounded by the retained chart-bank maximum. -/
theorem first_stage_le (evaluated : AreaRequest.Evaluation request retained) : evaluated.first.evaluated.chart.stage ≤
  evaluated.charts.stage := by
  rw [evaluated.first_eq, RetainedPoint.cast_stage]
  exact evaluated.charts.firstPoint_stage_le ⟨base.block.chain⟩ request.children_nonempty

/-- The original last endpoint reading stage is bounded by the retained chart-bank maximum. -/
theorem last_stage_le (evaluated : AreaRequest.Evaluation request retained) : evaluated.last.evaluated.chart.stage ≤
  evaluated.charts.stage := by
  rw [evaluated.last_eq, RetainedPoint.cast_stage]
  exact evaluated.charts.lastPoint_stage_le ⟨base.block.chain⟩ request.children_nonempty

/-- The retained integration model, polynomial rows and polynomial summary are reused. Only the requested chart readings
and their area are updated. -/
@[expose] public def refine (evaluated : AreaRequest.Evaluation request retained) (later : request.index ≤ index)
    (stage : Nat) (ready : evaluated.charts.stage ≤ stage) : AreaRequest.Evaluation request retained := by
  let charts := evaluated.charts.refine stage ready
  have shared := evaluated.charts.refine_shared request.shared base.block.chain stage ready
  have sourceEq : evaluated.pairs.map Prod.snd = charts.rows.map Prod.snd := by
    rw [evaluated.pairs_eq, Samples.rows_source, Samples.rows_source]
  let pairs := charts.refreshRows evaluated.pairs
  have pairsEq : pairs = charts.rows := charts.refreshRows_eq evaluated.pairs sourceEq
  have sameSource : evaluated.pairs.map Prod.snd = pairs.map Prod.snd :=
    sourceEq.trans (congrArg (List.map Prod.snd) pairsEq.symm)
  exact request.evaluateReadings retained later charts shared pairs pairsEq
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.castSummary sameSource
    evaluated.polynomial)

/-- Refining the original chart polygon preserves the exact refinement of its retained first endpoint. -/
theorem refine_first (evaluated : AreaRequest.Evaluation request retained) (later : request.index ≤ index)
    (stage : Nat) (ready : evaluated.charts.stage ≤ stage) :
    (evaluated.refine later stage ready).first = evaluated.first.refine stage (evaluated.first_stage_le.trans ready) :=
      by
  rw [(evaluated.refine later stage ready).first_eq]
  change ((evaluated.charts.refine stage ready).firstPoint ⟨base.block.chain⟩ request.children_nonempty).cast _ = _
  rw [Samples.firstPoint_refine, RetainedPoint.refine_cast]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.apply_proof_congr evaluated.first_eq.symm (fun
    point ready => point.refine stage ready) _ _

/-- Refining the original chart polygon preserves the exact refinement of its retained last endpoint. -/
theorem refine_last (evaluated : AreaRequest.Evaluation request retained) (later : request.index ≤ index)
    (stage : Nat) (ready : evaluated.charts.stage ≤ stage) :
    (evaluated.refine later stage ready).last = evaluated.last.refine stage (evaluated.last_stage_le.trans ready) := by
  rw [(evaluated.refine later stage ready).last_eq]
  change ((evaluated.charts.refine stage ready).lastPoint ⟨base.block.chain⟩ request.children_nonempty).cast _ = _
  rw [Samples.lastPoint_refine, RetainedPoint.refine_cast]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.apply_proof_congr evaluated.last_eq.symm (fun
    point ready => point.refine stage ready) _ _

/-- The refined original first chart value is the negative sample of its retained endpoint stream at the chosen stage.
-/
theorem refine_first_value (evaluated : AreaRequest.Evaluation request retained) (later : request.index ≤ index)
    (stage : Nat) (ready : evaluated.charts.stage ≤ stage) :
    (evaluated.refine later stage ready).first.vertex.value =
      -(evaluated.first.request.prepared.coordinates.chartApproximation capSample).toApproximation.sample stage := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation.refine_first]
  change -(ChartReading.build _ capSample stage).value = _
  rw [ChartReading.value_sample]
  rfl

/-- The refined original last chart value is the negative sample of its retained endpoint stream at the chosen stage. -/
theorem refine_last_value (evaluated : AreaRequest.Evaluation request retained) (later : request.index ≤ index)
    (stage : Nat) (ready : evaluated.charts.stage ≤ stage) :
    (evaluated.refine later stage ready).last.vertex.value =
      -(evaluated.last.request.prepared.coordinates.chartApproximation capSample).toApproximation.sample stage := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation.refine_last]
  change -(ChartReading.build _ capSample stage).value = _
  rw [ChartReading.value_sample]
  rfl

end Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest
