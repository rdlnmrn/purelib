module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedChartRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

public section

/-!
# Shared source acquisition and complete parent chart comparison

Prepare the original controlled primitive request together with the chart
request. The shared polynomial stage and fine depth are chosen before either
bank is sampled. Chart plans remain available for a later common reading
stage; acquiring one parent uses their computed stage directly.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageCharts

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

set_option genInjectivity false in
/-- An original coupled source-area plan and cap-chart request with their common model stage.

Both owners are retained so later preparation reuses their exact samples and bounds. -/
structure StageChartRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
    (sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
      Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original coupled local-area plan. -/ source :
    Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan data sourceTarget
    reciprocalTarget coefficientTarget areaTarget totalTarget minimum
  /-- The original joined-chart request. -/ cap :
    JoinedChartRequest prepared totalTarget areaTarget minimum
  /-- The common required model stage. -/ index : Nat
  /-- The common stage is exactly the maximum of the original request stages. -/ index_eq : index = max source.index
    cap.index

constructive_injectivity StageChartRequest

namespace StageChartRequest

/-- Prepare the original source and cap requests with their positive targets and retain the maximum required model
stage.

Both original requests retain the same inputs and minimum. Their maximum
index selects a stage sufficient for the source preparation and cap charts. -/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  (sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Normalization.InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum :=
  let source := Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan.build data
    sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget
    sourcePositive reciprocalPositive coefficientPositive areaPositive totalPositive minimum
  let cap := JoinedChartRequest.build prepared totalTarget
    areaTarget totalPositive areaPositive minimum
  ⟨source, cap, max source.index cap.index, rfl⟩

variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {sourceTarget
  reciprocalTarget coefficientTarget totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth : Nat} {box : Rational.Box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared sourceTarget
    reciprocalTarget coefficientTarget totalTarget areaTarget minimum}

set_option genInjectivity false in
/-- The original evaluated source request and exact supplied cap sample, with a retained chart plan and its stage
bounds. -/
structure Prepared (request : Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared sourceTarget
  reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth : Nat) where
  /-- The original evaluated coupled local-area request. -/ original :
    Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaRequest cover sourceTarget
    reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth
  /-- The retained original request has exactly the selected common index. -/ original_index : original.area.index =
    index
  /-- The actual retained cap sample. -/ capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential original.area.index box
  /-- The cap sample is exactly the supplied original sample, with its dependent identity. -/ capSample_eq : HEq
    capSample sample
  /-- The chart plan on that exact original sample. -/ chart :
    JoinedChartRequest.Plan request.cap capSample minimum
  /-- The original model-stage requirement is met. -/ later : request.cap.index ≤ original.area.index
  /-- The original fine-depth requirement is met. -/ fine_later : request.cap.depth ≤ depth

constructive_injectivity Prepared

/-- Evaluate the original coupled source once and prepare its chart on the supplied retained cap sample.

The model-stage and spatial-depth bounds pay the same original requests.
The retained cap sample has its exact dependent identity at the source index. -/
@[expose] def prepare (request : Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared
  sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth : Nat)
    (later : request.index ≤ index) (fineLater : request.cap.depth ≤ depth) :
      Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest.Prepared request sample depth :=
  let indices := request.index_eq.ge.trans later
  let original := request.source.evaluate cover proper index depth ((Data.Nat.Order.le_max_left _ _).trans indices)
  let chart := JoinedChartRequest.Plan.build request.cap sample
    minimum
  ⟨original, rfl, sample, HEq.rfl, chart, (Data.Nat.Order.le_max_right _ _).trans indices, fineLater⟩

namespace Prepared

variable {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Evaluate the retained original chart at any sufficiently late reading stage. -/
@[expose] def evaluate (retained : Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest.Prepared request
  sample depth) (readingIndex : Nat) (later : retained.chart.stage ≤ readingIndex) :
    JoinedChartRequest.Plan.Evaluation retained.original.area
      retained.chart readingIndex :=
  retained.chart.evaluate retained.later retained.fine_later readingIndex later

end Prepared

set_option genInjectivity false in
/-- Automatic finite acquisition retains the original controlled request,
its shared sample and the full certified chart replacement. -/
structure Acquisition (request : Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared
  sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (depthFloor : Nat) where
  /-- The original cap sample acquired at the common request stage. -/ sample :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential request.index collar.box
  /-- The chosen common subdivision depth. -/ depth : Nat
  /-- The depth is exactly the maximum of the requested floor and original cap depth. -/ depth_eq : depth = max
    depthFloor request.cap.depth
  /-- The original prepared chart with its exact supplied sample. -/ retained :
    Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest.Prepared request sample depth
  /-- The chart evaluated at its retained sufficient stage. -/ evaluated :
    JoinedChartRequest.Plan.Evaluation retained.original.area
    retained.chart retained.chart.stage

constructive_injectivity Acquisition

/-- Acquire the original cap sample once, select the common depth and retain the prepared chart and its first
evaluation.

The depth is the maximum of the supplied floor and cap requirement.
Preparation and evaluation consume that exact sample at the retained
sufficient model and reading stages. -/
@[expose] def acquire (request : Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest prepared
  sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (depthFloor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.StageCharts.StageChartRequest.Acquisition request depthFloor :=
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap differential request.index collar.box
  let depth := max depthFloor request.cap.depth
  let retained := request.prepare proper sample depth le_rfl (Data.Nat.Order.le_max_right _ _)
  ⟨sample, depth, rfl, retained, retained.evaluate retained.chart.stage le_rfl⟩

end StageChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageCharts
