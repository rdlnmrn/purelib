module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

/-!
# Chart acquisition for the original synchronized parent request

The old request remains the owner of the controlled source and endpoint
certificates. Its joined evaluation consumes the chart readings directly.
The replacement retains all of that evaluation's paths and corrections.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {sourceTarget
    reciprocalTarget coefficientTarget totalTarget areaTarget target : Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum}

set_option genInjectivity false in
/-- The original replacement charts and a reading stage shared with the retained synchronized parent request. -/
structure ChartPlan (request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget
  reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (replacement : ChartReplacementRequest prepared target
      minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) where
  /-- The actual original replacement chart plans for the supplied cap sample. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans sample minimum replacement.charts
  /-- The retained common numerical reading stage. -/ stage : Nat
  /-- The reading stage equals the maximum of the original cap requirement and chart maximum. -/ stage_eq : stage = max
    request.cap.readingIndex charts.maximum

constructive_injectivity ChartPlan

set_option genInjectivity false in
/-- The actual chart replacement of the original synchronized parent evaluation.

Keep the retained source cells, endpoint-reading identity, junction stages and paid area comparison. -/
structure ChartReplacement (replacement :
  ChartReplacementRequest prepared target minimum)
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth
      readingIndex) where
  /-- The actual chart plans on the original evaluation's retained cap sample. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans evaluated.capSample minimum replacement.charts
  /-- The original replacement vertices read from the retained polynomial cells. -/ vertices :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex charts
    evaluated.cap.polynomial.cells
  /-- The source model meets the original endpoint-request stage. -/ model_later : request.cap.endpoints.maximum ≤
    evaluated.original.area.index
  /-- The numerical reading stage meets the original endpoint requirements. -/ reading_later :
    request.cap.endpoints.readingMaximum ≤ readingIndex
  /-- The numerical reading stage meets the original junction requirements. -/ junction_later :
    request.cap.junctions.maximum ≤ readingIndex
  /-- The original evaluated cap uses exactly these retained chart endpoint readings. -/ readings_eq :
    evaluated.cap.readings = charts.endpointReadings evaluated.cap.polynomial.cells vertices request.cap.endpoints
    model_later reading_later
  /-- The actual joined-chart replacement on the original cells, vertices and endpoint readings. -/ replacement :
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement charts evaluated.cap.polynomial.cells vertices
    request.cap.endpoints
    evaluated.cap.readings evaluated.cap.firstValue
  /-- The original joined area and its actual replacement differ by less than the retained target. -/ area_error :
    Data.Gaussian.Norm.Basic.normSq (replacement.summary.area - evaluated.cap.joined.summary.area) < target

constructive_injectivity ChartReplacement

namespace ChartPlan

variable {replacement : ChartReplacementRequest prepared
  target minimum}

/-- Prepare the original replacement charts once and cache the maximum of their reading stage and the existing cap
requirement. -/
@[expose] def build (request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget
  reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (replacement : ChartReplacementRequest prepared target
      minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) :
      Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartPlan request replacement sample :=
  let charts := Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.build sample minimum
    replacement.charts
  ⟨charts, max request.cap.readingIndex charts.maximum, rfl⟩

/-- Evaluate the original parent request using the retained chart readings and return its exact replacement with the
paid area bound. -/
@[expose] def evaluate (plan : Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartPlan request replacement
  sample)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (later : request.index ≤ index) (chartLater : replacement.charts.maximum ≤ index)
    (fineLater : replacement.charts.depthMaximum ≤ depth) (readingLater : plan.stage ≤ readingIndex) :
    Σ evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth
      readingIndex, Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartReplacement replacement evaluated :=
      by
  have indices := request.index_eq.ge.trans later
  let original := request.source.evaluate cover proper index depth ((Data.Nat.Order.le_max_left _ _).trans indices)
  have capIndices := request.cap.index_eq.ge.trans ((Data.Nat.Order.le_max_right _ _).trans indices)
  have stages := plan.stage_eq.ge.trans readingLater
  have capReadingLater := (Data.Nat.Order.le_max_left _ _).trans stages
  have endpointReadingLater := (Data.Nat.Order.le_max_left _ _).trans (request.cap.readingIndex_eq.ge.trans
    capReadingLater)
  let polynomial := request.cap.polynomial.evaluate original.area sample ((Data.Nat.Order.le_max_left _ _).trans
    capIndices)
  let vertices := plan.charts.evaluate polynomial.cells chartLater fineLater ((Data.Nat.Order.le_max_right _ _).trans
    stages)
  let readings := plan.charts.endpointReadings polynomial.cells vertices request.cap.endpoints
    ((Data.Nat.Order.le_max_right _ _).trans capIndices) endpointReadingLater
  let compared := request.cap.evaluateWithReadings polynomial readings capReadingLater
  let evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth
    readingIndex :=
    ⟨original, rfl, sample, HEq.rfl, compared, compared.boundary.first,
      compared.boundary.first_value.trans compared.firstValue_eq.symm, compared.boundary.last,
      (compared.boundary.last_value compared.firstValue).trans compared.joined.lastValue_eq.symm,
      compared.boundary.firstReading, rfl, compared.boundary.lastReading, rfl⟩
  let replaced := Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement.build plan.charts polynomial.cells
    vertices request.cap.endpoints readings compared.firstValue
  exact ⟨evaluated, plan.charts, vertices, (Data.Nat.Order.le_max_right _ _).trans capIndices, endpointReadingLater,
    (Data.Nat.Order.le_max_right _ _).trans (request.cap.readingIndex_eq.ge.trans capReadingLater), rfl, replaced,
    (replaced.area_error compared.joined).trans_lt replacement.paid⟩

end ChartPlan
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
