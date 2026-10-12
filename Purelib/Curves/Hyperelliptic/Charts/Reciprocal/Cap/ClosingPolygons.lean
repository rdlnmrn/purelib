module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartPolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSidePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Tactic.Ring

public section

/-!
# The closing increment of the actual joined cap polygon

The cached totals telescope through the retained vertices and junctions.
Thus the negative cached total is exactly the initial-minus-final reading,
whose requested bound comes from the operational closing comparison.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {target :
    Normalization.InverseRootPolynomial.Coordinate}

/-- The recursive finish of a nonempty retained vertex list is its actual last entry. -/
private theorem last_value : ∀ (first : Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex capSample target) (rest :
  List (Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex capSample target)),
    (first :: rest).getLast? = some (Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.finish first rest)
  | _, [] => rfl
  | _, next :: rest => Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.last_value next rest

/-- The sum of the original consecutive vertex increments is the last value minus the first value. -/
theorem increments_sum_of_endpoints {vertices : List (Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex capSample
  target)} {first last : Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex capSample target}
    (starts : vertices.head? = some first) (finishes : vertices.getLast? = some last) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.increments vertices)
      = last.value - first.value := by
  cases vertices with
  | nil => cases starts
  | cons head rest =>
      have startEq : head = first := Option.some.inj starts
      have finishEq : Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.finish head rest = last := Option.some.inj
        ((Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.last_value head rest).symm.trans finishes)
      rw [← startEq, ← finishEq]
      exact Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.steps_sum head rest

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {parent : Parent curve differential} {data : ParentData cap differential count parent}
  {integrationTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {base :
    Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data integrationTarget floor}
  {totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate} {request :
    Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget areaTarget}
  {index : Nat} {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample
    cap differential index box}
  {retained : Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Sample base capSample}

/-- The evaluated original chart total is its retained last vertex value minus its first vertex value. -/
theorem total_endpoints (evaluated : Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation request
  retained) :
    evaluated.chart.total = evaluated.last.vertex.value - evaluated.first.vertex.value := by
  rw [evaluated.chart.total_eq, ← evaluated.vertex_increments]
  exact Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.increments_sum_of_endpoints evaluated.vertex_first
    evaluated.vertex_last

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent Bank)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {index : Nat} {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample
    cap differential index box}

/-- The complete nonempty original connected summary is its entry correction plus the last reading minus the first
reading. -/
private theorem connected_total : ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) (entry :
      Normalization.InverseRootPolynomial.Gaussian), parents ≠ [] →
    (charts.connectedSummary entry).total = entry + charts.lastValue - charts.firstValue
  | [], .nil, _, _, _, _, _, _, _, _, nonempty => (nonempty rfl).elim
  | [_], .cons _ .nil, _, _, _, _, _, _, charts, entry, _ => by
      change entry + charts.1.chart.total + 0 = entry + charts.1.last.vertex.value - charts.1.first.vertex.value
      rw [charts.1.total_endpoints]
      ring1
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, entry, _ => by
      change entry + charts.1.chart.total +
        (charts.2.connectedSummary (charts.2.1.first.vertex.value - charts.1.last.vertex.value)).total =
        entry + charts.2.lastValue - charts.1.first.vertex.value
      rw [Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connected_total charts.2 _ (by
        intro impossible; cases impossible), charts.1.total_endpoints]
      change entry + (charts.1.last.vertex.value - charts.1.first.vertex.value) +
        (charts.2.1.first.vertex.value - charts.1.last.vertex.value + charts.2.lastValue -
          charts.2.1.first.vertex.value) = _
      ring1

/-- The existing connected summary is the displacement between its retained
external readings, including all parent and lap handoffs. -/
theorem connected_total_endpoints : ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine), (charts.connectedSummary
      0).total = charts.lastValue - charts.firstValue
  | [], .nil, _, _, _, _, _, _, _ => by change (0 : Normalization.InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | _ :: _, .cons _ _, _, _, _, _, _, _, charts => by
      simpa only [Gaussian.Basic.zero_add] using
        Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connected_total charts 0 (by
          intro impossible;
          cases impossible)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
