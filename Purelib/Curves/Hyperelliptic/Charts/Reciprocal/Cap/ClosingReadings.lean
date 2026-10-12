module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinedArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
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
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

public section

/-!
# Requested closing discrepancies of the retained fine cap endpoints

The actual final and initial fine readings inherit the coarse closure join.
The one retained comparison supplies a common late stage and proves that the
closing increment tends below the request, without new polynomial sampling.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {index : Nat} {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample
    cap differential index box}

/-- The displayed initial value is read from the first retained polygon. -/
@[expose] public def firstValue : {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} → {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} →
    {target slope : Normalization.InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} → {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine →
      Normalization.InverseRootPolynomial.Gaussian
  | [], .nil, _, _, _, _, _, _, _ => 0
  | _ :: _, .cons _ _, _, _, _, _, _, _, charts => charts.1.first.vertex.value

/-- The displayed final value is read from the final retained polygon. -/
@[expose] public def lastValue : {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} → {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} →
    {target slope : Normalization.InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} → {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine →
      Normalization.InverseRootPolynomial.Gaussian
  | [], .nil, _, _, _, _, _, _, _ => 0
  | [_], .cons _ .nil, _, _, _, _, _, _, charts => charts.1.last.vertex.value
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
    lastValue charts.2

/-- The retained join from the original final fine chart to the supplied endpoint owner, trivial only for an empty bank.
-/
@[expose] public def LastEndpointJoin {point : Normalization.InverseRootPolynomial.Gaussian}
    {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)} (endpoint : Overlap cap
      point owner) :
    {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} → {bank :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} →
    {target slope : Normalization.InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} → {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine → Type
  | [], .nil, _, _, _, _, _, _, _ => PUnit
  | [_], .cons _ .nil, _, _, _, _, _, _, charts => Overlap.Join charts.1.last.request.prepared.coordinates endpoint
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
    LastEndpointJoin endpoint charts.2

/-- Transport the original coarse final join to the actual retained fine endpoint and supplied endpoint owner. -/
@[expose] public def lastEndpointJoin {firstPoint lastPoint : Normalization.InverseRootPolynomial.Gaussian}
    {firstOwner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : Overlap cap firstPoint firstOwner} {last : Overlap cap lastPoint lastOwner} (joined : Overlap.Join first
      last) :
    {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} → {bank :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} →
    {target slope : Normalization.InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} → {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.LastJoin first bank →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.LastEndpointJoin last charts
  | [], .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | [_], .cons data .nil, _, _, _, _, _, _, charts, coarse =>
      (data.point_join 1 (by decide) rfl data.last_eq.symm charts.1.last.request.prepared data.data.last).trans
        (coarse.trans joined)
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, coarse =>
    lastEndpointJoin joined charts.2
    coarse

/-- Prepare the original final fine-endpoint comparison using its retained join and the supplied endpoint floor. -/
@[expose] public def lastJunction {point : Normalization.InverseRootPolynomial.Gaussian}
    {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
    (endpoint : Overlap cap point owner) (endpointFloor : Nat) (error : Normalization.InverseRootPolynomial.Coordinate)
      (positive : 0 < error) :
    {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} → {bank :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} →
    {target slope : Normalization.InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} → {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.LastEndpointJoin endpoint charts → parents ≠ [] →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error
  | [], .nil, _, _, _, _, _, _, _, _, nonempty => (nonempty rfl).elim
  | [_], .cons _ .nil, _, _, _, _, _, _, charts, joined, _ =>
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.ofJoin joined capSample
        charts.1.last.evaluated.chart.stage endpointFloor error positive
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joined, _ =>
      lastJunction endpoint endpointFloor
        error positive charts.2 joined (by intro impossible; cases impossible)

/-- The final retained comparison targets the exact supplied endpoint's chart approximation. -/
theorem lastJunction_target {point : Normalization.InverseRootPolynomial.Gaussian}
    {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
    (endpoint : Overlap cap point owner) (endpointFloor : Nat) (error : Normalization.InverseRootPolynomial.Coordinate)
      (positive : 0 < error) :
    ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} {bank :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
      {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
        Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
      {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
        Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
      (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) (joined :
        Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.LastEndpointJoin endpoint charts) (nonempty :
        parents ≠ []),
      (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastJunction endpoint endpointFloor error positive
        charts joined nonempty).source.last =
        (endpoint.chartApproximation capSample).toApproximation
  | [], .nil, _, _, _, _, _, _, _, _, nonempty => (nonempty rfl).elim
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joined, _ =>
      lastJunction_target endpoint
        endpointFloor error positive charts.2 joined (by intro impossible; cases impossible)

/-- Refining the actual final chart reads the negative sample of the retained closing comparison's original source. -/
theorem lastJunction_value {point : Normalization.InverseRootPolynomial.Gaussian}
    {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
    (endpoint : Overlap cap point owner) (endpointFloor : Nat) (error : Normalization.InverseRootPolynomial.Coordinate)
      (positive : 0 < error) :
    ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} {bank :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
      {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
        Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
      {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
        Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
      (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) (joined :
        Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.LastEndpointJoin endpoint charts) (nonempty :
        parents ≠ [])
      (later : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage fine ≤ index) (next : Nat) (ready :
        charts.stage ≤ next),
      (charts.refine later next ready).lastValue =
        -(Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastJunction endpoint endpointFloor error
          positive charts joined nonempty).source.first.sample next
  | [], .nil, _, _, _, _, _, _, _, _, nonempty, _, _, _ => (nonempty rfl).elim
  | [_], .cons _ .nil, _, _, _, _, _, _, charts, _, _, later, next, ready =>
      charts.1.refine_last_value ((Purelib.Data.Nat.Order.le_max_left _ _).trans later) next
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans ready)
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joined, _, later, next, ready =>
      lastJunction_value endpoint
        endpointFloor error positive charts.2 joined (by intro impossible; cases impossible)
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans later) next ((Purelib.Data.Nat.Order.le_max_right _ _).trans
          ready)

set_option genInjectivity false in
/-- An empty path has no closing comparison; a nonempty path retains exactly
one. All late discrepancies refer to the actual refined endpoint values. -/
structure ClosingRequest {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
  {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) (error :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained list containing the original closing comparison when the parent bank is nonempty. -/ items : List
    (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error)
  /-- The actual closing comparison count is zero for an empty original parent bank and one otherwise. -/ count_eq :
    items.length = if parents = [] then 0 else 1
  /-- The sufficient common reading stage of the retained closing comparisons. -/ stage : Nat
  /-- The retained closing stage is exactly the maximum of the original comparison indices. -/ stage_eq : stage =
    Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum items
  /-- The actual refined initial-minus-final value equals the complete retained closing discrepancy sum. -/ value_eq : ∀
    (later : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage fine ≤ index) (next : Nat) (ready :
    charts.stage ≤ next),
    (charts.refine later next ready).firstValue - (charts.refine later next ready).lastValue =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun item => item.source.first.sample next -
        item.source.last.sample next))
  /-- At sufficient original chart and comparison stages, the actual refined closing increment meets the requested
    squared-norm error. -/ close : ∀ (later : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage fine
    ≤ index) (next : Nat) (ready : charts.stage ≤ next), stage ≤ next →
    Data.Gaussian.Norm.Basic.normSq ((charts.refine later next ready).firstValue - (charts.refine later next
      ready).lastValue) < error

constructive_injectivity ClosingRequest

namespace ClosingRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples in
/-- Prepare the unique original closing comparison for a nonempty retained fine path, or the exact empty request. -/
@[expose] public def build : ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} {bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {target slope : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {requests :
      Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor}
    {samples : Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    (charts : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine),
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ClosingJoin bank → (error :
      Normalization.InverseRootPolynomial.Coordinate) → 0 < error →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.ClosingRequest charts error
  | [], .nil, _, _, _, _, _, _, _, _, error, positive =>
      ⟨[], rfl, 0, rfl, (by intros; change (0 : Normalization.InverseRootPolynomial.Gaussian) - 0 = 0; ring1),
        (by intros; simpa only [Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.firstValue,
          Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastValue, Gaussian.Basic.sub_self,
          Gaussian.Norm.Basic.normSq_zero] using positive)⟩
  | _ :: _, .cons data rest, _, _, _, _, _, _, charts, coarse, error, positive => by
      let endpoint := charts.1.first.request.prepared.coordinates
      let joined := Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastEndpointJoin
        (data.point_join 0 (by decide) data.first_eq.symm rfl data.data.first charts.1.first.request.prepared) charts
          coarse
      let item := Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastJunction endpoint
        charts.1.first.evaluated.chart.stage error positive charts joined (by intro impossible; cases impossible)
      have values (later : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage _ ≤ index) (next : Nat)
        (ready : charts.stage ≤ next) :
          (charts.refine later next ready).firstValue - (charts.refine later next ready).lastValue =
            item.source.first.sample next - item.source.last.sample next := by
        rw [Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastJunction_value endpoint
          charts.1.first.evaluated.chart.stage error positive charts joined (by intro impossible; cases impossible)
          later next ready]
        change (charts.1.refine ((Purelib.Data.Nat.Order.le_max_left _ _).trans later) next
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans ready)).first.vertex.value - _ = _
        rw [Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest.Evaluation.refine_first_value,
          Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.lastJunction_target endpoint
            charts.1.first.evaluated.chart.stage error positive charts joined (by intro impossible; cases impossible)]
        change -charts.1.firstStream.sample next - -item.source.first.sample next =
          item.source.first.sample next - charts.1.firstStream.sample next
        ring1
      refine ⟨[item], rfl, Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum [item], rfl,
        ?_, ?_⟩
      · intro later next ready
        simpa only [List.map_cons, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, _root_.add_zero] using values
          later next ready
      · intro later next ready enough
        rw [values later next ready]
        have bounds := Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.indices_le [item] item
          (List.mem_cons_self ..)
        exact item.comparison.close (bounds.1.trans enough) (bounds.2.trans enough)

end ClosingRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
