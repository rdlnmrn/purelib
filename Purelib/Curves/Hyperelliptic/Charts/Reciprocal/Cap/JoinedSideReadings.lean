module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinedArea
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CommonReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Basic
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
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

public section

/-!
# One finite reading index for every retained cap-side junction

The junction comparisons use the actual cached polygon endpoint channels.
Their indices and the existing reading indices determine one common stage;
all parent polygons can then be refined against their retained source rows.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank (Requests Samples)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}
  {index : Nat} {box : Geometry.Rational.Box} {capSample :
    Primitives.Sample cap differential index box}

/-- Read the maximum current chart-reading stage over the retained fine parent polygons. -/
@[expose] public def stage : {parents : List (Parent curve differential)} → {bank : Bank cap
  differential count parents} →
    {target slope : Coordinate} → {floor : Nat} → {requests : Requests bank target floor} →
    {samples : Samples requests capSample} → {fine : FineRequests requests slope} → FineSamples samples
      fine → Nat
  | _, .nil, _, _, _, _, _, _, _ => 0
  | _, .cons _ _, _, _, _, _, _, _, charts => max charts.1.charts.stage
    (FineSamples.stage charts.2)

/-- Refine every retained fine polygon to the supplied common stage while preserving its original source request. -/
@[expose] public def refine : {parents : List (Parent curve differential)} → {bank : Bank cap
  differential count parents} →
    {target slope : Coordinate} → {floor : Nat} → {requests : Requests bank target floor} →
    {samples : Samples requests capSample} → {fine : FineRequests requests slope} →
    (charts : FineSamples samples fine) → FineRequests.stage fine ≤ index → (next : Nat) →
    charts.stage ≤ next → FineSamples samples fine
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => ⟨⟩
  | _, .cons _ _, _, _, _, _, _, _, charts, later, next, ready =>
      ⟨charts.1.refine ((Data.Nat.Order.le_max_left _ _).trans later) next ((Data.Nat.Order.le_max_left
        _ _).trans ready),
        refine charts.2 ((Data.Nat.Order.le_max_right _ _).trans later) next
          ((Data.Nat.Order.le_max_right _ _).trans ready)⟩

set_option genInjectivity false in
/-- The actual two cached endpoint channels at a parent boundary. -/
structure StreamPair where
  /-- The first actual endpoint approximation stream at the retained parent boundary. -/ first :
    ApproximationData
  /-- The second actual endpoint approximation stream at the retained parent boundary. -/ last :
    ApproximationData
  /-- The retained first endpoint's current reading stage. -/ firstFloor : Nat
  /-- The retained second endpoint's current reading stage. -/ lastFloor : Nat

constructive_injectivity StreamPair

set_option genInjectivity false in
/-- An operational comparison of the actual endpoint streams at one retained parent junction. -/
structure Junction (error : Coordinate) where
  /-- The exact pair of cached endpoint streams and their retained stage floors. -/ source :
    StreamPair
  /-- The comparison certificate pays the supplied error for these exact two streams. -/ comparison :
    Comparison source.first source.last source.firstFloor source.lastFloor error

constructive_injectivity Junction

namespace Junction

/-- Request an operational comparison of the endpoint streams certified by the supplied coordinate join. -/
@[expose] public def ofJoin {firstPoint lastPoint : Gaussian}
    {firstOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : RootCoordinates.Overlap cap firstPoint firstOwner}
    {last : RootCoordinates.Overlap cap lastPoint lastOwner}
    (join : RootCoordinates.Overlap.Join first last)
    (sample : Primitives.Sample cap differential index box)
    (firstFloor lastFloor : Nat) (error : Coordinate) (positive : 0 < error) :
      Junction error :=
  ⟨⟨(first.chartApproximation sample).toApproximation, (last.chartApproximation sample).toApproximation,
    firstFloor, lastFloor⟩, (join.readings sample).compare firstFloor lastFloor error positive⟩

/-- Compute a common stage above both indices of every retained endpoint comparison. -/
@[expose] public def maximum {error : Coordinate} : List
  (Junction error) → Nat
  | [] => 0
  | item :: rest => max item.comparison.leftIndex (max item.comparison.rightIndex
    (Junction.maximum rest))

/-- Both indices of any retained junction comparison are bounded by the cached list maximum. -/
theorem indices_le {error : Coordinate} (items : List
  (Junction error))
    (item : Junction error) (member : item ∈
      items) :
    item.comparison.leftIndex ≤ maximum
      items ∧ item.comparison.rightIndex ≤
      maximum items := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases Purelib.Data.List.Membership.mem_cons.mp member with
      | inl equal =>
          subst item
          exact ⟨Data.Nat.Order.le_max_left _ _, (Data.Nat.Order.le_max_left _ _).trans
            (Data.Nat.Order.le_max_right _ _)⟩
      | inr member =>
          have retained := ih member
          have tailLe : maximum tail ≤
            maximum (head :: tail) :=
            (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
          exact ⟨retained.1.trans tailLe, retained.2.trans tailLe⟩

end Junction

section Boundary

variable {parent next : Parent curve differential} {parents
  : List (Parent curve differential)}
    {data : ParentData cap differential count parent}
      {nextData : ParentData cap differential count next}
    {remaining : Bank cap differential count parents}
      {target slope : Coordinate} {floor : Nat}
    {requests : Requests (.cons data (.cons
      nextData remaining)) target floor}
    {samples : Samples requests capSample} {fine :
      FineRequests requests slope}

/-- Read the exact last and first endpoint streams of two consecutive retained parent polygons. -/
@[expose] public def headStreams (charts : FineSamples samples fine) : StreamPair :=
  ⟨charts.1.lastStream, charts.2.1.firstStream,
    charts.1.last.evaluated.chart.stage, charts.2.1.first.evaluated.chart.stage⟩

/-- Build the comparison for the first retained parent boundary from its cached endpoint join. -/
@[expose] public def headJunction (charts : FineSamples samples fine) (joins : EndpointJoins charts)
    (error : Coordinate) (positive : 0 < error) :
      Junction error :=
  Junction.ofJoin joins.head capSample
    charts.1.last.evaluated.chart.stage charts.2.1.first.evaluated.chart.stage error positive

end Boundary

/-- Read every actual parent-boundary endpoint pair in its retained order. -/
@[expose] public def streamPairs : {parents : List (Parent curve differential)} → {bank : Bank cap
  differential count parents} →
    {target slope : Coordinate} → {floor : Nat} → {requests : Requests bank target floor} →
    {samples : Samples requests capSample} → {fine : FineRequests requests slope} →
    FineSamples samples fine → List
      StreamPair
  | [], .nil, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, _ => []
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
      headStreams charts ::
        FineSamples.streamPairs charts.2

set_option genInjectivity false in
/-- Flat retained comparisons, with exact ordered provenance for every junction. -/
structure JunctionRequests {parents : List (Parent curve differential)} {bank : Bank cap
  differential count parents}
    {target slope : Coordinate} {floor : Nat} {requests : Requests bank target floor}
    {samples : Samples requests capSample} {fine : FineRequests requests slope}
    (charts : FineSamples samples fine) (error : Coordinate) where
  /-- The cached ordered endpoint comparisons for all retained parent boundaries. -/ items : List
    (Junction error)
  /-- The comparison sources are exactly the ordered endpoint pairs of the retained fine polygons. -/ sources_eq :
    items.map Junction.source =
    streamPairs charts
  /-- The cached common stage above both indices of every retained junction comparison. -/ stage : Nat
  /-- The retained common stage equals the maximum of both comparison indices at every junction. -/ stage_eq : stage =
    Junction.maximum items

constructive_injectivity JunctionRequests

namespace JunctionRequests

/-- Construct one endpoint comparison per retained parent boundary from its exact cached coordinate join. -/
@[expose] public def buildItems : {parents : List (Parent curve differential)} → {bank : Bank cap
  differential count parents} →
    {target slope : Coordinate} → {floor : Nat} → {requests : Requests bank target floor} →
    {samples : Samples requests capSample} → {fine : FineRequests requests slope} →
    (charts : FineSamples samples fine) → EndpointJoins charts → (error :
      Coordinate) → 0 < error → List
      (Junction error)
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, _ => []
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joins, error, positive =>
      headJunction charts joins error positive ::
        JunctionRequests.buildItems
          charts.2 joins.tail error positive

/-- The constructed junction comparisons preserve the exact ordered endpoint-stream provenance. -/
public theorem buildItems_sources : {parents : List (Parent curve differential)} → {bank : Bank cap
  differential count parents} →
    {target slope : Coordinate} → {floor : Nat} → {requests : Requests bank target floor} →
    {samples : Samples requests capSample} → {fine : FineRequests requests slope} →
    (charts : FineSamples samples fine) → (joins : EndpointJoins charts) → (error :
      Coordinate) → (positive : 0 < error) →
    (buildItems charts joins
      error positive).map Junction.source =
      streamPairs charts
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joins, error, positive =>
      congrArg (List.cons _)
        (buildItems_sources
        charts.2 joins.tail error positive)

/-- Cache the complete ordered junction-comparison list and its common reading stage. -/
@[expose] public def build {parents : List (Parent curve differential)} {bank : Bank cap
  differential count parents}
    {target slope : Coordinate} {floor : Nat} {requests : Requests bank target floor}
    {samples : Samples requests capSample} {fine : FineRequests requests slope}
    (charts : FineSamples samples fine) (joins : EndpointJoins charts) (error :
      Coordinate) (positive : 0 < error) :
    JunctionRequests charts error :=
  let items := buildItems
    charts joins error positive
  ⟨items,
    buildItems_sources
    charts joins error positive, Junction.maximum
    items, rfl⟩

end JunctionRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
