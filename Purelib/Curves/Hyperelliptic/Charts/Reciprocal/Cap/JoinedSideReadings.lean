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

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the maximum current chart-reading stage over the retained fine parent polygons. -/
@[expose] public def stage : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} → Bank.FineSamples samples
      fine → Nat
  | _, .nil, _, _, _, _, _, _, _ => 0
  | _, .cons _ _, _, _, _, _, _, _, charts => max charts.1.charts.stage
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.stage charts.2)

/-- Refine every retained fine polygon to the supplied common stage while preserving its original source request. -/
@[expose] public def refine : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → FineRequests.stage fine ≤ index → (next : Nat) →
    charts.stage ≤ next → Bank.FineSamples samples fine
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => ⟨⟩
  | _, .cons _ _, _, _, _, _, _, _, charts, later, next, ready =>
      ⟨charts.1.refine ((Purelib.Data.Nat.Order.le_max_left _ _).trans later) next ((Purelib.Data.Nat.Order.le_max_left
        _ _).trans ready),
        refine charts.2 ((Purelib.Data.Nat.Order.le_max_right _ _).trans later) next
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans ready)⟩

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
structure Junction (error : InverseRootPolynomial.Coordinate) where
  /-- The exact pair of cached endpoint streams and their retained stage floors. -/ source :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.StreamPair
  /-- The comparison certificate pays the supplied error for these exact two streams. -/ comparison :
    Gaussian.Equivalence.Comparison source.first source.last source.firstFloor source.lastFloor error

constructive_injectivity Junction

namespace Junction

/-- Request an operational comparison of the endpoint streams certified by the supplied coordinate join. -/
@[expose] public def ofJoin {firstPoint lastPoint : InverseRootPolynomial.Gaussian}
    {firstOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : RootCoordinates.Overlap cap firstPoint firstOwner}
    {last : RootCoordinates.Overlap cap lastPoint lastOwner}
    (join : RootCoordinates.Overlap.Join first last)
    (sample : Primitives.Sample cap differential index box)
    (firstFloor lastFloor : Nat) (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error :=
  ⟨⟨(first.chartApproximation sample).toApproximation, (last.chartApproximation sample).toApproximation,
    firstFloor, lastFloor⟩, (join.readings sample).compare firstFloor lastFloor error positive⟩

/-- Compute a common stage above both indices of every retained endpoint comparison. -/
@[expose] public def maximum {error : InverseRootPolynomial.Coordinate} : List
  (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error) → Nat
  | [] => 0
  | item :: rest => max item.comparison.leftIndex (max item.comparison.rightIndex
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum rest))

/-- Both indices of any retained junction comparison are bounded by the cached list maximum. -/
theorem indices_le {error : InverseRootPolynomial.Coordinate} (items : List
  (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error))
    (item : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error) (member : item ∈
      items) :
    item.comparison.leftIndex ≤ Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum
      items ∧ item.comparison.rightIndex ≤
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum items := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases Purelib.Data.List.Membership.mem_cons.mp member with
      | inl equal =>
          subst item
          exact ⟨Purelib.Data.Nat.Order.le_max_left _ _, (Purelib.Data.Nat.Order.le_max_left _ _).trans
            (Purelib.Data.Nat.Order.le_max_right _ _)⟩
      | inr member =>
          have retained := ih member
          have tailLe : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum tail ≤
            Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum (head :: tail) :=
            (Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)
          exact ⟨retained.1.trans tailLe, retained.2.trans tailLe⟩

end Junction

section Boundary

variable {parent next : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents
  : List (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent}
      {nextData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count next}
    {remaining : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
      {target slope : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
    {requests : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests (.cons data (.cons
      nextData remaining)) target floor}
    {samples : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample} {fine :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}

/-- Read the exact last and first endpoint streams of two consecutive retained parent polygons. -/
@[expose] public def headStreams (charts : Bank.FineSamples samples fine) : StreamPair :=
  ⟨charts.1.lastStream, charts.2.1.firstStream,
    charts.1.last.evaluated.chart.stage, charts.2.1.first.evaluated.chart.stage⟩

/-- Build the comparison for the first retained parent boundary from its cached endpoint join. -/
@[expose] public def headJunction (charts : Bank.FineSamples samples fine) (joins : FineSamples.EndpointJoins charts)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.ofJoin joins.head capSample
    charts.1.last.evaluated.chart.stage charts.2.1.first.evaluated.chart.stage error positive

end Boundary

/-- Read every actual parent-boundary endpoint pair in its retained order. -/
@[expose] public def streamPairs : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    Bank.FineSamples samples fine → List
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.StreamPair
  | [], .nil, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, _ => []
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.headStreams charts ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.streamPairs charts.2

set_option genInjectivity false in
/-- Flat retained comparisons, with exact ordered provenance for every junction. -/
structure JunctionRequests {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap
  differential count parents}
    {target slope : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine : Bank.FineRequests requests slope}
    (charts : Bank.FineSamples samples fine) (error : InverseRootPolynomial.Coordinate) where
  /-- The cached ordered endpoint comparisons for all retained parent boundaries. -/ items : List
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error)
  /-- The comparison sources are exactly the ordered endpoint pairs of the retained fine polygons. -/ sources_eq :
    items.map Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.source =
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.streamPairs charts
  /-- The cached common stage above both indices of every retained junction comparison. -/ stage : Nat
  /-- The retained common stage equals the maximum of both comparison indices at every junction. -/ stage_eq : stage =
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum items

constructive_injectivity JunctionRequests

namespace JunctionRequests

/-- Construct one endpoint comparison per retained parent boundary from its exact cached coordinate join. -/
@[expose] public def buildItems : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → FineSamples.EndpointJoins charts → (error :
      InverseRootPolynomial.Coordinate) → 0 < error → List
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction error)
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, _ => []
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joins, error, positive =>
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.headJunction charts joins error positive ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests.buildItems
          charts.2 joins.tail error positive

/-- The constructed junction comparisons preserve the exact ordered endpoint-stream provenance. -/
public theorem buildItems_sources : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (joins : FineSamples.EndpointJoins charts) → (error :
      InverseRootPolynomial.Coordinate) → (positive : 0 < error) →
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests.buildItems charts joins
      error positive).map Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.source =
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.streamPairs charts
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, joins, error, positive =>
      congrArg (List.cons _)
        (buildItems_sources
        charts.2 joins.tail error positive)

/-- Cache the complete ordered junction-comparison list and its common reading stage. -/
@[expose] public def build {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap
  differential count parents}
    {target slope : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine : Bank.FineRequests requests slope}
    (charts : Bank.FineSamples samples fine) (joins : FineSamples.EndpointJoins charts) (error :
      InverseRootPolynomial.Coordinate) (positive : 0 < error) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests charts error :=
  let items := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests.buildItems
    charts joins error positive
  ⟨items,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests.buildItems_sources
    charts joins error positive, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.Junction.maximum
    items, rfl⟩

end JunctionRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
