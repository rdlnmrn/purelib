module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinedArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideReadings
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CommonReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
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
# Actual connectors between the refined cap polygons

The junction increments are differences of retained polygon endpoints. Their
bounds come from the requested streams at the same common index as every
vertex of the refined polygons. Summaries reuse the cached parent areas.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Path.IncrementAreaJoins
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank (Requests Samples)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the actual coordinate differences joining consecutive retained fine polygons. -/
@[expose] public def gaps : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    Bank.FineSamples samples fine → List InverseRootPolynomial.Gaussian
  | [], .nil, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, _ => []
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
      (charts.2.1.first.vertex.value - charts.1.last.vertex.value) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.gaps charts.2

/-- Refined polygon gaps equal the differences of their exact retained endpoint streams at the common stage. -/
theorem gaps_refine : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential
  count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (later : FineRequests.stage fine ≤ index) → (next : Nat) →
    (ready : charts.stage ≤ next) →
    (charts.refine later next ready).gaps = charts.streamPairs.map (fun pair => pair.first.sample next -
      pair.last.sample next)
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, later, next, ready => by
      simp only [Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.gaps, FineSamples.refine,
        FineSamples.streamPairs, List.map_cons,
        Evaluation.refine_first_value,
        Evaluation.refine_last_value]
      apply congrArg₂ List.cons
      · change -charts.2.1.firstStream.sample next - -charts.1.lastStream.sample next =
          charts.1.lastStream.sample next - charts.2.1.firstStream.sample next
        ring1
      · exact Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.gaps_refine charts.2
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans later) next ((Purelib.Data.Nat.Order.le_max_right _ _).trans
          ready)

namespace JunctionRequests

/-- At every later common stage, each retained junction stream pair satisfies its requested error. -/
theorem close {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap differential count
  parents}
    {target slope error : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine : Bank.FineRequests requests slope} {charts : Bank.FineSamples
      samples fine}
    (junctions : FineSamples.JunctionRequests charts error) {next : Nat} (later : junctions.stage ≤ next)
    (pair : FineSamples.StreamPair) (member : pair ∈ charts.streamPairs) :
    Data.Gaussian.Norm.Basic.normSq (pair.first.sample next - pair.last.sample next) < error := by
  rw [← junctions.sources_eq] at member
  obtain ⟨item, retained, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  have upper : Junction.maximum junctions.items ≤ next := junctions.stage_eq ▸ later
  have indices := Junction.indices_le junctions.items item retained
  exact item.comparison.close (indices.1.trans upper) (indices.2.trans upper)

/-- Every actual refined polygon connector satisfies the paid junction error at the selected common stage. -/
theorem gaps_small {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap differential count
  parents}
    {target slope error : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine : Bank.FineRequests requests slope} {charts : Bank.FineSamples
      samples fine}
    (junctions : FineSamples.JunctionRequests charts error) (later : FineRequests.stage fine ≤ index) (next : Nat)
    (ready : charts.stage ≤ next) (joined : junctions.stage ≤ next) :
    ∀ gap ∈ (charts.refine later next ready).gaps, Data.Gaussian.Norm.Basic.normSq gap < error := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.gaps_refine]
  intro gap member
  obtain ⟨pair, retained, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  exact junctions.close joined pair retained

end JunctionRequests

/-- Each connector belongs to the next retained polygon. The first entry can be zero, giving a duplicate initial vertex
without an added area term. -/
@[expose] public def connectedBlocks : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank
  cap differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    Bank.FineSamples samples fine → InverseRootPolynomial.Gaussian → List (InverseRootPolynomial.Gaussian × List
      InverseRootPolynomial.Gaussian)
  | [], .nil, _, _, _, _, _, _, _, _ => []
  | [_], .cons _ .nil, _, _, _, _, _, _, charts, entry => [(entry, charts.1.pairs.map Prod.fst)]
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, entry =>
      (entry, charts.1.pairs.map Prod.fst) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connectedBlocks charts.2
        (charts.2.1.first.vertex.value - charts.1.last.vertex.value)

/-- There is exactly one connected path block per retained parent. -/
theorem connectedBlocks_length : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (entry : InverseRootPolynomial.Gaussian) → (charts.connectedBlocks
      entry).length = parents.length
  | [], .nil, _, _, _, _, _, _, _, _ => rfl
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, _ =>
      congrArg Nat.succ
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connectedBlocks_length charts.2
        _)

/-- Removing the retained incoming connectors recovers exactly the original fine polygon paths. -/
theorem connectedBlocks_source : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (entry : InverseRootPolynomial.Gaussian) →
    (charts.connectedBlocks entry).map Prod.snd = charts.pairs.map Prod.fst
  | [], .nil, _, _, _, _, _, _, _, _ => rfl
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _ => rfl
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, _ =>
      congrArg (List.cons _)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connectedBlocks_source charts.2
        _)

/-- Every connected block's actual incoming connector satisfies the supplied shared norm bound. -/
theorem connectedBlocks_small : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope error : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target
      floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (entry : InverseRootPolynomial.Gaussian) →
      Data.Gaussian.Norm.Basic.normSq entry ≤ error →
    (∀ gap ∈ charts.gaps, Data.Gaussian.Norm.Basic.normSq gap ≤ error) → ∀ block ∈ charts.connectedBlocks
      entry, Data.Gaussian.Norm.Basic.normSq block.1 ≤ error
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _, member => by cases member
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _, _, small, _, _, member => by
      cases Purelib.Data.List.Membership.mem_cons.mp member with
      | inl equal => subst equal; exact small
      | inr member => cases member
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, _, charts, _, small, bounded, _, member => by
      cases Purelib.Data.List.Membership.mem_cons.mp member with
      | inl equal => subst equal; exact small
      | inr member =>
          exact Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connectedBlocks_small
            charts.2 _ (bounded _ (List.mem_cons_self))
            (fun gap retained => bounded gap (List.mem_cons_of_mem _ retained)) _ member

/-- Compose the cached summaries; do not sum the fine increments again. -/
@[expose] public def connectedSummary : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank
  cap differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine : Bank.FineRequests requests slope} →
    (charts : Bank.FineSamples samples fine) → (entry : InverseRootPolynomial.Gaussian) →
    IncrementArea.Summary ((charts.connectedBlocks entry).map (fun block => block.1 :: block.2)).flatten
  | [], .nil, _, _, _, _, _, _, _, _ => IncrementArea.Summary.build []
  | [_], .cons _ .nil, _, _, _, _, _, _, charts, entry => (Summary.prepend charts.1.chart entry).append
    (IncrementArea.Summary.build [])
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, entry =>
      (Summary.prepend charts.1.chart entry).append
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.connectedSummary charts.2 _)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
