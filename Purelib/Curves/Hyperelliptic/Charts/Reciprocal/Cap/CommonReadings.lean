module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
import Init.Data.List.Basic
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
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
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

public section

/-!
# Common-index refinement of retained cap readings

One finite index refines every cached point request. Shared parent vertices
remain literal shared readings, while the polynomial preparation and source
factor values are reused.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {center :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval center)} {count :
    Nat}
  {terminal : Terminal cap owner count} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential
    genus}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample terminal.preparation capSample}

namespace RetainedPoint

/-- Refine the original cached cap endpoint readings to one supplied later stage while reusing their requests and
polynomial samples. -/
@[expose] public def refine {point : InverseRootPolynomial.Gaussian} (retained : FineCharts.RetainedPoint comparison
  source point target floor)
    (stage : Nat) (later : retained.evaluated.chart.stage ≤ stage) : FineCharts.RetainedPoint comparison source point
      target floor :=
  ⟨retained.request, retained.evaluated.refine stage later⟩

/-- Transport of the original endpoint index preserves its retained reading stage. -/
theorem cast_stage {first last : InverseRootPolynomial.Gaussian} (retained : FineCharts.RetainedPoint comparison source
  first target floor) (equal : first = last) :
    (retained.cast equal).evaluated.chart.stage = retained.evaluated.chart.stage := by
  cases equal
  rfl

/-- Refining an original endpoint reading commutes with transport of its physical-point index. -/
theorem refine_cast {first last : InverseRootPolynomial.Gaussian} (retained : FineCharts.RetainedPoint comparison source
  first target floor)
    (equal : first = last) (stage : Nat) (later : retained.evaluated.chart.stage ≤ stage) :
    (retained.refine stage later).cast equal =
      (retained.cast equal).refine stage (by
          rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.RetainedPoint.cast_stage];
          exact later) := by
  cases equal
  rfl

end RetainedPoint

namespace PointRequest

/-- Equal original endpoint requests give exactly equal chart vertices after refinement to the same retained stage. -/
theorem refine_vertex_eq {first last : InverseRootPolynomial.Gaussian} (equal : first = last)
    {firstRequest : FineCharts.PointRequest comparison first target floor} {lastRequest : FineCharts.PointRequest
      comparison last target floor}
    (same : HEq firstRequest lastRequest)
    (left : PointRequest.Evaluation firstRequest source) (right : PointRequest.Evaluation lastRequest source)
    (stage : Nat) (leftLater : left.chart.stage ≤ stage) (rightLater : right.chart.stage ≤ stage) :
    (left.refine stage leftLater).vertex = (right.refine stage rightLater).vertex := by
  cases equal
  have requests := eq_of_heq same
  cases requests
  rfl

end PointRequest

namespace Samples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples in
/-- Compute a common stage above every original cached child endpoint reading. -/
@[expose] public def stage : {children : List (Parent curve differential)} → {requests : FineCharts.Requests comparison
  target floor children} →
    FineCharts.Samples source requests → Nat
  | _, .nil, _ => 0
  | _, .cons _ _, samples => max samples.1.first.chart.stage (max samples.1.last.chart.stage (stage samples.2))

/-- Refine the original cached cap endpoint readings to one supplied later stage while reusing their requests and
polynomial samples. -/
@[expose] public def refine : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) (next : Nat), samples.stage ≤ next → FineCharts.Samples source
      requests
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons _ _, samples, next, later =>
      ⟨ChildRequest.Evaluation.ofPoints
        (samples.1.first.refine next ((Purelib.Data.Nat.Order.le_max_left _ _).trans later))
        (samples.1.last.refine next ((Purelib.Data.Nat.Order.le_max_left _ _).trans
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))),
        refine samples.2 next ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _
          _).trans later))⟩

/-- The original first endpoint reading stage is bounded by the retained child-bank maximum. -/
theorem firstPoint_stage_le : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ []),
    (samples.firstPoint chain nonempty).evaluated.chart.stage ≤ samples.stage
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | child :: _, .cons request _, samples, _, _, chain, _ => by
      obtain ⟨chain⟩ := chain
      cases chain
      exact (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.RetainedPoint.cast_stage ⟨request.first,
        samples.1.first⟩ child.edge.point_zero).trans_le (Purelib.Data.Nat.Order.le_max_left _ _)

/-- The original last endpoint reading stage is bounded by the retained child-bank maximum. -/
theorem lastPoint_stage_le : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ []),
    (samples.lastPoint chain nonempty).evaluated.chart.stage ≤ samples.stage
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | [child], .cons request .nil, samples, _, _, chain, _ => by
      obtain ⟨chain⟩ := chain
      cases chain with
      | cons _ tail =>
          cases tail
          exact (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.RetainedPoint.cast_stage ⟨request.last,
            samples.1.last⟩ child.edge.point_one).trans_le
            ((Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _))
  | _ :: _ :: _, .cons _ (.cons _ _), samples, _, _, chain, _ =>
      (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.lastPoint_stage_le samples.2 _ (by
        intro impossible;
        cases impossible)).trans
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _))

/-- The first endpoint of the refined original bank is exactly the refinement of its retained first endpoint. -/
theorem firstPoint_refine : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ [])
    (next : Nat) (later : samples.stage ≤ next),
    (samples.refine next later).firstPoint chain nonempty =
      (samples.firstPoint chain nonempty).refine next ((samples.firstPoint_stage_le chain nonempty).trans later)
  | [], .nil, _, _, _, _, nonempty, _, _ => (nonempty rfl).elim
  | child :: _, .cons request _, samples, _, _, chain, _, next, later => by
      obtain ⟨chain⟩ := chain
      cases chain
      exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.RetainedPoint.refine_cast ⟨request.first,
        samples.1.first⟩ child.edge.point_zero next
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans later)

/-- The last endpoint of the refined original bank is exactly the refinement of its retained last endpoint. -/
theorem lastPoint_refine : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ [])
    (next : Nat) (later : samples.stage ≤ next),
    (samples.refine next later).lastPoint chain nonempty =
      (samples.lastPoint chain nonempty).refine next ((samples.lastPoint_stage_le chain nonempty).trans later)
  | [], .nil, _, _, _, _, nonempty, _, _ => (nonempty rfl).elim
  | [child], .cons request .nil, samples, _, _, chain, _, next, later => by
      obtain ⟨chain⟩ := chain
      cases chain with
      | cons _ tail =>
          cases tail
          exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.RetainedPoint.refine_cast ⟨request.last,
            samples.1.last⟩ child.edge.point_one next
            ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))
  | _ :: _ :: _, .cons _ (.cons _ _), samples, _, _, _, _, next, later =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.lastPoint_refine samples.2 _ (by
        intro impossible;
        cases impossible) next ((Purelib.Data.Nat.Order.le_max_right _ _).trans
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))

/-- The first original child begins at the retained chain's actual starting coordinate. -/
private theorem head_coordinate {child : Parent curve differential} {children : List (Parent curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain (child :: children) (start := first) (finish := last)) :
      child.edge.point 0 = first.coordinate := by
  cases chain
  exact child.edge.point_zero

/-- A common later stage preserves literal shared chart vertices along the original retained child chain. -/
theorem refine_shared : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests), Requests.Shared requests → {first last : Lifted.Basic.LiftedPoint 2}
      →
    PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last) → (next : Nat) → (later :
      samples.stage ≤ next) →
      (samples.refine next later).Shared
  | [], .nil, _, _, _, _, _, _, _ => trivial
  | [_], .cons _ .nil, _, _, _, _, _, _, _ => trivial
  | child :: _ :: _, .cons _ (.cons _ _), samples, shared, _, _, .cons _ tail, next, later =>
      ⟨PointRequest.refine_vertex_eq (child.edge.point_one.trans
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.head_coordinate tail).symm) shared.1
        samples.1.last samples.2.1.first next _ _,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.refine_shared samples.2 shared.2 tail next
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))⟩

/-- Read only the cached chart increments, without evaluating the source polynomial again to recover the other
projection of a row. -/
@[expose] public def increments : {children : List (Parent curve differential)} → {requests : FineCharts.Requests
  comparison target floor children} →
    FineCharts.Samples source requests → List InverseRootPolynomial.Gaussian
  | _, .nil, _ => []
  | _, .cons _ _, samples => samples.1.increment ::
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.increments samples.2

/-- The cached original chart increment list is exactly the first projection of the retained row list. -/
theorem increments_rows : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests), samples.increments = samples.rows.map Prod.fst
  | _, .nil, _ => rfl
  | _, .cons _ _, samples => congrArg (List.cons _)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.increments_rows samples.2)

/-- Zipping the two original list projections reconstructs the exact retained pair list. -/
private theorem zip_projections : ∀ (pairs : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)),
  List.zip (pairs.map Prod.fst) (pairs.map Prod.snd) = pairs
  | [] => rfl
  | pair :: pairs => congrArg (List.cons pair)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.zip_projections pairs)

/-- Reuse every previously evaluated source value while replacing only the chart increment. The certificate identifies
the complete resulting row list. -/
@[expose] public def refreshRows {children : List (Parent curve differential)} {requests : FineCharts.Requests
  comparison target floor children}
    (samples : FineCharts.Samples source requests) (cached : List (InverseRootPolynomial.Gaussian ×
      InverseRootPolynomial.Gaussian)) : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) :=
  List.zip samples.increments (cached.map Prod.snd)

/-- Refreshing chart increments while retaining equal original source projections reconstructs the exact evaluated rows.
-/
theorem refreshRows_eq {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison target
  floor children}
    (samples : FineCharts.Samples source requests) (cached : List (InverseRootPolynomial.Gaussian ×
      InverseRootPolynomial.Gaussian))
    (sourceEq : cached.map Prod.snd = samples.rows.map Prod.snd) : samples.refreshRows cached = samples.rows := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.refreshRows,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.increments_rows, sourceEq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.zip_projections _

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
