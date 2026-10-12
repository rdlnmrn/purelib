module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Tactic.Ring

public section

/-!
# Literal polygons through the retained cap-chart readings

Each common subdivision endpoint contributes one cached vertex. The old
increment area is exactly the area of this vertex polygon with its closing
edge included, even when its first and last root readings are different.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent)
open Purelib.Integration.Path.BoundaryRibbon (area)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus}
  {target : Coordinate} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Vertex

/-- Read consecutive differences of the cached original cap-chart vertex values. -/
@[expose] public def steps (first : FineCharts.Vertex capSample target) : List (FineCharts.Vertex capSample target) →
  List InverseRootPolynomial.Gaussian
  | [] => []
  | next :: remaining => (next.value - first.value) ::
    steps next remaining

/-- Read the ordered increments of the original retained vertex polygon. -/
@[expose] public def increments : List (FineCharts.Vertex capSample target) → List InverseRootPolynomial.Gaussian
  | [] => []
  | first :: remaining => steps first remaining

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex in
/-- Read the last original retained vertex, using the supplied first vertex when the tail is empty. -/
@[expose] public def finish (first : FineCharts.Vertex capSample target) : List (FineCharts.Vertex capSample target) →
  FineCharts.Vertex capSample target
  | [] => first
  | next :: remaining => finish next remaining

/-- Sum the oriented edge areas along the original retained open vertex chain. -/
@[expose] public def openArea (first : FineCharts.Vertex capSample target) : List (FineCharts.Vertex capSample target) →
  InverseRootPolynomial.Gaussian
  | [] => 0
  | next :: remaining => BoundaryRibbon.area first.value next.value +
    openArea next remaining

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex
/-- The closing edge is explicit and need not be a zero edge. -/
@[expose] public def closedArea : List (FineCharts.Vertex capSample target) → InverseRootPolynomial.Gaussian
  | [] => 0
  | first :: remaining => openArea first remaining +
    BoundaryRibbon.area (finish first remaining).value first.value

/-- The original retained vertex increments telescope to the last value minus the first. -/
theorem steps_sum (first : FineCharts.Vertex capSample target) (remaining : List (FineCharts.Vertex capSample target)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (steps
      first remaining) = (finish first remaining).value - first.value := by
  induction remaining generalizing first with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = first.value - first.value; ring1
  | cons next remaining previous =>
      simp only [steps,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, finish, previous]
      ring1

end

/-- Tracing the original retained increments from the first value gives the open vertex-chain area. -/
theorem steps_area (first : FineCharts.Vertex capSample target) (remaining : List (FineCharts.Vertex capSample target))
  :
    IncrementArea.traceArea first.value (steps first
      remaining) = openArea first remaining := by
  induction remaining generalizing first with
  | nil => rfl
  | cons next remaining previous =>
      rewrite [steps, IncrementArea.traceArea,
        openArea,
        show first.value + (next.value - first.value) = next.value by ring1, previous]
      exact Eq.refl _

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex in
/-- The original increment path area equals the retained vertex polygon area with its explicit closing edge. -/
theorem area_eq (vertices : List (FineCharts.Vertex capSample target)) :
    IncrementArea.pathArea (increments vertices) =
      closedArea vertices := by
  cases vertices with
  | nil => rfl
  | cons first remaining =>
      have translated := IncrementArea.traceArea_eq first.value
        (steps first remaining)
      rw [steps_area,
        steps_sum, BoundaryRibbon.area_sub_self_right] at translated
      have reverse : BoundaryRibbon.area (finish first remaining).value first.value = -BoundaryRibbon.area first.value
        (finish first remaining).value := by
        unfold BoundaryRibbon.area
        ring1
      simp only [increments,
        closedArea, reverse, translated]
      ring1

end Vertex

set_option genInjectivity false in
/-- A finite chart polygon keeps its existing total and area summaries. The closing edge belongs to the area
specification; root closure is not a precondition of this data. -/
structure Polygon (capSample : Primitives.Sample cap differential index box) where
  /-- The original square-residual target shared by the retained chart vertices. -/ target :
    InverseRootPolynomial.Coordinate
  /-- The original ordered chart vertices at the retained square-residual target. -/ vertices : List (FineCharts.Vertex
    capSample target)
  /-- The cached sum of the original retained polygon increments. -/ total : InverseRootPolynomial.Gaussian
  /-- The cached total is exactly the sum of the actual vertex increments. -/ total_eq : total =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.increments vertices)
  /-- The cached oriented area including the original explicit closing edge. -/ area : InverseRootPolynomial.Gaussian
  /-- The cached area equals the closed area of these exact original vertices. -/ area_eq : area =
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.closedArea vertices

constructive_injectivity Polygon

variable {center : Gaussian} {owner :
  Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
  ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval center)}
  {count : Nat} {terminal : Terminal cap owner count} {comparison :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential}
  {floor : Nat} {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample
    terminal.preparation capSample}

/-- The two actual endpoint chart values differ by the retained original child increment. -/
private theorem child_step {child : Parent curve differential} {request : FineCharts.ChildRequest comparison child
  target floor}
    (evaluated : ChildRequest.Evaluation request source) : evaluated.last.vertex.value - evaluated.first.vertex.value =
      evaluated.increment := by
  rw [evaluated.increment_eq]
  change -evaluated.last.chart.reading.value - -evaluated.first.chart.reading.value = _
  ring1

namespace Samples

/-- Read the retained terminal chart vertex of every original evaluated child. -/
@[expose] public def finishes : {children : List (Parent curve differential)} → {requests : FineCharts.Requests
  comparison target floor children} →
    FineCharts.Samples source requests → List (FineCharts.Vertex capSample target)
  | _, .nil, _ => []
  | _, .cons _ _, samples => samples.1.last.vertex ::
    finishes samples.2

/-- Read the original first chart vertex followed by every retained child's terminal vertex. -/
@[expose] public def vertices : {children : List (Parent curve differential)} → {requests : FineCharts.Requests
  comparison target floor children} →
    FineCharts.Samples source requests → List (FineCharts.Vertex capSample target)
  | _, .nil, _ => []
  | _, .cons _ _, samples => samples.1.first.vertex ::
    finishes samples

/-- The retained terminal chart vertices display exactly the original child endpoint coordinates. -/
theorem finishes_points : {children : List (Parent curve differential)} → {requests : FineCharts.Requests comparison
  target floor children} →
    (samples : FineCharts.Samples source requests) →
      (finishes samples).map Vertex.point = children.map
      (fun child => child.edge.point 1)
  | _, .nil, _ => rfl
  | _, .cons _ _, samples => congrArg (List.cons _)
    (finishes_points samples.2)

/-- There is exactly one retained terminal chart vertex for each original child. -/
theorem finishes_length : {children : List (Parent curve differential)} → {requests : FineCharts.Requests comparison
  target floor children} →
    (samples : FineCharts.Samples source requests) →
      (finishes samples).length = children.length
  | _, .nil, _ => rfl
  | _, .cons _ _, samples => congrArg Nat.succ
    (finishes_length samples.2)

/-- A nonempty original child chain has one more retained chart vertex than children. -/
theorem vertices_length {child : Parent curve differential} {children : List (Parent curve differential)}
    {requests : FineCharts.Requests comparison target floor (child :: children)} (samples : FineCharts.Samples source
      requests) :
    samples.vertices.length = (child :: children).length + 1 := by
  cases requests with
  | cons request remaining =>
    exact congrArg Nat.succ (finishes_length samples)

/-- The original nonempty retained child chain has exactly its child count plus one vertices. -/
theorem vertices_length_of_nonempty {children : List (Parent curve differential)}
    {requests : FineCharts.Requests comparison target floor children} (samples : FineCharts.Samples source requests)
      (nonempty : children ≠ []) :
    samples.vertices.length = children.length + 1 := by
  cases children with
  | nil => exact False.elim (nonempty rfl)
  | cons child children => exact samples.vertices_length

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples in
/-- The retained polygon points are the original chain start followed by its actual child endpoints. -/
theorem vertices_points {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison target
  floor children}
    (samples : FineCharts.Samples source requests) (nonempty : children ≠ []) {start finish : Lifted.Basic.LiftedPoint
      2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain children (start := start) (finish := finish)) :
    samples.vertices.map Vertex.point = start.coordinate :: children.map (fun child => child.edge.point 1) := by
  cases chain with
  | nil _ => exact False.elim (nonempty rfl)
  | cons child tail =>
      cases requests with
      | cons request remaining =>
          simp only [vertices, List.map_cons,
            finishes_points]
          exact congrArg (fun first => first :: _) child.edge.point_zero

/-- With exactly shared chart vertices, the original polygon increments equal the retained child increment rows. -/
theorem increments_eq : {children : List (Parent curve differential)} → {requests : FineCharts.Requests comparison
  target floor children} →
    (samples : FineCharts.Samples source requests) → samples.Shared →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.increments samples.vertices = samples.rows.map
      Prod.fst
  | _, .nil, _, _ => rfl
  | _, .cons _ .nil, samples, _ => by
      change [samples.1.last.vertex.value - samples.1.first.vertex.value] = [samples.1.increment]
      exact congrArg (fun value => [value]) (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.child_step samples.1)
  | _, .cons _ (.cons _ _), samples, shared => by
      change (samples.1.last.vertex.value - samples.1.first.vertex.value) ::
        Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.steps samples.1.last.vertex
        (finishes samples.2) =
        samples.1.increment :: samples.2.rows.map Prod.fst
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.child_step, shared.1]
      exact congrArg (List.cons samples.1.increment)
        (increments_eq samples.2 shared.2)

/-- The retained child increment area equals the original closed chart-vertex polygon area. -/
theorem polygon_area {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison target
  floor children}
    (samples : FineCharts.Samples source requests) (shared : samples.Shared) :
    IncrementArea.pathArea (samples.rows.map Prod.fst) =
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.closedArea samples.vertices := by
  rw [← samples.increments_eq shared, Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex.area_eq]

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
