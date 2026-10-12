module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
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
# Shared chart vertices on each retained parent path

The cached requests at a common child endpoint agree before any polynomial
stage is selected. Their evaluated vertices therefore agree literally.
The resulting vertex list reuses the retained readings and preserves its
closing-edge term when interpreted as a finite polygon.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)
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

set_option genInjectivity false in
/-- The displayed base point, retained root coordinate, and negative cap primitive value used by the positive reciprocal
integrator. -/
structure Vertex (capSample : Primitives.Sample cap differential index box) (target : InverseRootPolynomial.Coordinate)
  where
  /-- The original physical endpoint displayed by the retained chart vertex. -/ point : InverseRootPolynomial.Gaussian
  /-- The cached original root-coordinate reading at this endpoint. -/ coordinate : InverseRootPolynomial.Gaussian
  /-- The cached signed cap primitive value at the retained chart coordinate. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached value is exactly the negative original regular or ramified cap primitive evaluation. -/ value_eq :
    value = -(if HyperellipticReciprocal.originOrder curve = 0 then coordinate * capSample.primitive.value.eval point
    else capSample.primitive.value.eval coordinate)
  /-- The retained coordinate satisfies the original quarter-budget root-square relation. -/ square_bound :
    Data.Gaussian.Norm.Basic.normSq (coordinate * coordinate - point ^ HyperellipticReciprocal.originOrder
    curve) < target / 4

constructive_injectivity Vertex

namespace PointRequest

/-- Read the original point, retained root coordinate and signed cap primitive value from this exact endpoint
evaluation. -/
@[expose] public def Evaluation.vertex {point : InverseRootPolynomial.Gaussian} {request : FineCharts.PointRequest
  comparison point target floor}
    {source : PolynomialPullback.Sample terminal.preparation capSample}
    (evaluated : PointRequest.Evaluation request source) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Vertex
      capSample target :=
  ⟨point, evaluated.chart.reading.coordinate, -evaluated.chart.reading.value,
    congrArg Neg.neg evaluated.chart.reading.value_eq, evaluated.chart.square_accurate⟩

/-- Equal original physical endpoints give heterogeneously equal retained point requests. -/
theorem build_heq {first last : InverseRootPolynomial.Gaussian} (equal : first = last)
    (firstInside : terminal.neighborhood.patch.box.Contains first) (lastInside :
      terminal.neighborhood.patch.box.Contains last)
    (firstCap : collar.box.Contains first) (lastCap : collar.box.Contains last)
    (positive : 0 < target) :
    HEq (PointRequest.build comparison first firstInside firstCap target positive floor)
      (PointRequest.build comparison last lastInside lastCap target positive floor) := by
  cases equal
  rfl

/-- Equal original endpoint requests give exactly equal evaluated chart vertices at the same retained polynomial stage.
-/
theorem evaluate_vertex_eq {first last : InverseRootPolynomial.Gaussian} (equal : first = last)
    {firstRequest : FineCharts.PointRequest comparison first target floor} {lastRequest : FineCharts.PointRequest
      comparison last target floor}
    (same : HEq firstRequest lastRequest)
    (source : PolynomialPullback.Sample terminal.preparation capSample)
    (firstLater : firstRequest.request.index ≤ index) (lastLater : lastRequest.request.index ≤ index) :
    (firstRequest.evaluate source firstLater).vertex = (lastRequest.evaluate source lastLater).vertex := by
  cases equal
  have requests := eq_of_heq same
  cases requests
  rfl

end PointRequest

namespace Requests

/-- Adjacent original child requests retain exactly matching endpoint preparations. -/
@[expose] public def Shared : {children : List (Parent curve differential)} → FineCharts.Requests comparison target
  floor children → Prop
  | _, .nil => True
  | _, .cons _ .nil => True
  | _, .cons request (.cons next remaining) => HEq request.last next.first ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.Shared (.cons next remaining)

/-- The original first child begins at the retained path chain's actual starting coordinate. -/
private theorem head_coordinate {child : Parent curve differential} {children : List (Parent curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.DirectPathChain (child ::
      children) (start := start) (finish := finish)) :
    child.edge.point 0 = start.coordinate := by
  cases chain
  exact child.edge.point_zero

/-- Preparing the original retained child chain gives matching requests at every shared physical endpoint. -/
theorem build_shared {parent : Parent curve differential} {data : ParentData cap differential count parent}
    {integrationTarget : InverseRootPolynomial.Coordinate} (request : PreparedPrimitives.Request data integrationTarget
      floor)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (children : List (Parent curve differential)) → (within : ∀ child ∈ children, child ∈ request.block.children) →
    {start finish : Lifted.Basic.LiftedPoint 2} → PreparedDirectDyadicRefinements.DirectPathChain children (start :=
      start) (finish := finish) →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.Shared (Requests.build request target positive
        children within)
  | [], _, _, _, .nil _ => trivial
  | [_], _, _, _, .cons _ _ => trivial
  | child :: next :: children, within, _, _, .cons _ tail => by
      refine ⟨?_, Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.build_shared request target
        positive (next :: children)
        (fun next member => within next (List.mem_cons_of_mem child member)) tail⟩
      have junction : child.edge.point 1 = next.edge.point 0 := child.edge.point_one.trans
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.head_coordinate tail).symm
      exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.build_heq junction _ _ _ _ positive

end Requests

namespace Samples

variable {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample terminal.preparation
  capSample}

/-- Adjacent original evaluated children retain literally equal chart endpoint vertices. -/
@[expose] public def Shared : {children : List (Parent curve differential)} → {requests : FineCharts.Requests comparison
  target floor children} →
    FineCharts.Samples source requests → Prop
  | _, .nil, _ => True
  | _, .cons _ .nil, _ => True
  | _, .cons _ (.cons _ _), samples => samples.1.last.vertex = samples.2.1.first.vertex ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.Shared samples.2

/-- Evaluate the original shared requests on one later polynomial stage and preserve exact common chart vertices. -/
theorem build_shared (source : PolynomialPullback.Sample terminal.preparation capSample) :
    {children : List (Parent curve differential)} → (requests : FineCharts.Requests comparison target floor children) →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.Shared requests → {start finish :
      Lifted.Basic.LiftedPoint 2} →
    PreparedDirectDyadicRefinements.DirectPathChain children (start := start) (finish := finish) →
    (later : requests.index ≤ index) → Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.Shared
      (Samples.build source requests later)
  | _, .nil, _, _, _, .nil _, _ => trivial
  | _, .cons _ .nil, _, _, _, .cons _ _, _ => trivial
  | child :: _ :: _, .cons request (.cons next remaining), shared, _, _, .cons _ tail, later => by
      refine ⟨?_, Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.build_shared source (.cons next
        remaining) shared.2 tail ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)⟩
      have junction : child.edge.point 1 = _ := child.edge.point_one.trans
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.head_coordinate tail).symm
      have requestLater : request.index ≤ index := (Purelib.Data.Nat.Order.le_max_left _ _).trans later
      have nextLater : next.index ≤ index := (Purelib.Data.Nat.Order.le_max_left _ _).trans
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)
      exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.evaluate_vertex_eq junction shared.1
        source
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans requestLater) ((Purelib.Data.Nat.Order.le_max_left _ _).trans
          nextLater)

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
