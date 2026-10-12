module
meta import Purelib.Elab.ConstructiveInjectivity
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedPoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartPolygons
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods

public section

/-!
# Retained endpoint evaluations of actual fine cap polygons

Read the first and last evaluations from the existing child spine. The
coordinate chain transports only their indices, and the vertex equations tie
the returned records to the displayed polygon's actual endpoints.
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

set_option genInjectivity false in
/-- An original endpoint request with its cached evaluation on the exact retained cap sample. -/
structure RetainedPoint (comparison : TerminalComparison.Data terminal differential)
    (source : PolynomialPullback.Sample terminal.preparation capSample) (point : InverseRootPolynomial.Gaussian)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original endpoint preparation at its retained target and reading floor. -/ request : FineCharts.PointRequest
    comparison point target floor
  /-- The cached evaluation of this exact original endpoint request. -/ evaluated : PointRequest.Evaluation request
    source

constructive_injectivity RetainedPoint

namespace RetainedPoint

variable {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample terminal.preparation
  capSample} {point : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

/-- Read the actual chart vertex from the original cached endpoint evaluation. -/
@[expose] def vertex (retained : RetainedPoint comparison source point target floor) : FineCharts.Vertex capSample
  target :=
  retained.evaluated.vertex

/-- Transport the original retained endpoint along physical-point equality without changing its request or reading.

Only the physical-point index is transported. The cached endpoint request
and evaluated sample remain the same retained data. -/
@[expose] def cast {first last : InverseRootPolynomial.Gaussian} (retained : RetainedPoint comparison source first
  target floor) (equal : first = last) :
    RetainedPoint comparison source last target floor := by
  cases equal
  exact retained

/-- Transporting the original endpoint index preserves its cached chart vertex. -/
theorem cast_vertex {first last : InverseRootPolynomial.Gaussian} (retained : RetainedPoint comparison source first
  target floor) (equal : first = last) :
    (retained.cast equal).vertex = retained.vertex := by
  cases equal
  rfl

end RetainedPoint

namespace Samples

variable {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample terminal.preparation
  capSample}

/-- Read the original first cached endpoint evaluation from a nonempty retained child spine.

The supplied chain identifies its initial coordinate with the original
head child; that equality transports the cached first evaluation. -/
@[expose] def firstPoint : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children},
    FineCharts.Samples source requests → {first last : Lifted.Basic.LiftedPoint 2} →
    Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)) → children ≠
      [] →
      RetainedPoint comparison source first.coordinate target floor
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | _ :: _, .cons request _, samples, _, _, chain, _ =>
      (RetainedPoint.mk request.first samples.1.first).cast (DirectPathChain.head_coordinate chain)

/-- Read the original last cached endpoint evaluation from a nonempty retained child spine.

Structural recursion follows the original ordered children. The terminal
chain equation transports the final cached evaluation without selecting a new sample. -/
@[expose] def lastPoint : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children},
    FineCharts.Samples source requests → {first last : Lifted.Basic.LiftedPoint 2} →
    Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)) → children ≠
      [] →
      RetainedPoint comparison source last.coordinate target floor
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | [_], .cons request .nil, samples, _, _, chain, _ =>
      (RetainedPoint.mk request.last samples.1.last).cast (DirectPathChain.single_last chain)
  | _ :: _ :: _, .cons _ (.cons _ _), samples, _, _, chain, _ =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.lastPoint samples.2
        (DirectPathChain.tail_chain chain) (by intro impossible; cases impossible)

/-- The first retained chain endpoint displays exactly the original first child's chart vertex. -/
theorem firstPoint_vertex {child : Parent curve differential} {children : List (Parent curve differential)}
    {request : FineCharts.ChildRequest comparison child target floor} {requests : FineCharts.Requests comparison target
      floor children}
    (samples : FineCharts.Samples source (.cons request requests)) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain (child :: children) (start := first) (finish :=
      last))) :
    (samples.firstPoint chain (by intro impossible; cases impossible)).vertex = samples.1.first.vertex := by
  exact RetainedPoint.cast_vertex ⟨request.first, samples.1.first⟩ (DirectPathChain.head_coordinate chain)

/-- The last cached child finish is exactly the original retained chain endpoint vertex. -/
theorem lastPoint_finishes : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ []),
    samples.finishes.getLast? = some (samples.lastPoint chain nonempty).vertex
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | [_], .cons request .nil, samples, _, _, chain, _ => by
      rw [show
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.lastPoint samples chain (by
          intro impossible;
          cases impossible)).vertex = samples.1.last.vertex from
        RetainedPoint.cast_vertex ⟨request.last, samples.1.last⟩ (DirectPathChain.single_last chain)]
      rfl
  | _ :: _ :: _, .cons _ (.cons _ _), samples, _, _, chain, _ =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.lastPoint_finishes samples.2
        (DirectPathChain.tail_chain chain) (by intro impossible; cases impossible)

/-- The retained chart polygon begins at the actual original first endpoint evaluation. -/
theorem vertices_first : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ []),
    samples.vertices.head? = some (samples.firstPoint chain nonempty).vertex
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | _ :: _, .cons _ _, samples, _, _, chain, _ => by
      rw [samples.firstPoint_vertex chain]
      rfl

/-- The retained chart polygon ends at the actual original last endpoint evaluation. -/
theorem vertices_last : ∀ {children : List (Parent curve differential)} {requests : FineCharts.Requests comparison
  target floor children}
    (samples : FineCharts.Samples source requests) {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain children (start := first) (finish := last)))
      (nonempty : children ≠ []),
    samples.vertices.getLast? = some (samples.lastPoint chain nonempty).vertex
  | [], .nil, _, _, _, _, nonempty => (nonempty rfl).elim
  | _ :: _, .cons _ _, samples, _, _, chain, nonempty => samples.lastPoint_finishes chain nonempty

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
