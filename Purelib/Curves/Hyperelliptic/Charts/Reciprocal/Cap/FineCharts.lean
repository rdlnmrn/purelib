module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartSamples
import Init.Data.List.Lemmas
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
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
import Purelib.Tactic.Ring

public section

/-!
# Global chart values on the retained integration subdivision

Prepare every endpoint comparison on the already cached child block. Its
finite maximum selects the common polynomial stage, while chart-coordinate
readings may advance afterward without changing any integration child.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Rat
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison (PreparedPoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap (Endpoint ChartRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {center :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval center)} {count :
    Nat}
  {terminal : Terminal cap owner count} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential
    genus}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential} {point
    : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

set_option genInjectivity false in
/-- An original endpoint preparation and cap-coordinate comparison request.

The retained target pays both polynomial-to-source and source-to-chart errors while keeping an independent chart reading
floor. -/
structure PointRequest (comparison : TerminalComparison.Data terminal differential)
    (point : InverseRootPolynomial.Gaussian) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original endpoint comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached original terminal-neighborhood point and exact cap-coordinate comparison. -/ prepared : PreparedPoint
    comparison point
  /-- The retained quarter-budget polynomial-to-coordinate request with its original stage floor. -/ request :
    EndpointComparison.Request prepared.data (target / 4) floor

constructive_injectivity PointRequest

namespace PointRequest

/-- Acquire the original endpoint comparison and pay its quarter target at the supplied independent floor. -/
@[expose] public def build (comparison : TerminalComparison.Data terminal differential) (point :
  InverseRootPolynomial.Gaussian)
    (inside : terminal.neighborhood.patch.box.Contains point) (capInside : collar.box.Contains point)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest comparison point target floor :=
  let prepared := PreparedPoint.build comparison point inside capInside
  ⟨positive, prepared, EndpointComparison.Request.build prepared.data (target / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide)) floor⟩

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {index : Nat} {box :
  Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The retained endpoint, chart request and evaluation against one unchanged original source polynomial. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest comparison point
  target floor)
    (source : PolynomialPullback.Sample terminal.preparation capSample) where
  /-- The cached original endpoint evaluation on the retained shared cap polynomial. -/ endpoint : Endpoint
    request.prepared.coordinates capSample
  /-- The retained chart reading request at the original independent coordinate floor. -/ chartRequest : ChartRequest
    endpoint (target / 4) request.request.coordinate.rightIndex
  /-- The evaluated original chart request and its retained source and chart readings. -/ chart :
    ChartRequest.Evaluation chartRequest
  /-- The unchanged original source polynomial differs from the retained source reading by less than a quarter target.
  -/
  source_close : Data.Gaussian.Norm.Basic.normSq (source.value.eval point - chart.sourceValue) < target /
    4
  /-- The retained chart reading differs from the unchanged original source polynomial by less than the full target. -/
    accurate : Data.Gaussian.Norm.Basic.normSq (source.value.eval point - chart.reading.value) < target

constructive_injectivity Evaluation

/-- Two quarter-budget endpoint discrepancies combine into the original full squared-norm target. -/
public theorem point_accurate (first middle last : InverseRootPolynomial.Gaussian) (target :
  InverseRootPolynomial.Coordinate)
    (sourceClose : Data.Gaussian.Norm.Basic.normSq (first - middle) < target / 4) (chartClose :
      Data.Gaussian.Norm.Basic.normSq (middle - last) < target / 4) :
    Data.Gaussian.Norm.Basic.normSq (first - last) < target := by
  rw [show first - last = (first - middle) + (middle - last) by ring1]
  apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct sourceClose chartClose)).trans_eq
  rw [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- Evaluate the original endpoint request on the supplied later polynomial and retain the paid chart reading. -/
@[expose] public def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest comparison
  point target floor)
    (source : PolynomialPullback.Sample terminal.preparation capSample)
    (later : request.request.index ≤ index) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request source := by
  let endpoint := Endpoint.build request.prepared.coordinates capSample
  let chartRequest := ChartRequest.build endpoint (target / 4)
    (Fraction.Order.Field.div_pos_direct request.positive (by decide)) request.request.coordinate.rightIndex
  let chart := chartRequest.evaluate
  have sourceClose : Data.Gaussian.Norm.Basic.normSq (source.value.eval point - chart.sourceValue) < target / 4
    := by
    rw [chart.sourceValue_eq]
    exact request.request.accurate source endpoint later chartRequest.comparison.left_ge
  exact ⟨endpoint, chartRequest, chart, sourceClose,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.point_accurate _ _ _ _ sourceClose
    chart.accurate⟩

/-- Only the chart reading changes. Both the retained polynomial and the source factor value remain those of the
original evaluation. -/
@[expose] public def Evaluation.refine {request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest
  comparison point target floor}
    {source : PolynomialPullback.Sample terminal.preparation capSample}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request source) (stage :
      Nat) (later : evaluated.chart.stage ≤ stage) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request source :=
  let chart := evaluated.chart.refine stage later
  ⟨evaluated.endpoint, evaluated.chartRequest, chart, evaluated.source_close,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.point_accurate _ _ _ _
      evaluated.source_close chart.accurate⟩

end PointRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)

set_option genInjectivity false in
/-- The two original endpoint requests of one actual retained integration child. -/
structure ChildRequest (comparison : TerminalComparison.Data terminal differential)
    (child : Parent curve differential) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained request or evaluated reading at the original child's first endpoint. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest comparison (child.edge.point 0) target floor
  /-- The retained request or evaluated reading at the original child's last endpoint. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest comparison (child.edge.point 1) target floor

constructive_injectivity ChildRequest

namespace ChildRequest

variable {parent child : Parent curve differential} {data : ParentData cap differential count parent}
  {integrationTarget target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Both endpoints of every actual retained integration child lie in its original local patch and cap collar. -/
public theorem child_inside (request : PreparedPrimitives.Request data integrationTarget floor)
    (member : child ∈ request.block.children) :
    (data.terminal.neighborhood.patch.box.Contains (child.edge.point 0) ∧
      data.terminal.neighborhood.patch.box.Contains (child.edge.point 1)) ∧
    (collar.box.Contains (child.edge.point 0) ∧ collar.box.Contains (child.edge.point 1)) :=
  ⟨⟨PreparedPrimitivePaths.block_starts_inside request.block _
      (data.first_eq ▸ data.segment.firstInside) (data.last_eq ▸ data.segment.lastInside) child member,
    PreparedPrimitivePaths.block_finishes_inside request.block _
      (data.first_eq ▸ data.segment.firstInside) (data.last_eq ▸ data.segment.lastInside) child member⟩,
   ⟨PreparedPrimitivePaths.block_starts_inside request.block _
      (data.first_eq ▸ data.segment.comparison.firstCap) (data.last_eq ▸ data.segment.comparison.lastCap) child member,
    PreparedPrimitivePaths.block_finishes_inside request.block _
      (data.first_eq ▸ data.segment.comparison.firstCap) (data.last_eq ▸ data.segment.comparison.lastCap) child member⟩⟩

/-- Prepare both original endpoints of this actual retained integration child using its existing containment
certificates. -/
@[expose] public def build (request : PreparedPrimitives.Request data integrationTarget floor)
    (child : Parent curve differential) (member : child ∈ request.block.children)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest data.comparison child target floor :=
  let inside := Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.child_inside request member
  ⟨PointRequest.build data.comparison _ inside.1.1 inside.2.1 target positive floor,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.build data.comparison _ inside.1.2 inside.2.2
      target positive floor⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest in
/-- The common polynomial stage is the maximum of the retained endpoint requests and original floor. -/
@[expose] public def index (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest comparison
  child target floor) : Nat :=
  max request.first.request.index request.last.request.index

variable {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The two retained endpoint evaluations and their cached signed original child increment. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest comparison child
  target floor)
    (source : PolynomialPullback.Sample terminal.preparation capSample) where
  /-- The retained request or evaluated reading at the original child's first endpoint. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request.first source
  /-- The retained request or evaluated reading at the original child's last endpoint. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request.last source
  /-- The cached signed difference of the two original chart endpoint readings. -/ increment :
    InverseRootPolynomial.Gaussian
  /-- The cached child increment is exactly the negative last-minus-first chart reading difference. -/ increment_eq :
    increment = -(last.chart.reading.value - first.chart.reading.value)
  /-- The cached signed child increment differs from the original polynomial increment by less than four endpoint
    targets. -/ accurate : Data.Gaussian.Norm.Basic.normSq (increment - -(source.value.eval (child.edge.point
    1) - source.value.eval (child.edge.point 0))) < 4 * target

constructive_injectivity Evaluation

/-- Combine the two already evaluated original endpoint requests into their signed child increment and error
certificate. -/
@[expose] public def Evaluation.ofPoints {request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest
  comparison child target floor}
    {source : PolynomialPullback.Sample terminal.preparation capSample}
    (first : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request.first source) (last :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.PointRequest.Evaluation request.last source) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.Evaluation request source := by
  refine ⟨first, last, -(last.chart.reading.value - first.chart.reading.value), rfl, ?_⟩
  rw [show -(last.chart.reading.value - first.chart.reading.value) -
    -(source.value.eval (child.edge.point 1) - source.value.eval (child.edge.point 0)) =
      (source.value.eval (child.edge.point 1) - last.chart.reading.value) -
      (source.value.eval (child.edge.point 0) - first.chart.reading.value) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct last.accurate first.accurate)).trans_eq (by ring1))

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest in
/-- Evaluate both original child endpoint requests on the supplied common later source polynomial. -/
@[expose] public def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest comparison
  child target floor)
    (source : PolynomialPullback.Sample terminal.preparation capSample)
    (later : request.index ≤ index) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.Evaluation
      request source :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.Evaluation.ofPoints (request.first.evaluate source
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans later))
    (request.last.evaluate source ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))

/-- Read the retained chart increment paired with the unchanged original polynomial child increment. -/
@[expose] public def Evaluation.row {request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest
  comparison child target floor}
    {source : PolynomialPullback.Sample terminal.preparation capSample}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.Evaluation request source) :
      InverseRootPolynomial.Gaussian × Gaussian :=
  (evaluated.increment, -(source.value.eval (child.edge.point 1) - source.value.eval (child.edge.point 0)))

end ChildRequest

set_option genInjectivity false in
/-- Chart requests indexed by the original retained integration child list.

Each occurrence keeps its exact original child and endpoint owners before selecting the shared model floor. -/
inductive Requests (comparison : TerminalComparison.Data terminal differential)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) : List (Parent curve differential) → Type 3
  /-- The empty original integration child list retains no chart requests. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor []
  /-- Retain the exact original child's endpoint requests followed by the original child-list tail. -/ | cons {child :
    Parent curve differential} {children : List (Parent curve differential)}
      (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest comparison child target floor)
        (remaining : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor
        children) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor (child :: children)

constructive_injectivity Requests

namespace Requests

variable {parent : Parent curve differential} {data : ParentData cap differential count parent}
  {integrationTarget target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare chart endpoint requests in the exact original retained child order. -/
@[expose] public def build (request : PreparedPrimitives.Request data integrationTarget floor)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (children : List (Parent curve differential)) → (∀ child ∈ children, child ∈ request.block.children) →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests data.comparison target floor children
  | [], _ => .nil
  | child :: children, within => .cons (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.build request
    child (within child (List.mem_cons_self ..)) target positive)
      (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests.build request target positive children
        (fun next member => within next (List.mem_cons_of_mem child member)))

/-- The common polynomial stage is the maximum of the retained endpoint requests and original floor. -/
@[expose] public def index : {children : List (Parent curve differential)} →
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children → Nat
  | _, .nil => floor
  | _, .cons request remaining => max request.index remaining.index

end Requests

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index : Nat} {box :
  Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Evaluations of the original chart request spine against one retained source polynomial.

The dependent product keeps the original endpoint readings and actual integration child order. -/
@[expose] public def Samples (source : PolynomialPullback.Sample terminal.preparation capSample) :
    {children : List (Parent curve differential)} → Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests
      comparison target floor children → Type 3
  | _, .nil => PUnit
  | _, .cons request remaining => Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.ChildRequest.Evaluation request
    source × Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source remaining

namespace Samples

/-- Evaluate the retained request spine on one later common source polynomial, reusing the original child preparations.
-/
@[expose] public def build (source : PolynomialPullback.Sample terminal.preparation capSample) :
    {children : List (Parent curve differential)} → (requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children) →
      requests.index ≤ index → Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source requests
  | _, .nil, _ => ⟨⟩
  | _, .cons request remaining, later =>
      ⟨request.evaluate source ((Purelib.Data.Nat.Order.le_max_left _ _).trans later),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.build source remaining
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)⟩

variable {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample terminal.preparation
  capSample}

/-- Read all retained chart and original polynomial increment pairs in actual child order. -/
@[expose] public def rows : {children : List (Parent curve differential)} → {requests :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children} →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source requests → List (InverseRootPolynomial.Gaussian
      × InverseRootPolynomial.Gaussian)
  | _, .nil, _ => []
  | _, .cons _ _, samples => samples.1.row :: Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.rows
    samples.2

/-- There is one retained comparison row for each original integration child. -/
theorem rows_length : {children : List (Parent curve differential)} → {requests :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children} →
    (samples : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source requests) → samples.rows.length =
      children.length
  | _, .nil, _ => rfl
  | _, .cons _ _, samples => congrArg Nat.succ
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.rows_length samples.2)

/-- The right row components are exactly the signed original polynomial increments on the retained children. -/
theorem rows_source : {children : List (Parent curve differential)} → {requests :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children} →
    (samples : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source requests) → samples.rows.map
      Prod.snd = children.map
      (fun child => -(source.value.eval (child.edge.point 1) - source.value.eval (child.edge.point 0)))
  | _, .nil, _ => rfl
  | _, .cons _ _, samples => congrArg (List.cons _)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.rows_source samples.2)

/-- Every retained chart-to-polynomial increment row satisfies four times the original endpoint target. -/
theorem rows_accurate : {children : List (Parent curve differential)} → {requests :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Requests comparison target floor children} →
    (samples : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples source requests) → ∀ row ∈ samples.rows,
      Data.Gaussian.Norm.Basic.normSq (row.1 - row.2) ≤ 4 * target
  | _, .nil, _, _, member => by cases member
  | _, .cons _ _, samples, row, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · exact samples.1.accurate.le
      · exact Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Samples.rows_accurate samples.2 row member

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
