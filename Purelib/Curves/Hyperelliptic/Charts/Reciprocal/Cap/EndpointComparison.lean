module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
public import Purelib.Approximation.Request.PairedFloors
public import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
public import Purelib.Riemann.Normalization.InverseModelRootRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FactorBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Tactic.Ring

public section

/-!
# Requested cap polynomial values on retained local occurrences

The terminal neighborhood supplies the local q inverse and the cap supplies
the regular R inverse. Their independent owner requests and the certified
inverse-product coordinate stream connect q A B K to the actual cap endpoint
lambda K. All request scales are fixed before the shared polynomial index.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Apart
open Purelib.Approximation.Request
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open Purelib.Riemann.Normalization.ContinuedInverseRootRequests
open Purelib.Riemann.Normalization.InverseModelRootRequests
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot
open Purelib.Riemann.RootContinuation

open Purelib.Approximation.Request.PairedFloors (RequestData)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Comparison)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {center :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {centerOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval center)} {count :
    Nat}
  {terminal : Terminal cap centerOwner count} {differential :
    Differential genus}
  {coordinate : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {reciprocalOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval coordinate)}
  {coordinates : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap coordinate
    reciprocalOwner}

set_option genInjectivity false in
/-- Keep the point certificate and the retained source name abstract while caching their executable ownership
comparison. -/
structure PointOwnership (pointType : Type u) (pointName : pointType → Gaussian.Name.Basic.Named)
    (sourceName : Gaussian.Name.Basic.Named) where
  /-- The retained original terminal-neighborhood point certificate. -/ point : pointType
  /-- The retained source root name is operationally equivalent to this exact point certificate's name. -/ equivalent :
    Gaussian.Equivalence.NamedEquivalent sourceName (pointName point)

constructive_injectivity PointOwnership

set_option genInjectivity false in
/-- Cache a point in the actual terminal neighborhood, its retained cap coordinate occurrence, and fixed multiplication
budgets before any stage. -/
structure Data (comparison : TerminalComparison.Data terminal differential)
    (coordinates : RootCoordinates.Overlap cap coordinate reciprocalOwner) where
  /-- The actual coordinate lies in the retained terminal-neighborhood rectangle. -/ inside :
    terminal.neighborhood.patch.box.Contains coordinate
  /-- The retained neighborhood point and its exact comparison with the supplied reciprocal coordinate occurrence. -/
    owner : PointOwnership (ContinuedNeighborhood.Point
    terminal.neighborhood.patch coordinate)
    (fun point => point.certificate.value.name) coordinates.reciprocal.value.name
  /-- The cached reciprocal radicand value at the actual coordinate. -/ parameter : InverseRootPolynomial.Gaussian
  /-- The cached parameter equals the original reciprocal radicand evaluated at this coordinate. -/ parameter_eq :
    parameter = (HyperellipticReciprocal.polynomial curve).eval coordinate
  /-- The cached squared-norm bound for sampled reciprocal root inverses. -/ inverseUpper :
    InverseRootPolynomial.Coordinate
  /-- The inverse bound is the reciprocal of the original root apartness lower bound. -/ inverseUpper_eq : inverseUpper
    = coordinates.reciprocal.apart.certificate.lowerSq⁻¹
  /-- The cached scale transporting the two inverse-root errors through the original radicand product. -/ productScale :
    InverseRootPolynomial.Coordinate
  /-- The product scale is twice the parameter squared norm times the sum of the two inverse bounds. -/ productScale_eq
    : productScale = 2 * Data.Gaussian.Norm.Basic.normSq parameter *
    (comparison.bounds.factor.base.inverseUpper + inverseUpper)
  /-- The cached squared-norm ceiling for the endpoint primitive coefficient. -/ coefficientUpper :
    InverseRootPolynomial.Coordinate
  /-- The coefficient ceiling uses the original coordinate power and the terminal factor bound. -/ coefficientUpper_eq :
    coefficientUpper = Data.Gaussian.Norm.Basic.normSq (coordinate ^
    (1 - HyperellipticReciprocal.originOrder curve)) * comparison.bounds.factor.bound

constructive_injectivity Data

namespace Data

/-- Cache endpoint ownership and multiplication bounds from the supplied terminal-neighborhood point and its exact
coordinate comparison. -/
@[expose] public def ofPoint (comparison : TerminalComparison.Data terminal differential)
    (coordinates : RootCoordinates.Overlap cap coordinate reciprocalOwner)
    (point : ContinuedNeighborhood.Point terminal.neighborhood.patch coordinate)
    (inside : terminal.neighborhood.patch.box.Contains coordinate)
    (equivalent : Gaussian.Equivalence.NamedEquivalent coordinates.reciprocal.value.name point.certificate.value.name) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison coordinates :=
  let parameter := (HyperellipticReciprocal.polynomial curve).eval coordinate
  let inverseUpper := coordinates.reciprocal.apart.certificate.lowerSq⁻¹
  ⟨inside, ⟨point, equivalent⟩, parameter, rfl, inverseUpper, rfl,
    2 * Data.Gaussian.Norm.Basic.normSq parameter * (comparison.bounds.factor.base.inverseUpper +
      inverseUpper), rfl,
    Data.Gaussian.Norm.Basic.normSq (coordinate ^ (1 - HyperellipticReciprocal.originOrder curve)) *
      comparison.bounds.factor.bound, rfl⟩

/-- At the retained center reuse the supplied coordinate occurrence. -/
@[expose] public def atCenter (comparison : TerminalComparison.Data terminal differential)
    (coordinates : RootCoordinates.Overlap cap center centerOwner) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison coordinates :=
  let point := ContinuedNeighborhood.Point.acquire terminal.neighborhood.patch center terminal.center_inside
  ofPoint comparison coordinates point
    terminal.center_inside (by
    rw [coordinates.reciprocal_eq]
    exact terminal.pointEquivalent point)

variable {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential}

/-- The cached reciprocal inverse bound is positive by the retained root apartness. -/
theorem inverseUpper_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison
  coordinates) : 0 < data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact Fraction.Order.Field.inv_pos_direct coordinates.reciprocal.apart.certificate.positive

/-- The cached product discrepancy scale is nonnegative. -/
theorem productScale_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison
  coordinates) : 0 ≤ data.productScale := by
  rw [data.productScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    (add_nonneg comparison.bounds.factor.base.inverseUpper_positive.le data.inverseUpper_positive.le)

/-- The cached primitive coefficient bound is nonnegative. -/
theorem coefficientUpper_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data
  comparison coordinates) : 0 ≤ data.coefficientUpper := by
  rw [data.coefficientUpper_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    comparison.bounds.factor.bound_nonnegative

/-- Every sampled reciprocal root inverse satisfies the cached squared-norm bound. -/
theorem inverse_le (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison coordinates)
  (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Field.inv ((Sampling.approximation
      coordinates.reciprocal.value.name).sample index)) ≤ data.inverseUpper := by
  rw [data.inverseUpper_eq, Data.Gaussian.Field.normSq_inv _
    (Sampling.sampled_nonzero coordinates.reciprocal.value coordinates.reciprocal.apart index)]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct coordinates.reciprocal.apart.certificate.positive
    (Sampling.sampled_lower coordinates.reciprocal.value coordinates.reciprocal.apart index)

/-- The cached endpoint coefficient satisfies the terminal comparison bound. -/
theorem coefficient_le (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison
  coordinates) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (endpoint : Overlap.Endpoint coordinates capSample) :
    Data.Gaussian.Norm.Basic.normSq endpoint.coefficient ≤ data.coefficientUpper := by
  rw [endpoint.coefficient_eq, endpoint.factor_eq, data.coefficientUpper_eq, Data.Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (comparison.bounds.factor.factor_le capSample coordinates.regular.channel.inside)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)

end Data

set_option genInjectivity false in
/-- Prepare both owners at an arbitrary contained endpoint from the actual terminal neighborhood. The local continuation
is materialized once. -/
structure PreparedPoint (comparison : TerminalComparison.Data terminal differential) (coordinate :
  InverseRootPolynomial.Gaussian) where
  /-- The retained original terminal-neighborhood point certificate. -/ point : ContinuedNeighborhood.Point
    terminal.neighborhood.patch coordinate
  /-- The retained cap coordinate occurrence built from this exact neighborhood point owner. -/ coordinates :
    RootCoordinates.Overlap cap coordinate point.owner
  /-- The endpoint ownership and multiplication bounds for these same retained coordinates. -/ data :
    Data comparison coordinates

constructive_injectivity PreparedPoint

namespace PreparedPoint

/-- Prepare one terminal-neighborhood point and cache its cap coordinates and endpoint comparison bounds. -/
@[expose] public def build (comparison : TerminalComparison.Data terminal differential) (coordinate :
  InverseRootPolynomial.Gaussian)
    (inside : terminal.neighborhood.patch.box.Contains coordinate) (capInside : collar.box.Contains coordinate) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.PreparedPoint comparison coordinate :=
  let point := ContinuedNeighborhood.Point.acquire terminal.neighborhood.patch coordinate inside
  let coordinates := Overlap.build cap coordinate capInside point.owner
  ⟨point, coordinates, Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data.ofPoint comparison coordinates
    point inside (by
    rw [coordinates.reciprocal_eq]
    exact NamedEquivalent.refl _)⟩

end PreparedPoint

variable {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential}

/-- The paired reciprocal and regular inverse requests with independent coordinate-reading floors and a shared
polynomial stage. -/
abbrev Request (data : Data comparison coordinates)
  (target : InverseRootPolynomial.Coordinate) (floor : Nat) :=
  PairedFloors.RequestData data.coefficientUpper data.productScale
    (fun rootTarget => ContinuedInverseRootRequests.InverseRequest data.owner.point coordinates.reciprocal rootTarget
      floor)
    (fun rootTarget => InverseModelRootRequests.InverseRequest coordinates.regular.channel rootTarget floor)
    (fun _ request => request.index) (fun _ request => request.observation.comparison.leftIndex)
    (fun _ request => request.index) (fun _ request => request.comparison.rightIndex)
    (CoordinateSamples.inverseProduct coordinates.reciprocal coordinates.regularRoot).toApproximation
    (Sampling.approximation coordinates.coordinate.prepared.denominator.name) target floor

namespace Request

/-- Pay the two inverse-root errors and coordinate comparison at independent reading floors, then retain their shared
polynomial stage. -/
@[expose] public def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison
  coordinates) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Request data target floor :=
  let budget := target / (4 * (data.coefficientUpper + 1))
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.coefficientUpper_nonnegative (by decide)))
  let rootTarget := budget / (data.productScale + 1)
  have rootPositive : 0 < rootTarget := Fraction.Order.Field.div_pos_direct budgetPositive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.productScale_nonnegative (by decide))
  let reciprocal := InverseRequest.build data.owner.point
    data.inside coordinates.reciprocal data.owner.equivalent rootTarget rootPositive floor
  let regular := InverseRequest.build coordinates.regular.channel rootTarget rootPositive floor
  let coordinate := (CoordinateSamples.inverseProduct_equivalent coordinates.coordinate coordinates.reciprocal
    (NamedEquivalent.refl _)).compare
    (max reciprocal.observation.comparison.leftIndex regular.comparison.rightIndex) floor budget budgetPositive
  ⟨positive, budget, rfl, rootTarget, rfl, reciprocal, regular, coordinate, max reciprocal.index regular.index, rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Data comparison coordinates}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The shared polynomial stage is at least the requested floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Request data target floor) :
  floor ≤ request.index := by
  rw [request.index_eq]
  exact request.reciprocal.floor_le.trans (Purelib.Data.Nat.Order.le_max_left _ _)

/-- The coefficient-adjusted endpoint error budget is positive. -/
theorem budget_positive (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Request data target
  floor) : 0 < request.budget := by
  rw [request.budget_eq]
  exact Fraction.Order.Field.div_pos_direct request.positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.coefficientUpper_nonnegative (by decide)))

/-- At every later shared model stage, the inverse-polynomial product is within the retained budget of its sampled
coordinate product. -/
private theorem model_product_error (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Request
  data target floor) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : PolynomialPullback.Sample terminal.preparation capSample) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (data.parameter * sample.reciprocal.value.eval coordinate *
      capSample.inverse.value.eval coordinate -
      (CoordinateSamples.inverseProduct coordinates.reciprocal coordinates.regularRoot).sample
        request.coordinate.leftIndex) < request.budget := by
  let first := sample.reciprocal.value.eval coordinate
  let second := capSample.inverse.value.eval coordinate
  let left := Data.Gaussian.Field.inv ((Sampling.approximation coordinates.reciprocal.value.name).sample
    request.coordinate.leftIndex)
  let right := Data.Gaussian.Field.inv ((Sampling.approximation coordinates.regularRoot.value.name).sample
    request.coordinate.leftIndex)
  have indices := later
  rw [request.index_eq] at indices
  have firstClose : Data.Gaussian.Norm.Basic.normSq (first - left) < request.rootTarget := by
    dsimp only [first, left]
    rw [sample.reciprocal_eq]
    have scalar := request.reciprocal.accurate ((Purelib.Data.Nat.Order.le_max_left _ _).trans indices)
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans request.coordinate.left_ge)
    let reading := (Sampling.approximation coordinates.reciprocal.value.name).sample request.coordinate.leftIndex
    have inverseEq : Data.Gaussian.Basic.Canonical.inv reading = Data.Gaussian.Field.inv reading := by
      change reading⁻¹ = Data.Gaussian.Field.inv reading
      exact Data.Gaussian.Field.inv_eq reading
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, inverseEq] at scalar
    simpa only [SeededNeighborhood.refine] using scalar
  have secondClose : Data.Gaussian.Norm.Basic.normSq (second - right) < request.rootTarget := by
    have right_eq : right = Data.Gaussian.Field.inv ((Sampling.approximation
        coordinates.regular.certificate.value.name).sample request.coordinate.leftIndex) :=
      congrArg (fun root : CertifiedSquareRoot.Certificate (cap.polynomial.eval coordinate) =>
        Data.Gaussian.Field.inv ((Sampling.approximation root.value.name).sample request.coordinate.leftIndex))
        coordinates.regularRoot_eq
    rw [right_eq]
    dsimp only [second]
    rw [capSample.inverse_eq]
    have scalar := request.regular.accurate ((Purelib.Data.Nat.Order.le_max_right _ _).trans indices)
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans request.coordinate.left_ge)
    let reading := (Sampling.approximation coordinates.regular.channel.certificate.value.name).sample
      request.coordinate.leftIndex
    have inverseEq : Data.Gaussian.Basic.Canonical.inv reading = Data.Gaussian.Field.inv reading := by
      change reading⁻¹ = Data.Gaussian.Field.inv reading
      exact Data.Gaussian.Field.inv_eq reading
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, inverseEq] at scalar
    simpa only [Owners.Point.certificate] using scalar
  have secondBound := comparison.bounds.factor.base.inverse_norm_le capSample.inverse coordinates.regular.channel.inside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at secondBound
  have leftBound := data.inverse_le request.coordinate.leftIndex
  have estimate : Data.Gaussian.Norm.Basic.normSq (first * second - left * right) ≤
      2 * (request.rootTarget * comparison.bounds.factor.base.inverseUpper + data.inverseUpper * request.rootTarget) :=
        by
    rw [show first * second - left * right = (first - left) * second + left * (second - right) by ring1]
    apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
    exact add_le_add
      (Fraction.Order.Arithmetic.mul_le_mul_direct firstClose.le secondBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        request.reciprocal.positive.le)
      (Fraction.Order.Arithmetic.mul_le_mul_direct leftBound secondClose.le (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        data.inverseUpper_positive.le)
  have stream_eq : (CoordinateSamples.inverseProduct coordinates.reciprocal coordinates.regularRoot).sample
      request.coordinate.leftIndex = data.parameter * left * right :=
    (CoordinateSamples.inverseProduct_sample _ _ _).trans
      (congrArg (fun parameter => parameter * left * right) data.parameter_eq.symm)
  rw [stream_eq,
    show data.parameter * first * second - data.parameter * left * right = data.parameter * (first * second - left *
      right) by ring1,
    Data.Gaussian.Norm.Basic.normSq_mul]
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct estimate (Data.Gaussian.Norm.Basic.normSq_nonneg
    _)).trans_lt
  have algebra : Data.Gaussian.Norm.Basic.normSq data.parameter * (2 * (request.rootTarget *
    comparison.bounds.factor.base.inverseUpper +
      data.inverseUpper * request.rootTarget)) = data.productScale * request.rootTarget := by
    calc
      _ = (2 * Data.Gaussian.Norm.Basic.normSq data.parameter * (comparison.bounds.factor.base.inverseUpper +
        data.inverseUpper)) * request.rootTarget := by
        ring1
      _ = _ := congrArg (fun scale => scale * request.rootTarget) data.productScale_eq.symm
  rw [algebra]
  have positive := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.productScale_nonnegative (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 1)
  have rootPositive := request.reciprocal.positive
  calc
    _ < (data.productScale + 1) * request.rootTarget :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by
          simpa only [_root_.add_zero] using
            Fraction.Order.Arithmetic.add_lt_add_left_direct
              (by decide : (0 : InverseRootPolynomial.Coordinate) < 1) data.productScale) rootPositive
    _ = request.budget := by
      rw [request.rootTarget_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- The actual comparison polynomial approximates the retained cap endpoint at every later shared model stage and every
later independent coordinate reading. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison.Request data target floor)
  {index coordinateIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : PolynomialPullback.Sample terminal.preparation capSample)
    (endpoint : Overlap.Endpoint coordinates capSample)
    (later : request.index ≤ index) (coordinateLater : request.coordinate.rightIndex ≤ coordinateIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.value.eval coordinate - endpoint.approximation.sample
      coordinateIndex) < target := by
  let product := data.parameter * sample.reciprocal.value.eval coordinate * capSample.inverse.value.eval coordinate
  let middle := (CoordinateSamples.inverseProduct coordinates.reciprocal coordinates.regularRoot).sample
    request.coordinate.leftIndex
  let coordinateReading := (Sampling.approximation coordinates.coordinate.prepared.denominator.name).sample
    coordinateIndex
  have first := request.model_product_error sample later
  have second := request.coordinate.close (Nat.le_refl request.coordinate.leftIndex) coordinateLater
  have close : Data.Gaussian.Norm.Basic.normSq (product - coordinateReading) < 4 * request.budget := by
    rw [show product - coordinateReading = (product - middle) + (middle - coordinateReading) by ring1]
    apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first second)).trans_eq
    ring1
  have value_eq : sample.value.eval coordinate = product * endpoint.coefficient := by
    rw [sample.value_eq, endpoint.coefficient_eq, endpoint.factor_eq]
    dsimp only [product]
    rw [data.parameter_eq]
    ring1
  rw [value_eq, endpoint.sample_eq,
    show product * endpoint.coefficient - coordinateReading * endpoint.coefficient = (product - coordinateReading) *
      endpoint.coefficient by ring1,
    Data.Gaussian.Norm.Basic.normSq_mul]
  have weightPositive : 0 < data.coefficientUpper + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    data.coefficientUpper_nonnegative (by decide)
  calc
    _ ≤ Data.Gaussian.Norm.Basic.normSq (product - coordinateReading) * (data.coefficientUpper + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        ((data.coefficient_le endpoint).trans (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (by
          decide))) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < (4 * request.budget) * (data.coefficientUpper + 1) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct close weightPositive
    _ = target := by
      rw [show (4 * request.budget) * (data.coefficientUpper + 1) = request.budget * (4 * (data.coefficientUpper + 1))
        by ring1,
        request.budget_eq]
      exact Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) weightPositive).ne'

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
