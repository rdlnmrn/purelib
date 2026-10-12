module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRadialRibbon
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order

public section

/-!
# Requested connectors between retained reciprocal cap endpoints

The coordinate join is already cached by the complete parent preparation.
Its finite comparison supplies a common reading floor before a polynomial
stage is chosen. The cached coefficient bound applies to every shared cap
sample, so later endpoint readings satisfy the requested connector bound.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests

open Purelib.Data.Nat

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {lastCount : Nat} {lastParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve
    differential}
  {lastPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch lastParent} {lastSource :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data lastPatch lastCount}
  {firstEdge lastEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
  {firstCell : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell source firstEdge} {lastCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell lastSource lastEdge}
  {firstModel : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel firstCell}
    {lastModel : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel lastCell}
  {firstParameter lastParameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {first :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap firstModel firstParameter} {last :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap lastModel lastParameter}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Joined original endpoints have exactly the same retained differential coefficient at a shared cap polynomial stage.

Both endpoints refer to the same joined cap point and retained polynomial stage; their exact factor and coefficient
equations identify the displayed values. -/
theorem coefficient_eq (joined : ArcOwners.Join first last) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (left : Coordinates.Overlap.Endpoint first.coordinates capSample)
    (right : Coordinates.Overlap.Endpoint last.coordinates capSample) : left.coefficient = right.coefficient := by
  rw [left.coefficient_eq, right.coefficient_eq, left.factor_eq, right.factor_eq, joined.point_eq]

set_option genInjectivity false in
/-- A paid connector request between the original retained cap endpoint coordinates.

The budget independently accounts for primitive coefficient error, radial energy and the original collar coordinate
clearance. -/
structure Request (data : EndpointComparison.Data regular first) (joined : ArcOwners.Join first last)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original connector target is strictly positive. -/ positive : 0 < target
  /-- The fixed original padded-cap coefficient bounds shared by every later polynomial stage. -/ energyBounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded
  /-- The cached squared radial-connector coefficient scale. -/ energyScale : InverseRootPolynomial.Coordinate
  /-- The energy scale is exactly 512 times the square of the original coefficient ceiling. -/ energyScale_eq :
    energyScale = 512 * energyBounds.coefficientUpper differential ^ 2
  /-- The retained coordinate comparison budget paying all original connector obligations. -/ budget :
    InverseRootPolynomial.Coordinate
  /-- The budget is the minimum of the original coefficient, radial-energy and collar-clearance tolerances. -/ budget_eq
    : budget = min (min (target / (data.coefficientUpper + 1))
    (target / (energyScale + 1))) (collar.coordinateBound / 64)
  /-- The original coordinate-owner comparison at the exact retained budget and independent reading floors. -/
    comparison : Gaussian.Equivalence.Comparison
    (Sampling.approximation first.coordinates.coordinate.prepared.denominator.name)
    (Sampling.approximation last.coordinates.coordinate.prepared.denominator.name) floor floor budget
  /-- The cached common coordinate comparison stage. -/ index : Nat
  /-- The common stage is the maximum of the two original comparison reading indices. -/ index_eq : index = max
    comparison.leftIndex comparison.rightIndex

constructive_injectivity Request

namespace Request

/-- Retain the original coordinate join and select its paid common reading floor using the fixed coefficient and
radial-energy ceilings.

The cached comparison retains the original join and budget; its common stage is the maximum of the two selected reading
indices. -/
@[expose] def build (data : EndpointComparison.Data regular first) (joined : ArcOwners.Join first last)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request data joined target floor :=
  let energyBounds := UniformBounds.build regular.padded
  let energyScale : Coordinate := 512 * energyBounds.coefficientUpper differential ^ 2
  have scaleNonnegative : 0 ≤ energyScale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let budget := min (min (target / (data.coefficientUpper + 1))
    (target / (energyScale + 1))) (collar.coordinateBound / 64)
  have budgetPositive : 0 < budget := Basic.lt_min (Basic.lt_min (Fraction.Order.Field.div_pos_direct positive
    (Arithmetic.add_pos_of_nonneg_of_pos_direct data.coefficientUpper_nonnegative (by decide)))
    (Fraction.Order.Field.div_pos_direct positive (Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by
      decide))))
    (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide +kernel))
  let comparison := joined.coordinate.compare floor floor budget budgetPositive
  ⟨positive, energyBounds, energyScale, rfl, budget, rfl, comparison, max comparison.leftIndex comparison.rightIndex,
    rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular first} {joined :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The cached connector reading stage respects the original caller floor.

The retained comparison respects the caller floor on its left reading, and that reading lies below the cached common
stage. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request data joined target
  floor) : floor ≤ request.index := by
  rw [request.index_eq]
  rw [Order.max_eq_natMax]
  exact request.comparison.left_ge.trans (Order.le_max_left _ _)

/-- The root-coordinate comparison is paid independently of the primitive coefficient and applies at independently
selected later reading stages.

Each supplied later stage lies above both retained comparison indices. The collar component of the paid minimum bounds
their coordinate difference. -/
theorem coordinate_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request data joined
  target floor) {leftIndex rightIndex : Nat}
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq ((Sampling.approximation
      last.coordinates.coordinate.prepared.denominator.name).sample rightIndex -
      (Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex) <
      collar.coordinateBound / 64 := by
  have leftStage : request.comparison.leftIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have rightStage : request.comparison.rightIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_right _ _
  have close := request.comparison.close (leftStage.trans leftLater) (rightStage.trans rightLater)
  have reverse (left right : InverseRootPolynomial.Gaussian) : Data.Gaussian.Norm.Basic.normSq (right - left) =
    Data.Gaussian.Norm.Basic.normSq (left - right) := by
    rw [show right - left = -(left - right) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  rw [reverse]
  exact close.trans_le (request.budget_eq.trans_le (Basic.min_le_right _ _))

/-- The actual retained coefficients are reused; neither primitive is reevaluated to justify the connector between these
readings.

The coefficient ceiling and the paid coefficient tolerance bound the original cached sample difference at the supplied
later stages. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request data joined target
  floor) {index leftIndex rightIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (left : Coordinates.Overlap.Endpoint first.coordinates capSample)
    (right : Coordinates.Overlap.Endpoint last.coordinates capSample)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq (right.approximation.sample rightIndex - left.approximation.sample
      leftIndex) < target := by
  have leftStage : request.comparison.leftIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have rightStage : request.comparison.rightIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_right _ _
  have close := request.comparison.close (leftStage.trans leftLater) (rightStage.trans rightLater)
  rw [left.sample_eq, right.sample_eq, ← Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.coefficient_eq
    joined left right,
    show (Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex *
      left.coefficient -
        (Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex *
          left.coefficient =
      -((Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex -
        (Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex) *
          left.coefficient by ring1,
    Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_neg]
  have enlarged : data.coefficientUpper ≤ data.coefficientUpper + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct (by decide : (0 : Coordinate) ≤ 1) data.coefficientUpper
    calc
      data.coefficientUpper = 0 + data.coefficientUpper := by ring1
      _ ≤ 1 + data.coefficientUpper := shifted
      _ = data.coefficientUpper + 1 := by ring1
  have positive : 0 < data.coefficientUpper + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct
    data.coefficientUpper_nonnegative (by decide)
  calc
    _ ≤ Data.Gaussian.Norm.Basic.normSq _ * (data.coefficientUpper + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((data.coefficient_le left).trans enlarged) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < request.budget * (data.coefficientUpper + 1) := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct close
      positive
    _ ≤ target := by
      rw [request.budget_eq]
      exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct ((Basic.min_le_left _ _).trans
        (Basic.min_le_left _ _)) positive.le).trans_eq
        (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')

/-- The same comparison pays the radial connector for the original cached readings, at every common energy depth. Padded
containment is supplied by those readings' chart certificates.

The original energy ceiling and paid radial tolerance bound the connector between the two certified padded readings at
the supplied energy depth. -/
theorem radial_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request data joined
  target floor)
    {index leftIndex rightIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    {left : Coordinates.Overlap.Endpoint first.coordinates capSample}
    {right : Coordinates.Overlap.Endpoint last.coordinates capSample}
    (leftReading : ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : ChartReadings.Endpoint.Reading right rightIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootRadialGeometry.radialArea capSample.primitive.value.eval depth
      rightReading.coordinate -
      RootRadialGeometry.radialArea capSample.primitive.value.eval depth leftReading.coordinate -
      BoundaryRibbon.area (capSample.primitive.value.eval leftReading.coordinate)
        (capSample.primitive.value.eval rightReading.coordinate)) < target := by
  have leftStage : request.comparison.leftIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have rightStage : request.comparison.rightIndex ≤ request.index := by
    rw [request.index_eq, Order.max_eq_natMax]
    exact Order.le_max_right _ _
  have estimate := request.energyBounds.radial_connector_bound capSample branch leftInside rightInside depth
  rw [← request.energyScale_eq] at estimate
  have close : Data.Gaussian.Norm.Basic.normSq (rightReading.coordinate - leftReading.coordinate) <
    request.budget := by
    rw [leftReading.coordinate_eq, rightReading.coordinate_eq,
      show (Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex -
        (Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex =
        -((Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex -
          (Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact request.comparison.close (leftStage.trans leftLater) (rightStage.trans rightLater)
  have scaleNonnegative : 0 ≤ request.energyScale := by
    rw [request.energyScale_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have enlarged : request.energyScale ≤ request.energyScale + 1 := by
    have shifted := Arithmetic.add_le_add_right_direct (by decide : (0 : Coordinate) ≤ 1) request.energyScale
    calc
      request.energyScale = 0 + request.energyScale := by ring1
      _ ≤ 1 + request.energyScale := shifted
      _ = request.energyScale + 1 := by ring1
  have positive : 0 < request.energyScale + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide)
  apply estimate.trans_lt
  calc
    _ ≤ (request.energyScale + 1) * Data.Gaussian.Norm.Basic.normSq (rightReading.coordinate -
      leftReading.coordinate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < (request.energyScale + 1) * request.budget :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    _ ≤ target := by
      rw [Fraction.Field.mul_comm, request.budget_eq]
      exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        ((Basic.min_le_left _ _).trans (Basic.min_le_right _ _)) positive.le).trans_eq
          (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
