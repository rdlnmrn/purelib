module
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
public import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveEndpoint
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveTotals
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Full requested-bank comparison retains the polygon joining parent blocks. -/
namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent (RequestedPrimitiveParent)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {areaTarget :
    Purelib.Data.Rat.Fraction.Rational}

namespace RequestedPrimitiveParents

open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Prepend the original primitive increment pair and its exact numerical block total. -/
@[expose] def prependEndpointPairs {parent : CenteredEdge curve differential}
    (head : RequestedPrimitiveParent request parent other count areaTarget)
    (tail : List (PrimitivePoint × PrimitivePoint)) : List (PrimitivePoint × PrimitivePoint) :=
  (⟨head.2.2.1.2.2.increment, head.2.2.2.val.2.2.increment⟩,
    PairedIncrementArea.total (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments head.1)) :: tail

/-- Read the original primitive/numerical endpoint pairs in retained parent order. -/
@[expose] def endpointPairs : {parents : List (CenteredEdge curve differential)} →
    RequestedPrimitiveParents request other count areaTarget parents → List (PrimitivePoint × PrimitivePoint)
  | _, .nil => []
  | _, .cons head _ tail =>
    prependEndpointPairs head
    tail.endpointPairs

/-- There is exactly one retained endpoint pair per original parent. -/
theorem endpointPairs_length {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.endpointPairs.length = parents.length := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg Nat.succ ih

/-- The original primitive endpoint projection reads back the retained primitive totals. -/
theorem endpointPairs_left {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.endpointPairs.map Prod.fst = prepared.primitives.primitiveTotals := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg (_ :: ·) ih

open Purelib.Integration.Path in
/-- The original numerical endpoint projection reads back the retained block totals. -/
theorem endpointPairs_right {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.endpointPairs.map Prod.snd = prepared.bank.incrementBlocks.map PairedIncrementArea.total := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg (_ :: ·) ih

open Purelib.Riemann.Readings in
/-- Each original endpoint pair satisfies the shared retained componentwise error target. -/
theorem endpointPairs_errors {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (pair.1.sub pair.2) areaTarget := by
  induction prepared with
  | nil => intro pair member; cases member
  | cons head charge tail ih =>
    intro pair member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact head.endpoint_bounded
    · exact ih pair member

open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Bound the original numerical endpoints by both retained densities and a common movement bound. -/
theorem endpointPairs_numerical {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents)
    (otherProfile : DifferentialProfile profile other.exponent) {movement : Fraction.Rational}
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ movement) :
    ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2
      ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * movement) := by
  intro pair member
  have inTotals := Map.mem_map_of_mem (f := Prod.snd) member
  rw [prepared.endpointPairs_right] at inTotals
  obtain ⟨block, inBlocks, equal⟩ := Map.mem_map.mp inTotals
  rw [← equal]
  exact (PreparedNewtonPairedBank.PairedBoundaryParents.block_bounds prepared.bank otherProfile movements block
    inBlocks).2

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Surface in
/-- Bound the original polygon-of-totals error from retained endpoint comparisons.

A nonnegative local target at most one and the numerical magnitude bound give factor 32 times parent count to the fourth
power times target times magnitude plus one. -/
theorem polygon_error_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents)
    {magnitude : Fraction.Rational} (nonnegative : 0 ≤ magnitude) (positive : 0 ≤ areaTarget) (small : areaTarget ≤ 1)
    (numeric : ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area prepared.primitives.primitiveTotals -
      PairedIncrementArea.area (prepared.bank.incrementBlocks.map PairedIncrementArea.total)) ≤
        32 * (parents.length : Fraction.Rational)^4 * areaTarget * (magnitude + 1) := by
  have step : magnitude ≤ magnitude + 1 :=
    le_add_of_nonneg_right (by decide : (0 : Fraction.Rational) ≤ 1)
  have doubled : magnitude + 1 ≤ (magnitude + 1) + (magnitude + 1) :=
    le_add_of_nonneg_right (add_nonneg nonnegative (by decide : (0 : Fraction.Rational) ≤ 1))
  have enlarged : magnitude ≤ 2 * (magnitude + 1) :=
    step.trans (doubled.trans_eq (by ring1))
  have left : ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 (2 * (magnitude + 1))
    := by
    intro pair member
    have bounded := Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded (numeric pair member)
      (prepared.endpointPairs_errors pair member)
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (le_refl magnitude) small) (by
      decide : (0 : Fraction.Rational) ≤ 2)
    exact ⟨bounded.1.trans upper, bounded.2.trans upper⟩
  have right : ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 (2 * (magnitude + 1))
    := by
    intro pair member
    exact ⟨(numeric pair member).1.trans enlarged, (numeric pair member).2.trans enlarged⟩
  have bounded := PairedIncrementComparison.area_difference_bound prepared.endpointPairs positive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg nonnegative (by decide))) prepared.endpointPairs_errors left right
  rw [prepared.endpointPairs_length, prepared.endpointPairs_left, prepared.endpointPairs_right] at bounded
  exact bounded.trans_eq (by ring1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Combine original internal-area and endpoint-polygon errors for the retained flattened paths.

The exact block decomposition keeps count-squared and count-to-the-fourth payments separate before the final factor-two
estimate. -/
theorem full_area_error_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents)
    {magnitude : Fraction.Rational} (nonnegative : 0 ≤ magnitude) (positive : 0 ≤ areaTarget) (small : areaTarget ≤ 1)
    (numeric : ∀ pair ∈ prepared.endpointPairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 magnitude) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area prepared.primitives.primitiveBlocks.flatten -
      PairedIncrementArea.area prepared.bank.incrementBlocks.flatten) ≤
        2 * ((parents.length : Fraction.Rational)^2 + 32 * (parents.length : Fraction.Rational)^4 * (magnitude + 1)) *
          areaTarget := by
  have identity : PairedIncrementArea.area prepared.primitives.primitiveBlocks.flatten -
      PairedIncrementArea.area prepared.bank.incrementBlocks.flatten =
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveBlocks.map PairedIncrementArea.area) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.bank.incrementBlocks.map PairedIncrementArea.area)) +
    (PairedIncrementArea.area prepared.primitives.primitiveTotals -
      PairedIncrementArea.area (prepared.bank.incrementBlocks.map PairedIncrementArea.total)) := by
    rw [prepared.primitives.primitiveBlocks_area, PairedAreaBlocks.area_flatten]
    ring1
  rw [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add prepared.internal_area_error_le (prepared.polygon_error_le nonnegative positive small numeric)) (by
        decide)).trans_eq (by ring1))

/-- The original first-row maximum comparison bound is below the shared nonnegative target. -/
theorem firstBound_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) (nonnegative : 0 ≤ areaTarget) :
    prepared.primitives.firstBound ≤ areaTarget := by
  induction prepared with
  | nil => exact nonnegative
  | cons head charge tail ih => exact Fraction.Order.Basic.max_le head.2.2.2.property.2.1 ih

/-- The left projection of original primitive totals is exactly the retained first reading list. -/
theorem primitiveTotals_left {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.primitives.primitiveTotals.map PrimitivePoint.left = prepared.primitives.firstReadings := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg (_ :: ·) ih

/-- The original second-row maximum comparison bound is below the shared nonnegative target. -/
theorem secondBound_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) (nonnegative : 0 ≤ areaTarget) :
    prepared.primitives.secondBound ≤ areaTarget := by
  induction prepared with
  | nil => exact nonnegative
  | cons head charge tail ih => exact Fraction.Order.Basic.max_le head.2.2.2.property.2.2 ih

/-- The right projection of original primitive totals is exactly the retained second reading list. -/
theorem primitiveTotals_right {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.primitives.primitiveTotals.map PrimitivePoint.right = prepared.primitives.secondReadings := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg (_ :: ·) ih

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- The two original cached path totals differ within parent count squared times target.

Exact block-total and coordinate readbacks connect both actual summaries to their retained first/second comparison
bounds. -/
theorem total_error_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) (nonnegative : 0 ≤ areaTarget)
    (primitive : PairedIncrementArea.Summary prepared.primitives.primitiveBlocks.flatten)
    (numerical : PairedIncrementArea.Summary prepared.bank.incrementBlocks.flatten) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (primitive.totalValue.sub numerical.totalValue) ((parents.length :
      Fraction.Rational)^2 * areaTarget) := by
  rw [primitive.total_eq, PairedAreaBlocks.total_flatten,
    prepared.primitives.primitiveBlocks_totals, numerical.total_eq]
  have squaredNonnegative : (0 : Fraction.Rational) ≤ (parents.length : Fraction.Rational)^2 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2
  constructor
  · change Basic.Canonical.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveTotals.map
      PrimitivePoint.left) -
      (PairedIncrementArea.total prepared.bank.incrementBlocks.flatten).left) ≤ _
    rw [prepared.primitiveTotals_left]
    have bounded := prepared.primitives.first_sample_error_le
    rw [Norm.Basic.normSq_eq_canonical] at bounded
    have rearrange : (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) *
      prepared.primitives.firstBound) =
        (parents.length : Fraction.Rational)^2 * prepared.primitives.firstBound := by ring1
    exact bounded.trans (rearrange.le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (prepared.firstBound_le nonnegative)
        squaredNonnegative))
  · change Basic.Canonical.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveTotals.map
      PrimitivePoint.right) -
      (PairedIncrementArea.total prepared.bank.incrementBlocks.flatten).right) ≤ _
    rw [prepared.primitiveTotals_right]
    have bounded := prepared.primitives.second_sample_error_le
    rw [Norm.Basic.normSq_eq_canonical] at bounded
    have rearrange : (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) *
      prepared.primitives.secondBound) =
        (parents.length : Fraction.Rational)^2 * prepared.primitives.secondBound := by ring1
    exact bounded.trans (rearrange.le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (prepared.secondBound_le nonnegative)
        squaredNonnegative))

end RequestedPrimitiveParents
end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
