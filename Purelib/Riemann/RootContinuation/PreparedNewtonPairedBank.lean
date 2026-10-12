module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Riemann.RootContinuation.PreparedNewtonPairedArea
import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Mathlib.Order.Basic

public section

/-! Common paired refinements across a complete parent bank. Child depths may differ. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank

open Purelib
open Purelib.Data.Rat

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the paired-bank bounds. -/
private abbrev Coordinate := Fraction.Rational

open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample
open Purelib.Integration.Path.PairedAreaBlocks
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Paired refinements indexed by the exact original ordered parent list.

Each retained head keeps both differential refinements of one original parent, while its tail retains the remaining
original owners. -/
inductive PairedBoundaryParents (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus) :
    List (CenteredEdge curve differential) → Type 2
  /-- The empty paired bank for the exact empty original parent list. -/ | nil : PairedBoundaryParents request other []
  /-- Prepend one original paired parent to its retained tail bank. -/ | cons {parent : CenteredEdge curve differential}
    {rest : List (CenteredEdge curve differential)}
      (head : PairedBoundaryParent request parent other) (tail : PairedBoundaryParents request other rest) :
      PairedBoundaryParents request other (parent :: rest)

constructive_injectivity PairedBoundaryParents

namespace PairedBoundaryParents
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}

open Purelib.Curves.Hyperelliptic in
/-- Build paired refinements for the original boundary parent list.

Each original parent must lie on the retained band boundary and have a strictly increasing parameter interval; the
recursive construction keeps their order and properness witnesses. -/
@[expose] def build (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus) :
    ∀ (parents : List (CenteredEdge curve differential)),
      (∀ parent ∈ parents, ParentOnBoundary parent request.sample.output.box) →
      (∀ parent ∈ parents, parent.edge.left.parameter < parent.edge.request.endpoint.parameter) →
      PairedBoundaryParents request other parents
  | [], _, _ => .nil
  | parent :: rest, boundary, proper =>
    .cons (PairedBoundaryParent.build request parent other (boundary parent (List.mem_cons_self ..))
      (proper parent (List.mem_cons_self ..)))
      (build request other rest (fun child member => boundary child (List.mem_cons_of_mem parent member))
        (fun child member => proper child (List.mem_cons_of_mem parent member)))

open Purelib.Riemann.RootContinuation in
/-- Read the original paired increment lists in retained parent order. -/
@[expose] def incrementBlocks : {parents : List (CenteredEdge curve differential)} →
    PairedBoundaryParents request other parents → List (List PrimitivePoint)
  | _, .nil => []
  | _, .cons head tail => PreparedNewtonPairedIncrements.PairedBoundaryParent.increments head :: tail.incrementBlocks

/-- There is exactly one retained increment block per original parent. -/
theorem incrementBlocks_length {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) : bank.incrementBlocks.length = parents.length := by
  induction bank with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Each original paired block satisfies its retained area and total bounds.

Both differential densities and a common upper bound on original parent movement determine the separate squared-area and
primitive-point estimates. -/
theorem block_bounds {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents)
    (otherProfile : DifferentialProfile profile other.exponent) {movement : Fraction.Rational}
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ movement) :
    ∀ block ∈ bank.incrementBlocks,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area block) ≤
          4 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
            PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * movement)^2 ∧
      PrimitiveAreaBounds.PrimitivePoint.Bounded
        (PairedIncrementArea.total block)
        ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
          PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * movement) := by
  induction bank with
  | nil => intro block member; cases member
  | @cons parent rest head tail ih =>
    intro block member
    rcases Data.List.Membership.mem_cons.mp member with rfl | inTail
    · have firstNonnegative := PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
        request.errorPositive.le
      have secondNonnegative := PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile
        request.errorPositive.le
      have movementNonnegative := PreparedPrimitiveRequests.movement_nonnegative parent
      have movementLe := movements _ (List.mem_cons_self ..)
      have densityNonnegative := add_nonneg firstNonnegative secondNonnegative
      have productLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe densityNonnegative
      constructor
      · exact (PreparedNewtonPairedArea.PairedBoundaryParent.paired_area_density_bound head otherProfile).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
              movementNonnegative) productLe 2)
            (by decide))
      · constructor
        · rw [← Norm.Basic.normSq_eq_canonical]
          change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments head).map PrimitivePoint.left)) ≤ _
          rw [PreparedNewtonPairedIncrements.PairedBoundaryParent.total_left head]
          exact head.first_integral_density_bound.trans
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (le_add_of_nonneg_right secondNonnegative) movementNonnegative).trans productLe)
        · rw [← Norm.Basic.normSq_eq_canonical]
          change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments head).map PrimitivePoint.right)) ≤ _
          rw [PreparedNewtonPairedIncrements.PairedBoundaryParent.total_right head]
          exact (head.second_integral_density_bound otherProfile).trans
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (le_add_of_nonneg_left firstNonnegative) movementNonnegative).trans productLe)
    · exact ih (fun parent member => movements parent (List.mem_cons_of_mem _ member)) block inTail

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Bound the flattened original paired area using the retained dyadic parent count.

The quarter-radius movement bounds yield factor 16 times the square of the summed differential densities times total
movement. -/
theorem area_density_bound {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) (otherProfile : DifferentialProfile profile other.exponent)
    (movement : Fraction.Rational) (depth : Nat) (nonnegative : 0 ≤ movement) (count : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents,
      PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius movement depth) :
          Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area bank.incrementBlocks.flatten) ≤
      16 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * movement)^2 :=
  PairedAreaBlocks.dyadic_blocks_area_bound bank.incrementBlocks depth
    (bank.incrementBlocks_length.trans count)
    (add_nonneg (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
      request.errorPositive.le)
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile
        request.errorPositive.le)) nonnegative
    (fun block member => (bank.block_bounds otherProfile movements block member).1)
    (fun block member => (bank.block_bounds otherProfile movements block member).2)

end PairedBoundaryParents
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
