module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Refining complete prepared boundary parent banks

Each retained parent consumes the same coefficient-error request, but may
choose its own refinement depth. The integral estimates first sum within each
parent and then across the original dyadic side. Both growing squared counts
are paid, without assuming that all final child depths agree.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandBank

open Purelib.Data.List

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement (RefinedBoundaryParent)

open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
/-- An ordered bank of original boundary-parent refinements for the same retained band request.

Each refinement retains its original parent index and exact child block, preserving the complete original parent list.
-/
inductive RefinedBoundaryParents (request : PreparedBandRequest fixed target) : List (CenteredEdge curve differential) →
  Type 2
  /-- The empty original parent list has an empty retained refinement bank. -/ | nil : RefinedBoundaryParents request []
  /-- Retain the exact original head refinement and ordered tail bank. -/ | cons {parent : CenteredEdge curve
    differential} {remaining : List (CenteredEdge curve differential)}
      (head : RefinedBoundaryParent request parent) (tail : RefinedBoundaryParents request remaining) :
      RefinedBoundaryParents request (parent :: remaining)

constructive_injectivity RefinedBoundaryParents

namespace RefinedBoundaryParents

variable {request : PreparedBandRequest fixed target}

open Purelib.Riemann.RootContinuation in
/-- Refine the original ordered boundary parents using their exact boundary and properness certificates. -/
@[expose] def build (request : PreparedBandRequest fixed target) :
    ∀ (parents : List (CenteredEdge curve differential)),
      (∀ parent ∈ parents, ParentOnBoundary parent request.sample.output.box) →
      (∀ parent ∈ parents, parent.edge.left.parameter < parent.edge.request.endpoint.parameter) →
        RefinedBoundaryParents request parents
  | [], _, _ => .nil
  | parent :: remaining, boundary, proper =>
      .cons (PreparedNewtonBandRefinement.PreparedBandRequest.refineParent request parent (boundary parent
        (List.mem_cons_self ..)) (proper parent (List.mem_cons_self ..)))
        (build request remaining (fun other member => boundary other (List.mem_cons_of_mem parent member))
          (fun other member => proper other (List.mem_cons_of_mem parent member)))

/-- Collect the exact original retained child blocks as a refinement of the same ordered parent list. -/
@[expose] def blocks : {parents : List (CenteredEdge curve differential)} →
    RefinedBoundaryParents request parents → DirectBlockRefinement parents
  | _, .nil => .nil
  | _, .cons head tail => .cons head.refinement.block tail.blocks

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read each original retained parent refinement's integral sample in parent-list order. -/
@[expose] def samples : {parents : List (CenteredEdge curve differential)} → RefinedBoundaryParents request parents →
  List Basic.Canonical
  | _, .nil => []
  | _, .cons head tail =>
      (Basic.PathModel.mk (head.refinement.block.children.map CenteredEdge.model)).integralSample :: tail.samples

/-- The retained sample list has exactly one entry per original parent. -/
theorem samples_length {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents) :
    bank.samples.length = parents.length := by
  induction bank with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained parent sample sum equals the integral of their exact concatenated original child models.

Concatenation follows the same original parent order. The head block integral
and the unchanged retained tail are transported by scalar Gaussian addition. -/
theorem samples_sum {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum bank.samples = (Basic.PathModel.mk (bank.blocks.children.map
      CenteredEdge.model)).integralSample := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      rewrite [samples, Data.Gaussian.Norm.Sum.Basic.gaussianSum, blocks,
        DirectBlockRefinement.children, Map.map_append,
        Basic.PathModel.integralSample_mk_append, ih]
      exact Eq.refl _

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Each original retained parent sample obeys the common density times dyadic-movement bound.

Every displayed sample belongs to its original retained parent refinement.
Its density bound is multiplied by that parent's certified dyadic movement;
the tail uses the same common request. -/
theorem samples_bounded {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents)
    (movement : Fraction.Rational) (depth : Nat)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius movement
      depth) :
    ∀ value ∈ bank.samples, Data.Gaussian.Norm.Basic.normSq value ≤ PreparedNewtonBandSamples.Sample.preparedDensity
      request.sample fixed request.error * Geometric.Basic.quarterRadius movement depth := by
  induction bank with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      rcases Membership.mem_cons.mp member with rfl | member
      · exact head.integral_density_bound.trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (movements _ (List.mem_cons_self ..)) (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
              request.sample fixed request.errorPositive.le))
      · exact ih (fun other member => movements other (List.mem_cons_of_mem _ member)) value member

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation
/-- The retained dyadic parent bank's integral is bounded by the original density times full movement.

The exact parent count and geometric movement scale cancel in the finite Gaussian sum estimate without changing the
original child-model list. -/
theorem integral_density_bound {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request
  parents)
    (movement : Fraction.Rational) (depth : Nat) (count : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius movement
      depth) :
    Data.Gaussian.Norm.Basic.normSq (Basic.PathModel.mk (bank.blocks.children.map CenteredEdge.model)).integralSample ≤
      PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error * movement := by
  rw [← bank.samples_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le bank.samples _ (bank.samples_bounded movement depth movements)
  rw [bank.samples_length, count] at bounded
  apply bounded.trans_eq
  calc
    _ = PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error *
        (((2 ^ depth : Nat) : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) *
          Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]

/-- The exact retained parent-bank integral satisfies the original Newton-band target. -/
theorem bound {parents : List (CenteredEdge curve differential)} (bank : RefinedBoundaryParents request parents)
    (movement : Fraction.Rational) (depth : Nat) (count : parents.length = 2 ^ depth)
    (movementLe : movement ≤ 32 * request.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius movement
      depth) :
    Data.Gaussian.Norm.Basic.normSq (Basic.PathModel.mk (bank.blocks.children.map CenteredEdge.model)).integralSample ≤
      target :=
  (bank.integral_density_bound movement depth count movements).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
        request.errorPositive.le)).trans
      ((PreparedNewtonBandSamples.Sample.preparedDensity_movement_le request.sample fixed request.error_le_one
        request.radius_le_one).trans request.paid))

end RefinedBoundaryParents

end Purelib.Riemann.RootContinuation.PreparedNewtonBandBank
