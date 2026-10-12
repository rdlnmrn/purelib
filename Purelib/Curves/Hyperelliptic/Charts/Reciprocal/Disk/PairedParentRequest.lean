module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonTotalRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Init.Core
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Branches
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon

/-! Count-paid paired area requests on the retained parent spine. Each
parent keeps its two covers and complete common mesh. The budget also pays
the cross-parent polygon, using the root-chain comparison in PairedParentArea. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest (AreaRequest TotalRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledLocalPlan)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Integration.Path.PairedIncrementArea (area total)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Read the maximum of zero and all original retained parent source slopes. -/
@[expose] def sourceMaximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  UniformReciprocalCover.ParentCovers parents → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons _ data _ tail => max data.sourceSlope
    (sourceMaximum tail)

/-- The retained maximum of original parent source slopes is nonnegative. -/
theorem sourceMaximum_nonnegative {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  (covers : UniformReciprocalCover.ParentCovers parents) :
    0 ≤ sourceMaximum covers := by
  induction covers with
  | nil => exact le_rfl
  | cons patch data cover tail ih => exact ih.trans (Fraction.Order.Basic.le_max_right ..)

set_option genInjectivity false in
/-- One original parent's paired covers, complete common mesh and paid area, total and controlled-source requests. -/
structure Plan (regular : RegularBounds.Data cap)
    (differential other : Differentials.Basic.Differential genus) (allowance : InverseRootPolynomial.Coordinate)
      (minimum : Nat) where
  /-- The exact original source parent retained by this paired plan. -/ parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential
  /-- The original first-differential patch on this retained parent. -/ patch :
    UniformPrimitiveSheetCompatibility.PreparedPatch parent
  /-- The original second-differential patch on this same recast parent. -/ otherPatch :
    UniformPrimitiveSheetCompatibility.PreparedPatch (PreparedEdgeRecasting.recastCenteredEdge other parent)
  /-- The retained first patch's uniform reciprocal model data. -/ data : UniformReciprocalModels.Data patch genus
  /-- The retained second patch's uniform reciprocal model data. -/ otherData : UniformReciprocalModels.Data otherPatch
    genus
  /-- The actual retained first-differential cover on the original parent. -/ left : UniformReciprocalCover.Cover data
  /-- The actual retained second-differential cover on that same original parent. -/ right :
    UniformReciprocalCover.Cover otherData
  /-- The complete actual common mesh of both original parent covers. -/ common :
    UniformReciprocalCommonCover.CommonCover left right
  /-- The original common-ribbon request on the complete paired cover mesh. -/ request :
    CommonRibbonFamily.CommonRibbonRequest regular common allowance minimum
  /-- The retained paired area preparation on the original common ribbon request. -/ prepared :
    CommonAreaRequest.AreaRequest request
  /-- The separate retained total-discrepancy request on that same original paired area preparation. -/ totals :
    CommonAreaRequest.TotalRequest prepared allowance
  /-- The original first-differential controlled local plan with the retained common allowance. -/ source :
    PreparedReciprocalControlledRequests.CoupledLocalPlan data allowance allowance allowance minimum
  /-- The original second-differential controlled local plan with that same allowance. -/ otherSource :
    PreparedReciprocalControlledRequests.CoupledLocalPlan otherData allowance allowance allowance minimum

constructive_injectivity Plan

namespace Plan
variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Prepare both original cover banks in parent order, retaining each exact common mesh and paid area, total and source
requests. -/
@[expose] def build (regular : RegularBounds.Data cap) (other : Differentials.Basic.Differential genus)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (minimum : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
      UniformReciprocalCover.ParentCovers parents →
    UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge other)) → List
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other allowance
      minimum)
  | [], .nil, .nil => []
  | _ :: _, .cons patch data left tail, .cons otherPatch otherData right otherTail =>
      let common := CommonCover.build left right
      let request := CommonRibbonRequest.build regular common allowance positive minimum
      let prepared := AreaRequest.build request positive
      ⟨_, patch, otherPatch, data, otherData, left, right, common, request,
        prepared, TotalRequest.build prepared allowance positive,
        CoupledLocalPlan.build data allowance allowance allowance positive positive positive minimum,
        CoupledLocalPlan.build otherData allowance allowance allowance positive positive positive minimum⟩ ::
        build regular other allowance
          positive minimum tail otherTail

/-- Constructing actual paired plans preserves the exact original parent list and order. -/
theorem build_parents (regular : RegularBounds.Data cap) (other : Differentials.Basic.Differential genus)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (minimum : Nat)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (left :
      UniformReciprocalCover.ParentCovers parents)
    (right : UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge other))) :
    (build regular other allowance positive minimum
      left right).map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent = parents := by
  induction left with
  | nil => cases right; rfl
  | cons patch data cover tail ih =>
      cases right with
      | cons otherPatch otherData otherCover otherTail =>
          exact congrArg (List.cons _) (ih otherTail)

/-- Both actual source slopes in the retained parent plan satisfy the supplied common bound. -/
@[expose] def SourceBound (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular
  differential other allowance minimum) (slope : InverseRootPolynomial.Coordinate) : Prop :=
  plan.data.sourceSlope ≤ slope ∧ plan.otherData.sourceSlope ≤ slope

/-- Every constructed parent plan satisfies the maximum of both original parent-cover slope bounds. -/
theorem build_bounds (regular : RegularBounds.Data cap) (other : Differentials.Basic.Differential genus)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (minimum : Nat)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (left :
      UniformReciprocalCover.ParentCovers parents)
    (right : UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge other))) :
    ∀ plan ∈ build regular other allowance positive
      minimum left right,
      plan.SourceBound (max (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum left)
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum right)) := by
  induction left with
  | nil => cases right; intro plan member; exact False.elim (List.not_mem_nil member)
  | cons patch data cover tail ih =>
      cases right with
      | cons otherPatch otherData otherCover otherTail =>
          intro plan member
          rcases Data.List.Membership.mem_cons.mp member with same | member
          · subst plan
            exact ⟨(Fraction.Order.Basic.le_max_left ..).trans (Fraction.Order.Basic.le_max_left ..),
              (Fraction.Order.Basic.le_max_left ..).trans (Fraction.Order.Basic.le_max_right ..)⟩
          · have bound := ih otherTail plan member
            have larger : max (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum tail)
              (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum otherTail) ≤
                max (max data.sourceSlope (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum
                  tail)) (max otherData.sourceSlope
                  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum otherTail)) :=
              Fraction.Order.Basic.max_le ((Fraction.Order.Basic.le_max_right ..).trans
                (Fraction.Order.Basic.le_max_left ..)) ((Fraction.Order.Basic.le_max_right ..).trans
                (Fraction.Order.Basic.le_max_right ..))
            exact ⟨bound.1.trans larger, bound.2.trans larger⟩

/-- Read the common stage paying this actual parent's area-total and both controlled source plans. -/
@[expose] def index (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential
  other allowance minimum) : Nat :=
  max plan.totals.index (max plan.source.index plan.otherSource.index)

/-- Read the maximum retained paired-plan stage together with the original caller floor. -/
@[expose] def maximumIndex : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular
  differential other allowance minimum) → Nat
  | [] => minimum
  | head :: tail => max head.index
    (maximumIndex tail)

/-- Every actual retained plan stage is bounded by the complete plan-list maximum. -/
theorem index_le {plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular
  differential other allowance minimum)}
    {plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other allowance
      minimum} (member : plan ∈ plans) :
    plan.index ≤ maximumIndex plans := by
  induction plans with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst plan; exact Data.Nat.Order.le_max_left ..
      · exact (ih member).trans (Data.Nat.Order.le_max_right ..)

/-- Read the maximum original common-cover depth over the retained plan list. -/
@[expose] def maximumDepth : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular
  differential other allowance minimum) → Nat
  | [] => 0
  | head :: tail => max head.common.depth
    (maximumDepth tail)

/-- Every actual retained common-cover depth is bounded by the complete plan-list maximum. -/
theorem depth_le {plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular
  differential other allowance minimum)}
    {plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other allowance
      minimum} (member : plan ∈ plans) :
    plan.common.depth ≤ maximumDepth plans := by
  induction plans with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst plan; exact Data.Nat.Order.le_max_left ..
      · exact (ih member).trans (Data.Nat.Order.le_max_right ..)

end Plan

set_option genInjectivity false in
/-- The original parent spine's paid paired area, total and source comparison request.

Both cover banks, parent properness, source mass and complete paired plans are retained before sampling; the allowance
separately pays local sums and the cross-parent polygon. -/
structure Request (regular : RegularBounds.Data cap)
    (other : Differentials.Basic.Differential genus) (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
      differential))
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained first-differential cover bank on the exact original parent spine. -/ left :
    UniformReciprocalCover.ParentCovers parents
  /-- The retained second-differential cover bank on that same recast parent spine. -/ right :
    UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge other))
  /-- Every actual original parent has a strictly increasing source parameter interval. -/ proper :
    PreparedDyadicRefinements.AllParentsProper parents
  /-- The cached common upper bound on both original parent-cover source slopes. -/ slope :
    InverseRootPolynomial.Coordinate
  /-- The slope cache is exactly the maximum of the two original cover-bank maxima. -/ slope_eq : slope = max
    (sourceMaximum left)
    (sourceMaximum right)
  /-- The retained common source-slope bound is nonnegative. -/ slope_nonnegative : 0 ≤ slope
  /-- The cached parent-count and slope coefficient for the full concatenated area comparison. -/ coefficient :
    InverseRootPolynomial.Coordinate
  /-- The coefficient cache is exactly the prescribed parent-count quadratic and quartic expression. -/ coefficient_eq :
    coefficient = 2 * ((parents.length : InverseRootPolynomial.Coordinate)^2 +
    16 * (parents.length : InverseRootPolynomial.Coordinate)^4 * (2 * (slope + 1)))
  /-- The retained full-area coefficient is nonnegative. -/ coefficient_nonnegative : 0 ≤ coefficient
  /-- The cached movement mass of the exact original parent list. -/ sourceMass : InverseRootPolynomial.Coordinate
  /-- The source-mass cache equals the actual original parent movement mass. -/ sourceMass_eq : sourceMass =
    PreparedRefinementMovement.movementMass parents
  /-- The cached positive common allowance paying all original local and whole-path obligations. -/ allowance :
    InverseRootPolynomial.Coordinate
  /-- The allowance is exactly the minimum of the unit, count, full-area and source-mass budgets. -/ allowance_eq :
    allowance = min 1 (min (Aggregate.perTerm target parents.length)
    (min (target / (coefficient + 1)) ((target / 2) / (sourceMass + 1))))
  /-- The retained common allowance is strictly positive. -/ positive : 0 < allowance
  /-- The retained common allowance is at most one. -/ allowance_le_one : allowance ≤ 1
  /-- The retained allowance pays the original source-mass comparison budget. -/ source_paid : allowance ≤ (target / 2)
    / (sourceMass + 1)
  /-- The original parent count squared times the retained allowance is below the requested target. -/ paid :
    (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate) *
    allowance) < target
  /-- The original full-area coefficient times the retained allowance is below the requested target. -/ full_paid :
    coefficient * allowance < target
  /-- The cached complete ordered list of actual paired parent plans. -/ plans : List
    (Plan regular differential other allowance minimum)
  /-- The retained paired plans project to exactly the original parent list. -/ parents_eq : plans.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent = parents
  /-- Every actual retained plan satisfies the same cached original source-slope bound. -/ plan_bounds : ∀ plan ∈ plans,
    plan.SourceBound slope
  /-- The cached sufficient stage for all original paired parent plans. -/ index : Nat
  /-- The request stage is exactly the maximum of the retained plan stages and original floor. -/ index_eq : index =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.maximumIndex plans
  /-- The cached maximum common-cover depth across all actual original parent plans. -/ depth : Nat
  /-- The request depth is exactly the maximum original retained plan depth. -/ depth_eq : depth =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.maximumDepth plans

constructive_injectivity Request

namespace Request
variable {parents : List (CenteredEdge curve differential)}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Cache both original cover banks and select a positive allowance paying local sums, source movement and the complete
cross-parent area bound. -/
@[expose] def build (regular : RegularBounds.Data cap) (other : Differentials.Basic.Differential genus)
    (left : UniformReciprocalCover.ParentCovers parents) (right : UniformReciprocalCover.ParentCovers (parents.map
      (PreparedEdgeRecasting.recastCenteredEdge other)))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other parents target minimum := by
  let slope := max (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum left)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum right)
  have slopeNonnegative : 0 ≤ slope :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum_nonnegative left).trans
    (Fraction.Order.Basic.le_max_left ..)
  let coefficient := 2 * ((parents.length : InverseRootPolynomial.Coordinate)^2 + 16 * (parents.length :
    InverseRootPolynomial.Coordinate)^4 * (2 * (slope + 1)))
  have nonnegative : 0 ≤ coefficient := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le parents.length))
      4))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg slopeNonnegative (by decide)))))
  have denominatorPositive : 0 < coefficient + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    nonnegative (by decide)
  have quotientPositive := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  let sourceMass := PreparedRefinementMovement.movementMass parents
  have sourcePositive : 0 < (target / 2) / (sourceMass + 1) := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide))
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative
      parents) (by decide))
  let allowance := min 1 (min (Aggregate.perTerm target parents.length)
    (min (target / (coefficient + 1)) ((target / 2) / (sourceMass + 1))))
  have h : 0 < allowance := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min
    (Aggregate.perTerm_positive positive parents.length)
    (Fraction.Order.Basic.lt_min quotientPositive sourcePositive))
  have allowanceLe : allowance ≤ Aggregate.perTerm target parents.length :=
    (Fraction.Order.Basic.min_le_right ..).trans (Fraction.Order.Basic.min_le_left ..)
  have paid : (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate)
    * allowance) < target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowanceLe (Fraction.Cast.Order.natCast_le_direct
      (Nat.zero_le _)))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans_lt (Aggregate.count_mul_perTerm_lt positive
        parents.length)
  have fullPaid : coefficient * allowance < target := by
    have smaller := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (show allowance ≤ target / (coefficient + 1) from
        (Fraction.Order.Basic.min_le_right ..).trans ((Fraction.Order.Basic.min_le_right ..).trans
          (Fraction.Order.Basic.min_le_left ..))) nonnegative
    have increase := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show coefficient < coefficient + 1 from by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct (show (0 : Coordinate) < 1 from by decide)
          coefficient
        rewrite [AddZeroClass.add_zero] at shifted
        exact shifted) quotientPositive
    exact smaller.trans_lt (increase.trans_eq ((Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne target (coefficient + 1) denominatorPositive.ne')))
  let plans := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.build regular other allowance h
    minimum left right
  exact ⟨left, right, proper, slope, rfl, slopeNonnegative, coefficient, rfl, nonnegative, sourceMass, rfl,
    allowance, rfl, h, Fraction.Order.Basic.min_le_left ..,
    (Fraction.Order.Basic.min_le_right ..).trans ((Fraction.Order.Basic.min_le_right ..).trans
      (Fraction.Order.Basic.min_le_right ..)), paid, fullPaid, plans,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.build_parents regular other allowance h minimum
      left right,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.build_bounds regular other allowance h minimum
      left right, Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.maximumIndex plans, rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.maximumDepth plans, rfl⟩

variable {stage fine : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other parents
    target minimum}

/-- Every actual member of a proper original parent bank has strictly increasing source endpoints. -/
theorem proper_member {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (proper : PreparedDyadicRefinements.AllParentsProper parents) {parent : PreparedSubdivisionModelCore.CenteredEdge
      curve differential}
    (member : parent ∈ parents) : parent.edge.left.parameter < parent.edge.request.endpoint.parameter := by
  induction parents with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst parent; exact proper.1
      · exact ih proper.2 member

/-- The original parent's controlled primitive request at the supplied common error allowance and stage floor. -/
@[expose] def SourceRequest (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (allowance :
  InverseRootPolynomial.Coordinate) (minimum : Nat) :=
  PreparedControlledPrimitiveRequests.ControlledLocalRequest parent genus allowance allowance minimum

/-- The local fine depth compensating the actual common-cover depth to the original whole-parent depth. -/
@[expose] def localDepth (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular
  other parents target minimum)
    (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other
      request.allowance minimum) (fine : Nat) : Nat :=
  request.depth - plan.common.depth + fine

/-- Each actual member plan's cover depth plus local fine depth equals the retained common depth plus refinement. -/
theorem localDepth_eq (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
  parents target minimum)
    (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other
      request.allowance minimum) (fine : Nat)
    (member : plan ∈ request.plans) : plan.common.depth + request.localDepth plan fine = request.depth + fine := by
  have lower : plan.common.depth ≤ request.depth := request.depth_eq ▸
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.depth_le member
  change plan.common.depth + (request.depth - plan.common.depth + fine) = _
  rw [← Nat.add_assoc, Data.Nat.Subtraction.add_sub_of_le lower]

set_option genInjectivity false in
/-- One actual paired parent evaluation retaining both original controlled source requests and exact primitive
readbacks. -/
structure Entry (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other parents
  target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (fine : Nat) where
  /-- The exact original paired parent plan consumed by this entry. -/ plan :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other request.allowance
    minimum
  /-- The retained paired area certificate on the supplied original cap samples and local depth. -/ certified :
    AreaRequest.Certified plan.prepared sample otherSample (request.localDepth plan fine)
  /-- The actual entry's cover and local depths give exactly the original request depth plus refinement. -/ depth_eq :
    plan.common.depth + request.localDepth plan fine = request.depth + fine
  /-- The shared original model stage is at least two. -/ ready : 2 ≤ stage
  /-- The actual retained paired totals satisfy the original common allowance. -/ total_accurate : certified.TotalError
    request.allowance
  /-- The retained first controlled source request sharing the original area primitive. -/ source :
    SourceRequest plan.parent request.allowance
    minimum
  /-- The retained second controlled source request sharing the original paired area primitive. -/ otherSource :
    SourceRequest
    (PreparedEdgeRecasting.recastCenteredEdge other plan.parent) request.allowance minimum
  /-- The first controlled source request uses exactly the original primitive already retained by the area certificate.
  -/
  source_eq : source.localRequest.request.model.primitive.value = certified.source.primitive.value
  /-- The second controlled source request uses exactly the other original primitive retained by that certificate. -/
    otherSource_eq : otherSource.localRequest.request.model.primitive.value = certified.otherSource.primitive.value

constructive_injectivity Entry

/-- The actual first controlled source increment is the left component of the retained paired source summary. -/
theorem Entry.source_increment (entry : Entry
  request sample otherSample fine) :
    Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.increment entry.source.localRequest =
      entry.certified.compared.firstSummary.totalValue.left := by
  rw [entry.certified.compared.firstSummary.total_eq, (Certified.source_path entry.certified),
    DyadicPairedPrimitivePaths.increments_total]
  change _ = entry.certified.source.primitive.value.eval (entry.plan.parent.edge.point 1) -
    entry.certified.source.primitive.value.eval (entry.plan.parent.edge.point 0)
  unfold LocalRequest.increment
  rw [entry.source_eq]

/-- The actual second controlled source increment is the right component of the retained paired source summary. -/
theorem Entry.otherSource_increment (entry :
  Entry request sample otherSample fine) :
    Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.increment entry.otherSource.localRequest =
      entry.certified.compared.firstSummary.totalValue.right := by
  rw [entry.certified.compared.firstSummary.total_eq, (Certified.source_path entry.certified),
    DyadicPairedPrimitivePaths.increments_total]
  change _ = entry.certified.otherSource.primitive.value.eval (entry.plan.parent.edge.point 1) -
    entry.certified.otherSource.primitive.value.eval (entry.plan.parent.edge.point 0)
  unfold LocalRequest.increment
  rw [entry.otherSource_eq]
  rfl

/-- Read the actual original source and cap increment paths at their shared retained whole-parent depth. -/
@[expose] def Entry.pair (entry : Entry request
  sample otherSample fine) : List Stokes.PrimitivePoint × List PrimitivePoint :=
  (entry.certified.compared.firstPath,
    DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.capValues (parent := entry.plan.parent) sample otherSample)
      (request.depth + fine) 0 1)

/-- The actual retained source/cap path-area discrepancy satisfies the original common local allowance. -/
theorem Entry.accurate (entry : Entry request
  sample otherSample fine) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area entry.pair.1 - PairedIncrementArea.area
      entry.pair.2) < request.allowance := by
  have bound := entry.certified.accurate
  rw [entry.certified.compared.firstSummary.area_eq, (Certified.cap_area entry.certified), entry.depth_eq] at bound
  exact bound

/-- Read the actual local area discrepancy from the original cached paired summaries. -/
@[expose] def Entry.difference (entry : Entry
  request sample otherSample fine) : Gaussian :=
  entry.certified.compared.firstSummary.areaValue - entry.certified.compared.secondSummary.areaValue

/-- The cached local discrepancy equals the areas of the exact retained source and cap increment paths. -/
theorem Entry.difference_eq (entry : Entry
  request sample otherSample fine) :
    entry.difference = PairedIncrementArea.area entry.pair.1 - PairedIncrementArea.area entry.pair.2 := by
  unfold Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.difference
  rw [entry.certified.compared.firstSummary.area_eq, (Certified.cap_area entry.certified), entry.depth_eq]
  rfl

/-- The actual retained entry discrepancies agree pointwise with the original paired path-area differences. -/
theorem differences_eq (retained : List (Entry
  request sample otherSample fine)) :
    retained.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.difference =
      (retained.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.pair).map (fun pair =>
      PairedIncrementArea.area pair.1 - PairedIncrementArea.area pair.2) := by
  induction retained with
  | nil => rfl
  | cons head tail ih => exact congrArg₂ List.cons head.difference_eq ih

/-- Evaluate the supplied original member plans with the shared cap samples, retaining both source requests and their
exact primitive identities. -/
@[expose] def entries (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
  parents target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤ stage) (fine : Nat) :
    (plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other
      request.allowance minimum)) →
    (∀ plan ∈ plans, plan ∈ request.plans) → List
      (Entry request sample otherSample fine)
  | [], _ => []
  | plan :: tail, member =>
      let after := (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.index_le (member plan
        List.mem_cons_self)).trans (request.index_eq ▸ later)
      let totalAfter := (Data.Nat.Order.le_max_left _ _).trans after
      let sourceAfter := ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
      let otherAfter := ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
      let inParents : plan.parent ∈ parents := Eq.mp
        (congrArg (fun values => plan.parent ∈ values) request.parents_eq)
        (Map.mem_map_of_mem (f := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent) (member
          plan List.mem_cons_self))
      let proper := proper_member request.proper
        inParents
      let certified := plan.prepared.evaluate sample otherSample chart (plan.totals.area_le.trans totalAfter)
        (request.localDepth plan fine)
      ⟨plan, certified, request.localDepth_eq plan fine (member plan List.mem_cons_self),
        plan.prepared.ready.trans (plan.totals.area_le.trans totalAfter),
        plan.totals.accurate_total certified totalAfter,
        plan.source.sourceRequest proper certified.source sourceAfter,
        plan.otherSource.sourceRequest proper certified.otherSource otherAfter,
        plan.source.sourceRequest_primitive proper certified.source sourceAfter,
        plan.otherSource.sourceRequest_primitive proper certified.otherSource otherAfter⟩ ::
      entries request sample otherSample
        chart later fine tail
        (fun plan inTail => member plan (List.mem_cons_of_mem _ inTail))

/-- Evaluating original member plans preserves their exact ordered plan list. -/
theorem entries_plans (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
  parents target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤ stage) (fine : Nat)
    (plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan regular differential other
      request.allowance minimum))
    (member : ∀ plan ∈ plans, plan ∈ request.plans) :
    (entries request sample otherSample chart
      later fine plans member).map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.plan =
      plans := by
  induction plans with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) (ih _)

set_option genInjectivity false in
/-- The complete original paired parent evaluations and cached count-paid sum of local area errors. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
  parents target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (fine : Nat) where
  /-- The cached ordered list of actual original paired parent evaluations. -/ retained : List
    (Entry request sample otherSample fine)
  /-- The actual evaluations consume exactly the original retained plan list. -/ plans_eq : retained.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.plan = request.plans
  /-- The cached ordered list of actual source/cap increment path pairs. -/ pairs : List (List Stokes.PrimitivePoint ×
    List Stokes.PrimitivePoint)
  /-- The pair cache is exactly the readback of all retained original evaluations. -/ pairs_eq : pairs = retained.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.pair
  /-- The cached Gaussian sum of actual local parent area discrepancies. -/ localError : Data.Gaussian.Basic.Canonical
  /-- The local-error cache equals the exact sum of original paired path-area differences. -/ localError_eq : localError
    = Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => PairedIncrementArea.area pair.1 -
    PairedIncrementArea.area pair.2))
  /-- The actual summed local error satisfies the original parent-count squared allowance. -/ local_bound :
    Data.Gaussian.Norm.Basic.normSq localError ≤ (parents.length : InverseRootPolynomial.Coordinate) *
    ((parents.length : InverseRootPolynomial.Coordinate) * request.allowance)
  /-- The cached complete local-area error satisfies the original whole requested target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq localError < target

constructive_injectivity Evaluation

/-- Evaluate every original retained parent plan on the supplied shared samples and cache its exact paid local-error
sum. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
  parents target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤ stage) (fine : Nat) :
    Evaluation request sample otherSample fine
      := by
  let retained := entries request sample
    otherSample chart later fine request.plans (fun _ h => h)
  have plans := entries_plans request sample
    otherSample chart later fine request.plans (fun _ h => h)
  let pairs := retained.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.pair
  let errors := retained.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.difference
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le errors request.allowance (by
    intro value member
    obtain ⟨entry, _, rfl⟩ := Map.mem_map.mp member
    exact entry.certified.accurate.le)
  have count : retained.length = parents.length := by
    have h := congrArg List.length ((congrArg (List.map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent) plans).trans request.parents_eq)
    simp only [Data.List.Map.length_map, -eq_self, -iff_self] at h
    exact h
  simp only [errors, Data.List.Map.length_map, count, -eq_self, -iff_self] at bound
  exact ⟨retained, plans, pairs, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum errors, congrArg
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (differences_eq retained),
    bound, bound.trans_lt request.paid⟩

/-- Full concatenation preserves the polygon of parent totals. The local error is computed from the already certified
per-parent summaries. -/
theorem Evaluation.area_decomposition (evaluated :
  Evaluation request sample otherSample fine) :
    PairedIncrementArea.area (evaluated.pairs.map Prod.fst).flatten - PairedIncrementArea.area (evaluated.pairs.map
      Prod.snd).flatten =
      evaluated.localError + (PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).map PairedIncrementArea.total) -
        PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map PairedIncrementArea.total)) := by
  rw [PairedAreaBlocks.area_flatten, PairedAreaBlocks.area_flatten,
    evaluated.localError_eq, Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub]
  simp only [Data.List.Map.map_map, -eq_self, -iff_self]
  dsimp only [Function.comp_def]
  ring1

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
