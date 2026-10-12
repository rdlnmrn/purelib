module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbon
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.List
open Purelib.Riemann.Normalization

/-! One finite request for all paired ribbons on a retained common cover.
The aggregate keeps the endpoint sum explicit; it is not an area-smallness
claim for the source path before those offsets have been accounted for. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive CellPrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon (PairedRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbon (evaluateCommon)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Cover data} {secondCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- One original common interval with its two retained cell comparisons and paid paired ribbon request. -/
structure CommonRibbonPlan (regular : RegularBounds.Data cap)
    (firstCover : UniformReciprocalCover.Cover data) (secondCover : UniformReciprocalCover.Cover otherData) (allowance :
      InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The actual original interval of the retained common cover. -/ interval :
    UniformReciprocalCommonCover.CommonInterval firstCover secondCover
  /-- The retained first cell comparison or sample on this exact original common interval. -/ first : ArcSamples.Data
    regular interval.first.cell
  /-- The retained second cell comparison or sample on this exact original common interval. -/ second : ArcSamples.Data
    regular interval.second.cell
  /-- The paid paired ribbon request indexed by these original cell comparisons. -/ request :
    PairedRibbon.PairedRibbonRequest first second allowance minimum

constructive_injectivity CommonRibbonPlan

namespace CommonRibbonPlan
variable {allowance : Coordinate} {minimum : Nat}

/-- Cache the original common interval plans and their paid shared-stage request using the actual finite cover count. -/
@[expose] def build (regular : RegularBounds.Data cap) (interval : UniformReciprocalCommonCover.CommonInterval
  firstCover secondCover)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover secondCover
      allowance minimum :=
  let first := ArcSamples.Data.build regular interval.first.cell
  let second := ArcSamples.Data.build regular interval.second.cell
  ⟨interval, first, second, PairedRibbonRequest.build first second allowance positive minimum⟩

/-- Compute a stage above all original retained interval requests, preserving the supplied minimum on an empty list. -/
@[expose] def maximumIndex : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan
  regular firstCover secondCover allowance minimum) → Nat
  | [] => minimum
  | head :: tail => max head.request.index
    (maximumIndex tail)

/-- Every original retained interval request is bounded by the computed common maximum stage. -/
theorem index_le {plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular
  firstCover secondCover allowance minimum)}
    {plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover allowance minimum} (member : plan ∈ plans) :
    plan.request.index ≤ maximumIndex
      plans := by
  induction plans with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst plan; exact Data.Nat.Order.le_max_left ..
      · exact (ih member).trans (Data.Nat.Order.le_max_right ..)

end CommonRibbonPlan

set_option genInjectivity false in
/-- One cached stage request for the complete original common reciprocal cover.

The retained per-interval budget pays both finite sum factors, and the exact interval readback ties every plan to the
original cover. -/
structure CommonRibbonRequest (regular : RegularBounds.Data cap)
    (common : UniformReciprocalCommonCover.CommonCover firstCover secondCover) (target :
      InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The cached number of original common-cover intervals. -/ count : Nat
  /-- The cached count equals the original common interval-list length. -/ count_eq : count = common.intervals.length
  /-- The cached per-interval allowance paying the original full-cover target. -/ allowance :
    InverseRootPolynomial.Coordinate
  /-- The allowance is the original aggregate budget for this exact interval count. -/ allowance_eq : allowance =
    Aggregate.perTerm target count
  /-- The retained per-interval allowance is strictly positive. -/ positive : 0 < allowance
  /-- Both original finite sum factors are paid by the retained allowance. -/ paid : (count :
    InverseRootPolynomial.Coordinate) * ((count : InverseRootPolynomial.Coordinate) * allowance) < target
  /-- The cached paired ribbon plans for every original common interval. -/ plans : List
    (CommonRibbonPlan regular firstCover secondCover
    allowance minimum)
  /-- The retained plans enumerate exactly the original common-cover intervals in order. -/ intervals_eq : plans.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.interval = common.intervals
  /-- The cached common polynomial stage for the original complete interval bank. -/ index : Nat
  /-- The common stage is exactly the maximum of the original retained interval requests. -/ index_eq : index =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.maximumIndex plans

constructive_injectivity CommonRibbonRequest

namespace CommonRibbonRequest
variable {common : CommonCover firstCover
  secondCover} {target : Coordinate} {minimum : Nat}

/-- Cache the original common interval plans and their paid shared-stage request using the actual finite cover count. -/
@[expose] def build (regular : RegularBounds.Data cap) (common : UniformReciprocalCommonCover.CommonCover firstCover
  secondCover)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum
      := by
  let count := common.intervals.length
  let allowance := Aggregate.perTerm target count
  have allowancePositive := Aggregate.perTerm_positive positive count
  let plans := common.intervals.map (fun interval =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.build regular interval allowance
    allowancePositive minimum)
  have intervals : plans.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.interval =
    common.intervals := by
    dsimp only [plans]
    generalize common.intervals = entries
    induction entries with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact ⟨count, rfl, allowance, rfl, allowancePositive, Aggregate.count_mul_perTerm_lt positive count,
    plans, intervals, Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.maximumIndex
      plans, rfl⟩

variable {stage depth : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : SourcePrimitive data stage}
    {otherSource : SourcePrimitive otherData
    stage}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common
    target minimum}

set_option genInjectivity false in
/-- Each entry retains its actual samples, signs and ribbon certificate. -/
structure Entry (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular
  common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage) (depth : Nat) where
  /-- The original retained common-interval plan for this evaluated entry. -/ plan :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover secondCover
    request.allowance minimum
  /-- The retained first cell comparison or sample on this exact original common interval. -/ first : ArcSamples.Sample
    plan.first sample
  /-- The retained second cell comparison or sample on this exact original common interval. -/ second :
    ArcSamples.Sample plan.second otherSample
  /-- The retained sheet alignment of the actual first cap sample. -/ left : SheetAlignment.RegularAlignment first
  /-- The retained sheet alignment of the actual second cap sample. -/ right : SheetAlignment.RegularAlignment second
  /-- The cached paired ribbon certificate for these exact original samples and interval. -/ evaluated :
    PairedRibbonRequest.Evaluation plan.request source otherSource left right
    plan.interval.edge.left.parameter plan.interval.edge.right.parameter depth

constructive_injectivity Entry

/-- Evaluate one original interval's paired cap samples and retained sheet signs, caching its actual ribbon certificate.
-/
@[expose] def evaluateEntry (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (depth : Nat)
    (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover request.allowance minimum)
    (later : plan.request.index ≤ stage) :
      Entry request sample
      otherSample source otherSource depth :=
  let first := ArcSamples.Sample.ofPrimitive plan.first sample (CellPrimitive.build plan.interval.first.cell stage) rfl
  let second := ArcSamples.Sample.ofPrimitive plan.second otherSample (CellPrimitive.build plan.interval.second.cell
    stage) rfl
  let left := RegularAlignment.build first chart
  let right := RegularAlignment.build second chart
  ⟨plan, first, second, left, right, CommonRibbon.evaluateCommon plan.interval plan.request source otherSource left
    right later depth⟩

/-- Evaluate each original retained interval plan at the supplied common stage and finite spatial depth. -/
@[expose] def evaluateEntries (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (depth : Nat) :
    (plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover request.allowance minimum)) →
    (∀ plan ∈ plans, plan.request.index ≤ stage) → List
      (Entry request sample
      otherSample source otherSource depth)
  | [], _ => []
  | plan :: tail, later =>
      evaluateEntry request sample
        otherSample source otherSource chart depth plan (later plan List.mem_cons_self) ::
        evaluateEntries
          request sample otherSample source otherSource chart depth tail
          (fun plan member => later plan (List.mem_cons_of_mem _ member))

/-- The evaluated original entry bank reads back exactly its retained plan list. -/
theorem evaluateEntries_plans (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (depth : Nat)
    (plans : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover request.allowance minimum))
    (later : ∀ plan ∈ plans, plan.request.index ≤ stage) :
    (evaluateEntries request sample
      otherSample source otherSource chart depth plans later).map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.plan = plans := by
  induction plans with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) (ih _)

set_option genInjectivity false in
/-- Cached complete source and cap areas with the original open endpoint correction sum.

Every entry retains its actual samples and signs, and the summed remainder is certified against the shared requested
target. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
  regular common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage) (depth : Nat) where
  /-- The actual original evaluated ribbon entries in retained cover order. -/ entries : List
    (Entry request sample otherSample
    source otherSource depth)
  /-- The evaluated entries read back exactly the original request's plan list. -/ plans_eq : entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.plan = request.plans
  /-- The cached sum of original paired source interval areas. -/ sourceArea : InverseRootPolynomial.Gaussian
  /-- The source area is exactly the sum of the retained original entry source areas. -/ sourceArea_eq : sourceArea =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sourceArea))
  /-- The cached sum of original retained cap interval areas. -/ capArea : InverseRootPolynomial.Gaussian
  /-- The cap area is exactly the sum of the retained original entry cap areas. -/ capArea_eq : capArea =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.capArea))
  /-- The cached sum of actual original open endpoint corrections. -/ endpoint : InverseRootPolynomial.Gaussian
  /-- The endpoint correction is exactly the sum of the retained original entry endpoint terms. -/ endpoint_eq :
    endpoint = Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.endpoint))
  /-- The cached original source-minus-cap area after all endpoint corrections. -/ remainder :
    InverseRootPolynomial.Gaussian
  /-- The retained remainder is exactly source area minus cap area minus the original endpoint sum. -/ remainder_eq :
    remainder = sourceArea - capArea - endpoint
  /-- The actual retained full-cover remainder satisfies the original requested target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq remainder < target

constructive_injectivity Evaluation

/-- Fold the original cached ribbon entries once, preserving their endpoint corrections and paying the actual
finite-count budget. -/
@[expose] def ofEntries (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
  regular common target minimum)
    (entries : List (Entry request
      sample otherSample source otherSource depth))
    (plans : entries.map Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.plan =
      request.plans) : Evaluation
      request sample otherSample source otherSource depth := by
  let sourceArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
    entry.evaluated.sourceArea))
  let capArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.capArea))
  let endpoint := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.endpoint))
  let remainder := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.remainder))
  have identity : remainder = sourceArea - capArea - endpoint := by
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.remainder)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sourceArea)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.capArea)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.endpoint))
    clear plans sourceArea capArea endpoint remainder
    induction entries with
    | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0 - 0; ring1
    | cons head tail ih =>
        change head.evaluated.remainder + _ = (_ + _) - (_ + _) - (_ + _)
        rw [head.evaluated.remainder_eq, ih]
        ring1
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (entries.map (fun entry => entry.evaluated.remainder)) request.allowance (by
      intro value member
      obtain ⟨entry, _, rfl⟩ := Map.mem_map.mp member
      exact entry.evaluated.accurate.le)
  have length : entries.length = request.count := by
    have first := congrArg List.length plans
    have second := congrArg List.length request.intervals_eq
    rw [Data.List.Map.length_map] at first second
    exact (first.trans second).trans request.count_eq.symm
  rw [Data.List.Map.length_map, length] at bound
  exact ⟨entries, plans, sourceArea, rfl, capArea, rfl, endpoint, rfl, remainder, identity, bound.trans_lt request.paid⟩

/-- A shared late stage evaluates every requested interval at any spatial depth. The source polynomials are shared
across the complete family. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
  regular common target minimum)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (source : UniformReciprocalPrimitives.SourcePrimitive data stage) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData stage)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤ stage) (depth : Nat) :
    Evaluation request sample
      otherSample source otherSource depth := by
  have allLater (plan) (member : plan ∈ request.plans) : plan.request.index ≤ stage :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan.index_le member).trans
      (request.index_eq ▸ later)
  exact ofEntries request
    (evaluateEntries request sample
    otherSample source otherSource chart depth request.plans allLater)
    (evaluateEntries_plans request
      sample otherSample source otherSource chart depth request.plans allLater)

end CommonRibbonRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
