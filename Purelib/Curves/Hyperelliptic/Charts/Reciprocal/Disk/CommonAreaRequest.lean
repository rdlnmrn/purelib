module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonIncrementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

open Purelib.Data.Rat

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

/-! A computed model stage pays the uncorrected whole-parent area error.
All constants depend on the retained cover, not on final spatial depth. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {secondCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat} {request :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum}

/-- Take the maximum of both original regular scales over the retained common ribbon plans. -/
@[expose] def regularMaximum {allowance : Normalization.InverseRootPolynomial.Coordinate} : List
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover secondCover allowance
  minimum) → Normalization.InverseRootPolynomial.Coordinate
  | [] => 0
  | head :: tail => max (max (Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale head.first)
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale head.second))
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum tail)

/-- The maximum retained regular scale is nonnegative. -/
private theorem regularMaximum_nonnegative {allowance : Normalization.InverseRootPolynomial.Coordinate}
    (plans : List (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover allowance minimum)) : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum plans
      := by
  induction plans with
  | nil => exact le_rfl
  | cons head tail ih => exact ih.trans (Fraction.Order.Basic.le_max_right ..)

/-- The original regular-scale maximum used by the area-request constructor is nonnegative. -/
theorem regularMaximum_nonnegative_for_build {allowance : Normalization.InverseRootPolynomial.Coordinate}
    (plans : List (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover allowance minimum)) : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum plans
      := by
  induction plans with
  | nil => exact le_rfl
  | cons head tail ih => exact ih.trans (Fraction.Order.Basic.le_max_right ..)

/-- Each retained ribbon plan's two original regular scales are below the common maximum. -/
private theorem regularMaximum_bounds {allowance : Normalization.InverseRootPolynomial.Coordinate}
    {plans : List (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover
      secondCover allowance minimum)}
    {plan : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonPlan regular firstCover secondCover
      allowance minimum} (member : plan ∈ plans) :
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale plan.first) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum plans ∧
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale plan.second) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum plans := by
  induction plans with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst plan; exact ⟨(Fraction.Order.Basic.le_max_left ..).trans (Fraction.Order.Basic.le_max_left ..),
          (Fraction.Order.Basic.le_max_right ..).trans (Fraction.Order.Basic.le_max_left ..)⟩
      · exact ⟨(ih member).1.trans (Fraction.Order.Basic.le_max_right ..), (ih member).2.trans
          (Fraction.Order.Basic.le_max_right ..)⟩

set_option genInjectivity false in
/-- A computed stage paying the original whole-parent area error.

Cache the actual plan count, cover-dependent scales and geometric error with exact identities and strict payment. -/
structure AreaRequest (request : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular
  common target minimum) where
  /-- The cached number of original common ribbon plans. -/ count : Nat
  /-- The cached count is exactly the original retained plan-list length. -/ count_eq : count = request.plans.length
  /-- The maximum regular scale of the original ribbon plans. -/ regularScale :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The cached regular scale equals the exact original plan maximum. -/ regularScale_eq : regularScale =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum request.plans
  /-- The retained regular scale is nonnegative. -/ regularScale_nonnegative : 0 ≤ regularScale
  /-- The maximum slope of the two original source models. -/ sourceSlope :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The cached slope is exactly the maximum of the original two source slopes. -/ sourceSlope_eq : sourceSlope = max
    data.sourceSlope otherData.sourceSlope
  /-- The retained common source slope is nonnegative. -/ sourceSlope_nonnegative : 0 ≤ sourceSlope
  /-- The cached common increment-density allowance. -/ density : Normalization.InverseRootPolynomial.Coordinate
  /-- The density equals twice the sum of the retained source slope and regular scale. -/ density_eq : density = 2 *
    (sourceSlope + regularScale)
  /-- The retained increment-density allowance is nonnegative. -/ density_nonnegative : 0 ≤ density
  /-- The cached count-weighted scale of the original whole-parent area bound. -/ scale :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The scale is the exact original quadratic-and-quartic count expression times the retained regular scale and
    density. -/ scale_eq : scale = 32 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 + (count :
    Normalization.InverseRootPolynomial.Coordinate)^4) * regularScale * density
  /-- The retained whole-parent error scale is nonnegative. -/ scale_nonnegative : 0 ≤ scale
  /-- The computed model stage paying the original area target. -/ index : Nat
  /-- The stage is the original first-quarter-below search result above the request floor and stage two. -/ index_eq :
    index = Rational.Geometric.Search.firstQuarterBelow scale (max request.index 2) target
  /-- The retained area stage meets the original ribbon-request stage. -/ original_le : request.index ≤ index
  /-- The retained area stage is at least two. -/ ready : 2 ≤ index
  /-- The cached geometric area allowance at the retained stage. -/ error :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The cached error is the quarter-radius of the retained scale at its actual stage. -/ error_eq : error =
    Rational.Geometric.Basic.quarterRadius scale index
  /-- The retained geometric allowance is strictly below the original target. -/ accurate : error < target

constructive_injectivity AreaRequest

/-- Cache the actual plan count and cover scales, then search for a stage paying the retained positive target. -/
@[expose] def AreaRequest.build (request : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
  regular common target minimum) (positive : 0 < target) :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request := open Purelib.Data.Rat in by
  let count := request.plans.length
  let regularScale := Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum request.plans
  have regularNonnegative := Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum_nonnegative_for_build
    request.plans
  let sourceSlope := max data.sourceSlope otherData.sourceSlope
  have sourceNonnegative : 0 ≤ sourceSlope := data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left ..)
  let density := 2 * (sourceSlope + regularScale)
  have densityNonnegative : 0 ≤ density := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    sourceNonnegative regularNonnegative)
  let scale := 32 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 + (count :
    Normalization.InverseRootPolynomial.Coordinate)^4) * regularScale * density
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)))
    regularNonnegative) densityNonnegative
  let index := Rational.Geometric.Search.firstQuarterBelow scale (max request.index 2) target
  have later := Rational.Geometric.Search.firstQuarterBelow_ge scale (max request.index 2) target
  exact ⟨count, rfl, regularScale, rfl, regularNonnegative, sourceSlope, rfl, sourceNonnegative, density, rfl,
    densityNonnegative,
    scale, rfl, scaleNonnegative, index, rfl, (Data.Nat.Order.le_max_left ..).trans later, (Data.Nat.Order.le_max_right
      ..).trans later,
    Rational.Geometric.Basic.quarterRadius scale index, rfl, Rational.Geometric.Search.firstQuarterBelow_accurate scale
      scaleNonnegative _ target positive⟩

variable {stage depth : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data stage} {otherSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData stage}
  {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation request sample
    otherSample source otherSource depth}

/-- The geometric quarter-radius is monotone in its rational scale at each fixed stage. -/
private theorem quarter_mono {first last : Normalization.InverseRootPolynomial.Coordinate} (order : first ≤ last) (stage
  : Nat) : Rational.Geometric.Basic.quarterRadius first stage ≤ Rational.Geometric.Basic.quarterRadius last stage :=
  open Purelib.Data.Rat in by
  rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) stage)

/-- Each original evaluated ribbon entry meets the retained common increment-error and slope bounds. -/
theorem AreaRequest.entry_bounds (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request)
    (entry : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry request sample
      otherSample source otherSource depth) (member : entry ∈ evaluated.entries) :
    entry.incrementError ≤ Rational.Geometric.Basic.quarterRadius prepared.regularScale stage ∧ entry.incrementSlope ≤
      prepared.density := open Purelib in open Purelib.Data.Rat in by
  have retained : entry.plan ∈ request.plans := evaluated.plans_eq ▸ Data.List.Map.mem_map_of_mem member
  have bounds := Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.regularMaximum_bounds retained
  rw [← prepared.regularScale_eq] at bounds
  have leftError := Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.quarter_mono bounds.1 stage
  have rightError := Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.quarter_mono bounds.2 stage
  have errorSmall := Rational.Geometric.Basic.quarterRadius_le_scale prepared.regularScale_nonnegative stage
  have firstSource : data.sourceSlope ≤ prepared.sourceSlope := prepared.sourceSlope_eq ▸
    Fraction.Order.Basic.le_max_left ..
  have secondSource : otherData.sourceSlope ≤ prepared.sourceSlope := prepared.sourceSlope_eq ▸
    Fraction.Order.Basic.le_max_right ..
  have sourceDensity : prepared.sourceSlope ≤ prepared.density := by
    rw [prepared.density_eq]
    have sumNonnegative := add_nonneg prepared.sourceSlope_nonnegative prepared.regularScale_nonnegative
    calc
      _ ≤ prepared.sourceSlope + prepared.regularScale := le_add_of_nonneg_right prepared.regularScale_nonnegative
      _ ≤ (prepared.sourceSlope + prepared.regularScale) + (prepared.sourceSlope + prepared.regularScale) :=
        le_add_of_nonneg_right sumNonnegative
      _ = _ := by ring1
  refine ⟨Fraction.Order.Basic.max_le leftError rightError, Fraction.Order.Basic.max_le (Fraction.Order.Basic.max_le
    (firstSource.trans sourceDensity) (secondSource.trans sourceDensity)) ?_⟩
  rw [prepared.density_eq]
  exact Fraction.Order.Basic.max_le (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct firstSource (leftError.trans errorSmall)) (by decide))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      secondSource (rightError.trans errorSmall)) (by decide))

/-- Each original ribbon's area, total-error and magnitude allowances fit the retained common bounds. -/
theorem AreaRequest.entry_allowances (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest
  request)
    (entry : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry request sample
      otherSample source otherSource depth) (member : entry ∈ evaluated.entries) :
    entry.areaAllowance ≤ 16 * Rational.Geometric.Basic.quarterRadius prepared.regularScale stage * prepared.density ∧
    entry.totalAllowance ≤ Rational.Geometric.Basic.quarterRadius prepared.regularScale stage ∧ entry.totalBound ≤
      prepared.density := open Purelib.Data.Rat in by
  have bounds := prepared.entry_bounds entry member
  have errorNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg prepared.regularScale_nonnegative stage
  have localSlopeNonnegative : 0 ≤ entry.incrementSlope :=
    (data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left ..)).trans (Fraction.Order.Basic.le_max_left
      ..)
  have width : entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter ≤ 1 := by
    have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
    have within := Fraction.Order.Arithmetic.sub_le_sub_direct entry.plan.interval.edge.right.inside.2
      entry.plan.interval.edge.left.inside.1
    rw [zeroDifference] at within
    exact within
  have widthNonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct entry.plan.interval.ordered
  have square : (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct widthNonnegative width 2).trans_eq (by decide)
  have fourth : (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^4 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct widthNonnegative width 4).trans_eq (by decide)
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct bounds.1 bounds.2 localSlopeNonnegative errorNonnegative
  have areaProduct := Fraction.Order.Arithmetic.mul_le_mul_direct product fourth
    (Fraction.Order.Arithmetic.pow_nonneg_direct widthNonnegative 4)
    (Fraction.Order.Arithmetic.mul_nonneg_direct errorNonnegative prepared.density_nonnegative)
  rw [mul_one] at areaProduct
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaProduct (show (0 :
    Normalization.InverseRootPolynomial.Coordinate) ≤ 16 by decide)
  refine ⟨?_, ?_, ?_⟩
  · exact (by
      unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Entry.areaAllowance;
      ring1 : entry.areaAllowance = 16 * ((entry.incrementError * entry.incrementSlope) *
        (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^4)).trans_le
        (paid.trans_eq (by ring1))
  · exact (Fraction.Order.Arithmetic.mul_le_mul_direct bounds.1 square (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      errorNonnegative).trans_eq (mul_one _)
  · exact (Fraction.Order.Arithmetic.mul_le_mul_direct bounds.2 square (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      prepared.density_nonnegative).trans_eq (mul_one _)

/-- The original shared block budget is bounded by the retained whole-parent geometric error. -/
theorem AreaRequest.budget_bound (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request)
    {shared : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair
      evaluated} (budget :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair.BlockBudget
      shared) :
    budget.error ≤ Rational.Geometric.Basic.quarterRadius prepared.scale stage := open Purelib.Data.Rat in by
  have errorNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg prepared.regularScale_nonnegative stage
  have areaNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (show
    (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16 by decide) errorNonnegative)
    prepared.density_nonnegative
  have bound := budget.error_le areaNonnegative errorNonnegative prepared.density_nonnegative
    (fun entry member => (prepared.entry_allowances entry member).1)
    (fun entry member => (prepared.entry_allowances entry member).2.1)
    (fun entry member => (prepared.entry_allowances entry member).2.2)
  have count : budget.count = prepared.count := by
    have length := congrArg List.length evaluated.plans_eq
    rw [Data.List.Map.length_map] at length
    exact budget.count_eq.trans (length.trans prepared.count_eq.symm)
  rw [count] at bound
  exact bound.trans_eq (by rw [prepared.scale_eq, Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
    Rational.Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

/-- At every sufficiently late stage the original block budget is strictly below the requested target. -/
theorem AreaRequest.budget_accurate (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest
  request)
    {shared : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair
      evaluated} (budget :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair.BlockBudget
      shared) (later : prepared.index ≤ stage) :
    budget.error < target :=
  (prepared.budget_bound budget).trans_lt
    ((quarterRadius_antitone prepared.scale_nonnegative later).trans_lt
      (prepared.error_eq ▸ prepared.accurate))

namespace AreaRequest

set_option genInjectivity false in
/-- Certified strict success for the actual two concatenated parent paths.
The source models, alignments, bounds, paths and summaries remain available. -/
structure Certified (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (fine : Nat) where
  /-- The first actual original source primitive model. -/ source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data stage
  /-- The second actual original source primitive model. -/ otherSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData stage
  /-- The original common ribbon evaluation using both retained source models. -/ ribbons :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation request sample otherSample
    source otherSource 0
  /-- The actual shared alignment of the two original ribbon paths. -/ shared :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair ribbons
  /-- The retained block budget of that exact shared alignment. -/ budget :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair.BlockBudget shared
  /-- The actual fine-stage comparison of the retained original blocks. -/ compared :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair.BlockComparison
    budget fine
  /-- The two original complete area summaries differ by less than the retained target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq
    (compared.firstSummary.areaValue - compared.secondSummary.areaValue) < target

constructive_injectivity Certified

/-- Evaluate both original source models and common ribbons, retaining the shared block comparison and strict area
certificate. -/
@[expose] def evaluate (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : prepared.index ≤
      stage) (fine : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared sample otherSample fine := by
  let source := Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive.build data stage
  let otherSource := Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive.build otherData stage
  let ribbons := request.evaluate sample otherSample source otherSource chart (prepared.original_le.trans later) 0
  let shared := ribbons.sharedPair (prepared.ready.trans later)
  let budget := shared.blockBudget
  let compared := budget.evaluate fine
  exact ⟨source, otherSource, ribbons, shared, budget, compared,
    compared.bounded.trans_lt (prepared.budget_accurate budget later)⟩

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
