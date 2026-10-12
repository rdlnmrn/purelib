module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentSigns
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon

/-! The complete parent-total polygon is paid using the retained common root
sign and the same cached summaries as the internal parent-area comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry Evaluation)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.PairedIncrementArea (area)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target : Coordinate} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Request regular other parents
    target minimum}

/-- The original source summary's two total coordinates satisfy the retained parent slope bound. -/
private theorem Entry.source_bound (entry : PairedParentRequest.Request.Entry request sample otherSample fine)
    (bounded : entry.plan.SourceBound request.slope) :
    PrimitivePoint.Bounded
      entry.certified.compared.firstSummary.totalValue request.slope := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  rw [entry.certified.compared.firstSummary.total_eq, (Certified.source_path entry.certified),
    DyadicPairedPrimitivePaths.increments_total]
  have left := entry.certified.source.increment_bound (first := 0) (last := 1) (by decide) (by decide)
  have right := entry.certified.otherSource.increment_bound (first := 0) (last := 1) (by decide) (by decide)
  simp only [zeroDifference, one_pow, mul_one, Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self]
    at left right
  exact ⟨left.trans bounded.1, right.trans bounded.2⟩

/-- A unit-bounded total discrepancy transfers the original source norm bound to its cap total. -/
private theorem cap_bound {a b : Data.Gaussian.Basic.Canonical} {slope : InverseRootPolynomial.Coordinate}
    (source : Data.Gaussian.Norm.Basic.normSq a ≤ slope) (error : Data.Gaussian.Norm.Basic.normSq (a -
      b) ≤ 1) : Data.Gaussian.Norm.Basic.normSq b ≤ 2 * (slope + 1) := by
  have identity : b = a - (a - b) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq identity).trans_le
    ((Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
      error) (by decide)))

/-- Both original source and cap totals satisfy the common retained enlarged slope bound. -/
private theorem Entry.total_bounds (entry : PairedParentRequest.Request.Entry request sample otherSample fine)
    (bounded : entry.plan.SourceBound request.slope) :
    PrimitivePoint.Bounded
      entry.certified.compared.firstSummary.totalValue (2 * (request.slope + 1)) ∧
    PrimitivePoint.Bounded
      entry.certified.compared.secondSummary.totalValue (2 * (request.slope + 1)) := by
  have source := entry.source_bound bounded
  have larger : request.slope ≤ 2 * (request.slope + 1) :=
    (le_add_of_nonneg_right (add_nonneg request.slope_nonnegative (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))).trans_eq (by ring1)
  have firstSource := source.1
  have secondSource := source.2
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstSource secondSource
  have firstCap := cap_bound firstSource
    (entry.total_accurate.1.le.trans request.allowance_le_one)
  have secondCap := cap_bound secondSource
    (entry.total_accurate.2.le.trans request.allowance_le_one)
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstCap secondCap
  exact ⟨⟨source.1.trans larger, source.2.trans larger⟩, firstCap, secondCap⟩

/-- The cached source totals are exactly the totals of the original retained source paths. -/
private theorem source_totals (entries : List (PairedParentRequest.Request.Entry request sample otherSample fine)) :
    entries.map (fun entry => entry.certified.compared.firstSummary.totalValue) =
      entries.map (fun entry => PairedIncrementArea.total entry.pair.1) := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg₂ List.cons head.certified.compared.firstSummary.total_eq ih

/-- The comparison uses cached totals, not totals recomputed from fine paths. -/
@[expose] def Evaluation.totalPairs (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample fine)
  : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint) :=
  evaluated.retained.map (fun entry => (entry.certified.compared.firstSummary.totalValue,
    entry.certified.compared.secondSummary.totalValue))

/-- The complete source/cap total-polygon discrepancy satisfies the original parent-count and slope estimate.

The actual root chain supplies one common sign, and the estimate uses the same cached totals as the internal area
comparison. -/
theorem Evaluation.polygon_bound (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample fine)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).map
      PairedIncrementArea.total) -
      PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map PairedIncrementArea.total)) ≤
      16 * (parents.length : InverseRootPolynomial.Coordinate)^4 * request.allowance * (2 * (request.slope + 1)) := by
  have bounds (entry : PairedParentRequest.Request.Entry request sample otherSample fine) (member : entry ∈
    evaluated.retained) :=
    entry.total_bounds (request.plan_bounds entry.plan (evaluated.plans_eq ▸ Map.mem_map_of_mem member))
  have estimate := PairedIncrementComparison.area_difference_bound evaluated.totalPairs request.positive.le
    (bound := 2 * (request.slope + 1))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg request.slope_nonnegative (by decide)))
    (by
      intro pair member
      obtain ⟨entry, _, rfl⟩ := Map.mem_map.mp member
      have firstScalar := entry.total_accurate.1.le
      have secondScalar := entry.total_accurate.2.le
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      exact (bounds entry retained).1)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp member
      exact (bounds entry retained).2)
  have count : evaluated.retained.length = parents.length := by
    have h := congrArg List.length ((congrArg (List.map Plan.parent) evaluated.plans_eq).trans request.parents_eq)
    simpa only [Data.List.Map.length_map, -eq_self, -iff_self] using h
  simp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation.totalPairs,
    Data.List.Map.map_map, Data.List.Map.length_map, count, -eq_self, -iff_self] at estimate
  dsimp only [Function.comp_def] at estimate
  rw [evaluated.cap_polygon_unsigned chain roots,
    source_totals] at estimate
  rw [evaluated.pairs_eq] at estimate ⊢
  have compositionResult := estimate
  simp only [Data.List.Map.map_map, -eq_self, -iff_self] at compositionResult ⊢
  dsimp only [Function.comp_def] at compositionResult ⊢
  exact compositionResult

/-- The complete original flattened source and cap paired paths differ in area by less than the retained target. -/
@[expose] def Evaluation.FullAreaError (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample
  fine) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (evaluated.pairs.map Prod.fst).flatten -
    PairedIncrementArea.area (evaluated.pairs.map Prod.snd).flatten) < target

/-- All intermediate increments and all parent-total cross terms are paid. There is no remaining polygon correction in
this requested area bound. -/
theorem Evaluation.full_area_error (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample fine)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
    evaluated.FullAreaError := by
  unfold Request.Evaluation.FullAreaError
  rw [evaluated.area_decomposition]
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct evaluated.local_bound (evaluated.polygon_bound chain roots)) (by
      decide))
  have coefficient : 2 * ((parents.length : InverseRootPolynomial.Coordinate) * ((parents.length :
    InverseRootPolynomial.Coordinate) * request.allowance) +
      16 * (parents.length : InverseRootPolynomial.Coordinate)^4 * request.allowance * (2 * (request.slope + 1))) =
      request.coefficient * request.allowance := by rw [request.coefficient_eq]; ring1
  exact bound.trans_lt (coefficient.trans_lt request.full_paid)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request
