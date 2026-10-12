module
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Full conjugate parent-chain area keeps and pays the polygon of cached
parent totals, with the actual shared root sign. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat} {box otherBox :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other parents target minimum}

/-- The original paired source total satisfies the retained common slope bound. -/
private theorem Entry.source_bound (entry : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry
  request sample otherSample fine)
    (bounded : entry.plan.SourceBound request.slope) :
    Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded entry.certified.compared.firstSummary.totalValue
      request.slope := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  rw [entry.certified.compared.firstSummary.total_eq,
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.source_path
    entry.certified),
    Path.Dyadic.DyadicPairedPrimitivePaths.increments_total]
  have left := entry.certified.source.increment_bound (first := 0) (last := 1) (by decide) (by decide)
  have right := entry.certified.otherSource.increment_bound (first := 0) (last := 1) (by decide) (by decide)
  simp only [zeroDifference, one_pow, mul_one, Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self]
    at left right
  exact ⟨left.trans bounded.1, right.trans bounded.2⟩

/-- A source norm bound and unit comparison error bound the retained cap value by twice the slope plus one. -/
private theorem cap_bound {a b : Normalization.InverseRootPolynomial.Gaussian} {slope :
  Normalization.InverseRootPolynomial.Coordinate}
    (source : Data.Gaussian.Norm.Basic.normSq a ≤ slope) (error : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq b ≤ 2 * (slope + 1) := open Purelib.Data.Rat in by
  have identity : b = a - (a - b) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq identity).trans_le ((Gaussian.Norm.Bounds.normSq_sub_le_two _
    _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
      error) (by decide)))

/-- The actual source and cap totals satisfy the same twice-slope-plus-one magnitude bound. -/
private theorem Entry.total_bounds (entry : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry
  request sample otherSample fine)
    (bounded : entry.plan.SourceBound request.slope) :
    Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded entry.certified.compared.firstSummary.totalValue
      (2 * (request.slope + 1)) ∧
    Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      entry.certified.compared.secondSummary.totalValue (2 * (request.slope + 1)) := by
  have source := Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Entry.source_bound entry bounded
  have larger : request.slope ≤ 2 * (request.slope + 1) :=
    (le_add_of_nonneg_right (add_nonneg request.slope_nonnegative (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))).trans_eq (by ring1)
  have firstSource := source.1
  have secondSource := source.2
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at firstSource secondSource
  have firstCap := Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.cap_bound firstSource
    (entry.total_accurate.1.le.trans request.allowance_le_one)
  have secondCap := Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.cap_bound secondSource
    (entry.total_accurate.2.le.trans request.allowance_le_one)
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstCap secondCap
  exact ⟨⟨source.1.trans larger, source.2.trans larger⟩, firstCap, secondCap⟩

/-- The original cached source totals equal the totals of their complete paths after conjugating the first coordinate.
-/
private theorem conjugate_source_totals (entries : List
  (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry request sample otherSample fine)) :
    entries.map (fun entry => Path.ConjugateIncrementComparison.conjugateFirst
      entry.certified.compared.firstSummary.totalValue) =
      entries.map (fun entry => Path.ConjugateIncrementComparison.conjugateFirst (Path.PairedIncrementArea.total
        entry.pair.1)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    exact congrArg₂ List.cons (congrArg Path.ConjugateIncrementComparison.conjugateFirst
      head.certified.compared.firstSummary.total_eq) ih

/-- The two polygons of retained parent totals satisfy the original fourth-power count allowance with the shared root
sign preserved. -/
theorem Evaluation.conjugate_polygon_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine)
    {start finish : Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (Integration.PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish :=
      finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : Topology.PreparedRefinementRootChains.RootChain parents first
      last) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).map (fun values
      => Path.ConjugateIncrementComparison.conjugateFirst (Path.PairedIncrementArea.total values))) -
      Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map (fun values =>
        Path.ConjugateIncrementComparison.conjugateFirst (Path.PairedIncrementArea.total values)))) ≤
      16 * (parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 * request.allowance * (2 * (request.slope
        + 1)) := open Purelib.Data.Rat in by
  have bounds (entry : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry request sample otherSample
    fine) (member : entry ∈ evaluated.retained) :=
    Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Entry.total_bounds entry (request.plan_bounds entry.plan
      (evaluated.plans_eq ▸ Data.List.Map.mem_map_of_mem member))
  have estimate := Path.ConjugateIncrementComparison.conjugate_area_difference_bound evaluated.totalPairs
    request.positive.le
    (bound := 2 * (request.slope + 1))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg request.slope_nonnegative (by decide)))
    (by
      intro pair member
      obtain ⟨entry, _, rfl⟩ := Data.List.Map.mem_map.mp member
      have firstScalar := entry.total_accurate.1.le
      have secondScalar := entry.total_accurate.2.le
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      exact (bounds entry retained).1)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      exact (bounds entry retained).2)
  have count : evaluated.retained.length = parents.length := by
    have h := congrArg List.length ((congrArg (List.map
      Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent) evaluated.plans_eq).trans
      request.parents_eq)
    simpa only [Data.List.Map.length_map, -eq_self, -iff_self] using h
  simp only [Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation.totalPairs,
    Data.List.Map.map_map, Data.List.Map.length_map, count, -eq_self, -iff_self] at estimate
  dsimp only [Function.comp_def] at estimate
  rw [Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentSigns.Evaluation.conjugate_cap_polygon_unsigned evaluated
    chain roots,
    Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.conjugate_source_totals] at estimate
  rw [evaluated.pairs_eq] at estimate ⊢
  have compositionResult := estimate
  simp only [Data.List.Map.map_map, -eq_self, -iff_self] at compositionResult ⊢
  dsimp only [Function.comp_def] at compositionResult ⊢
  exact compositionResult

/-- Reuse the actual per-parent certificate at the common requested stage. -/
theorem Entry.conjugate_accurate (entry : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry request
  sample otherSample fine)
    (member : entry.plan ∈ request.plans) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (entry.pair.1.map
      Path.ConjugateIncrementComparison.conjugateFirst) - Path.PairedIncrementArea.area (entry.pair.2.map
      Path.ConjugateIncrementComparison.conjugateFirst)) < request.allowance := by
  have after : entry.plan.index ≤ stage :=
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.index_le member).trans (request.index_eq ▸ later)
  have totalAfter : entry.plan.totals.index ≤ stage := (Data.Nat.Order.le_max_left _ _).trans after
  have bound :=
    (Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest.AreaRequest.Certified.conjugate_unsigned_area_error
    entry.certified) (entry.plan.totals.area_le.trans totalAfter)
  rw [← Path.DyadicConjugateIncrementComparison.Bilinear.increments_conjugate,
    ← Path.DyadicConjugateIncrementComparison.Bilinear.increments_conjugate, ←
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.source_path
      entry.certified), entry.depth_eq] at bound
  exact bound

/-- The full conjugate area splits into actual block areas and the polygon of their retained totals. -/
private theorem conjugate_area_flatten (blocks : List (List Topology.Polygon.Stokes.PrimitivePoint)) :
    Path.PairedIncrementArea.area (blocks.flatten.map Path.ConjugateIncrementComparison.conjugateFirst) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map (fun values => Path.PairedIncrementArea.area
        (values.map Path.ConjugateIncrementComparison.conjugateFirst))) +
      Path.PairedIncrementArea.area (blocks.map (fun values => Path.ConjugateIncrementComparison.conjugateFirst
        (Path.PairedIncrementArea.total values))) := by
  rw [Data.List.Flatten.map_flatten, Path.PairedAreaBlocks.area_flatten, Data.List.Map.map_map, Data.List.Map.map_map]
  apply congrArg (fun values => Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map (fun values =>
    Path.PairedIncrementArea.area (values.map Path.ConjugateIncrementComparison.conjugateFirst))) +
    Path.PairedIncrementArea.area values)
  exact Data.List.Map.map_congr_left (fun values _ =>
    Path.DyadicConjugateIncrementComparison.PairedIncrementArea.total_conjugate values)

/-- The complete original source and cap increment lists have conjugate areas differing by less than the retained
target. -/
@[expose] def Evaluation.FullConjugateAreaError (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).flatten.map
    Path.ConjugateIncrementComparison.conjugateFirst) -
    Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).flatten.map
      Path.ConjugateIncrementComparison.conjugateFirst)) < target

/-- All internal conjugate areas and the polygon of parent totals are paid
by the original request. Both complete increment lists are retained. -/
theorem Evaluation.full_conjugate_area_error (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine)
    (later : request.index ≤ stage) {start finish : Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (Integration.PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish :=
      finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : Topology.PreparedRefinementRootChains.RootChain parents first
      last) :
    Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Evaluation.FullConjugateAreaError evaluated := open
      Purelib.Data.Rat in by
  have localBound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (evaluated.pairs.map (fun pair => Path.PairedIncrementArea.area (pair.1.map
      Path.ConjugateIncrementComparison.conjugateFirst) - Path.PairedIncrementArea.area (pair.2.map
      Path.ConjugateIncrementComparison.conjugateFirst))) request.allowance (by
      intro value member
      obtain ⟨pair, pairMember, rfl⟩ := Data.List.Map.mem_map.mp member
      rw [evaluated.pairs_eq] at pairMember
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp pairMember
      exact (Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Entry.conjugate_accurate entry
        (evaluated.plans_eq ▸ Data.List.Map.mem_map_of_mem retained) later).le)
  have count : evaluated.pairs.length = parents.length := by
    rw [evaluated.pairs_eq, Data.List.Map.length_map]
    have h := congrArg List.length ((congrArg (List.map
      Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent) evaluated.plans_eq).trans
      request.parents_eq)
    simpa only [Data.List.Map.length_map, -eq_self, -iff_self] using h
  rw [Data.List.Map.length_map, count, Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub] at localBound
  have polygon := Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Evaluation.conjugate_polygon_bound evaluated
    chain roots
  unfold Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.Evaluation.FullConjugateAreaError
  rw [Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.conjugate_area_flatten,
    Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea.conjugate_area_flatten]
  simp only [Data.List.Map.map_map, -eq_self, -iff_self] at polygon ⊢
  dsimp only [Function.comp_def] at polygon ⊢
  have rearrange (a b c d : Normalization.InverseRootPolynomial.Gaussian) : (a + b) - (c + d) = (a - c) + (b - d) := by
    ring1
  rw [rearrange]
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct localBound polygon) (by decide))
  have coefficient : 2 * ((parents.length : Normalization.InverseRootPolynomial.Coordinate) * ((parents.length :
    Normalization.InverseRootPolynomial.Coordinate) * request.allowance) +
      16 * (parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 * request.allowance * (2 * (request.slope
        + 1))) =
      request.coefficient * request.allowance := by rw [request.coefficient_eq]; ring1
  exact bound.trans_lt (coefficient.trans_lt request.full_paid)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea
