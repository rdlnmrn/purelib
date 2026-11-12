module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonIncrementArea
import Purelib.Integration.Path.PairedBlockComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib.Data.Rat

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Whole common-cover paths retain their cross-interval area terms. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount : Nat} {curve : Basic.HyperellipticCurve genus} {differential other :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : UniformReciprocalCover.Cover data} {secondCover :
    UniformReciprocalCover.Cover otherData}
  {regular : RegularBounds.Data cap} {common :
    UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Coordinate} {minimum stage depth : Nat} {box otherBox :
    Rational.Box}
  {sample : Cap.Primitives.Sample cap differential stage box}
  {otherSample : Cap.Primitives.Sample cap other stage otherBox}
  {source : UniformReciprocalPrimitives.SourcePrimitive data stage} {otherSource :
    UniformReciprocalPrimitives.SourcePrimitive otherData stage}
  {request : CommonRibbonRequest regular common target minimum}
  {evaluated : Evaluation request sample
    otherSample source otherSource depth}

/-- The original interval area allowance, retaining the increment error, common slope and fourth-power interval length.
-/
@[expose] def Entry.areaAllowance (entry :
  Entry request sample otherSample source
  otherSource depth) : Coordinate :=
  16 * entry.incrementError * entry.incrementSlope * (entry.plan.interval.edge.right.parameter -
    entry.plan.interval.edge.left.parameter)^4

/-- The original endpoint-total error allowance scaled by the retained squared interval length. -/
@[expose] def Entry.totalAllowance (entry :
  Entry request sample otherSample source
  otherSource depth) : Coordinate :=
  entry.incrementError * (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^2

/-- The original source and cap total bound scaled by the retained squared interval length. -/
@[expose] def Entry.totalBound (entry :
  Entry request sample otherSample source
  otherSource depth) : Coordinate :=
  entry.incrementSlope * (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^2

/-- Take the nonnegative maximum of the original rational readings over a finite list. -/
@[expose] def maximum {α : Type _} (value : α → Coordinate) : List α →
  Coordinate
  | [] => 0
  | head :: tail => max (value head)
    (CommonRibbonRequest.maximum value tail)

/-- The retained finite rational maximum with zero base is nonnegative. -/
theorem maximum_nonnegative {α : Type _} (value : α → Coordinate) (entries : List α)
  : 0 ≤ maximum value entries := by
  induction entries with
  | nil => exact le_rfl
  | cons head tail ih => exact ih.trans (Basic.le_max_right ..)

/-- Every original retained entry's rational reading is bounded by the finite maximum. -/
private theorem le_maximum {α : Type _} (value : α → Coordinate) {entries : List α}
  {entry : α}
    (member : entry ∈ entries) : value entry ≤
      maximum value entries := by
  induction entries with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst entry; exact Basic.le_max_left ..
      · exact (ih member).trans (Basic.le_max_right ..)

/-- A common nonnegative bound on every original entry bounds the retained finite maximum. -/
private theorem maximum_le {α : Type _} (value : α → Coordinate) (entries : List α)
  {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ entry ∈ entries, value entry ≤ bound) :
      maximum value entries ≤ bound := by
  induction entries with
  | nil => exact nonnegative
  | cons head tail ih =>
      exact Basic.max_le (bounded head List.mem_cons_self)
        (ih (fun entry member => bounded entry (List.mem_cons_of_mem _ member)))

namespace Evaluation.SharedPair

/-- Read the original source and shared-cap increment paths on one retained common interval at the supplied finite
depth. -/
@[expose] def block (shared :
  SharedPair evaluated) (entry :
  Entry request sample otherSample source
  otherSource depth) (fine : Nat) :
    List PrimitivePoint × List PrimitivePoint :=
  (Path.Dyadic.DyadicPairedPrimitivePaths.increments
    (sourceValues source otherSource) fine
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter,
    Path.Dyadic.DyadicPairedPrimitivePaths.increments shared.values fine
      entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter)

/-- The two original block totals and their difference satisfy the retained interval-scaled magnitude and error
allowances. -/
theorem block_totals (shared :
  SharedPair evaluated)
    (entry : Entry request sample
      otherSample source otherSource depth) (member : entry ∈ evaluated.entries) (fine : Nat) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Path.PairedIncrementArea.total (shared.block entry fine).1).sub
        (Path.PairedIncrementArea.total (shared.block entry fine).2)) entry.totalAllowance ∧
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total (shared.block entry fine).1) entry.totalBound ∧
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total (shared.block entry fine).2) entry.totalBound := open Purelib.Approximation in
        open Purelib.Data.Rat in by
  dsimp only [block]
  rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_total, Path.Dyadic.DyadicPairedPrimitivePaths.increments_total]
  have widthNonnegative := Arithmetic.sq_nonneg_direct (entry.plan.interval.edge.right.parameter -
    entry.plan.interval.edge.left.parameter)
  have errors := shared.increment_errors entry member ⟨le_rfl, entry.plan.interval.ordered⟩
    ⟨entry.plan.interval.ordered, le_rfl⟩
  have firstError : Rational.Geometric.Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.first) stage ≤
    entry.incrementError := Basic.le_max_left ..
  have secondError : Rational.Geometric.Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.second) stage ≤
    entry.incrementError := Basic.le_max_right ..
  have sourceFirst : data.sourceSlope ≤ entry.incrementSlope := (Basic.le_max_left ..).trans
    (Basic.le_max_left ..)
  have sourceSecond : otherData.sourceSlope ≤ entry.incrementSlope := (Basic.le_max_right ..).trans
    (Basic.le_max_left ..)
  have capFirst : 2 * (data.sourceSlope + Rational.Geometric.Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.first) stage) ≤
    entry.incrementSlope :=
    (Basic.le_max_left ..).trans (Basic.le_max_right ..)
  have capSecond : 2 * (otherData.sourceSlope + Rational.Geometric.Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.second) stage) ≤
    entry.incrementSlope :=
    (Basic.le_max_right ..).trans (Basic.le_max_right ..)
  have firstErrorScalar := errors.1
  have secondErrorScalar := errors.2
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstErrorScalar secondErrorScalar
  refine ⟨⟨firstErrorScalar.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct firstError
    widthNonnegative),
    secondErrorScalar.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct secondError widthNonnegative)⟩,
      ?_, ?_⟩
  · have firstScalar := source.increment_bound entry.plan.interval.edge.left.inside
      entry.plan.interval.edge.right.inside
    have secondScalar := otherSource.increment_bound entry.plan.interval.edge.left.inside
      entry.plan.interval.edge.right.inside
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
    exact ⟨firstScalar.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct sourceFirst widthNonnegative),
      secondScalar.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct sourceSecond widthNonnegative)⟩
  · have left := RegularArea.RegularAlignment.cap_increment_bound source entry.left
      ⟨entry.plan.interval.first.lower, entry.plan.interval.ordered.trans entry.plan.interval.first.upper⟩
      ⟨entry.plan.interval.first.lower.trans entry.plan.interval.ordered, entry.plan.interval.first.upper⟩
    have right := RegularArea.RegularAlignment.cap_increment_bound otherSource
      entry.right
      ⟨entry.plan.interval.second.lower, entry.plan.interval.ordered.trans entry.plan.interval.second.upper⟩
      ⟨entry.plan.interval.second.lower.trans entry.plan.interval.ordered, entry.plan.interval.second.upper⟩
    have unanchor (a b c : Gaussian.Basic.Canonical) : (b - c) - (a - c) = b - a := by ring1
    dsimp only [RegularArea.RegularAlignment.capValue] at left right
    rw [shared.first_owner entry member, unanchor] at left
    rw [shared.second_owner entry member, unanchor] at right
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
    exact ⟨left.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct capFirst widthNonnegative),
      right.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct capSecond widthNonnegative)⟩

set_option genInjectivity false in
/-- Numerical bounds are cached once from the retained entries. No spatial
depth occurs in this budget, and both coarse cross-term count factors remain. -/
structure BlockBudget (shared :
  SharedPair evaluated) where
  /-- The original retained common-interval count. -/ count : Nat
  /-- The stored count equals the actual retained entry-list length. -/ count_eq : count = evaluated.entries.length
  /-- The retained maximum original interval-area allowance. -/ areaError :
    Coordinate
  /-- The area allowance equals the exact maximum over original retained entries. -/ areaError_eq : areaError =
    maximum
    Entry.areaAllowance evaluated.entries
  /-- The retained maximum original interval-total error allowance. -/ totalError :
    Coordinate
  /-- The total error equals the exact maximum over the retained original entries. -/ totalError_eq : totalError =
    maximum
    Entry.totalAllowance evaluated.entries
  /-- The original maximum total-error allowance is nonnegative. -/ totalError_nonnegative : 0 ≤ totalError
  /-- The retained maximum magnitude allowance for both original block totals. -/ totalBound :
    Coordinate
  /-- The total magnitude bound equals its exact original retained entry maximum. -/ totalBound_eq : totalBound =
    maximum
    Entry.totalBound evaluated.entries
  /-- The original maximum block-total magnitude bound is nonnegative. -/ totalBound_nonnegative : 0 ≤ totalBound
  /-- The retained payment for complete original block areas and cross-interval errors. -/ error :
    Coordinate
  /-- The full error retains twice the count-squared area payment plus sixteen times the count-fourth-power total-error
    product. -/ error_eq : error = 2 * ((count : Coordinate)^2 * areaError + 16 *
    (count : Coordinate)^4 * totalError * totalBound)

constructive_injectivity BlockBudget

/-- Cache the original coarse entry count and maximum local allowances before choosing a fine spatial depth. -/
@[expose] def blockBudget (shared :
  SharedPair evaluated) :
  BlockBudget shared
  :=
  let count := evaluated.entries.length
  let areaError := maximum
    Entry.areaAllowance evaluated.entries
  let totalError := maximum
    Entry.totalAllowance evaluated.entries
  let totalBound := maximum
    Entry.totalBound evaluated.entries
  ⟨count, rfl, areaError, rfl, totalError, rfl,
    maximum_nonnegative _ _, totalBound,
    rfl, maximum_nonnegative _ _,
    2 * ((count : Coordinate)^2 * areaError + 16 * (count :
      Coordinate)^4 * totalError * totalBound), rfl⟩

/-- Common bounds on the original local area, total error and magnitude allowances bound the complete retained
coarse-block payment. -/
theorem BlockBudget.error_le {shared :
  SharedPair evaluated} (budget :
  BlockBudget shared)
    {area total density : Coordinate} (areaNonnegative : 0 ≤ area) (totalNonnegative
      : 0 ≤ total) (densityNonnegative : 0 ≤ density)
    (areas : ∀ entry ∈ evaluated.entries, entry.areaAllowance ≤ area)
    (totals : ∀ entry ∈ evaluated.entries, entry.totalAllowance ≤ total)
    (bounds : ∀ entry ∈ evaluated.entries, entry.totalBound ≤ density) :
    budget.error ≤ 2 * ((budget.count : Coordinate)^2 * area + 16 * (budget.count :
      Coordinate)^4 * total * density) := open Purelib.Data.Rat in by
  have areaLe : budget.areaError ≤ area := budget.areaError_eq ▸
    maximum_le _ _ areaNonnegative areas
  have totalLe : budget.totalError ≤ total := budget.totalError_eq ▸
    maximum_le _ _ totalNonnegative totals
  have boundLe : budget.totalBound ≤ density := budget.totalBound_eq ▸
    maximum_le _ _ densityNonnegative bounds
  have product := Arithmetic.mul_le_mul_direct totalLe boundLe budget.totalBound_nonnegative
    totalNonnegative
  rw [budget.error_eq]
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
  apply Arithmetic.add_le_add_direct (Arithmetic.mul_le_mul_of_nonneg_left_direct areaLe
    (Arithmetic.sq_nonneg_direct _))
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct product
    (show (0 : Coordinate) ≤ 16 * (budget.count :
      Coordinate)^4 from
      Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.pow_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le budget.count)) 4))
  exact (by ring1 : 16 * (budget.count : Coordinate)^4 * budget.totalError *
    budget.totalBound =
    (16 * (budget.count : Coordinate)^4) * (budget.totalError *
      budget.totalBound)).trans_le
      (paid.trans_eq (by ring1))

/-- The full original source and cap paths, including all cross-interval terms, satisfy the retained block area-error
bound. -/
theorem BlockBudget.area_bound {shared :
  SharedPair evaluated} (budget :
  BlockBudget shared)
  (fine : Nat) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((evaluated.entries.map (fun entry =>
      shared.block entry fine)).map Prod.fst).flatten -
      Path.PairedIncrementArea.area ((evaluated.entries.map (fun entry => shared.block entry fine)).map
        Prod.snd).flatten) ≤ budget.error := by
  have bounded := Path.PairedBlockComparison.blocks_area_difference_bound
    (evaluated.entries.map (fun entry => shared.block entry fine)) budget.totalError_nonnegative
      budget.totalBound_nonnegative
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      exact (shared.interval_area_bound entry retained fine).trans
        ((le_maximum
          Entry.areaAllowance
          retained).trans_eq budget.areaError_eq.symm))
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := (shared.block_totals entry retained fine).1
      have larger := (le_maximum
        Entry.totalAllowance
        retained).trans_eq budget.totalError_eq.symm
      exact ⟨bound.1.trans larger, bound.2.trans larger⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := (shared.block_totals entry retained fine).2.1
      have larger := (le_maximum
        Entry.totalBound retained).trans_eq
        budget.totalBound_eq.symm
      exact ⟨bound.1.trans larger, bound.2.trans larger⟩)
    (by
      intro pair member
      obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := (shared.block_totals entry retained fine).2.2
      have larger := (le_maximum
        Entry.totalBound retained).trans_eq
        budget.totalBound_eq.symm
      exact ⟨bound.1.trans larger, bound.2.trans larger⟩)
  rw [Data.List.Map.length_map, ← budget.count_eq, ← budget.error_eq] at bounded
  exact bounded

set_option genInjectivity false in
/-- Both complete paths and summaries are retained. This comparison has no
origin, ribbon-endpoint or chord correction subtracted from its error. -/
structure BlockComparison {shared :
  SharedPair evaluated} (budget :
  BlockBudget shared)
  (fine : Nat) where
  /-- The actual ordered original source/cap increment block pairs. -/ pairs : List (List
    PrimitivePoint × List PrimitivePoint)
  /-- The retained block pairs equal the exact original evaluated entry paths at the supplied depth. -/ pairs_eq : pairs
    = evaluated.entries.map (fun entry => shared.block entry fine)
  /-- The complete retained original source increment path. -/ firstPath : List PrimitivePoint
  /-- The source path is the ordered flattening of the original first block components. -/ firstPath_eq : firstPath =
    (pairs.map Prod.fst).flatten
  /-- The complete retained original shared-cap increment path. -/ secondPath : List
    PrimitivePoint
  /-- The cap path is the ordered flattening of the original second block components. -/ secondPath_eq : secondPath =
    (pairs.map Prod.snd).flatten
  /-- The cached finite summary of the exact retained source path. -/ firstSummary : Path.PairedIncrementArea.Summary
    firstPath
  /-- The cached finite summary of the exact retained cap path. -/ secondSummary : Path.PairedIncrementArea.Summary
    secondPath
  /-- The full retained signed areas satisfy the original complete-block error payment. -/ bounded :
    Gaussian.Norm.Basic.normSq (firstSummary.areaValue - secondSummary.areaValue) ≤ budget.error

constructive_injectivity BlockComparison

/-- Cache both complete original increment paths and their finite area summaries at the supplied depth. -/
@[expose] def BlockBudget.evaluate {shared :
  SharedPair evaluated} (budget :
  BlockBudget shared)
  (fine : Nat) :
  BlockComparison
  budget fine := by
  let pairs := evaluated.entries.map (fun entry => shared.block entry fine)
  let firstPath := (pairs.map Prod.fst).flatten
  let secondPath := (pairs.map Prod.snd).flatten
  let firstSummary := Path.PairedIncrementArea.Summary.build firstPath
  let secondSummary := Path.PairedIncrementArea.Summary.build secondPath
  have bounded : Gaussian.Norm.Basic.normSq (firstSummary.areaValue - secondSummary.areaValue) ≤ budget.error
    := by
    rw [firstSummary.area_eq, secondSummary.area_eq]
    exact budget.area_bound fine
  exact ⟨pairs, rfl, firstPath, rfl, secondPath, rfl, firstSummary, secondSummary, bounded⟩

end Evaluation.SharedPair
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
