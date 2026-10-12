module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds

/-! The paired parent total error is paid independently of its area error.
The comparison retains the actual shared sheet sign; unsigned total errors
are not inferred from sign-invariant bilinear area estimates. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest (AreaRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Integration.Path.PairedIncrementArea (total)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {secondCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common
    target minimum} {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest
    request}

/-- Both actual whole-parent total discrepancies satisfy the retained interval-count squared geometric bound with their
common signed primitive pair. -/
theorem AreaRequest.Certified.total_bound (certified : AreaRequest.Certified prepared sample otherSample fine) :
    PrimitivePoint.Bounded
      (certified.compared.firstSummary.totalValue.sub certified.compared.secondSummary.totalValue)
      ((prepared.count : InverseRootPolynomial.Coordinate)^2 * Geometric.Basic.quarterRadius prepared.regularScale
        stage) := by
  let pairs := certified.compared.pairs.map (fun pair => (PairedIncrementArea.total pair.1, PairedIncrementArea.total
    pair.2))
  have bounded : ∀ pair ∈ pairs,
      PrimitivePoint.Bounded
        (pair.1.sub pair.2) (Geometric.Basic.quarterRadius prepared.regularScale stage) := by
    intro pair member
    obtain ⟨block, inBlocks, rfl⟩ := Map.mem_map.mp member
    rw [certified.compared.pairs_eq] at inBlocks
    obtain ⟨entry, retained, rfl⟩ := Map.mem_map.mp inBlocks
    have bound := (certified.shared.block_totals entry retained fine).1
    have allowance := (prepared.entry_allowances entry retained).2.1
    exact ⟨bound.1.trans allowance, bound.2.trans allowance⟩
  have countEq : pairs.length = prepared.count := by
    have h := congrArg List.length certified.ribbons.plans_eq
    simp only [Data.List.Map.length_map, -eq_self, -iff_self] at h
    simp only [pairs, Data.List.Map.length_map, certified.compared.pairs_eq, prepared.count_eq, h, -eq_self, -iff_self]
    rfl
  have bound := PairedIncrementArea.total_bound
    (Geometric.Basic.quarterRadius_nonneg prepared.regularScale_nonnegative stage)
    (values := pairs.map (fun pair => pair.1.sub pair.2))
    (by
      intro point member
      obtain ⟨pair, retained, rfl⟩ := Map.mem_map.mp member
      exact bounded pair retained)
    (count := prepared.count) (by rw [Data.List.Map.length_map, countEq])
  rw [PairedIncrementComparison.total_differences] at bound
  rw [certified.compared.firstSummary.total_eq, certified.compared.secondSummary.total_eq,
    certified.compared.firstPath_eq, certified.compared.secondPath_eq,
    PairedAreaBlocks.total_flatten, PairedAreaBlocks.total_flatten]
  have compositionResult := bound
  simp only [pairs, Data.List.Map.map_map, -eq_self, -iff_self] at compositionResult ⊢
  dsimp only [Function.comp_def] at compositionResult ⊢
  exact compositionResult

set_option genInjectivity false in
/-- A separate paid total-discrepancy request on the original paired area comparison.

The retained count and regular scale determine a common geometric stage above the original area stage; the actual shared
sign choice is preserved. -/
structure TotalRequest (prepared : CommonAreaRequest.AreaRequest request) (tolerance : InverseRootPolynomial.Coordinate)
  where
  /-- The cached total-error scale for the complete original parent. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale is the original interval count squared times the retained regular comparison scale. -/ scale_eq : scale
    = (prepared.count : InverseRootPolynomial.Coordinate)^2 * prepared.regularScale
  /-- The retained total-error scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached sufficient common model stage. -/ index : Nat
  /-- The stage is the first retained geometric quarter-radius stage below the requested tolerance, above the original
    area stage. -/ index_eq : index = Search.firstQuarterBelow scale prepared.index tolerance
  /-- The retained total-error stage meets the original area-request stage. -/ area_le : prepared.index ≤ index
  /-- The cached geometric error bound at the retained stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The error cache is exactly the quarter radius of the retained scale and stage. -/ error_eq : error =
    Geometric.Basic.quarterRadius scale index
  /-- The cached total-error bound is strictly below the original requested tolerance. -/ accurate : error < tolerance

constructive_injectivity TotalRequest

/-- Cache the original count-weighted total-error scale and search above the retained area stage for the requested
tolerance. -/
@[expose] def TotalRequest.build (prepared : CommonAreaRequest.AreaRequest request) (tolerance :
  InverseRootPolynomial.Coordinate) (positive : 0 < tolerance) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.TotalRequest prepared tolerance := by
  let scale := (prepared.count : InverseRootPolynomial.Coordinate)^2 * prepared.regularScale
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct
    (prepared.count : InverseRootPolynomial.Coordinate)) prepared.regularScale_nonnegative
  let index := Search.firstQuarterBelow scale prepared.index tolerance
  exact ⟨scale, rfl, nonnegative, index, rfl, Search.firstQuarterBelow_ge _ _ _,
    Geometric.Basic.quarterRadius scale index, rfl, Search.firstQuarterBelow_accurate _ nonnegative _ _ positive⟩

/-- Both actual signed parent-total component discrepancies satisfy the supplied squared-norm tolerance. -/
@[expose] def AreaRequest.Certified.TotalError (certified : AreaRequest.Certified prepared sample otherSample fine)
    (tolerance : InverseRootPolynomial.Coordinate) : Prop :=
    Data.Gaussian.Norm.Basic.normSq
      (certified.compared.firstSummary.totalValue.left - certified.compared.secondSummary.totalValue.left) < tolerance ∧
    Data.Gaussian.Norm.Basic.normSq
      (certified.compared.firstSummary.totalValue.right - certified.compared.secondSummary.totalValue.right) < tolerance

/-- At every stage meeting the retained total request, both actual signed total discrepancies satisfy the original
tolerance. -/
theorem TotalRequest.accurate_total {tolerance : InverseRootPolynomial.Coordinate} (allocated :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.TotalRequest prepared tolerance)
    (certified : AreaRequest.Certified prepared sample otherSample fine) (later : allocated.index ≤ stage) :
    certified.TotalError tolerance := by
  have bound := certified.total_bound
  have scale : (prepared.count : InverseRootPolynomial.Coordinate)^2 * Geometric.Basic.quarterRadius
    prepared.regularScale stage =
      Geometric.Basic.quarterRadius allocated.scale stage := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, allocated.scale_eq]
    ring1
  have paid := (quarterRadius_antitone allocated.nonnegative later).trans_lt
    (allocated.error_eq ▸ allocated.accurate)
  rw [scale] at bound
  have firstScalar := bound.1
  have secondScalar := bound.2
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
  exact ⟨firstScalar.trans_lt paid, secondScalar.trans_lt paid⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
