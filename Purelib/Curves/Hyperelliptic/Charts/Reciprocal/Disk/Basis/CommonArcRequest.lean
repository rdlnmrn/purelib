module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

public section

/-! Prepay the common-interval arc errors before selecting polynomial readings.
The retained coordinate bank and angular requests share the final spatial depth. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest (BasisCommonCoordinateBounds
  BasisCommonCoordinateRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests (BasisCommonAngularRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs (basisArcScale)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target allowance : Coordinate}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

namespace BasisCommonCoordinateBounds

/-- The dyadic basis-arc error scale is monotone in the nonnegative coordinate slope. -/
private theorem arc_mono (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    {first last : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ first) (less : first ≤ last) (depth : Nat) :
    Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis first) depth ≤ Geometric.Basic.quarterRadius
      (ChartBasisArcs.basisArcScale basis last) depth := by
  have shifted := Fraction.Order.Arithmetic.add_le_add_direct less (le_refl (4 : InverseRootPolynomial.Coordinate))
  have shiftedNonnegative : 0 ≤ first + 4 := by
    simpa only [-eq_self, -iff_self, _root_.zero_add] using Fraction.Order.Arithmetic.add_le_add_direct nonnegative (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct shiftedNonnegative shifted 2
  have scale := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
      (Fraction.Order.Arithmetic.sq_nonneg_direct basis.coefficient))
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scale (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 4) depth)

/-- Every retained interval's coordinate-slope arc estimate fits the squared allowance at the shared depth. -/
@[expose] def ArcPaid (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds) (depth : Nat) (allowance :
  InverseRootPolynomial.Coordinate) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
      CommonCoordinateRequest.BasisCommonCoordinateBounds regular intervals → Prop
  | _, .nil => True
  | _, .cons head tail => Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis head.slope) depth ≤ (4 *
    allowance) ^ 2 ∧
      ArcPaid
        basis depth allowance tail

/-- A bound using the retained maximum coordinate slope pays every interval's arc estimate. -/
theorem arcPaid_of_uniform (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (depth : Nat) (allowance : InverseRootPolynomial.Coordinate) {intervals : List (CommonCover.BasisCommonInterval
      cover covers)}
    (coordinates : CommonCoordinateRequest.BasisCommonCoordinateBounds regular intervals)
    (paid : Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis coordinates.maximum) depth ≤ (4 *
      allowance) ^ 2) :
    ArcPaid basis depth
      allowance coordinates := by
  induction coordinates with
  | nil => exact True.intro
  | cons head tail ih =>
      have headBound :=
        arc_mono basis
        head.slope_nonnegative (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left head.slope tail.maximum) depth
      have tailBound :=
        arc_mono basis
        (BasisCommonCoordinateBounds.nonnegative tail) (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right head.slope
        tail.maximum) depth
      exact ⟨headBound.trans paid, ih (tailBound.trans paid)⟩

end BasisCommonCoordinateBounds

set_option genInjectivity false in
/-- A shared arc request paying all common intervals before polynomial acquisition.

The coordinate bank and angular requests retain the final spatial depth and a common positive reading tolerance. -/
structure BasisCommonArcRequest {coverFloor spatialFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (coordinate : CommonCoordinateRequest.BasisCommonCoordinateRequest regular common.intervals spatialFloor)
      (parentAllowance : InverseRootPolynomial.Coordinate) where
  /-- The shared linear arc allowance per retained common interval. -/ allowance : InverseRootPolynomial.Coordinate
  /-- The per-interval allowance is the weighted share of the parent allowance. -/ allowance_eq : allowance =
    Weighted.allowance parentAllowance (common.intervals.length : InverseRootPolynomial.Coordinate)
  /-- The retained per-interval arc allowance is strictly positive. -/ positive : 0 < allowance
  /-- The complete retained interval allowance fits the parent allowance. -/ sum_paid : (common.intervals.length :
    InverseRootPolynomial.Coordinate) * allowance ≤ parentAllowance
  /-- The selected common arc refinement depth. -/ depth : Nat
  /-- The depth is the deterministic first-quarter search paying the maximum retained basis-arc scale. -/ depth_eq :
    depth = Search.firstQuarterBelow (ChartBasisArcs.basisArcScale basis coordinate.bounds.maximum) coordinate.depth ((4
    * allowance) ^ 2)
  /-- The final depth refines the already paid coordinate depth. -/ coordinate_le : coordinate.depth ≤ depth
  /-- Every retained coordinate slope satisfies the arc bound at the final depth. -/ arc_paid :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonCoordinateBounds.ArcPaid basis depth
    allowance coordinate.bounds
  /-- The retained angular requests on the same interval list and final depth. -/ angular :
    CommonAngularRequests.BasisCommonAngularRequests regular depth common.intervals
  /-- The common root-reading tolerance for coordinate, angular and mesh constraints. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The tolerance is the minimum of the retained coordinate, angular and dyadic mesh tolerances. -/ tolerance_eq :
    tolerance = min coordinate.tolerance (min angular.tolerance (Geometric.Basic.quarterRadius 1 depth))
  /-- The common root-reading tolerance is strictly positive. -/ tolerance_positive : 0 < tolerance
  /-- The common tolerance fits the retained coordinate request. -/ coordinate_tolerance : tolerance ≤
    coordinate.tolerance
  /-- The common tolerance fits the retained angular requests. -/ angular_tolerance : tolerance ≤ angular.tolerance
  /-- The common tolerance fits the unit dyadic mesh bound. -/ mesh : tolerance ≤ Geometric.Basic.quarterRadius 1 depth

constructive_injectivity BasisCommonArcRequest

namespace BasisCommonArcRequest

/-- Allocate each interval's arc allowance, refine the common depth and retain a tolerance paying coordinate, angular
and mesh constraints. -/
@[expose] def build {coverFloor spatialFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (coordinate : CommonCoordinateRequest.BasisCommonCoordinateRequest regular common.intervals spatialFloor)
    (parentAllowance : InverseRootPolynomial.Coordinate) (positive : 0 < parentAllowance) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest common basis coordinate
      parentAllowance := by
  let allowance := Weighted.allowance parentAllowance (common.intervals.length : InverseRootPolynomial.Coordinate)
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ common.intervals.length :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have allowancePositive : 0 < allowance := Weighted.allowance_positive positive countNonnegative
  have budgetPositive : 0 < (4 * allowance) ^ 2 := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) allowancePositive) 2
  have scaleNonnegative : 0 ≤ ChartBasisArcs.basisArcScale basis coordinate.bounds.maximum :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let depth := Search.firstQuarterBelow (ChartBasisArcs.basisArcScale basis coordinate.bounds.maximum) coordinate.depth
    ((4 * allowance) ^ 2)
  have paid := (Search.firstQuarterBelow_accurate _ scaleNonnegative coordinate.depth _ budgetPositive).le
  let angular := BasisCommonAngularRequests.ofCommon common regular depth
  let tolerance := min coordinate.tolerance (min angular.tolerance (Geometric.Basic.quarterRadius 1 depth))
  have meshPositive : 0 < Geometric.Basic.quarterRadius 1 depth := Geometric.Basic.quarterRadius_pos (by decide) depth
  exact ⟨allowance, rfl, allowancePositive, Weighted.mul_allowance_le positive.le countNonnegative,
    depth, rfl, Search.firstQuarterBelow_ge _ _ _,
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonCoordinateBounds.arcPaid_of_uniform
      basis depth allowance coordinate.bounds paid,
    angular, tolerance, rfl, Purelib.Data.Rat.Fraction.Order.Basic.lt_min coordinate.positive
      (Purelib.Data.Rat.Fraction.Order.Basic.lt_min angular.positive meshPositive),
    Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _, (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _
      _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _),
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _)⟩

end BasisCommonArcRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
