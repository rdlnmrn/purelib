module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Choose a shared spatial depth and root-reading tolerance from the retained
common-cell coordinate bounds before polynomial acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
open Purelib.Data.Rat
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial (CoordinateBounds)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

set_option genInjectivity false in
/-- The ordered coordinate-slope bounds for every retained common interval. -/
inductive BasisCommonCoordinateBounds (regular : RegularBounds.Data cap) :
    List (CommonCover.BasisCommonInterval cover covers) → Type 1
  /-- The empty coordinate-bound bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds
    regular []
  /-- Retain the first interval's actual coordinate bounds and the bounds for its remaining intervals. -/ | cons
    {interval : CommonCover.BasisCommonInterval cover covers} {remaining : List (CommonCover.BasisCommonInterval cover
    covers)}
      (head : CoordinatePolynomial.CoordinateBounds (ArcSamples.Data.build regular interval.anchor.cell))
      (tail :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds
        regular remaining) :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds
        regular (interval :: remaining)

constructive_injectivity BasisCommonCoordinateBounds

namespace BasisCommonCoordinateBounds

/-- Build the coordinate-slope bounds on each retained interval in order.

Each bound retains the arc sample at the original interval anchor, and recursion preserves the remaining interval bank.
-/
@[expose] def build (regular : RegularBounds.Data cap) :
    (intervals : List (CommonCover.BasisCommonInterval cover covers)) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds regular
      intervals
  | [] => .nil
  | interval :: remaining => .cons
      (CoordinateBounds.build (ArcSamples.Data.build regular interval.anchor.cell))

        (build
        regular remaining)

/-- The maximum retained coordinate slope, or zero for an empty bank.

The recursive maximum reads the original bound at each retained interval and keeps the bank order unchanged. -/
@[expose] def maximum : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds regular
  intervals → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons head tail => max head.slope tail.maximum

/-- The maximum retained coordinate slope is nonnegative. -/
theorem nonnegative : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds
      regular intervals) → 0 ≤ bounds.maximum
  | _, .nil => le_rfl
  | _, .cons head _ => head.slope_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

end BasisCommonCoordinateBounds

set_option genInjectivity false in
/-- A common spatial depth and reading tolerance paying coordinate clearance on every retained interval.

The depth respects the supplied floor, and the tolerance fits the padded square, unit and collar constraints before
polynomial acquisition. -/
structure BasisCommonCoordinateRequest (regular : RegularBounds.Data cap)
    (intervals : List (CommonCover.BasisCommonInterval cover covers)) (minimum : Nat) where
  /-- The retained coordinate-bound bank on the actual common intervals. -/ bounds :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds regular
    intervals
  /-- The selected shared spatial depth. -/ depth : Nat
  /-- The shared depth is the deterministic first-quarter search for the retained maximum slope and clearance target. -/
    depth_eq : depth = Search.firstQuarterBelow (2 * bounds.maximum) minimum ((collar.coordinateBound / 20) / 2)
  /-- The selected depth respects the requested minimum. -/ minimum_le : minimum ≤ depth
  /-- The shared positive root-reading tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The tolerance is the minimum of the unit, padded-square and two collar allowances. -/ tolerance_eq : tolerance =
    min 1 (min regular.padded.squareTolerance
    (min (collar.coordinateBound / 4) (((collar.coordinateBound / 20) / 2) / 8)))
  /-- The shared reading tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The shared reading tolerance is at most one. -/ small : tolerance ≤ 1
  /-- The tolerance fits the retained padded square allowance. -/ padded : tolerance ≤ regular.padded.squareTolerance
  /-- The tolerance fits one quarter of the collar coordinate bound. -/ clearance : tolerance ≤ collar.coordinateBound /
    4
  /-- The combined spatial and reading error fits one twentieth of the collar coordinate bound. -/ paid : 2 *
    (Geometric.Basic.quarterRadius bounds.maximum depth + 4 * tolerance) ≤ collar.coordinateBound / 20

constructive_injectivity BasisCommonCoordinateRequest

namespace BasisCommonCoordinateRequest

/-- Search for a shared spatial depth and choose a positive reading tolerance paying all retained coordinate
constraints.

The original first-quarter search respects the supplied floor, and the displayed minimum pays the padded-square and
collar allowances. -/
@[expose] def build (regular : RegularBounds.Data cap)
    (intervals : List (CommonCover.BasisCommonInterval cover covers)) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest regular
      intervals minimum := by
  let bounds :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds.build regular
    intervals
  let half := (collar.coordinateBound / 20) / 2
  have halfPositive : 0 < half := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide +kernel)) (by decide)
  let depth := Search.firstQuarterBelow (2 * bounds.maximum) minimum half
  let tolerance := min 1 (min regular.padded.squareTolerance (min (collar.coordinateBound / 4) (half / 8)))
  have positive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min
    regular.padded.squareTolerance_positive
    (Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide))
      (Fraction.Order.Field.div_pos_direct halfPositive (by decide +kernel))))
  have toleranceLe : tolerance ≤ half / 8 :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))
  have numerical : 8 * tolerance ≤ half := by
    have bound := (Fraction.Order.Field.le_div_iff_pos (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 8)).mp toleranceLe
    exact (show 8 * tolerance = tolerance * 8 by ring1).trans_le bound
  have spatial := Search.firstQuarterBelow_accurate (2 * bounds.maximum)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.nonnegative) minimum half halfPositive
  have spatialEq : Geometric.Basic.quarterRadius (2 * bounds.maximum) depth = 2 * Geometric.Basic.quarterRadius
    bounds.maximum depth := by
    simp only [Geometric.Basic.quarterRadius, Purelib.Data.Rat.Fraction.Field.div_eq_mul_inv_direct]; ring1
  change Geometric.Basic.quarterRadius (2 * bounds.maximum) depth < half at spatial
  rw [spatialEq] at spatial
  refine ⟨bounds, depth, rfl, Search.firstQuarterBelow_ge _ _ _, tolerance, rfl, positive,
    Fraction.Order.Basic.min_le_left _ _,
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _),
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _)), ?_⟩
  have halves : half + half = collar.coordinateBound / 20 := by
    change ((collar.coordinateBound / 20) / 2) + ((collar.coordinateBound / 20) / 2) = _
    exact (show _ = ((collar.coordinateBound / 20) / 2) * 2 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact (show 2 * (Geometric.Basic.quarterRadius bounds.maximum depth + 4 * tolerance) =
    2 * Geometric.Basic.quarterRadius bounds.maximum depth + 8 * tolerance by ring1).trans_le
    ((Fraction.Order.Arithmetic.add_le_add_direct spatial.le numerical).trans_eq halves)

/-- Additional spatial refinement and a smaller angular tolerance preserve the already selected coordinate clearance. -/
theorem paid_later {intervals : List (CommonCover.BasisCommonInterval cover covers)} {minimum laterDepth : Nat}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest
      regular intervals minimum) {tolerance : InverseRootPolynomial.Coordinate}
    (later : request.depth ≤ laterDepth) (smaller : tolerance ≤ request.tolerance) :
    2 * (Geometric.Basic.quarterRadius request.bounds.maximum laterDepth + 4 * tolerance) ≤ collar.coordinateBound / 20
      :=
  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (quarterRadius_antitone request.bounds.nonnegative later)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans request.paid

end BasisCommonCoordinateRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
