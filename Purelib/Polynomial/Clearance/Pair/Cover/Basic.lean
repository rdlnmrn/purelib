module

import Purelib.Data.List.Membership
meta import Lean.Elab.Tactic.RCases

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Bisection
public import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Indexed finite polynomial clearance covers

A cover tree retains its baseline leaf and both bisection children. Its quadrance and coordinate floor indices combine
the baseline with the smaller child floor, and its ordered leaf regions cover exactly the supplied interval.
-/

namespace Purelib.Polynomial.Clearance.Pair

-- Preserve the established nominal carrier name without widening this setting to other owners.

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- The indices tie each cached aggregate to the actual finite certificate
tree.  A split retains its baseline proposal as well as both child covers.

The indexed tree retains its baseline leaf and both child intervals. Its aggregate floors and ordered regions are
computed from those same nodes. -/
public inductive Cover {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial} (source :
  Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial) :
    (parameters : Data.Rat.Interval.Bounds) → Fraction.Rational → Fraction.Rational → Type where
  /-- A single cached leaf supplies its exact quadrance and coordinate floor indices. -/ | leaf {parameters :
    Data.Rat.Interval.Bounds} (data : Cover.Leaf source parameters) :
      Cover source parameters data.normFloor data.coordinateFloor
  /-- Retain the baseline leaf and both half-interval covers, combining each floor by the maximum of the baseline and
    child minimum. -/ | split {parameters : Data.Rat.Interval.Bounds} (baseline : Cover.Leaf
    source parameters)
      {leftNorm leftCoordinate rightNorm rightCoordinate : Fraction.Rational}
      (left : Cover source (Data.Rat.Interval.Bisection.leftHalf parameters) leftNorm
        leftCoordinate)
      (right : Cover source (Data.Rat.Interval.Bisection.rightHalf parameters) rightNorm
        rightCoordinate) :
      Cover source parameters (max baseline.normFloor (min leftNorm rightNorm))
        (max baseline.coordinateFloor (min leftCoordinate rightCoordinate))

constructive_injectivity Cover

namespace Cover.split

end Cover.split

namespace Cover.split

end Cover.split

namespace Cover

variable {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial} {source :
  Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial}
  {parameters : Data.Rat.Interval.Bounds} {normFloor coordinateFloor : Fraction.Rational}

/-- The indexed quadrance floor of every finite cover is nonnegative.

A leaf supplies its own nonnegativity certificate. A split retains the baseline floor as one argument of the indexed
maximum. -/
public theorem norm_nonnegative (cover : Cover source parameters normFloor coordinateFloor) :
  0 ≤ normFloor := by
  cases cover with
  | leaf data => exact data.normFloor_nonnegative
  | split baseline _ _ => exact baseline.normFloor_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The indexed maximum-coordinate floor of every finite cover is nonnegative.

A leaf supplies its maximum-coordinate nonnegativity certificate. A split retains that baseline floor in the indexed
maximum. -/
public theorem coordinate_nonnegative (cover : Cover source parameters normFloor
  coordinateFloor) : 0 ≤ coordinateFloor := by
  cases cover with
  | leaf data => exact data.coordinateFloor_nonnegative
  | split baseline _ _ => exact baseline.coordinateFloor_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The cover's retained quadrance floor bounds pair evaluation throughout its original interval.

A contained parameter belongs to at least one half interval. The smaller child floor and baseline floor each bound the
same pair quadrance, so their maximum does too. -/
public theorem norm_le (cover : Cover source parameters normFloor coordinateFloor) {parameter
  : Fraction.Rational}
    (inside : parameters.Contains parameter) :
    normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 := by
  induction cover with
  | leaf data => exact data.normFloor_le inside
  | split baseline left right leftBound rightBound =>
      apply Fraction.Order.Basic.max_le (baseline.normFloor_le inside)
      rcases Data.Rat.Interval.Bisection.inside_half inside with leftInside | rightInside
      · exact (Fraction.Order.Basic.min_le_left _ _).trans (leftBound leftInside)
      · exact (Fraction.Order.Basic.min_le_right _ _).trans (rightBound rightInside)

/-- The cover's retained coordinate floor bounds the larger absolute coordinate throughout its original interval.

A contained parameter belongs to at least one half interval. The smaller child floor and baseline floor each bound the
same larger coordinate magnitude. -/
public theorem coordinate_le (cover : Cover source parameters normFloor coordinateFloor)
  {parameter : Fraction.Rational}
    (inside : parameters.Contains parameter) :
    coordinateFloor ≤ max (Fraction.abs (realPolynomial.eval parameter)) (Fraction.abs (imagPolynomial.eval parameter))
      := by
  induction cover with
  | leaf data => exact data.coordinateFloor_le inside
  | split baseline left right leftBound rightBound =>
      apply Fraction.Order.Basic.max_le (baseline.coordinateFloor_le inside)
      rcases Data.Rat.Interval.Bisection.inside_half inside with leftInside | rightInside
      · exact (Fraction.Order.Basic.min_le_left _ _).trans (leftBound leftInside)
      · exact (Fraction.Order.Basic.min_le_right _ _).trans (rightBound rightInside)

/-- List the retained leaf intervals in left-to-right tree order.

A leaf contributes its indexed interval once. A split concatenates the left child regions before the right child
regions, retaining tree order. -/
@[expose] public def regions : {parameters : Data.Rat.Interval.Bounds} → {normFloor coordinateFloor :
  Fraction.Rational} →
    Cover source parameters normFloor coordinateFloor → List Data.Rat.Interval.Bounds
  | parameters, _, _, .leaf _ => [parameters]
  | _, _, _, .split _ left right => left.regions ++ right.regions

/-- An explicit leaf witness covers every displayed parameter, including
original endpoints, midpoints and degenerate intervals.

Bisection assigns each contained parameter to a half interval. Structural recursion retains an explicit leaf-region
membership and containment witness. -/
public theorem covers (cover : Cover source parameters normFloor coordinateFloor) {parameter
  : Fraction.Rational}
    (inside : parameters.Contains parameter) :
    ∃ region, region ∈ cover.regions ∧ region.Contains parameter := by
  induction cover with
  | leaf data => exact ⟨_, List.mem_cons_self, inside⟩
  | split baseline left right leftCover rightCover =>
      rcases Data.Rat.Interval.Bisection.inside_half inside with leftInside | rightInside
      · obtain ⟨region, member, covered⟩ := leftCover leftInside
        exact ⟨region, Data.List.Membership.mem_append.mpr (Or.inl member), covered⟩
      · obtain ⟨region, member, covered⟩ := rightCover rightInside
        exact ⟨region, Data.List.Membership.mem_append.mpr (Or.inr member), covered⟩

/-- The cover neither extends nor reroutes its original interval.

Every listed leaf descends through the retained half-interval refinements. Containment therefore transports back to the
original indexed interval. -/
public theorem regions_subset (cover : Cover source parameters normFloor coordinateFloor)
  {region : Data.Rat.Interval.Bounds}
    (member : region ∈ cover.regions) {parameter : Fraction.Rational} (inside : region.Contains parameter) :
    parameters.Contains parameter := by
  induction cover with
  | leaf data =>
      have equal : region = _ := Data.List.Membership.mem_singleton.mp member
      exact equal ▸ inside
  | split baseline left right leftSubset rightSubset =>
      rcases Data.List.Membership.mem_append.mp member with leftMember | rightMember
      · exact Data.Rat.Interval.Bisection.leftHalf_subset (leftSubset leftMember)
      · exact Data.Rat.Interval.Bisection.rightHalf_subset (rightSubset rightMember)

/-- Every retained leaf has a strictly positive quadrance floor.

A leaf requires its cached quadrance floor to be positive. A split retains the conjunction of both child requirements.
-/
@[expose] public def AllPositive : {parameters : Data.Rat.Interval.Bounds} → {normFloor coordinateFloor :
  Fraction.Rational} →
    Cover source parameters normFloor coordinateFloor → Prop
  | _, _, _, .leaf data => 0 < data.normFloor
  | _, _, _, .split _ left right => left.AllPositive ∧ right.AllPositive

/-- Relative completeness: a fully certified generated cover supplies a
positive global floor.  No eventual-success claim is hidden in this law.

The conjunction supplies positive child floors. Their minimum is positive and bounded by the split node maximum, with no
eventual-success premise. -/
public theorem positive_of_all (cover : Cover source parameters normFloor coordinateFloor)
    (positive : cover.AllPositive) : 0 < normFloor := by
  induction cover with
  | leaf data => exact positive
  | split baseline left right leftPositive rightPositive =>
      exact (Fraction.Order.Basic.lt_min (leftPositive positive.1) (rightPositive positive.2)).trans_le
        (Fraction.Order.Basic.le_max_right _ _)

end Cover
end Purelib.Polynomial.Clearance.Pair
