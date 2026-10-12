module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.Track.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# A common finite refinement of operationally equal root owners

One strict inner box supplies an explicit four-sided margin.  Operational
equivalence selects close anchors, and a finite diameter request places an
actual tail of the second owner strictly inside both original boxes.  This is
an executable construction, not an assumed common root or an infinite limit.
-/

namespace Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement

open Purelib.Data
open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-- The exact rational carrier for root-owner interior margins. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original root readings. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

/-- The minimum signed coordinate margin between an inner and an outer box.

The left, right, bottom and top margins retain the original coordinate endpoints.
Their nested minimum is positive exactly when all four supplied margins are
positive, and the same radius bounds displacement in both coordinate directions. -/
@[expose] def interiorRadius (inner outer : Box) : Coordinate :=
  min (min (inner.xLower - outer.xLower) (outer.xUpper - inner.xUpper))
    (min (inner.yLower - outer.yLower) (outer.yUpper - inner.yUpper))

/-- Strict interior containment makes the four-coordinate interior radius positive.

Each retained strict side comparison gives its signed positive difference.
Taking the nested minimum preserves those four inequalities on the same two
original boxes. -/
theorem interiorRadius_positive {inner outer : Box}
    (strict : inner.StrictInterior outer) : 0 < interiorRadius inner outer :=
  Fraction.Order.Basic.lt_min (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.left)
      (Fraction.Order.Arithmetic.sub_pos_direct strict.right))
    (Fraction.Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct strict.bottom)
      (Fraction.Order.Arithmetic.sub_pos_direct strict.top))

open Purelib.Data.Gaussian in
/-- A positive squared radius bounds both signed coordinates of a smaller Gaussian distance.

Each coordinate square is bounded by their retained sum. Comparing those squares
with the positive radius bounds the coordinate and its negation, producing both
strict endpoints without choosing a square root. -/
private theorem signed_bounds {delta : Gaussian} {radius : Coordinate}
    (positive : 0 < radius) (close : normSq delta < radius ^ 2) :
    -radius < delta.re ∧ delta.re < radius ∧
      -radius < delta.im ∧ delta.im < radius := by
  simp only [Basic.Canonical.normSq, ← pow_two] at close
  have realSq : delta.re ^ 2 < radius ^ 2 :=
    (le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct delta.im)).trans_lt close
  have imagSq : delta.im ^ 2 < radius ^ 2 :=
    (le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct delta.re)).trans_lt close
  have realUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg positive.le realSq
  have imagUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg positive.le imagSq
  have negReal := Bounds.Square.lt_of_sq_lt_sq_of_nonneg positive.le
    (a := -delta.re) (by
      rewrite [show (-delta.re) ^ 2 = delta.re ^ 2 by ring1]
      exact realSq)
  have negImag := Bounds.Square.lt_of_sq_lt_sq_of_nonneg positive.le
    (a := -delta.im) (by
      rewrite [show (-delta.im) ^ 2 = delta.im ^ 2 by ring1]
      exact imagSq)
  exact ⟨by simpa only [neg_neg] using Fraction.Order.Arithmetic.neg_lt_neg_direct negReal,
    realUpper,
    by simpa only [neg_neg] using Fraction.Order.Arithmetic.neg_lt_neg_direct negImag,
    imagUpper⟩

/-- A retained lower-side margin and strict displacement bound keep the translated coordinate strictly above the outer
lower endpoint. -/
private theorem lower_of_close {outer inner point delta radius : Coordinate}
    (margin : radius ≤ inner - outer) (inside : inner ≤ point)
    (close : -radius < delta) : outer < point + delta := by
  calc
    outer = inner - (inner - outer) := by ring1
    _ ≤ inner - radius := Fraction.Order.Arithmetic.sub_le_sub_left_direct margin inner
    _ ≤ point - radius := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside radius
    _ < point + delta := by
      simpa only [_root_.sub_eq_add_neg] using Fraction.Order.Arithmetic.add_lt_add_left_direct close point

/-- A retained upper-side margin and strict displacement bound keep the translated coordinate strictly below the outer
upper endpoint. -/
private theorem upper_of_close {outer inner point delta radius : Coordinate}
    (margin : radius ≤ outer - inner) (inside : point ≤ inner)
    (close : delta < radius) : point + delta < outer := by
  calc
    point + delta < point + radius := Fraction.Order.Arithmetic.add_lt_add_left_direct close point
    _ ≤ inner + radius := Fraction.Order.Arithmetic.add_le_add_right_direct inside radius
    _ ≤ inner + (outer - inner) := Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) margin
    _ = outer := by ring1

open Purelib.Data.Gaussian in
/-- A point close to a point in the original inner box lies strictly inside the outer box.

The squared distance is smaller than the square of the exact minimum interior margin, retaining the original strict box
containment and point witness. -/
theorem nearby_inside {inner outer : Box} (strict : inner.StrictInterior outer)
    {point nearby : Gaussian} (inside : inner.Contains point)
    (close : normSq (nearby - point) < (interiorRadius inner outer) ^ 2) :
    outer.StrictContains nearby := by
  have bounds := signed_bounds (interiorRadius_positive strict) close
  have left := lower_of_close ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _))
    inside.1 bounds.1
  have right := upper_of_close ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_right _ _))
    inside.2.1 bounds.2.1
  have bottom := lower_of_close ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
    inside.2.2.1 bounds.2.2.1
  have top := upper_of_close ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
    inside.2.2.2 bounds.2.2.2
  simp only [Basic.sub_re, Basic.sub_im] at left right bottom top
  exact ⟨by convert left using 1; ring1, by convert right using 1; ring1,
    by convert bottom using 1; ring1, by convert top using 1; ring1⟩

set_option genInjectivity false in
/-- An indexed refinement of the original second root owner lying strictly inside both original owner boxes.

The record retains the exact second-owner refinement equation and two separate strict interior witnesses, so the common
owner preserves its construction and both input identities. -/
structure CommonRefinement {parameter : Gaussian} (first second : Owner parameter) where
  /-- The retained refinement index of the original second root owner. -/ index : Nat
  /-- The retained common root owner at the original exact parameter. -/ owner : Owner parameter
  /-- The common owner is exactly the original second owner refined at the retained index. -/ owner_eq : owner =
    second.refineAt index
  /-- The common owner's initial box lies strictly inside the original first owner's box. -/ strictFirst :
    owner.track.initial.box.StrictInterior first.track.initial.box
  /-- The common owner's initial box lies strictly inside the original second owner's box. -/ strictSecond :
    owner.track.initial.box.StrictInterior second.track.initial.box

constructive_injectivity CommonRefinement

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Construct a common strict refinement of two original root owners from their retained operational name equivalence.

A positive first-owner refinement supplies the interior margin. The original equivalence and second approximation select
an exact second-owner refinement index whose diameter and anchor proximity establish both retained interior relations.
-/
@[expose] def acquire {parameter : Gaussian} (first second : Owner parameter)
    (equivalent : NamedEquivalent (ownerRootName first.parameterNonzero first)
      (ownerRootName second.parameterNonzero second)) : CommonRefinement first second := by
  let inner := first.refineAt 1
  have innerStrict : inner.track.initial.box.StrictInterior first.track.initial.box :=
    state_strict_initial_of_pos first.track (by decide)
  let radius := interiorRadius inner.track.initial.box first.track.initial.box
  have radiusPositive : 0 < radius := interiorRadius_positive innerStrict
  let target := radius ^ 2 / 4
  have targetPositive : 0 < target := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2) (by decide)
  let firstApprox := CertifiedSquareRoot.approximation first.track
  let secondApprox := CertifiedSquareRoot.approximation second.track
  let raw := approximationEquivalent_of_rootEquivalent first.parameterNonzero first.track second.track equivalent
  let comparison := raw.compare 1 1 target targetPositive
  let secondIndex := secondApprox.refineIndex comparison.rightIndex target targetPositive
  let index := max (CertifiedSquareRoot.baseIndex second.track) secondIndex
  let owner := second.refineAt index
  have secondLater : comparison.rightIndex ≤ secondIndex :=
    secondApprox.refineIndex_ge comparison.rightIndex target targetPositive
  have indexPositive : 0 < index :=
    (comparison.right_ge.trans secondLater).trans (Nat.Order.le_max_right _ _)
  have firstLater : 1 ≤ max (CertifiedSquareRoot.baseIndex first.track) comparison.leftIndex :=
    comparison.left_ge.trans (Nat.Order.le_max_right _ _)
  let point := firstApprox.sample comparison.leftIndex
  have pointInside : inner.track.initial.box.Contains point := by
    change (CoherentRoot.state first.track 1).box.Contains
      ((CertifiedSquareRoot.approximation first.track).sample comparison.leftIndex)
    rw [CertifiedSquareRoot.approximation_sample]
    exact (CoherentRoot.state_refines_of_le first.track firstLater).contains
      (CoherentRoot.state first.track _).box.contains_anchor
  have anchorsClose : normSq (point - owner.track.initial.box.anchor) < target := by
    have bound : normSq (point - secondApprox.sample secondIndex) < target :=
      by simpa only [Norm.Basic.normSq_eq_canonical] using comparison.close (Nat.le_refl _) secondLater
    change normSq (point - (CertifiedSquareRoot.approximation second.track).sample
      secondIndex) < target at bound
    rw [CertifiedSquareRoot.approximation_sample] at bound
    exact bound
  have diameter : owner.track.initial.box.diagonalSq < target :=
    (CoherentRoot.state_diagonal_le second.track index).trans_lt
      (secondApprox.refineIndex_accurate comparison.rightIndex target targetPositive)
  have allInside : ∀ nearby : Gaussian, owner.track.initial.box.Contains nearby →
      first.track.initial.box.StrictContains nearby := by
    intro nearby inside
    apply nearby_inside innerStrict pointInside
    have distance := owner.track.initial.box.normSq_sub_le_diagonalSq inside
      owner.track.initial.box.contains_anchor
    rw [Norm.Basic.normSq_eq_canonical] at distance
    have triangle := Norm.Bounds.normSq_sub_le_via nearby owner.track.initial.box.anchor point
    simp only [Norm.Basic.normSq_eq_canonical] at triangle
    have reverse : normSq (owner.track.initial.box.anchor - point) =
        normSq (point - owner.track.initial.box.anchor) := by
      rw [← Basic.Canonical.normSq_neg (point - owner.track.initial.box.anchor)]
      congr 1
      ring1
    calc
      _ ≤ 2 * (normSq (nearby - owner.track.initial.box.anchor) +
          normSq (owner.track.initial.box.anchor - point)) := triangle
      _ < 2 * (target + target) := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) (Fraction.Order.Arithmetic.add_lt_add_direct (distance.trans_lt diameter)
          (reverse ▸ anchorsClose))
      _ = radius ^ 2 := by
        change 2 * (radius ^ 2 / 4 + radius ^ 2 / 4) = radius ^ 2
        calc
          _ = (radius ^ 2 / 4) * 4 := by ring1
          _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have anchorInside := allInside owner.track.initial.box.anchor owner.track.initial.box.contains_anchor
  have cornerInside := allInside
    ⟨owner.track.initial.box.xUpper, owner.track.initial.box.yUpper⟩
    ⟨owner.track.initial.box.x_valid, le_rfl, owner.track.initial.box.y_valid, le_rfl⟩
  exact ⟨index, owner, rfl, ⟨anchorInside.1, cornerInside.2.1, anchorInside.2.2.1, cornerInside.2.2.2⟩,
    state_strict_initial_of_pos second.track indexPositive⟩

end Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement

end
