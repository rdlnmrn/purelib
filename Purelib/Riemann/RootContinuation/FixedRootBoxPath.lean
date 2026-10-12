module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement

public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

public section

/-!
Finite comparison subdivisions propagate the same operational root through
two fixed winding-one boxes along a supplied rational parameter path. The
comparison mesh is evaluated only for a requested root comparison; its depth
does not impose a depth on the integration mesh.
-/

namespace Purelib.Riemann.RootContinuation.FixedRootBoxPath

open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.FixedRootBoxBudget
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

/-- A retained rational path parameter lies in the closed unit interval. -/
abbrev Inside (t : Coordinate) := 0 ≤ t ∧ t ≤ 1

set_option genInjectivity false in
/-- A nonvanishing rational-parameter path with separate movement budgets for two original fixed root boxes.

The record retains both original owners and budgets, bounds each source-to-path movement, and supplies a nonnegative
squared Lipschitz scale for comparing arbitrary retained parameters. -/
structure PathData {firstSource secondSource : Gaussian}
    {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
    (first : Budget firstOwner) (second : Budget secondOwner) where
  /-- The original Gaussian parameter path on rational parameters. -/ point : Coordinate → Gaussian
  /-- Every retained unit-interval path point is nonzero. -/ nonzero : ∀ t, Inside t → point t ≠ 0
  /-- Each path point satisfies the movement budget from the exact first source parameter. -/ firstMovement : ∀ t,
    Inside t → normSq (firstSource - point t) ≤ first.movement
  /-- Each path point satisfies the movement budget from the exact second source parameter. -/ secondMovement : ∀ t,
    Inside t → normSq (secondSource - point t) ≤ second.movement
  /-- The retained squared Lipschitz scale for parameter variation along the original path. -/ scale : Coordinate
  /-- The retained path variation scale is nonnegative. -/ scale_nonnegative : 0 ≤ scale
  /-- Squared movement between retained path points is bounded by the scale times their squared parameter difference. -/
    variation : ∀ left right, Inside left → Inside right →
    normSq (point left - point right) ≤ scale * (right - left) ^ 2

constructive_injectivity PathData

namespace PathData
variable {firstSource secondSource : Gaussian}
    {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
    {first : Budget firstOwner} {second : Budget secondOwner}
    (path : PathData first second)

/-- The first original budget's root owner at the exact retained path parameter. -/
@[irreducible, expose] def First (t : Coordinate) (inside : Inside t) : Owner (path.point t) :=
  first.ownerAt (path.nonzero t inside) (path.firstMovement t inside)

/-- The second original budget's root owner at the exact retained path parameter. -/
@[irreducible, expose] def Second (t : Coordinate) (inside : Inside t) : Owner (path.point t) :=
  second.ownerAt (path.nonzero t inside) (path.secondMovement t inside)

/-- Operational equivalence of the two original fixed-box root names at the retained path parameter. -/
@[irreducible, expose] def Agreement (t : Coordinate) (inside : Inside t) : Type :=
  NamedEquivalent (ownerRootName (path.nonzero t inside) (path.First t inside))
    (ownerRootName (path.nonzero t inside) (path.Second t inside))

open Purelib.Algebra in
/-- The midpoint of two retained unit-interval parameters remains in the unit interval.

Both supplied nonnegative endpoints give a nonnegative average. Their separate
upper bounds give a sum at most two, and multiplication by the positive half
retains the unit upper bound. -/
theorem midpoint_inside {left right : Coordinate}
    (leftInside : Inside left) (rightInside : Inside right) : Inside ((left + right) / 2) := by
  refine ⟨Fraction.Order.Field.div_nonneg_direct ((show 0 ≤ left + right from by
      simpa only [Fraction.Field.zero_add]
        using Fraction.Order.Arithmetic.add_le_add_direct leftInside.1 rightInside.1)) (by decide), ?_⟩
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.add_le_add_direct leftInside.2 rightInside.2) (by decide : (0 : Coordinate) ≤ 1 / 2)
  calc
    _ = (left + right) * (1 / 2) := by
      rewrite [Field.ExplicitField.div_eq_mul_inv, Field.ExplicitField.div_eq_mul_inv,
        Fraction.Field.one_mul]
      exact Eq.refl _
    _ ≤ (1 + 1) * (1 / 2) := bound
    _ = 1 := by decide

/-- The first path owner keeps the exact original first source-owner box. -/
theorem first_box (t : Coordinate) (inside : Inside t) :
    (path.First t inside).track.initial.box = firstOwner.track.initial.box := by unfold First; rfl

/-- The second path owner keeps the exact original second source-owner box. -/
theorem second_box (t : Coordinate) (inside : Inside t) :
    (path.Second t inside).track.initial.box = secondOwner.track.initial.box := by unfold Second; rfl

/-- The first path owner keeps the original first budget's cached clearance. -/
theorem first_clearance (t : Coordinate) (inside : Inside t) :
    (path.First t inside).track.initial.clearance.bound = first.clearance := by unfold First; rfl

/-- The second path owner keeps the original second budget's cached clearance. -/
theorem second_clearance (t : Coordinate) (inside : Inside t) :
    (path.Second t inside).track.initial.clearance.bound = second.clearance := by unfold Second; rfl

open Purelib.Geometry.Rational in
/-- Transport retained root-name agreement across a path step whose squared variation is below both original budget
clearances.

The fixed-box identities provide the two separate target refinement witnesses, preserving the original first and second
owners throughout the comparison. -/
@[expose] def oneStep (left right : Coordinate) (leftInside : Inside left) (rightInside : Inside right)
    (small : path.scale * (right - left) ^ 2 < min first.clearance second.clearance)
    (equivalent : path.Agreement left leftInside) : path.Agreement right rightInside := by
  unfold Agreement at *
  exact RootContinuationCongruence.retainedOwnersEquivalent (path.nonzero right rightInside)
    (path.First left leftInside) (path.Second left leftInside) equivalent
    (by
      rw [path.first_clearance]
      exact (path.variation left right leftInside rightInside).trans_lt (small.trans_le
        (Fraction.Order.Basic.min_le_left _ _)))
    (by
      rw [path.second_clearance]
      exact (path.variation left right leftInside rightInside).trans_lt (small.trans_le
        (Fraction.Order.Basic.min_le_right _ _)))
    (path.First right rightInside) (path.Second right rightInside)
    (by rw [path.first_box, path.first_box]; exact Box.refines_refl _)
    (by rw [path.second_box, path.second_box]; exact Box.refines_refl _)

/-- The displacement from the left parameter to the midpoint is half the original directed parameter difference. -/
theorem midpoint_sub_left (left right : Coordinate) :
    (left + right) / 2 - left = (right - left) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Coordinate) ≠ 0 by decide)
  calc
    ((left + right) / 2 - left) * 2 = (left + right) / 2 * 2 - left * 2 := by ring1
    _ = (left + right) - left * 2 := by rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 := (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

/-- The displacement from the midpoint to the right parameter is half the original directed parameter difference. -/
theorem right_sub_midpoint (left right : Coordinate) :
    right - (left + right) / 2 = (right - left) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (right - (left + right) / 2) * 2 = right * 2 - (left + right) / 2 * 2 := by ring1
    _ = right * 2 - (left + right) := by rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 := (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

open Purelib.Algebra in
/-- Squaring half a rational value multiplies its original square by one quarter.

The two identical retained denominators multiply to four. Exact scalar division
and multiplication readbacks identify the original two expressions without
changing the supplied rational value. -/
theorem half_square (value : Coordinate) : (value / 2) ^ 2 = value ^ 2 * (1 / 4) := by
  rw [pow_two, Fraction.Field.div_mul_div_direct, show (2 : Coordinate) * 2 = 4 by decide]
  rewrite [pow_two, Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv, Fraction.Field.one_mul]
  exact Eq.refl _

/-- Read the original operational root-name equivalence carried by the retained path agreement. -/
@[expose] def expose {t : Coordinate} {inside : Inside t} (agreement : path.Agreement t inside) :
    NamedEquivalent (ownerRootName (path.nonzero t inside) (path.First t inside))
      (ownerRootName (path.nonzero t inside) (path.Second t inside)) := by
  unfold Agreement at agreement
  exact agreement

section
open Purelib.Approximation.Rational
/-- Propagate retained path agreement through a finite dyadic subdivision at the supplied depth.

The original quarter-radius smallness bound pays each step against both fixed-box clearances. Recursive halves retain
the exact midpoint parameters and pass the first comparison into the second. -/
@[expose] def walk : (depth : Nat) → (left right : Coordinate) →
    (leftInside : Inside left) → (rightInside : Inside right) →
    Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) depth < min first.clearance second.clearance →
    path.Agreement left leftInside → path.Agreement right rightInside
  | 0, left, right, leftInside, rightInside, small, equivalent =>
      path.oneStep left right leftInside rightInside (by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct] using small)
          equivalent
  | depth + 1, left, right, leftInside, rightInside, small, equivalent =>
      let middle := (left + right) / 2
      have middleInside : Inside middle := midpoint_inside leftInside rightInside
      have firstSmall : Geometric.Basic.quarterRadius (path.scale * (middle - left) ^ 2) depth <
          min first.clearance second.clearance := by
        have equal : Geometric.Basic.quarterRadius (path.scale * (middle - left) ^ 2) depth =
            Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) (depth + 1) := by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ (1 / 4 :
            Coordinate) depth]
          dsimp only [middle]
          rw [midpoint_sub_left, half_square]
          ring1
        exact equal.symm ▸ small
      have secondSmall : Geometric.Basic.quarterRadius (path.scale * (right - middle) ^ 2) depth <
          min first.clearance second.clearance := by
        have equal : Geometric.Basic.quarterRadius (path.scale * (right - middle) ^ 2) depth =
            Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) (depth + 1) := by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ (1 / 4 :
            Coordinate) depth]
          dsimp only [middle]
          rw [right_sub_midpoint, half_square]
          ring1
        exact equal.symm ▸ small
      walk depth middle right middleInside rightInside secondSmall
        (walk depth left middle leftInside middleInside firstSmall equivalent)

/-- Propagate the original starting agreement to the final path parameter using a finite geometric depth search.

The path's nonnegative variation scale and both positive retained clearances determine a dyadic walk whose step bounds
certify the final operational comparison. -/
@[expose] def equivalent (start : path.Agreement 0 (by decide)) : path.Agreement 1 (by decide) := by
  unfold Agreement
  refine ⟨fun leftStart rightStart target positive => ?_⟩
  let depth := Geometric.Search.firstQuarterBelow path.scale 0 (min first.clearance second.clearance)
  have unitDifference : (1 - 0 : Coordinate) = 1 := by ring1
  have small : Geometric.Basic.quarterRadius (path.scale * (1 - 0) ^ 2) depth < min first.clearance second.clearance :=
    by
      simpa only [unitDifference, one_pow, Fraction.Field.mul_one_direct] using
        Geometric.Search.firstQuarterBelow_accurate path.scale path.scale_nonnegative 0
          (min first.clearance second.clearance) (Fraction.Order.Basic.lt_min first.clearance_positive
            second.clearance_positive)
  have walked := path.walk depth 0 1 (by decide) (by decide) small start
  exact (path.expose walked).compare leftStart rightStart target positive

end

/-- Compare the first fixed-budget path root name with a supplied same-parameter owner refining the original first box.
-/
@[expose] def firstRetained (t : Coordinate) (inside : Inside t) (reading : Owner (path.point t))
    (refines : reading.track.initial.box.Refines firstOwner.track.initial.box) :
    NamedEquivalent (ownerRootName (path.nonzero t inside) (path.First t inside))
      (ownerRootName reading.parameterNonzero reading) := by
  unfold First
  exact first.retainedEquivalent (path.nonzero t inside) (path.firstMovement t inside) reading refines

/-- Compare the second fixed-budget path root name with a supplied same-parameter owner refining the original second
box. -/
@[expose] def secondRetained (t : Coordinate) (inside : Inside t) (reading : Owner (path.point t))
    (refines : reading.track.initial.box.Refines secondOwner.track.initial.box) :
    NamedEquivalent (ownerRootName (path.nonzero t inside) (path.Second t inside))
      (ownerRootName reading.parameterNonzero reading) := by
  unfold Second
  exact second.retainedEquivalent (path.nonzero t inside) (path.secondMovement t inside) reading refines

/-- Transport equivalence of two retained starting owners to two retained finishing owners along the original path.

The four separate refinements to the two original fixed boxes remain explicit. Starting and finishing name comparisons
compose with the exact finite path agreement, preserving every retained input owner. -/
@[expose] def retainedEquivalent (firstStart secondStart : Owner (path.point 0))
    (firstStartRefines : firstStart.track.initial.box.Refines firstOwner.track.initial.box)
    (secondStartRefines : secondStart.track.initial.box.Refines secondOwner.track.initial.box)
    (start : NamedEquivalent (ownerRootName firstStart.parameterNonzero firstStart)
      (ownerRootName secondStart.parameterNonzero secondStart))
    (firstFinish secondFinish : Owner (path.point 1))
    (firstFinishRefines : firstFinish.track.initial.box.Refines firstOwner.track.initial.box)
    (secondFinishRefines : secondFinish.track.initial.box.Refines secondOwner.track.initial.box) :
    NamedEquivalent (ownerRootName firstFinish.parameterNonzero firstFinish)
      (ownerRootName secondFinish.parameterNonzero secondFinish) where
  compare := fun leftStart rightStart target positive =>
    let initial : path.Agreement 0 (by decide) := by
      unfold Agreement
      exact (path.firstRetained 0 (by decide) firstStart firstStartRefines).trans
        (start.trans (path.secondRetained 0 (by decide) secondStart secondStartRefines).symm)
    let result := (path.firstRetained 1 (by decide) firstFinish firstFinishRefines).symm.trans
      ((path.expose (path.equivalent initial)).trans
        (path.secondRetained 1 (by decide) secondFinish secondFinishRefines))
    result.compare leftStart rightStart target positive

end PathData
end Purelib.Riemann.RootContinuation.FixedRootBoxPath

end
