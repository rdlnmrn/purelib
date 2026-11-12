module

public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual finite owner moves on fixed-box parameter paths

Each dyadic leaf advances its retained source owner and keeps both the actual
advanced owner and the cached fixed-box endpoint owner. Their operational
handoff is derived internally. Recursive halves share the identical cached
middle owner, while each leaf bounds the whole original parameter subinterval.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation

open Purelib.Data.Gaussian

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Approximation.Rational
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.RootContinuation.FixedRootBoxBudget

attribute [local irreducible] ownerRootName

variable {firstSource secondSource : Gaussian} {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
variable {first : Budget firstOwner} {second : Budget secondOwner} (path : PathData first second)

/-- Advance the retained original owner to the same path's certified endpoint using its own movement payment. -/
@[irreducible] def move {left : Coordinate} (right : Coordinate) (rightInside : Inside right)
    (source : Owner (path.point left))
    (small : Norm.Basic.normSq (path.point left - path.point right) <
      source.track.initial.clearance.bound) : Owner (path.point right) :=
  source.advance (path.nonzero right rightInside) small

/-- The path move is the original owner's actual accepted advancement with the same endpoint and payment. -/
theorem move_eq_advance {left : Coordinate} (right : Coordinate) (rightInside : Inside right)
    (source : Owner (path.point left))
    (small : Norm.Basic.normSq (path.point left - path.point right) <
      source.track.initial.clearance.bound) :
    move path right rightInside source small = source.advance (path.nonzero right rightInside) small := by
  unfold move
  rfl

/-- The retained path scale bounds movement throughout an ordered original subinterval. -/
private theorem interval_movement {left right time : Coordinate}
    (leftInside : Inside left) (rightInside : Inside right) (between : left ≤ time ∧ time ≤ right) :
    Norm.Basic.normSq (path.point left - path.point time) ≤ path.scale * (right - left) ^ 2 := by
  rewrite [Norm.Basic.normSq_eq_canonical]
  have timeInside : Inside time := ⟨leftInside.1.trans between.1, between.2.trans rightInside.2⟩
  have difference := Arithmetic.sub_le_sub_right_direct between.2 left
  exact (path.variation left time leftInside timeInside).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct between.1) difference 2)
      path.scale_nonnegative)

set_option genInjectivity false in
/-- One actual owner advance with its original source, cached endpoint and whole-subinterval movement certificate. -/
structure Step (left right : Coordinate) (leftInside : Inside left) (rightInside : Inside right)
    (source : Owner (path.point left)) (target : Owner (path.point right)) where
  /-- The source cache is the original fixed-budget construction at the same parameter. -/
  source_eq : source = path.First left leftInside
  /-- The target cache is the original fixed-budget construction at the same endpoint. -/
  target_eq : target = path.First right rightInside
  /-- The retained original subinterval is ordered. -/ ordered : left ≤ right
  /-- The path's whole-subinterval scale is paid against this exact source owner. -/
  small : path.scale * (right - left) ^ 2 < source.track.initial.clearance.bound
  /-- The retained payment for the exact original endpoint displacement. -/
  pointSmall : Norm.Basic.normSq (path.point left - path.point right) <
    source.track.initial.clearance.bound
  /-- The actual advanced owner retained before its endpoint handoff. -/ advanced : Owner (path.point right)
  /-- The advanced cache is the original source owner's actual accepted move. -/
  advanced_eq : advanced = move path right rightInside source pointSmall
  /-- The actual moving owner agrees with the separate original cached endpoint owner. -/
  handoff : NamedEquivalent (ownerRootName advanced.parameterNonzero advanced)
    (ownerRootName target.parameterNonzero target)
  /-- Every intermediate original path point satisfies this same source-owned movement payment. -/
  movement : ∀ time, left ≤ time ∧ time ≤ right →
    Norm.Basic.normSq (path.point left - path.point time) ≤ path.scale * (right - left) ^ 2

constructive_injectivity Step

namespace Step

/-- Advance the retained original source and derive its handoff to the supplied exact endpoint cache. -/
def build (left right : Coordinate) (leftInside : Inside left) (rightInside : Inside right)
    (source : Owner (path.point left)) (target : Owner (path.point right))
    (source_eq : source = path.First left leftInside) (target_eq : target = path.First right rightInside)
    (ordered : left ≤ right) (small : path.scale * (right - left) ^ 2 < first.clearance) :
    Step path left right leftInside rightInside source target := by
  have sourceSmall : path.scale * (right - left) ^ 2 < source.track.initial.clearance.bound := by
    rewrite [source_eq, path.first_clearance]
    exact small
  have moveSmall : Norm.Basic.normSq (path.point left - path.point right) <
      source.track.initial.clearance.bound := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact (path.variation left right leftInside rightInside).trans_lt sourceSmall
  let advanced := move path right rightInside source moveSmall
  have refines : advanced.track.initial.box.Refines firstOwner.track.initial.box := by
    have nested := source.advance_initial_box_refines (path.nonzero right rightInside) moveSmall
    have sourceBox : source.track.initial.box = firstOwner.track.initial.box := by
      rewrite [source_eq, path.first_box]
      rfl
    have moved : advanced = source.advance (path.nonzero right rightInside) moveSmall :=
      move_eq_advance path right rightInside source moveSmall
    rewrite [moved]
    exact Eq.mp (congrArg (fun targetBox =>
      (source.advance (path.nonzero right rightInside) moveSmall).track.initial.box.Refines targetBox) sourceBox) nested
  have handoff : NamedEquivalent (ownerRootName advanced.parameterNonzero advanced)
      (ownerRootName target.parameterNonzero target) := by
    rewrite [target_eq]
    exact (path.firstRetained right rightInside advanced refines).symm
  exact
    { source_eq := source_eq
      target_eq := target_eq
      ordered := ordered
      small := sourceSmall
      pointSmall := moveSmall
      advanced := advanced
      advanced_eq := rfl
      handoff := handoff
      movement := fun _ between => interval_movement path leftInside rightInside between }

end Step

set_option genInjectivity false in
/-- A finite dyadic preparation whose two halves share their exact retained middle owner. -/
inductive Prepared : (left right : Coordinate) → (leftInside : Inside left) → (rightInside : Inside right) →
    Owner (path.point left) → Owner (path.point right) → Type
  /-- An actual leaf keeps the source move and its cached endpoint handoff. -/
  | step {left right leftInside rightInside source target}
      (move : Step path left right leftInside rightInside source target) :
      Prepared left right leftInside rightInside source target
  /-- Adjacent halves retain the identical original middle owner as their dependent index. -/
  | join {left middle right leftInside middleInside rightInside source center target}
      (middle_eq : middle = (left + right) / 2)
      (firstHalf : Prepared left middle leftInside middleInside source center)
      (secondHalf : Prepared middle right middleInside rightInside center target) :
      Prepared left right leftInside rightInside source target

constructive_injectivity Prepared

namespace Prepared

/-- Read the actual final advanced owner before its retained fixed-box handoff. -/
@[expose] def finishOwner : ∀ {left right leftInside rightInside source target},
    Prepared path left right leftInside rightInside source target → Owner (path.point right)
  | _, _, _, _, _, _, .step move => move.advanced
  | _, _, _, _, _, _, .join _ _ secondHalf => secondHalf.finishOwner

/-- The actual final advanced owner agrees with the exact cached endpoint retained by the same preparation. -/
def finish_agrees : ∀ {left right leftInside rightInside source target}
    (prepared : Prepared path left right leftInside rightInside source target),
    NamedEquivalent (ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner)
      (ownerRootName target.parameterNonzero target)
  | _, _, _, _, _, _, .step move => move.handoff
  | _, _, _, _, _, _, .join _ _ secondHalf => secondHalf.finish_agrees

/-- Prepare every original subinterval at a sufficient finite dyadic depth, computing each middle owner once. -/
def atDepth : (depth : Nat) → (left right : Coordinate) → (leftInside : Inside left) → (rightInside : Inside right) →
    (source : Owner (path.point left)) → (target : Owner (path.point right)) →
    source = path.First left leftInside → target = path.First right rightInside → left ≤ right →
    Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) depth < first.clearance →
    Prepared path left right leftInside rightInside source target
  | 0, left, right, leftInside, rightInside, source, target, source_eq, target_eq, ordered, small =>
      .step (Step.build path left right leftInside rightInside source target source_eq target_eq ordered (by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct] at small
        exact small))
  | depth + 1, left, right, leftInside, rightInside, source, target, source_eq, target_eq, ordered, small => by
      let middle := (left + right) / 2
      have middleInside : Inside middle := PathData.midpoint_inside leftInside rightInside
      let center := path.First middle middleInside
      have leftOrdered : left ≤ middle := by
        have translated := Arithmetic.add_le_add_right_direct ordered left
        apply (Fraction.Order.Field.le_div_iff_pos (by decide +kernel : (0 : Coordinate) < 2)).mpr
        calc
          left * 2 = left + left := by ring1
          _ ≤ right + left := translated
          _ = left + right := Fraction.Field.add_comm _ _
      have rightOrdered : middle ≤ right := by
        apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Coordinate) < 2)).mpr
        calc
          left + right ≤ right + right := Arithmetic.add_le_add_right_direct ordered right
          _ = right * 2 := by ring1
      have firstSmall : Geometric.Basic.quarterRadius (path.scale * (middle - left) ^ 2) depth < first.clearance := by
        have equal : Geometric.Basic.quarterRadius (path.scale * (middle - left) ^ 2) depth =
            Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) (depth + 1) := by
          unfold middle
          rewrite [PathData.midpoint_sub_left, PathData.half_square,
            Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
          ring1
        exact Eq.mp (congrArg (fun value => value < first.clearance) equal.symm) small
      have secondSmall : Geometric.Basic.quarterRadius (path.scale * (right - middle) ^ 2) depth < first.clearance := by
        have equal : Geometric.Basic.quarterRadius (path.scale * (right - middle) ^ 2) depth =
            Geometric.Basic.quarterRadius (path.scale * (right - left) ^ 2) (depth + 1) := by
          unfold middle
          rewrite [PathData.right_sub_midpoint, PathData.half_square,
            Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
          ring1
        exact Eq.mp (congrArg (fun value => value < first.clearance) equal.symm) small
      exact .join rfl
        (atDepth depth left middle leftInside middleInside source center source_eq rfl leftOrdered firstSmall)
        (atDepth depth middle right middleInside rightInside center target rfl target_eq rightOrdered secondSmall)

end Prepared

set_option genInjectivity false in
/-- A complete actual finite preparation with its computed depth and both original cached endpoint owners. -/
structure Result where
  /-- The computed sufficient dyadic preparation depth. -/ depth : Nat
  /-- The depth is the original finite quarter-radius search against the retained first clearance. -/
  depth_eq : depth = Geometric.Search.firstQuarterBelow path.scale 0 first.clearance
  /-- The actual cached starting fixed-box owner. -/ source : Owner (path.point 0)
  /-- The source is the original fixed-budget point construction. -/
  source_eq : source = path.First 0 (by decide +kernel)
  /-- The actual cached endpoint fixed-box owner. -/ target : Owner (path.point 1)
  /-- The endpoint cache is the original fixed-budget point construction. -/
  target_eq : target = path.First 1 (by decide +kernel)
  /-- The finite actual moves and original shared-owner handoffs. -/
  prepared : Prepared path 0 1 (by decide +kernel) (by decide +kernel) source target

constructive_injectivity Result

namespace Result

/-- Compute sufficient finite depth and construct actual moves retaining the same cached endpoint owners. -/
def build : Result path := by
  let depth := Geometric.Search.firstQuarterBelow path.scale 0 first.clearance
  let source := path.First 0 (by decide +kernel)
  let target := path.First 1 (by decide +kernel)
  have small : Geometric.Basic.quarterRadius (path.scale * (1 - 0) ^ 2) depth < first.clearance := by
    rewrite [show (1 - 0 : Coordinate) = 1 by ring1, one_pow, Fraction.Field.mul_one_direct]
    exact Geometric.Search.firstQuarterBelow_accurate path.scale path.scale_nonnegative 0 first.clearance
      first.clearance_positive
  exact
    { depth := depth
      depth_eq := rfl
      source := source
      source_eq := rfl
      target := target
      target_eq := rfl
      prepared := Prepared.atDepth path depth 0 1 (by decide +kernel) (by decide +kernel) source target rfl rfl
        (by decide +kernel) small }

/-- The actual final advanced owner retained by the complete preparation. -/
@[expose] def finishOwner (result : Result path) : Owner (path.point 1) := result.prepared.finishOwner

/-- The complete preparation derives operational agreement of its actual advanced finish with its cached target. -/
def finish_agrees (result : Result path) :
    NamedEquivalent (ownerRootName result.finishOwner.parameterNonzero result.finishOwner)
      (ownerRootName result.target.parameterNonzero result.target) :=
  result.prepared.finish_agrees

end Result

end Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
