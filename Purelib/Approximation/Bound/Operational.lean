module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Compatibility
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

public section

/-!
# Operational equivalence of finite bound processes

An operational equivalence is a finite joint scheduler.  Every request
refines both sides and proves all currently admitted rational values mutually
indistinguishable at the requested tolerance.  Transitivity uses an explicit
rational overlap witness from the coherent middle process.
-/

namespace Purelib.Approximation

namespace BoundProcess

/-- All independently scheduled finite states of one process overlap. This is a finite coherence law, not the assertion
of a common point of every state. -/
@[expose] def Coherent (process : Approximation.BoundProcess) : Prop :=
  ∀ left right : process.State,
    (process.bound left).Overlaps (process.bound right)

/-- The exact rational process has overlapping bounds at every pair of states. -/
theorem exact_coherent (value : Fraction.Rational) :
    (BoundProcess.exact value).Coherent := by
  intro left right
  exact ⟨le_rfl, le_rfl⟩

/-- Every displayed finite state explicitly contains the same rational anchor. -/
@[expose] def AnchoredAt (process : Approximation.BoundProcess) (value : Fraction.Rational) : Prop :=
  ∀ state : process.State, (process.bound state).Contains value

/-- A common displayed rational anchor gives finite pairwise coherence. -/
theorem coherent_of_anchoredAt (process : Approximation.BoundProcess) (value : Fraction.Rational)
    (anchored : process.AnchoredAt value) : process.Coherent := by
  intro left right
  exact Interval.overlaps_of_common (anchored left) (anchored right)

/-- Adding rationally anchored processes adds their retained anchors. -/
theorem anchoredAt_add (left right : Approximation.BoundProcess)
    (leftValue rightValue : Fraction.Rational)
    (leftAnchored : left.AnchoredAt leftValue)
    (rightAnchored : right.AnchoredAt rightValue) :
    (left.add right).AnchoredAt (leftValue + rightValue) := by
  intro state
  exact Interval.add_contains (leftAnchored state.1) (rightAnchored state.2)

/-- Negating a rationally anchored process negates its anchor. -/
theorem anchoredAt_neg (process : Approximation.BoundProcess) (value : Fraction.Rational)
    (anchored : process.AnchoredAt value) :
    process.neg.AnchoredAt (-value) := by
  intro state
  exact Interval.neg_contains (anchored state)

/-- Subtracting rationally anchored processes subtracts their anchors. -/
theorem anchoredAt_sub (left right : Approximation.BoundProcess)
    (leftValue rightValue : Fraction.Rational)
    (leftAnchored : left.AnchoredAt leftValue)
    (rightAnchored : right.AnchoredAt rightValue) :
    (left.sub right).AnchoredAt (leftValue - rightValue) := by
  exact left.anchoredAt_add right.neg leftValue (-rightValue)
    leftAnchored (right.anchoredAt_neg rightValue rightAnchored)

/-- Positive scaling preserves the displayed rational anchor after scaling it. -/
theorem anchoredAt_scalePositive (process : Approximation.BoundProcess)
    (value factor : Fraction.Rational) (positive : 0 < factor)
    (anchored : process.AnchoredAt value) :
    (process.scalePositive factor positive).AnchoredAt (factor * value) := by
  intro state
  exact Interval.scale_contains positive.le (anchored state)

end BoundProcess

set_option genInjectivity false in
/-- Finite joint request program witnessing operational equality of two rational enclosure processes. -/
structure OperationalEquivalence (left right : Approximation.BoundProcess) where
  /-- The retained joint scheduler state type. -/ State : Type
  /-- Read the left process state from a joint scheduler state. -/ leftState : State → left.State
  /-- Read the right process state from a joint scheduler state. -/ rightState : State → right.State
  /-- The distinguished initial joint scheduler state. -/ initial : State
  /-- Compute a joint refinement for the supplied positive rational tolerance. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- The joint request refines its original left enclosure. -/ left_refines : ∀ state epsilon positive,
    Interval.Refines
      (left.bound (leftState (request state epsilon positive)))
      (left.bound (leftState state))
  /-- The joint request refines its original right enclosure. -/ right_refines : ∀ state epsilon positive,
    Interval.Refines
      (right.bound (rightState (request state epsilon positive)))
      (right.bound (rightState state))
  /-- After the request, all admitted left and right values differ by less than the requested tolerance in both
    directions. -/ close : ∀ state epsilon positive {leftValue rightValue : Fraction.Rational},
    (left.bound (leftState (request state epsilon positive))).Contains
      leftValue →
    (right.bound (rightState (request state epsilon positive))).Contains
      rightValue →
    leftValue - rightValue < epsilon ∧
      rightValue - leftValue < epsilon

constructive_injectivity OperationalEquivalence

namespace OperationalEquivalence

/-- Every finite bound process is operationally equivalent to itself. -/
@[expose] def refl (process : Approximation.BoundProcess) :
    Approximation.OperationalEquivalence process process where
  State := process.State
  leftState state := state
  rightState state := state
  initial := process.initial
  request state epsilon positive := process.request state epsilon positive
  left_refines := process.request_refines
  right_refines := process.request_refines
  close state epsilon positive :=
    process.request_pairwise_difference_lt state epsilon positive

/-- A rationally anchored shrinking process is operationally equivalent to the exact rational anchor. Every comparison
is made after one finite request. -/
@[expose] def ofAnchoredAt (process : Approximation.BoundProcess) (value : Fraction.Rational)
    (anchored : process.AnchoredAt value) :
    Approximation.OperationalEquivalence process (BoundProcess.exact value) where
  State := process.State
  leftState state := state
  rightState _ := ()
  initial := process.initial
  request state epsilon positive := process.request state epsilon positive
  left_refines := process.request_refines
  right_refines state epsilon positive := Refines.refl _
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have rightEqual := (Interval.exact_contains_iff value rightValue).mp rightInside
    subst rightValue
    exact process.request_pairwise_difference_lt state epsilon positive
      leftInside (anchored (process.request state epsilon positive))

/-- Reverse a finite operational equivalence. -/
@[expose] def symm {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationalEquivalence left right) :
    Approximation.OperationalEquivalence right left where
  State := equivalent.State
  leftState := equivalent.rightState
  rightState := equivalent.leftState
  initial := equivalent.initial
  request := equivalent.request
  left_refines := equivalent.right_refines
  right_refines := equivalent.left_refines
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have close := equivalent.close state epsilon positive
      rightInside leftInside
    exact ⟨close.2, close.1⟩

/-- Addition respects finite operational equivalence. Endpoint comparisons avoid selecting a decomposition of an
arbitrary value admitted by a sum enclosure. -/
@[expose] def add {leftFirst rightFirst leftSecond rightSecond : Approximation.BoundProcess}
    (first : Approximation.OperationalEquivalence leftFirst rightFirst)
    (second : Approximation.OperationalEquivalence leftSecond rightSecond) :
    Approximation.OperationalEquivalence (leftFirst.add leftSecond)
      (rightFirst.add rightSecond) where
  State := first.State × second.State
  leftState state :=
    ⟨first.leftState state.1, second.leftState state.2⟩
  rightState state :=
    ⟨first.rightState state.1, second.rightState state.2⟩
  initial := ⟨first.initial, second.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := Fraction.Order.Field.div_pos_direct positive
      (by decide : (0 : Fraction.Rational) < 2)
    ⟨first.request state.1 half halfPositive,
      second.request state.2 half halfPositive⟩
  left_refines state epsilon positive :=
    Refines.add
      (first.left_refines state.1 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
      (second.left_refines state.2 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
  right_refines state epsilon positive :=
    Refines.add
      (first.right_refines state.1 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
      (second.right_refines state.2 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    let half := epsilon / 2
    have halfPositive : (0 : Fraction.Rational) < half :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let firstRequested := first.request state.1 half halfPositive
    let secondRequested := second.request state.2 half halfPositive
    let leftFirstBound := leftFirst.bound (first.leftState firstRequested)
    let rightFirstBound := rightFirst.bound (first.rightState firstRequested)
    let leftSecondBound := leftSecond.bound (second.leftState secondRequested)
    let rightSecondBound := rightSecond.bound (second.rightState secondRequested)
    change (leftFirstBound.add leftSecondBound).Contains leftValue at leftInside
    change (rightFirstBound.add rightSecondBound).Contains rightValue
      at rightInside
    have firstForward := first.close state.1 half halfPositive
      (leftValue := leftFirstBound.upper)
      (rightValue := rightFirstBound.lower)
      ⟨leftFirstBound.valid, le_rfl⟩ ⟨le_rfl, rightFirstBound.valid⟩
    have secondForward := second.close state.2 half halfPositive
      (leftValue := leftSecondBound.upper)
      (rightValue := rightSecondBound.lower)
      ⟨leftSecondBound.valid, le_rfl⟩ ⟨le_rfl, rightSecondBound.valid⟩
    have firstReverse := first.close state.1 half halfPositive
      (leftValue := leftFirstBound.lower)
      (rightValue := rightFirstBound.upper)
      ⟨le_rfl, leftFirstBound.valid⟩ ⟨rightFirstBound.valid, le_rfl⟩
    have secondReverse := second.close state.2 half halfPositive
      (leftValue := leftSecondBound.lower)
      (rightValue := rightSecondBound.upper)
      ⟨le_rfl, leftSecondBound.valid⟩ ⟨rightSecondBound.valid, le_rfl⟩
    have forwardSum := Fraction.Order.Arithmetic.add_lt_add_direct
      firstForward.1 secondForward.1
    have reverseSum := Fraction.Order.Arithmetic.add_lt_add_direct
      firstReverse.2 secondReverse.2
    constructor
    · calc
        leftValue - rightValue ≤
            (leftFirstBound.upper + leftSecondBound.upper) -
              (rightFirstBound.lower + rightSecondBound.lower) :=
          Fraction.Order.Arithmetic.sub_le_sub_direct leftInside.2 rightInside.1
        _ = (leftFirstBound.upper - rightFirstBound.lower) +
              (leftSecondBound.upper - rightSecondBound.lower) := by ring1
        _ < half + half := forwardSum
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon 2
                (by decide)
    · calc
        rightValue - leftValue ≤
            (rightFirstBound.upper + rightSecondBound.upper) -
              (leftFirstBound.lower + leftSecondBound.lower) :=
          Fraction.Order.Arithmetic.sub_le_sub_direct rightInside.2 leftInside.1
        _ = (rightFirstBound.upper - leftFirstBound.lower) +
              (rightSecondBound.upper - leftSecondBound.lower) := by ring1
        _ < half + half := reverseSum
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon 2
                (by decide)

/-- Additive inverse respects finite operational equivalence. -/
@[expose] def neg {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationalEquivalence left right) :
    Approximation.OperationalEquivalence left.neg right.neg where
  State := equivalent.State
  leftState := equivalent.leftState
  rightState := equivalent.rightState
  initial := equivalent.initial
  request := equivalent.request
  left_refines state epsilon positive :=
    (equivalent.left_refines state epsilon positive).neg
  right_refines state epsilon positive :=
    (equivalent.right_refines state epsilon positive).neg
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have original := equivalent.close state epsilon positive
      (Interval.neg_contains_iff.mp leftInside)
      (Interval.neg_contains_iff.mp rightInside)
    constructor
    · calc
        leftValue - rightValue =
            -rightValue - -leftValue := by ring1
        _ < epsilon := original.2
    · calc
        rightValue - leftValue =
            -leftValue - -rightValue := by ring1
        _ < epsilon := original.1

/-- Difference respects finite operational equivalence. -/
@[expose] def sub {leftFirst rightFirst leftSecond rightSecond : Approximation.BoundProcess}
    (first : Approximation.OperationalEquivalence leftFirst rightFirst)
    (second : Approximation.OperationalEquivalence leftSecond rightSecond) :
    Approximation.OperationalEquivalence (leftFirst.sub leftSecond)
      (rightFirst.sub rightSecond) :=
  first.add second.neg

/-- Positive rational scaling respects finite operational equivalence. -/
@[expose] def scalePositive {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationalEquivalence left right)
    (factor : Fraction.Rational) (factorPositive : 0 < factor) :
    Approximation.OperationalEquivalence
      (left.scalePositive factor factorPositive)
      (right.scalePositive factor factorPositive) where
  State := equivalent.State
  leftState := equivalent.leftState
  rightState := equivalent.rightState
  initial := equivalent.initial
  request state epsilon positive :=
    equivalent.request state (epsilon / factor)
      (Fraction.Order.Field.div_pos_direct positive factorPositive)
  left_refines state epsilon positive :=
    Refines.scale factor factorPositive.le
      (equivalent.left_refines state (epsilon / factor)
        (Fraction.Order.Field.div_pos_direct positive factorPositive))
  right_refines state epsilon positive :=
    Refines.scale factor factorPositive.le
      (equivalent.right_refines state (epsilon / factor)
        (Fraction.Order.Field.div_pos_direct positive factorPositive))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have requestPositive : 0 < epsilon / factor :=
      Fraction.Order.Field.div_pos_direct positive factorPositive
    let requested := equivalent.request state (epsilon / factor) requestPositive
    let leftBound := left.bound (equivalent.leftState requested)
    let rightBound := right.bound (equivalent.rightState requested)
    change (leftBound.scale factor factorPositive.le).Contains leftValue
      at leftInside
    change (rightBound.scale factor factorPositive.le).Contains rightValue
      at rightInside
    have forward := equivalent.close state (epsilon / factor) requestPositive
      (leftValue := leftBound.upper) (rightValue := rightBound.lower)
      ⟨leftBound.valid, le_rfl⟩ ⟨le_rfl, rightBound.valid⟩
    have reverse := equivalent.close state (epsilon / factor) requestPositive
      (leftValue := leftBound.lower) (rightValue := rightBound.upper)
      ⟨le_rfl, leftBound.valid⟩ ⟨rightBound.valid, le_rfl⟩
    have forwardScaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        factorPositive forward.1
    have reverseScaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        factorPositive reverse.2
    constructor
    · calc
        leftValue - rightValue ≤
            factor * leftBound.upper - factor * rightBound.lower :=
          Fraction.Order.Arithmetic.sub_le_sub_direct leftInside.2 rightInside.1
        _ = factor * (leftBound.upper - rightBound.lower) := by ring1
        _ < factor * (epsilon / factor) := forwardScaled
        _ = epsilon := by
          calc
            factor * (epsilon / factor) = (epsilon / factor) * factor := by
              ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon factor
                factorPositive.ne'
    · calc
        rightValue - leftValue ≤
            factor * rightBound.upper - factor * leftBound.lower :=
          Fraction.Order.Arithmetic.sub_le_sub_direct rightInside.2 leftInside.1
        _ = factor * (rightBound.upper - leftBound.lower) := by ring1
        _ < factor * (epsilon / factor) := reverseScaled
        _ = epsilon := by
          calc
            factor * (epsilon / factor) = (epsilon / factor) * factor := by
              ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon factor
                factorPositive.ne'

/-- Compose two finite joint schedulers. Coherence of the middle process constructs one rational overlap witness shared
by the two finite requests. -/
@[expose] def trans {first middle third : Approximation.BoundProcess}
    (firstMiddle : Approximation.OperationalEquivalence first middle)
    (middleThird : Approximation.OperationalEquivalence middle third)
    (middleCoherent : middle.Coherent) :
    Approximation.OperationalEquivalence first third where
  State := firstMiddle.State × middleThird.State
  leftState state := firstMiddle.leftState state.1
  rightState state := middleThird.rightState state.2
  initial := ⟨firstMiddle.initial, middleThird.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := Fraction.Order.Field.div_pos_direct positive
      (by decide : (0 : Fraction.Rational) < 2)
    ⟨firstMiddle.request state.1 half halfPositive,
      middleThird.request state.2 half halfPositive⟩
  left_refines state epsilon positive :=
    firstMiddle.left_refines state.1 (epsilon / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  right_refines state epsilon positive :=
    middleThird.right_refines state.2 (epsilon / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    let half := epsilon / 2
    have halfPositive : (0 : Fraction.Rational) < half :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let firstRequested := firstMiddle.request state.1 half halfPositive
    let thirdRequested := middleThird.request state.2 half halfPositive
    let middleLeft := middle.bound (firstMiddle.rightState firstRequested)
    let middleRight := middle.bound (middleThird.leftState thirdRequested)
    have middleOverlap : middleLeft.Overlaps middleRight :=
      middleCoherent _ _
    let witness := Interval.overlapWitness middleLeft middleRight
    have witnessInside := Interval.overlapWitness_inside middleOverlap
    have firstClose := firstMiddle.close state.1 half halfPositive
      leftInside witnessInside.1
    have thirdClose := middleThird.close state.2 half halfPositive
      witnessInside.2 rightInside
    have forward := Fraction.Order.Arithmetic.add_lt_add_direct
      firstClose.1 thirdClose.1
    have reverse := Fraction.Order.Arithmetic.add_lt_add_direct
      thirdClose.2 firstClose.2
    constructor
    · calc
        leftValue - rightValue =
            (leftValue - witness) + (witness - rightValue) := by ring1
        _ < half + half := forward
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon 2
                (by decide)
    · calc
        rightValue - leftValue =
            (rightValue - witness) + (witness - leftValue) := by ring1
        _ < half + half := reverse
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              Fraction.Field.div_mul_cancel_of_ne epsilon 2
                (by decide)

end OperationalEquivalence

/-- Propositional wrapper around an explicit finite joint scheduler. -/
@[expose] def OperationallyEquivalent (left right : Approximation.BoundProcess) : Prop :=
  Nonempty (Approximation.OperationalEquivalence left right)

/-- Every rational-bound process is operationally equivalent to itself. -/
theorem operationallyEquivalent_refl (process : Approximation.BoundProcess) :
    Approximation.OperationallyEquivalent process process :=
  ⟨OperationalEquivalence.refl process⟩

/-- A process with a retained rational anchor is operationally equivalent to that exact rational process. -/
theorem operationallyEquivalent_exact_of_anchoredAt
    (process : Approximation.BoundProcess) (value : Fraction.Rational)
    (anchored : process.AnchoredAt value) :
    Approximation.OperationallyEquivalent process (BoundProcess.exact value) :=
  ⟨OperationalEquivalence.ofAnchoredAt process value anchored⟩

/-- Reverse the existence of a finite operational comparison scheduler. -/
theorem operationallyEquivalent_symm {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationallyEquivalent left right) :
    Approximation.OperationallyEquivalent right left := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.symm⟩

/-- Adding two pairs of operationally equivalent processes preserves operational equivalence. -/
theorem operationallyEquivalent_add
    {leftFirst rightFirst leftSecond rightSecond : Approximation.BoundProcess}
    (first : Approximation.OperationallyEquivalent leftFirst rightFirst)
    (second : Approximation.OperationallyEquivalent leftSecond rightSecond) :
    Approximation.OperationallyEquivalent (leftFirst.add leftSecond)
      (rightFirst.add rightSecond) := by
  rcases first with ⟨firstWitness⟩
  rcases second with ⟨secondWitness⟩
  exact ⟨firstWitness.add secondWitness⟩

/-- Negation preserves operational equivalence. -/
theorem operationallyEquivalent_neg {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationallyEquivalent left right) :
    Approximation.OperationallyEquivalent left.neg right.neg := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.neg⟩

/-- Subtraction preserves operational equivalence of both operands. -/
theorem operationallyEquivalent_sub
    {leftFirst rightFirst leftSecond rightSecond : Approximation.BoundProcess}
    (first : Approximation.OperationallyEquivalent leftFirst rightFirst)
    (second : Approximation.OperationallyEquivalent leftSecond rightSecond) :
    Approximation.OperationallyEquivalent (leftFirst.sub leftSecond)
      (rightFirst.sub rightSecond) := by
  rcases first with ⟨firstWitness⟩
  rcases second with ⟨secondWitness⟩
  exact ⟨firstWitness.sub secondWitness⟩

/-- Positive rational scaling preserves operational equivalence. -/
theorem operationallyEquivalent_scalePositive {left right : Approximation.BoundProcess}
    (equivalent : Approximation.OperationallyEquivalent left right)
    (factor : Fraction.Rational) (positive : 0 < factor) :
    Approximation.OperationallyEquivalent
      (left.scalePositive factor positive)
      (right.scalePositive factor positive) := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.scalePositive factor positive⟩

/-- Compose operational equivalences when the shared middle process has finite pairwise coherence. -/
theorem operationallyEquivalent_trans
    {first middle third : Approximation.BoundProcess}
    (firstMiddle : Approximation.OperationallyEquivalent first middle)
    (middleThird : Approximation.OperationallyEquivalent middle third)
    (middleCoherent : middle.Coherent) :
    Approximation.OperationallyEquivalent first third := by
  rcases firstMiddle with ⟨firstWitness⟩
  rcases middleThird with ⟨thirdWitness⟩
  exact ⟨firstWitness.trans thirdWitness middleCoherent⟩

end Purelib.Approximation

end
