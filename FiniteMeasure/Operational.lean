import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Protocol

/-!
# Operational equivalence of finite bound processes

An operational equivalence is a finite joint scheduler.  Every request
refines both sides and proves all currently admitted rational values mutually
indistinguishable at the requested tolerance.  Transitivity uses an explicit
rational overlap witness from the coherent middle process.
-/

namespace FiniteMeasure

namespace BoundProcess

/-- All independently scheduled finite states of one process overlap.  This
is a finite coherence law, not the assertion of a common point of every
state. -/
def Coherent (process : BoundProcess) : Prop :=
  ∀ left right : process.State,
    (process.bound left).Overlaps (process.bound right)

theorem exact_coherent (value : Coordinate) :
    (BoundProcess.exact value).Coherent := by
  intro left right
  exact ⟨le_rfl, le_rfl⟩

/-- Every displayed finite state explicitly contains the same rational
anchor. -/
def AnchoredAt (process : BoundProcess) (value : Coordinate) : Prop :=
  ∀ state : process.State, (process.bound state).Contains value

/-- A common displayed rational anchor gives finite pairwise coherence. -/
theorem coherent_of_anchoredAt (process : BoundProcess) (value : Coordinate)
    (anchored : process.AnchoredAt value) : process.Coherent := by
  intro left right
  exact Bound.overlaps_of_common (anchored left) (anchored right)

theorem anchoredAt_add (left right : BoundProcess)
    (leftValue rightValue : Coordinate)
    (leftAnchored : left.AnchoredAt leftValue)
    (rightAnchored : right.AnchoredAt rightValue) :
    (left.add right).AnchoredAt (leftValue + rightValue) := by
  intro state
  exact Bound.add_contains (leftAnchored state.1) (rightAnchored state.2)

theorem anchoredAt_neg (process : BoundProcess) (value : Coordinate)
    (anchored : process.AnchoredAt value) :
    process.neg.AnchoredAt (-value) := by
  intro state
  exact Bound.neg_contains (anchored state)

theorem anchoredAt_sub (left right : BoundProcess)
    (leftValue rightValue : Coordinate)
    (leftAnchored : left.AnchoredAt leftValue)
    (rightAnchored : right.AnchoredAt rightValue) :
    (left.sub right).AnchoredAt (leftValue - rightValue) := by
  exact left.anchoredAt_add right.neg leftValue (-rightValue)
    leftAnchored (right.anchoredAt_neg rightValue rightAnchored)

theorem anchoredAt_scalePositive (process : BoundProcess)
    (value factor : Coordinate) (positive : 0 < factor)
    (anchored : process.AnchoredAt value) :
    (process.scalePositive factor positive).AnchoredAt (factor * value) := by
  intro state
  exact Bound.scale_contains positive.le (anchored state)

end BoundProcess

/-- Finite joint request program witnessing operational equality of two
rational enclosure processes. -/
structure OperationalEquivalence (left right : BoundProcess) where
  State : Type
  leftState : State → left.State
  rightState : State → right.State
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  left_refines : ∀ state epsilon positive,
    Bound.Refines
      (left.bound (leftState (request state epsilon positive)))
      (left.bound (leftState state))
  right_refines : ∀ state epsilon positive,
    Bound.Refines
      (right.bound (rightState (request state epsilon positive)))
      (right.bound (rightState state))
  close : ∀ state epsilon positive {leftValue rightValue : Coordinate},
    (left.bound (leftState (request state epsilon positive))).Contains
      leftValue →
    (right.bound (rightState (request state epsilon positive))).Contains
      rightValue →
    leftValue - rightValue < epsilon ∧
      rightValue - leftValue < epsilon

namespace OperationalEquivalence

/-- Every finite bound process is operationally equivalent to itself. -/
def refl (process : BoundProcess) :
    OperationalEquivalence process process where
  State := process.State
  leftState state := state
  rightState state := state
  initial := process.initial
  request state epsilon positive := process.request state epsilon positive
  left_refines := process.request_refines
  right_refines := process.request_refines
  close state epsilon positive :=
    process.request_pairwise_difference_lt state epsilon positive

/-- A rationally anchored shrinking process is operationally equivalent to
the exact rational anchor.  Every comparison is made after one finite
request. -/
def ofAnchoredAt (process : BoundProcess) (value : Coordinate)
    (anchored : process.AnchoredAt value) :
    OperationalEquivalence process (BoundProcess.exact value) where
  State := process.State
  leftState state := state
  rightState _ := ()
  initial := process.initial
  request state epsilon positive := process.request state epsilon positive
  left_refines := process.request_refines
  right_refines state epsilon positive := Bound.Refines.refl _
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have rightEqual := (Bound.exact_contains_iff value rightValue).mp rightInside
    subst rightValue
    exact process.request_pairwise_difference_lt state epsilon positive
      leftInside (anchored (process.request state epsilon positive))

/-- Reverse a finite operational equivalence. -/
def symm {left right : BoundProcess}
    (equivalent : OperationalEquivalence left right) :
    OperationalEquivalence right left where
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

/-- Addition respects finite operational equivalence.  Endpoint comparisons
avoid selecting a decomposition of an arbitrary value admitted by a sum
enclosure. -/
def add {leftFirst rightFirst leftSecond rightSecond : BoundProcess}
    (first : OperationalEquivalence leftFirst rightFirst)
    (second : OperationalEquivalence leftSecond rightSecond) :
    OperationalEquivalence (leftFirst.add leftSecond)
      (rightFirst.add rightSecond) where
  State := first.State × second.State
  leftState state :=
    ⟨first.leftState state.1, second.leftState state.2⟩
  rightState state :=
    ⟨first.rightState state.1, second.rightState state.2⟩
  initial := ⟨first.initial, second.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
      (by decide : (0 : Coordinate) < 2)
    ⟨first.request state.1 half halfPositive,
      second.request state.2 half halfPositive⟩
  left_refines state epsilon positive :=
    Bound.Refines.add
      (first.left_refines state.1 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
      (second.left_refines state.2 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
  right_refines state epsilon positive :=
    Bound.Refines.add
      (first.right_refines state.1 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
      (second.right_refines state.2 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    let half := epsilon / 2
    have halfPositive : (0 : Coordinate) < half :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
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
    have forwardSum := RFAP.ConstructiveFraction.add_lt_add_direct
      firstForward.1 secondForward.1
    have reverseSum := RFAP.ConstructiveFraction.add_lt_add_direct
      firstReverse.2 secondReverse.2
    constructor
    · calc
        leftValue - rightValue ≤
            (leftFirstBound.upper + leftSecondBound.upper) -
              (rightFirstBound.lower + rightSecondBound.lower) :=
          RFAP.ConstructiveFraction.sub_le_sub_direct leftInside.2 rightInside.1
        _ = (leftFirstBound.upper - rightFirstBound.lower) +
              (leftSecondBound.upper - rightSecondBound.lower) := by ring1
        _ < half + half := forwardSum
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
                (by decide)
    · calc
        rightValue - leftValue ≤
            (rightFirstBound.upper + rightSecondBound.upper) -
              (leftFirstBound.lower + leftSecondBound.lower) :=
          RFAP.ConstructiveFraction.sub_le_sub_direct rightInside.2 leftInside.1
        _ = (rightFirstBound.upper - leftFirstBound.lower) +
              (rightSecondBound.upper - leftSecondBound.lower) := by ring1
        _ < half + half := reverseSum
        _ = epsilon := by
          dsimp only [half]
          calc
            epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
            _ = epsilon :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
                (by decide)

/-- Additive inverse respects finite operational equivalence. -/
def neg {left right : BoundProcess}
    (equivalent : OperationalEquivalence left right) :
    OperationalEquivalence left.neg right.neg where
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
      (Bound.neg_contains_iff.mp leftInside)
      (Bound.neg_contains_iff.mp rightInside)
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
def sub {leftFirst rightFirst leftSecond rightSecond : BoundProcess}
    (first : OperationalEquivalence leftFirst rightFirst)
    (second : OperationalEquivalence leftSecond rightSecond) :
    OperationalEquivalence (leftFirst.sub leftSecond)
      (rightFirst.sub rightSecond) :=
  first.add second.neg

/-- Positive rational scaling respects finite operational equivalence. -/
def scalePositive {left right : BoundProcess}
    (equivalent : OperationalEquivalence left right)
    (factor : Coordinate) (factorPositive : 0 < factor) :
    OperationalEquivalence
      (left.scalePositive factor factorPositive)
      (right.scalePositive factor factorPositive) where
  State := equivalent.State
  leftState := equivalent.leftState
  rightState := equivalent.rightState
  initial := equivalent.initial
  request state epsilon positive :=
    equivalent.request state (epsilon / factor)
      (RFAP.ConstructiveFraction.div_pos_direct positive factorPositive)
  left_refines state epsilon positive :=
    Bound.Refines.scale factor factorPositive.le
      (equivalent.left_refines state (epsilon / factor)
        (RFAP.ConstructiveFraction.div_pos_direct positive factorPositive))
  right_refines state epsilon positive :=
    Bound.Refines.scale factor factorPositive.le
      (equivalent.right_refines state (epsilon / factor)
        (RFAP.ConstructiveFraction.div_pos_direct positive factorPositive))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    have requestPositive : 0 < epsilon / factor :=
      RFAP.ConstructiveFraction.div_pos_direct positive factorPositive
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
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        factorPositive forward.1
    have reverseScaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        factorPositive reverse.2
    constructor
    · calc
        leftValue - rightValue ≤
            factor * leftBound.upper - factor * rightBound.lower :=
          RFAP.ConstructiveFraction.sub_le_sub_direct leftInside.2 rightInside.1
        _ = factor * (leftBound.upper - rightBound.lower) := by ring1
        _ < factor * (epsilon / factor) := forwardScaled
        _ = epsilon := by
          calc
            factor * (epsilon / factor) = (epsilon / factor) * factor := by
              ring1
            _ = epsilon :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon factor
                factorPositive.ne'
    · calc
        rightValue - leftValue ≤
            factor * rightBound.upper - factor * leftBound.lower :=
          RFAP.ConstructiveFraction.sub_le_sub_direct rightInside.2 leftInside.1
        _ = factor * (rightBound.upper - leftBound.lower) := by ring1
        _ < factor * (epsilon / factor) := reverseScaled
        _ = epsilon := by
          calc
            factor * (epsilon / factor) = (epsilon / factor) * factor := by
              ring1
            _ = epsilon :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon factor
                factorPositive.ne'

/-- Compose two finite joint schedulers.  Coherence of the middle process
constructs one rational overlap witness shared by the two finite requests. -/
def trans {first middle third : BoundProcess}
    (firstMiddle : OperationalEquivalence first middle)
    (middleThird : OperationalEquivalence middle third)
    (middleCoherent : middle.Coherent) :
    OperationalEquivalence first third where
  State := firstMiddle.State × middleThird.State
  leftState state := firstMiddle.leftState state.1
  rightState state := middleThird.rightState state.2
  initial := ⟨firstMiddle.initial, middleThird.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
      (by decide : (0 : Coordinate) < 2)
    ⟨firstMiddle.request state.1 half halfPositive,
      middleThird.request state.2 half halfPositive⟩
  left_refines state epsilon positive :=
    firstMiddle.left_refines state.1 (epsilon / 2)
      (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
  right_refines state epsilon positive :=
    middleThird.right_refines state.2 (epsilon / 2)
      (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
  close state epsilon positive {leftValue} {rightValue}
      leftInside rightInside := by
    let half := epsilon / 2
    have halfPositive : (0 : Coordinate) < half :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let firstRequested := firstMiddle.request state.1 half halfPositive
    let thirdRequested := middleThird.request state.2 half halfPositive
    let middleLeft := middle.bound (firstMiddle.rightState firstRequested)
    let middleRight := middle.bound (middleThird.leftState thirdRequested)
    have middleOverlap : middleLeft.Overlaps middleRight :=
      middleCoherent _ _
    let witness := Bound.overlapWitness middleLeft middleRight
    have witnessInside := Bound.overlapWitness_inside middleOverlap
    have firstClose := firstMiddle.close state.1 half halfPositive
      leftInside witnessInside.1
    have thirdClose := middleThird.close state.2 half halfPositive
      witnessInside.2 rightInside
    have forward := RFAP.ConstructiveFraction.add_lt_add_direct
      firstClose.1 thirdClose.1
    have reverse := RFAP.ConstructiveFraction.add_lt_add_direct
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
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
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
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
                (by decide)

end OperationalEquivalence

/-- Propositional wrapper around an explicit finite joint scheduler. -/
def OperationallyEquivalent (left right : BoundProcess) : Prop :=
  Nonempty (OperationalEquivalence left right)

theorem operationallyEquivalent_refl (process : BoundProcess) :
    OperationallyEquivalent process process :=
  ⟨OperationalEquivalence.refl process⟩

theorem operationallyEquivalent_exact_of_anchoredAt
    (process : BoundProcess) (value : Coordinate)
    (anchored : process.AnchoredAt value) :
    OperationallyEquivalent process (BoundProcess.exact value) :=
  ⟨OperationalEquivalence.ofAnchoredAt process value anchored⟩

theorem operationallyEquivalent_symm {left right : BoundProcess}
    (equivalent : OperationallyEquivalent left right) :
    OperationallyEquivalent right left := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.symm⟩

theorem operationallyEquivalent_add
    {leftFirst rightFirst leftSecond rightSecond : BoundProcess}
    (first : OperationallyEquivalent leftFirst rightFirst)
    (second : OperationallyEquivalent leftSecond rightSecond) :
    OperationallyEquivalent (leftFirst.add leftSecond)
      (rightFirst.add rightSecond) := by
  rcases first with ⟨firstWitness⟩
  rcases second with ⟨secondWitness⟩
  exact ⟨firstWitness.add secondWitness⟩

theorem operationallyEquivalent_neg {left right : BoundProcess}
    (equivalent : OperationallyEquivalent left right) :
    OperationallyEquivalent left.neg right.neg := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.neg⟩

theorem operationallyEquivalent_sub
    {leftFirst rightFirst leftSecond rightSecond : BoundProcess}
    (first : OperationallyEquivalent leftFirst rightFirst)
    (second : OperationallyEquivalent leftSecond rightSecond) :
    OperationallyEquivalent (leftFirst.sub leftSecond)
      (rightFirst.sub rightSecond) := by
  rcases first with ⟨firstWitness⟩
  rcases second with ⟨secondWitness⟩
  exact ⟨firstWitness.sub secondWitness⟩

theorem operationallyEquivalent_scalePositive {left right : BoundProcess}
    (equivalent : OperationallyEquivalent left right)
    (factor : Coordinate) (positive : 0 < factor) :
    OperationallyEquivalent
      (left.scalePositive factor positive)
      (right.scalePositive factor positive) := by
  rcases equivalent with ⟨witness⟩
  exact ⟨witness.scalePositive factor positive⟩

theorem operationallyEquivalent_trans
    {first middle third : BoundProcess}
    (firstMiddle : OperationallyEquivalent first middle)
    (middleThird : OperationallyEquivalent middle third)
    (middleCoherent : middle.Coherent) :
    OperationallyEquivalent first third := by
  rcases firstMiddle with ⟨firstWitness⟩
  rcases middleThird with ⟨thirdWitness⟩
  exact ⟨firstWitness.trans thirdWitness middleCoherent⟩

end FiniteMeasure
