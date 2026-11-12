module
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Bound.Process
public import Purelib.Data.Rat.Interval.Intersection
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Rat.Interval.Comparison
public import Purelib.Data.Rat.Bounds.Quarter
public import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Rational coordinate intervals from Gaussian finite processes

An original Gaussian process retains finite witnesses and squared-radius
requests. Each scalar request refines that same state, encloses the chosen
coordinate with an explicit rational radius and intersects it with the saved
interval. No completed Gaussian or real value is selected.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Coordinate

open Purelib.Data.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Gaussian.Enclosure

/-- Enclose one scalar coordinate of a Gaussian ball using a nonnegative rational radius. -/
@[expose] def ballInterval (read : Basic.Canonical → Fraction.Rational) (ball : Ball)
    (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) : Rat.Interval where
  lower := read ball.center - radius
  upper := read ball.center + radius
  valid := by
    have signed := Arithmetic.neg_le_self_of_nonnegative nonnegative
    have shifted := Arithmetic.add_le_add_right_direct signed (read ball.center)
    have first : -radius + read ball.center = read ball.center - radius := by ring1
    have second : radius + read ball.center = read ball.center + radius := by ring1
    rw [first, second] at shifted
    exact shifted

/-- The exact scalar interval width is twice its retained radius. -/
theorem ballInterval_width (read : Basic.Canonical → Fraction.Rational) (ball : Ball)
    (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    (ballInterval read ball radius nonnegative).width = radius + radius := by
  change (read ball.center + radius) - (read ball.center - radius) = radius + radius
  ring1

/-- A squared coordinate bound turns the original Gaussian ball into a rational interval admission. -/
theorem ballInterval_contains (read : Basic.Canonical → Fraction.Rational)
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (ball : Ball) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) (radiusBound : ball.radiusSq ≤ radius ^ 2)
    (value : Basic.Canonical) (inside : ball.Contains value) :
    (ballInterval read ball radius nonnegative).Contains (read value) := by
  have square := (coordinateSq value ball.center).trans (inside.trans radiusBound)
  have upper := Arithmetic.le_of_sq_le_sq_direct nonnegative square
  have lower := Arithmetic.neg_le_of_sq_le_sq_direct nonnegative square
  have shiftedLower := Arithmetic.add_le_add_right_direct lower (read ball.center)
  have shiftedUpper := Arithmetic.add_le_add_right_direct upper (read ball.center)
  have lowerLeft : -radius + read ball.center = read ball.center - radius := by ring1
  have lowerRight : (read value - read ball.center) + read ball.center = read value := by ring1
  have upperRight : radius + read ball.center = read ball.center + radius := by ring1
  rw [lowerLeft, lowerRight] at shiftedLower
  rw [lowerRight, upperRight] at shiftedUpper
  exact ⟨shiftedLower, shiftedUpper⟩

/-- A nonnegative squared allowance plus one gives a positive explicit coordinate radius. -/
@[expose] def initialRadius (ball : Ball) : Fraction.Rational := ball.radiusSq + 1

/-- The initial coordinate radius is positive, including a zero squared allowance. -/
theorem initialRadius_pos (ball : Ball) : 0 < initialRadius ball := by
  have shifted := Arithmetic.add_le_add_right_direct ball.radiusSq_nonneg 1
  rw [Fraction.Field.zero_add] at shifted
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le shifted

/-- The initial radius pays for the original ball's squared allowance. -/
theorem initialRadius_sq (ball : Ball) : ball.radiusSq ≤ (initialRadius ball) ^ 2 := by
  have square := Arithmetic.sq_nonneg_direct ball.radiusSq
  have extra := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct square ball.radiusSq_nonneg) (by decide : (0 : Fraction.Rational) ≤ 1)
  have zero : (0 : Fraction.Rational) + 0 + 0 = 0 := by decide
  rw [zero] at extra
  have shifted := Arithmetic.add_le_add_right_direct extra ball.radiusSq
  change ball.radiusSq ≤ (ball.radiusSq + 1) ^ 2
  calc
    ball.radiusSq = 0 + ball.radiusSq := by ring1
    _ ≤ (ball.radiusSq ^ 2 + ball.radiusSq + 1) + ball.radiusSq := shifted
    _ = (ball.radiusSq + 1) ^ 2 := by ring1

/-- The original Gaussian state has an explicit initial rational coordinate interval. -/
@[expose] def initialInterval (process : Process) (origin : process.State)
    (read : Basic.Canonical → Fraction.Rational) : Rat.Interval :=
  ballInterval read (process.ball origin) (initialRadius (process.ball origin)) (initialRadius_pos _).le

set_option genInjectivity false in
/-- A Gaussian process state with its retained finite coordinate interval.

The original process and initial state remain indexed owners. Every actual
possible Gaussian reading has its coordinate in the cached interval, which
itself refines the initial interval. -/
structure State (process : Process) (origin : process.State) (read : Basic.Canonical → Fraction.Rational) where
  /-- The actual original Gaussian process state. -/ current : process.State
  /-- Every reading possible at this state remains possible at the original state. -/ origin_persists :
    ∀ {value}, process.Possible current value → process.Possible origin value
  /-- The cached rational interval for the selected coordinate. -/ interval : Rat.Interval
  /-- All original possible Gaussian readings have a coordinate in this interval. -/ admits :
    ∀ value, process.Possible current value → interval.Contains (read value)
  /-- The cached interval refines the exact initial interval. -/ initial_refines :
    interval.Refines (initialInterval process origin read)

constructive_injectivity State

/-- Coordinate states with the same original Gaussian state and interval are equal. -/
theorem State.ext {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (first second : State process origin read) (current_eq : first.current = second.current)
    (interval_eq : first.interval = second.interval) : first = second := by
  cases first with
  | mk firstCurrent firstPersists firstInterval firstAdmits firstRefines =>
    cases second with
    | mk secondCurrent secondPersists secondInterval secondAdmits secondRefines =>
      cases current_eq
      cases interval_eq
      rfl

/-- Compare retained Gaussian-coordinate states using their original state and rational interval endpoints. -/
instance {process : Process} [DecidableEq process.State] {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} : DecidableEq (State process origin read) := by
  intro first second
  by_cases current_eq : first.current = second.current
  · by_cases lower_eq : first.interval.lower = second.interval.lower
    · by_cases upper_eq : first.interval.upper = second.interval.upper
      · exact isTrue (State.ext first second current_eq (Rat.Interval.ext lower_eq upper_eq))
      · exact isFalse (fun same => upper_eq (by cases same; rfl))
    · exact isFalse (fun same => lower_eq (by cases same; rfl))
  · exact isFalse (fun same => current_eq (congrArg State.current same))

namespace State

/-- Construct the initial coordinate state from the returned ball of the original Gaussian origin.

The supplied ball and its specification are consumed directly. Its interval
retains the original origin, and every reading possible there is admitted. -/
@[expose] def initialWith (process : Process) (origin : process.State) (read : Basic.Canonical → Fraction.Rational)
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (observed : Ball) (observed_eq : observed = process.ball origin) : State process origin read where
  current := origin
  origin_persists := fun possible => possible
  interval := ballInterval read observed (initialRadius observed) (initialRadius_pos _).le
  admits := by
    intro value possible
    apply ballInterval_contains read coordinateSq observed (initialRadius observed) (initialRadius_pos _).le
      (initialRadius_sq _) value
    rw [observed_eq]
    exact process.possible_inside possible
  initial_refines := by
    rw [observed_eq]
    exact Rat.Interval.Refines.refl _

/-- Construct the original initial coordinate interval from the retained Gaussian state. -/
@[expose] def initial (process : Process) (origin : process.State) (read : Basic.Canonical → Fraction.Rational)
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center)) :
    State process origin read :=
  let observed := process.ball origin
  initialWith process origin read coordinateSq observed rfl

/-- A returned original ball constructs the exact original initial coordinate state. -/
theorem initialWith_eq (process : Process) (origin : process.State) (read : Basic.Canonical → Fraction.Rational)
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (observed : Ball) (observed_eq : observed = process.ball origin) :
    initialWith process origin read coordinateSq observed observed_eq = initial process origin read coordinateSq := by
  cases observed_eq
  rfl

/-- Assemble a coordinate refinement from the returned original process state and ball.

The state and ball are the exact outputs of the original process request and
readback. The saved interval and those returned outputs are consumed once;
the new process witness proves that the two intervals overlap. -/
@[expose] def requestWith {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (next : process.State)
    (next_eq : next = process.refine previous.current ((tolerance / 4) ^ 2)
      (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2))
    (observed : Ball) (observed_eq : observed = process.ball next) : State process origin read := by
  let radius := tolerance / 4
  have radiusPositive : 0 < radius := Bounds.Quarter.quarter_pos positive
  let target := radius ^ 2
  have targetPositive : 0 < target := Arithmetic.pow_pos_direct radiusPositive 2
  have persists : ∀ {value}, process.Possible next value → process.Possible previous.current value := by
    intro value possible
    rw [next_eq] at possible
    exact process.refine_persists previous.current target targetPositive possible
  let fresh := ballInterval read observed radius radiusPositive.le
  have freshAdmits : ∀ value, process.Possible next value → fresh.Contains (read value) := by
    intro value possible
    have radiusBound : observed.radiusSq ≤ radius ^ 2 := by
      rw [observed_eq, next_eq]
      exact (process.accurate previous.current target targetPositive).le
    have inside : observed.Contains value := by
      rw [observed_eq]
      exact process.possible_inside possible
    exact ballInterval_contains read coordinateSq observed radius radiusPositive.le radiusBound value inside
  let witness := process.witness next
  have oldInside := previous.admits witness.val (persists witness.property)
  have freshInside := freshAdmits witness.val witness.property
  have overlaps := Rat.Interval.overlaps_of_common oldInside freshInside
  let retained := previous.interval.intersect fresh overlaps
  exact
    { current := next
      origin_persists := fun possible => previous.origin_persists (persists possible)
      interval := retained
      admits := by
        intro value possible
        have prior := previous.admits value (persists possible)
        exact (Rat.Interval.intersect_contains_iff previous.interval fresh overlaps (read value)).mpr
          ⟨prior, freshAdmits value possible⟩
      initial_refines := (Rat.Interval.intersect_refines_left previous.interval fresh overlaps).trans
        previous.initial_refines }

/-- Refine the original Gaussian state and intersect its actual scalar interval with the saved one. -/
@[expose] def request {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    State process origin read :=
  let next := process.refine previous.current ((tolerance / 4) ^ 2)
    (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2)
  let observed := process.ball next
  requestWith coordinateSq previous tolerance positive next rfl observed rfl

/-- The returned original state and ball assemble to the same complete coordinate request. -/
theorem requestWith_eq {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (next : process.State)
    (next_eq : next = process.refine previous.current ((tolerance / 4) ^ 2)
      (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2))
    (observed : Ball) (observed_eq : observed = process.ball next) :
    requestWith coordinateSq previous tolerance positive next next_eq observed observed_eq =
      request coordinateSq previous tolerance positive := by
  cases next_eq
  cases observed_eq
  rfl

/-- A coordinate request refines the exact saved rational interval. -/
theorem request_refines {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (request coordinateSq previous tolerance positive).interval.Refines previous.interval := by
  dsimp only [request, requestWith]
  apply Rat.Interval.intersect_refines_left

/-- The actual coordinate interval produced by a positive request is narrower than that request. -/
theorem request_accurate {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (request coordinateSq previous tolerance positive).interval.width < tolerance := by
  dsimp only [request, requestWith]
  apply lt_of_le_of_lt (b := tolerance / 2) _ (Fraction.Order.Field.half_lt_self positive)
  apply le_trans _ (le_of_eq (Bounds.Quarter.two_quarters tolerance))
  rw [← ballInterval_width read]
  · apply Rat.Interval.Refines.width_le
    apply Rat.Interval.intersect_refines_right
  · exact (Bounds.Quarter.quarter_pos positive).le

end State

set_option genInjectivity false in
/-- Two coordinate observations with a common retained state of their original Gaussian process.

The common state need not be either coordinate's current state. Every
possible reading at the common state must remain possible at both coordinate
states, so their two cached intervals admit the same Gaussian reading. -/
structure Paired (process : Process) (origin : process.State) where
  /-- The original retained real-coordinate state and interval. -/ real : State process origin Basic.Canonical.re
  /-- The original retained imaginary-coordinate state and interval. -/ imaginary :
    State process origin Basic.Canonical.im
  /-- An actual later Gaussian state shared by both coordinate admissions. -/ current : process.State
  /-- Every common-state reading is possible at the retained real state. -/ real_persists :
    ∀ {value}, process.Possible current value → process.Possible real.current value
  /-- Every common-state reading is possible at the retained imaginary state. -/ imaginary_persists :
    ∀ {value}, process.Possible current value → process.Possible imaginary.current value

constructive_injectivity Paired

namespace Paired

/-- Start both coordinates from the same original Gaussian state. -/
@[expose] def initial (process : Process) (origin : process.State) : Paired process origin where
  real := State.initial process origin Basic.Canonical.re Norm.Coordinates.re_sub_sq_le_basic_normSq
  imaginary := State.initial process origin Basic.Canonical.im Norm.Coordinates.im_sub_sq_le_basic_normSq
  current := origin
  real_persists := fun possible => possible
  imaginary_persists := fun possible => possible

/-- Attach an imaginary coordinate using the returned original Gaussian origin ball.

The supplied real coordinate remains the exact original state. The imaginary
initial interval consumes the supplied ball without another process readback. -/
@[expose] def fromRealWith {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) (observed : Ball) (observed_eq : observed = process.ball origin) :
    Paired process origin where
  real := real
  imaginary := State.initialWith process origin Basic.Canonical.im Norm.Coordinates.im_sub_sq_le_basic_normSq
    observed observed_eq
  current := real.current
  real_persists := fun possible => possible
  imaginary_persists := real.origin_persists

/-- Attach an imaginary coordinate to an already retained real coordinate and its original Gaussian state. -/
@[expose] def fromReal {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) : Paired process origin :=
  let observed := process.ball origin
  fromRealWith real observed rfl

/-- A returned original origin ball constructs the exact original paired coordinate state. -/
theorem fromRealWith_eq {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) (observed : Ball) (observed_eq : observed = process.ball origin) :
    fromRealWith real observed observed_eq = fromReal real := by
  cases observed_eq
  rfl

/-- Pair construction preserves the exact supplied real-coordinate state. -/
theorem fromRealWith_real {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) (observed : Ball) (observed_eq : observed = process.ball origin) :
    (fromRealWith real observed observed_eq).real = real := rfl

/-- Every reading possible at the actual common Gaussian state is admitted by both retained coordinates. -/
theorem admits {process : Process} {origin : process.State} (paired : Paired process origin)
    (value : Basic.Canonical) (possible : process.Possible paired.current value) :
    paired.real.interval.Contains value.re ∧ paired.imaginary.interval.Contains value.im :=
  ⟨paired.real.admits value (paired.real_persists possible),
    paired.imaginary.admits value (paired.imaginary_persists possible)⟩

/-- View the saved real interval at the actual shared Gaussian state. -/
@[expose] def realBase {process : Process} {origin : process.State} (paired : Paired process origin) :
    State process origin Basic.Canonical.re where
  current := paired.current
  origin_persists := fun possible => paired.real.origin_persists (paired.real_persists possible)
  interval := paired.real.interval
  admits := fun value possible => paired.real.admits value (paired.real_persists possible)
  initial_refines := paired.real.initial_refines

/-- View the saved imaginary interval at a returned state that refines the shared Gaussian state. -/
@[expose] def imaginaryBase {process : Process} {origin : process.State} (paired : Paired process origin)
    (realNext : State process origin Basic.Canonical.re)
    (realPrevious : ∀ {value}, process.Possible realNext.current value → process.Possible paired.current value) :
    State process origin Basic.Canonical.im where
  current := realNext.current
  origin_persists := realNext.origin_persists
  interval := paired.imaginary.interval
  admits := fun value possible => paired.imaginary.admits value (paired.imaginary_persists (realPrevious possible))
  initial_refines := paired.imaginary.initial_refines

/-- View the saved imaginary interval at the pair's exact current Gaussian state. -/
@[expose] def imaginaryAtCurrent {process : Process} {origin : process.State} (paired : Paired process origin) :
    State process origin Basic.Canonical.im :=
  paired.imaginaryBase paired.realBase (fun possible => possible)

/-- Retain the original real coordinate and attach an imaginary state refining the current shared state.

The supplied state and its persistence evidence become the new common
owner. Both coordinate intervals still admit every reading possible there. -/
@[expose] def withImaginary {process : Process} {origin : process.State} (paired : Paired process origin)
    (imaginary : State process origin Basic.Canonical.im)
    (previous : ∀ {value}, process.Possible imaginary.current value → process.Possible paired.current value) :
    Paired process origin where
  real := paired.real
  imaginary := imaginary
  current := imaginary.current
  real_persists := fun possible => paired.real_persists (previous possible)
  imaginary_persists := fun possible => possible

/-- Refine only the imaginary coordinate, starting from the exact retained shared Gaussian state.

The original real coordinate and its interval remain unchanged. The new
imaginary interval and common state come from the actual original process
request, so no real-coordinate refinement is repeated. -/
@[expose] def requestImaginary {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) : Paired process origin := by
  let next := State.request Norm.Coordinates.im_sub_sq_le_basic_normSq paired.imaginaryAtCurrent tolerance positive
  have previous : ∀ {value}, process.Possible next.current value → process.Possible paired.current value := by
    intro value possible
    exact process.refine_persists paired.current _ _ possible
  exact paired.withImaginary next previous

/-- An imaginary-only request preserves the exact original real-coordinate state. -/
theorem requestImaginary_real {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (paired.requestImaginary tolerance positive).real = paired.real := rfl

/-- The imaginary request continues the exact shared Gaussian predecessor. -/
theorem requestImaginary_current {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (paired.requestImaginary tolerance positive).current =
      process.refine paired.current ((tolerance / 4) ^ 2)
        (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2) := rfl

/-- The imaginary-only request narrows the original saved imaginary interval. -/
theorem requestImaginary_refines {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (paired.requestImaginary tolerance positive).imaginary.interval.Refines paired.imaginary.interval :=
  State.request_refines Norm.Coordinates.im_sub_sq_le_basic_normSq paired.imaginaryAtCurrent tolerance positive

/-- The returned imaginary interval meets its original positive request. -/
theorem requestImaginary_accurate {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    (paired.requestImaginary tolerance positive).imaginary.interval.width < tolerance :=
  State.request_accurate Norm.Coordinates.im_sub_sq_le_basic_normSq paired.imaginaryAtCurrent tolerance positive

/-- Refine both coordinates in sequence through the same actual original Gaussian process.

The real request starts from the shared state; the imaginary request starts
from that exact returned state. Both new intervals retain their saved
predecessors, and the final Gaussian state supplies their joint admission. -/
@[expose] def request {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    Paired process origin := by
  let realAt := paired.realBase
  let realNext := State.request Norm.Coordinates.re_sub_sq_le_basic_normSq realAt realTolerance realPositive
  have realPrevious : ∀ {value}, process.Possible realNext.current value → process.Possible paired.current value := by
    intro value possible
    exact process.refine_persists paired.current _ _ possible
  let imaginaryAt := paired.imaginaryBase realNext realPrevious
  let imaginaryNext := State.request Norm.Coordinates.im_sub_sq_le_basic_normSq imaginaryAt
    imaginaryTolerance imaginaryPositive
  exact
    { real := realNext
      imaginary := imaginaryNext
      current := imaginaryNext.current
      real_persists := fun possible => process.refine_persists realNext.current _ _ possible
      imaginary_persists := fun possible => possible }

/-- The paired real request continues the exact previously shared Gaussian state. -/
theorem request_real_current {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).real.current =
      process.refine paired.current ((realTolerance / 4) ^ 2)
        (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos realPositive) 2) := rfl

/-- The paired imaginary request continues the exact Gaussian state returned by the real request. -/
theorem request_current {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).current =
      process.refine (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).real.current
        ((imaginaryTolerance / 4) ^ 2)
        (Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos imaginaryPositive) 2) := rfl

/-- The real-coordinate interval of a paired request refines the saved real interval. -/
theorem request_real_refines {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).real.interval.Refines
      paired.real.interval := by
  exact State.request_refines Norm.Coordinates.re_sub_sq_le_basic_normSq _ realTolerance realPositive

/-- The imaginary-coordinate interval of a paired request refines the saved imaginary interval. -/
theorem request_imaginary_refines {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).imaginary.interval.Refines
      paired.imaginary.interval := by
  exact State.request_refines Norm.Coordinates.im_sub_sq_le_basic_normSq _ imaginaryTolerance imaginaryPositive

/-- The paired real interval meets its actual positive coordinate request. -/
theorem request_real_accurate {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).real.interval.width <
      realTolerance := by
  exact State.request_accurate Norm.Coordinates.re_sub_sq_le_basic_normSq _ realTolerance realPositive

/-- The paired imaginary interval meets its actual positive coordinate request. -/
theorem request_imaginary_accurate {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    (paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive).imaginary.interval.width <
      imaginaryTolerance := by
  exact State.request_accurate Norm.Coordinates.im_sub_sq_le_basic_normSq _ imaginaryTolerance imaginaryPositive

/-- The Gaussian rational formed from the two actual retained interval midpoints. -/
@[expose] def midpoint {process : Process} {origin : process.State} (paired : Paired process origin) :
    Basic.Canonical := ⟨paired.real.interval.midpoint, paired.imaginary.interval.midpoint⟩

/-- The same possible Gaussian reading differs from the paired midpoint by the two squared half-width budgets. -/
theorem normSq_sub_midpoint_le {process : Process} {origin : process.State} (paired : Paired process origin)
    (value : Basic.Canonical) (possible : process.Possible paired.current value) :
    Norm.Basic.normSq (value - paired.midpoint) ≤
      (paired.real.interval.width * (1 / 2)) ^ 2 + (paired.imaginary.interval.width * (1 / 2)) ^ 2 := by
  have inside := paired.admits value possible
  have realBound := Rat.Interval.abs_sub_midpoint_le inside.1
  have imaginaryBound := Rat.Interval.abs_sub_midpoint_le inside.2
  exact Norm.Coordinates.sub_normSq_le value paired.midpoint
    (paired.real.interval.width * (1 / 2)) (paired.imaginary.interval.width * (1 / 2)) realBound imaginaryBound

/-- Two paired midpoint readings agree within their coordinate budgets when they admit one common Gaussian reading.

The explicit common reading is possible at each original retained Gaussian
state. Independent states without such joint admission do not imply this
comparison. -/
theorem midpoints_normSq_le {process : Process} {leftOrigin rightOrigin : process.State}
    (left : Paired process leftOrigin) (right : Paired process rightOrigin) (value : Basic.Canonical)
    (leftPossible : process.Possible left.current value) (rightPossible : process.Possible right.current value) :
    Norm.Basic.normSq (left.midpoint - right.midpoint) ≤
      (left.real.interval.width + right.real.interval.width) ^ 2 +
        (left.imaginary.interval.width + right.imaginary.interval.width) ^ 2 := by
  have leftInside := left.admits value leftPossible
  have rightInside := right.admits value rightPossible
  have realOverlap := Rat.Interval.overlaps_of_common leftInside.1 rightInside.1
  have imaginaryOverlap := Rat.Interval.overlaps_of_common leftInside.2 rightInside.2
  have realBound := Rat.Interval.abs_sub_le_of_overlaps left.real.interval.midpoint_contains
    right.real.interval.midpoint_contains realOverlap
  have imaginaryBound := Rat.Interval.abs_sub_le_of_overlaps left.imaginary.interval.midpoint_contains
    right.imaginary.interval.midpoint_contains imaginaryOverlap
  exact Norm.Coordinates.sub_normSq_le left.midpoint right.midpoint
    (left.real.interval.width + right.real.interval.width)
    (left.imaginary.interval.width + right.imaginary.interval.width) realBound imaginaryBound

end Paired

/-- Construct a rational bound process retaining the original Gaussian states and coordinate intervals. -/
@[expose] def boundProcess (process : Process) (origin : process.State) (read : Basic.Canonical → Fraction.Rational)
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center)) :
    Approximation.BoundProcess where
  State := State process origin read
  bound := State.interval
  initial := State.initial process origin read coordinateSq
  request := State.request coordinateSq
  request_refines := State.request_refines coordinateSq
  accurate := State.request_accurate coordinateSq
  refinesInitial := State.initial_refines

/-- Project the actual real coordinates of an original Gaussian process into rational bounds. -/
@[expose] def real (process : Process) (origin : process.State) : Approximation.BoundProcess :=
  boundProcess process origin Basic.Canonical.re Norm.Coordinates.re_sub_sq_le_basic_normSq

/-- Project the actual imaginary coordinates of an original Gaussian process into rational bounds. -/
@[expose] def imaginary (process : Process) (origin : process.State) : Approximation.BoundProcess :=
  boundProcess process origin Basic.Canonical.im Norm.Coordinates.im_sub_sq_le_basic_normSq

end Purelib.Approximation.Gaussian.Process.Coordinate

end
