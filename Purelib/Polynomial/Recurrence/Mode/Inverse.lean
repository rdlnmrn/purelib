module

public import Purelib.Polynomial.Recurrence.Mode.Bounds
public import Purelib.Data.Vector.Dependent
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Inverse coefficients of the original Jordan mode shift

A retained inverse root and the same original generalized-mode producer give
the coefficients of negative finite shift powers. Their backward transition
is algebraic. Gaussian inverse roots inside the unit circle pay the same
original finite inside-mode requests, without any formal-field assumption.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat.Fraction

variable {K : Type*} [CommRing K]

/-- Compute a finite inverse-Jordan coefficient through the same original generalized mode.

The zero power has only its diagonal coefficient. A positive power uses
one retained inverse root and the original binomial mode at the shifted
natural index; no additional binomial or power producer is introduced.
-/
@[expose] def inverseEntry (inverse : K) (order : Nat) : Nat → K
  | 0 => if order = 0 then 1 else 0
  | steps + 1 => (-inverse) ^ order * inverse * entry inverse order (steps + order)

/-- The diagonal inverse-shift coefficient is the original natural power of the same inverse root. -/
theorem inverseEntry_zero_order (inverse : K) (steps : Nat) : inverseEntry inverse 0 steps = inverse ^ steps := by
  cases steps with
  | zero => rewrite [inverseEntry, if_pos rfl, pow_zero]; rfl
  | succ steps =>
      rewrite [inverseEntry, pow_zero, _root_.one_mul, entry_zero_order, Nat.add_zero, pow_succ, _root_.mul_comm]
      rfl

/-- Multiplying a positive inverse coefficient by its root removes its one retained inverse factor. -/
private theorem inverseEntry_mul_root (root inverse : K) (unit : inverse * root = 1) (order steps : Nat) :
    inverseEntry inverse order (steps + 1) * root =
      (-inverse) ^ order * entry inverse order (steps + order) := by
  rewrite [inverseEntry]
  calc
    _ = ((-inverse) ^ order * entry inverse order (steps + order)) * (inverse * root) := by ring0
    _ = _ := by rewrite [unit, _root_.mul_one]; rfl

/-- The inverse diagonal advances backward through the same original root-unit equation. -/
theorem inverseEntry_step_zero (root inverse : K) (unit : inverse * root = 1) (steps : Nat) :
    inverseEntry inverse 0 (steps + 1) * root = inverseEntry inverse 0 steps := by
  rewrite [inverseEntry_zero_order, inverseEntry_zero_order, pow_succ, _root_.mul_assoc, unit, _root_.mul_one]
  rfl

/-- Consecutive inverse coefficients undo the same original Jordan predecessor transition.

Only the displayed root-unit equation is used. The original Pascal
recurrence supplies every order, including the identity power's vanishing
strict-upper coefficients, over the original commutative ring.
-/
theorem inverseEntry_step (root inverse : K) (unit : inverse * root = 1) (order steps : Nat) :
    inverseEntry inverse (order + 1) (steps + 1) * root + inverseEntry inverse order (steps + 1) =
      inverseEntry inverse (order + 1) steps := by
  rewrite [inverseEntry_mul_root root inverse unit]
  cases steps with
  | zero =>
      rewrite [inverseEntry, inverseEntry, if_neg (Nat.succ_ne_zero order), Nat.zero_add,
        Nat.zero_add, entry_start, entry_start, _root_.mul_one, _root_.mul_one, pow_succ]
      ring0
  | succ steps =>
      change (-inverse) ^ (order + 1) * entry inverse (order + 1) (steps + 1 + (order + 1)) +
        (-inverse) ^ order * inverse * entry inverse order (steps + 1 + order) =
          (-inverse) ^ (order + 1) * inverse * entry inverse (order + 1) (steps + (order + 1))
      have first : steps + 1 + (order + 1) = (steps + order + 1) + 1 := by omega0
      have second : steps + 1 + order = steps + order + 1 := by omega0
      have third : steps + (order + 1) = steps + order + 1 := by omega0
      rewrite [first, second, third, entry_succ, pow_succ]
      ring0

open Purelib.Data.Gaussian

/-- A positive inverse-shift coefficient is no larger in quadrance than its same original reciprocal-root mode.

A Gaussian inverse root of quadrance at most one contributes only factors
of quadrance at most one. The binomial growth and its finite observation
index remain exactly those of the original generalized mode.
-/
theorem normSq_inverseEntry_le (inverse : Canonical) (bounded : Norm.Basic.normSq inverse ≤ 1)
    (order steps : Nat) : Norm.Basic.normSq (inverseEntry inverse order (steps + 1)) ≤
      Norm.Basic.normSq (entry inverse order (steps + order)) := by
  rewrite [inverseEntry, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Power.normSq_pow,
    Norm.Basic.normSq_neg]
  have powers := Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg inverse) bounded order
  rewrite [one_pow] at powers
  have factor := Order.Arithmetic.mul_le_mul_direct powers bounded (Norm.Basic.normSq_nonneg inverse)
    (by decide : (0 : Rational) ≤ 1)
  rewrite [one_mul] at factor
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factor (Norm.Basic.normSq_nonneg _)).trans_eq
    (_root_.one_mul _)

namespace Inside

/-- The same original inside-mode request bounds every sufficiently late inverse-shift coefficient. -/
theorem inverseEntry_bound {ceiling epsilon : Rational} {order : Nat}
    (request : Inside ceiling order epsilon) (lessOne : ceiling < 1) (inverse : Canonical)
    (pointBound : Norm.Basic.normSq inverse ≤ ceiling) (steps : Nat) (later : request.index ≤ steps + order) :
    Norm.Basic.normSq (inverseEntry inverse order (steps + 1)) ≤ epsilon :=
  (normSq_inverseEntry_le inverse (pointBound.trans lessOne.le) order steps).trans
    (request.bound inverse pointBound (steps + order) later)

end Inside

namespace InverseRequest

/-- Retained original inside requests for every strict-upper distance of the same finite block. -/
abbrev Entries (ceiling : Rational) (count : Nat) (epsilon : Rational) :=
  DependentVector fun order : Fin count => Inside ceiling order.val epsilon

end InverseRequest

set_option genInjectivity false in
/-- One source-fixed common late index bounding every reciprocal-mode coefficient in a finite outside block.

The supplied quadrance floor is strictly above one. Its reciprocal ceiling
and one original inside request per bounded order are prepared before any
Gaussian root is observed. Their stored maximum selects one common positive
index for all actual roots satisfying that same original floor.
-/
structure InverseRequest (floor : Rational) (count : Nat) (epsilon : Rational) where
  /-- The original outside quadrance floor lies strictly above one. -/
  floorAboveOne : 1 < floor
  /-- The requested common coefficient bound is positive. -/
  epsilonPositive : 0 < epsilon
  /-- The once-computed reciprocal quadrance ceiling. -/
  ceiling : Rational
  /-- The same original outside floor determines that reciprocal ceiling. -/
  ceiling_eq : ceiling = floor⁻¹
  /-- The retained reciprocal ceiling is nonnegative. -/
  ceilingNonnegative : 0 ≤ ceiling
  /-- The retained reciprocal ceiling lies strictly below one. -/
  ceilingInside : ceiling < 1
  /-- One retained original inside request for each bounded predecessor distance. -/
  entries : InverseRequest.Entries ceiling count epsilon
  /-- Every request is the same original producer on that retained ceiling and bounded order. -/
  entries_eq : entries = DependentVector.ofFn (fun order =>
    Inside.prepare ceiling ceilingNonnegative ceilingInside order.val epsilon epsilonPositive)
  /-- The retained sufficient common positive late index. -/
  index : Nat
  /-- The index is one plus the original maximum of these same retained inside thresholds. -/
  index_eq : index = entries.maximum (fun _ request => request.index) + 1

constructive_injectivity InverseRequest

namespace InverseRequest

/-- Prepare one common late inverse-coefficient bound before any Gaussian outside root is observed. -/
@[expose] def prepare (floor : Rational) (floorAboveOne : 1 < floor) (count : Nat)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) : InverseRequest floor count epsilon := by
  let ceiling := floor⁻¹
  have floorPositive : 0 < floor := (by decide : (0 : Rational) < 1).trans floorAboveOne
  have ceilingNonnegative : 0 ≤ ceiling := (Order.Field.inv_pos_direct floorPositive).le
  have ceilingInside : ceiling < 1 := by
    apply Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := floor) _ floorPositive
    rewrite [Fraction.Field.inv_mul_cancel floor floorPositive.ne', _root_.one_mul]
    exact floorAboveOne
  let entries : Entries ceiling count epsilon := DependentVector.ofFn (fun order =>
    Inside.prepare ceiling ceilingNonnegative ceilingInside order.val epsilon epsilonPositive)
  let index := entries.maximum (fun _ request => request.index) + 1
  exact
    { floorAboveOne := floorAboveOne
      epsilonPositive := epsilonPositive
      ceiling := ceiling
      ceiling_eq := rfl
      ceilingNonnegative := ceilingNonnegative
      ceilingInside := ceilingInside
      entries := entries
      entries_eq := rfl
      index := index
      index_eq := rfl }

variable {floor epsilon : Rational} {count : Nat}

/-- Every original inside threshold is strictly below the same stored common positive index. -/
theorem entry_before (request : InverseRequest floor count epsilon) (order : Fin count) :
    (request.entries.get order).index < request.index := by
  rewrite [request.index_eq]
  exact Nat.lt_succ_of_le (request.entries.get_le_maximum (fun _ entry => entry.index) order)

/-- Every actual Gaussian root above the same floor has all inverse coefficients bounded after the common index.

Only the actual Gaussian reciprocal is used. The strict outside floor proves
its nonzero denominator and the original reciprocal quadrance bound; no
formal root, coefficient-ring element or original formal shift is inverted.
-/
theorem bound (request : InverseRequest floor count epsilon) (root : Canonical)
    (pointBound : floor ≤ Norm.Basic.normSq root) (order : Fin count) (steps : Nat)
    (later : request.index ≤ steps) :
    Norm.Basic.normSq (inverseEntry (Field.inv root) order.val steps) ≤ epsilon := by
  have floorPositive : 0 < floor := (by decide : (0 : Rational) < 1).trans request.floorAboveOne
  have nonzero : root ≠ 0 := by
    intro zero
    have positive := floorPositive.trans_le pointBound
    rewrite [zero, Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl (0 : Rational)) positive
  have inverseBound : Norm.Basic.normSq (Field.inv root) ≤ request.ceiling := by
    rewrite [Field.normSq_inv root nonzero, request.ceiling_eq]
    exact Order.Field.inv_le_inv_of_pos_direct floorPositive pointBound
  have afterEntry := (request.entry_before order).trans_le later
  cases steps with
  | zero => exact False.elim (Nat.not_lt_zero _ afterEntry)
  | succ steps =>
      exact (request.entries.get order).inverseEntry_bound request.ceilingInside (Field.inv root) inverseBound steps
        ((Nat.le_of_lt_succ afterEntry).trans (Nat.le_add_right steps order.val))

/-- Every retained common inverse request is exactly its original automatic constructor. -/
theorem restore (request : InverseRequest floor count epsilon) :
    request = prepare floor request.floorAboveOne count epsilon request.epsilonPositive := by
  cases request with
  | mk above positive ceiling ceilingEq nonnegative inside entries entriesEq index indexEq =>
      cases ceilingEq
      cases entriesEq
      cases indexEq
      rfl

end InverseRequest

end Purelib.Polynomial.Recurrence.Mode

end
