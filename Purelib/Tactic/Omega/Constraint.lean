module

import Lean.Elab.Tactic.Omega
meta import Lean.Elab.Tactic.Omega.Frontend
meta import Lean.Elab.Tactic.Omega.OmegaM
public import Purelib.Tactic.Omega.Coefficients
import Purelib.Tactic.Ring
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Int.Division

section

open Lean.Omega

namespace Purelib.Tactic.Omega.Constraint

/-- Boolean satisfaction supplies every retained lower and upper integer bound.

The two original optional bounds are read separately. Their Boolean
certificates yield the corresponding comparisons without changing either
the constraint or its integer value. -/
private theorem bounds_of_sat (constraint : Lean.Omega.Constraint) (value : Int)
    (satisfies : constraint.sat value = true) :
    (∀ lower, constraint.lowerBound = some lower → lower ≤ value) ∧
    (∀ upper, constraint.upperBound = some upper → value ≤ upper) := by
  have both : LowerBound.sat constraint.lowerBound value = true ∧
      UpperBound.sat constraint.upperBound value = true :=
    of_decide_eq_true satisfies
  constructor
  · intro lower retained
    have certified := both.1
    change constraint.lowerBound.all (fun bound => decide (bound ≤ value)) = true
      at certified
    rw [retained] at certified
    exact of_decide_eq_true certified
  · intro upper retained
    have certified := both.2
    change constraint.upperBound.all (fun bound => decide (value ≤ bound)) = true
      at certified
    rw [retained] at certified
    exact of_decide_eq_true certified

/-- Retained lower and upper comparisons certify original Boolean satisfaction.

An absent bound contributes the original true Boolean. A displayed bound
contributes its supplied comparison, so the same constraint and value
satisfy the original conjunction checker. -/
private theorem sat_of_bounds (constraint : Lean.Omega.Constraint) (value : Int)
    (lowerBound : ∀ lower, constraint.lowerBound = some lower → lower ≤ value)
    (upperBound : ∀ upper, constraint.upperBound = some upper → value ≤ upper) :
    constraint.sat value = true := by
  change decide (LowerBound.sat constraint.lowerBound value = true ∧
    UpperBound.sat constraint.upperBound value = true) = true
  apply decide_eq_true
  constructor
  · change constraint.lowerBound.all (fun bound => decide (bound ≤ value)) = true
    cases retained : constraint.lowerBound with
    | none => rfl
    | some lower =>
        exact decide_eq_true (lowerBound lower retained)
  · change constraint.upperBound.all (fun bound => decide (value ≤ bound)) = true
    cases retained : constraint.upperBound with
    | none => rfl
    | some upper =>
        exact decide_eq_true (upperBound upper retained)

/-- Scale the retained bounds by an integer, reversing them for a negative factor.

A zero factor keeps an impossible input constraint impossible and otherwise
produces the exact zero constraint. Every other factor maps the endpoints in
the order determined by its sign. -/
@[expose] public def scale (factor : Int) (constraint : Lean.Omega.Constraint) :
    Lean.Omega.Constraint :=
  if factor = 0 then
    if (match constraint.lowerBound with
      | none => false
      | some lower =>
          match constraint.upperBound with
          | none => false
          | some upper => decide (upper < lower)) then
      constraint
    else Lean.Omega.Constraint.exact 0
  else if 0 ≤ factor then
    constraint.map (factor * ·)
  else
    constraint.flip.map (factor * ·)

/-- Form an integer linear combination of two retained bound constraints.

Each input is scaled with its sign and zero-factor cases retained. Adding the
resulting lower and upper bounds gives the original finite combination. -/
@[expose] public def combo (leftScale : Int) (left : Lean.Omega.Constraint)
    (rightScale : Int) (right : Lean.Omega.Constraint) : Lean.Omega.Constraint :=
  Lean.Omega.Constraint.add (scale leftScale left) (scale rightScale right)

open Purelib.Data.Int in
/-- Satisfaction excludes contradictory retained bounds.

The supplied value lies above every retained lower bound and below every
retained upper bound. Their weak comparison therefore excludes the strict
reversal tested by the incompatibility checker. -/
private theorem incompatibleBounds_false_of_sat (constraint : Lean.Omega.Constraint)
    (value : Int) (satisfies : constraint.sat value = true) :
    (match constraint.lowerBound with
      | none => false
      | some lower =>
          match constraint.upperBound with
          | none => false
          | some upper => decide (upper < lower)) = false := by
  have bounds := bounds_of_sat constraint value satisfies
  cases lowerEquation : constraint.lowerBound with
  | none => rfl
  | some lower =>
      cases upperEquation : constraint.upperBound with
      | none => rfl
      | some upper =>
          apply decide_eq_false
          intro strict
          exact (Order.lt_iff_le_and_not_ge.mp strict).2
            (Order.le_trans (bounds.1 lower lowerEquation)
              (bounds.2 upper upperEquation))

/-- An order-preserving scalar map transports the retained satisfaction bounds.

Each present endpoint is mapped separately. The supplied scalar monotonicity
transports the original comparison without changing the retained input. -/
private theorem map_sat_of_monotone (constraint : Lean.Omega.Constraint)
    (value : Int) (operation : Int → Int)
    (monotone : ∀ left right, left ≤ right → operation left ≤ operation right)
    (satisfies : constraint.sat value = true) :
    (constraint.map operation).sat (operation value) = true := by
  have bounds := bounds_of_sat constraint value satisfies
  apply sat_of_bounds
  · intro lower retained
    change constraint.lowerBound.map operation = some lower at retained
    cases original : constraint.lowerBound with
    | none => rw [original] at retained; nomatch retained
    | some endpoint =>
        rw [original] at retained
        have readback := Option.some.inj retained
        rw [← readback]
        exact monotone endpoint value (bounds.1 endpoint original)
  · intro upper retained
    change constraint.upperBound.map operation = some upper at retained
    cases original : constraint.upperBound with
    | none => rw [original] at retained; nomatch retained
    | some endpoint =>
        rw [original] at retained
        have readback := Option.some.inj retained
        rw [← readback]
        exact monotone value endpoint (bounds.2 endpoint original)

/-- An order-reversing scalar map transports the reversed retained bounds.

The original upper endpoint becomes the mapped lower endpoint, and the original
lower endpoint becomes the mapped upper endpoint. The supplied antitonicity
certifies each transported comparison. -/
private theorem flip_map_sat_of_antitone (constraint : Lean.Omega.Constraint)
    (value : Int) (operation : Int → Int)
    (antitone : ∀ left right, left ≤ right → operation right ≤ operation left)
    (satisfies : constraint.sat value = true) :
    (constraint.flip.map operation).sat (operation value) = true := by
  have bounds := bounds_of_sat constraint value satisfies
  apply sat_of_bounds
  · intro lower retained
    change constraint.upperBound.map operation = some lower at retained
    cases original : constraint.upperBound with
    | none => rw [original] at retained; nomatch retained
    | some endpoint =>
        rw [original] at retained
        have readback := Option.some.inj retained
        rw [← readback]
        exact antitone value endpoint (bounds.2 endpoint original)
  · intro upper retained
    change constraint.lowerBound.map operation = some upper at retained
    cases original : constraint.lowerBound with
    | none => rw [original] at retained; nomatch retained
    | some endpoint =>
        rw [original] at retained
        have readback := Option.some.inj retained
        rw [← readback]
        exact antitone endpoint value (bounds.1 endpoint original)

open Purelib.Data.Int
/-- Scaling a satisfied constraint preserves satisfaction of its scaled value.

Zero scaling uses the original compatibility witness to produce the exact zero
constraint. Positive and negative scaling transport the displayed comparisons
through multiplication, reversing their order for a negative factor. -/
private theorem scale_sat (factor : Int) (constraint : Lean.Omega.Constraint)
    (value : Int) (satisfies : constraint.sat value = true) :
    (scale factor constraint).sat (factor * value) = true := by
  by_cases zero : factor = 0
  · have compatible := incompatibleBounds_false_of_sat constraint value satisfies
    rw [scale, if_pos zero, compatible, zero, Arithmetic.zero_mul]
    apply sat_of_bounds
    · intro lower retained
      have readback : (0 : Int) = lower := Option.some.inj retained
      rewrite [← readback]
      exact Order.le_refl 0
    · intro upper retained
      have readback : (0 : Int) = upper := Option.some.inj retained
      rewrite [← readback]
      exact Order.le_refl 0
  · rw [scale, if_neg zero]
    by_cases nonnegative : 0 ≤ factor
    · rw [if_pos nonnegative]
      exact map_sat_of_monotone constraint value (factor * ·)
        (fun _ _ bound => Order.mul_le_mul_of_nonneg_left bound nonnegative) satisfies
    · rw [if_neg nonnegative]
      have nonpositive : factor ≤ 0 := by
        cases Order.le_total factor 0 with
        | inl bound => exact bound
        | inr bound => exact (nonnegative bound).elim
      exact flip_map_sat_of_antitone constraint value (factor * ·)
        (fun _ _ bound => Order.mul_le_mul_of_nonpos_left bound nonpositive) satisfies

/-- Adding satisfied constraints preserves satisfaction of their summed values.

A present sum endpoint retains both original endpoints. Their two scalar
comparisons add to certify the corresponding lower or upper sum bound. -/
private theorem add_sat (left right : Lean.Omega.Constraint)
    (leftValue rightValue : Int)
    (leftSatisfies : left.sat leftValue = true)
    (rightSatisfies : right.sat rightValue = true) :
    (Lean.Omega.Constraint.add left right).sat (leftValue + rightValue) = true := by
  have leftBounds := bounds_of_sat left leftValue leftSatisfies
  have rightBounds := bounds_of_sat right rightValue rightSatisfies
  apply sat_of_bounds
  · intro lower retained
    change (left.lowerBound.bind fun first =>
      right.lowerBound.map fun second => first + second) = some lower at retained
    cases firstEquation : left.lowerBound with
    | none => rw [firstEquation] at retained; nomatch retained
    | some first =>
        rw [firstEquation] at retained
        cases secondEquation : right.lowerBound with
        | none => rw [secondEquation] at retained; nomatch retained
        | some second =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rw [← readback]
            exact Order.add_le_add (leftBounds.1 first firstEquation)
              (rightBounds.1 second secondEquation)
  · intro upper retained
    change (left.upperBound.bind fun first =>
      right.upperBound.map fun second => first + second) = some upper at retained
    cases firstEquation : left.upperBound with
    | none => rw [firstEquation] at retained; nomatch retained
    | some first =>
        rw [firstEquation] at retained
        cases secondEquation : right.upperBound with
        | none => rw [secondEquation] at retained; nomatch retained
        | some second =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rw [← readback]
            exact Order.add_le_add (leftBounds.2 first firstEquation)
              (rightBounds.2 second secondEquation)

/-- Two satisfied constraints certify the conjunction of their retained bounds.

The original conjunction keeps each lone endpoint and selects the larger lower
endpoint or smaller upper endpoint when both are present. The corresponding
input comparison directly certifies every selected endpoint. -/
public theorem combine_sat' (left right : Lean.Omega.Constraint) (source values : Coeffs)
    (leftSatisfies : left.sat' source values)
    (rightSatisfies : right.sat' source values) :
    (left.combine right).sat' source values := by
  have leftBounds := bounds_of_sat left (Coeffs.dot source values) leftSatisfies
  have rightBounds := bounds_of_sat right (Coeffs.dot source values) rightSatisfies
  apply sat_of_bounds
  · intro lower retained
    change (Option.merge (fun first second : Int => if first ≤ second then second else first)
      left.lowerBound right.lowerBound) = some lower at retained
    cases firstEquation : left.lowerBound with
    | none =>
        rw [firstEquation] at retained
        cases secondEquation : right.lowerBound with
        | none => rw [secondEquation] at retained; nomatch retained
        | some second =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rewrite [← readback]
            exact rightBounds.1 second secondEquation
    | some first =>
        rw [firstEquation] at retained
        cases secondEquation : right.lowerBound with
        | none =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rewrite [← readback]
            exact leftBounds.1 first firstEquation
        | some second =>
            rw [secondEquation] at retained
            change some (if first ≤ second then second else first) = some lower at retained
            by_cases selected : first ≤ second
            · rw [if_pos selected] at retained
              have readback := Option.some.inj retained
              rewrite [← readback]
              exact rightBounds.1 second secondEquation
            · rw [if_neg selected] at retained
              have readback := Option.some.inj retained
              rewrite [← readback]
              exact leftBounds.1 first firstEquation
  · intro upper retained
    change (Option.merge (fun first second : Int => if first ≤ second then first else second)
      left.upperBound right.upperBound) = some upper at retained
    cases firstEquation : left.upperBound with
    | none =>
        rw [firstEquation] at retained
        cases secondEquation : right.upperBound with
        | none => rw [secondEquation] at retained; nomatch retained
        | some second =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rewrite [← readback]
            exact rightBounds.2 second secondEquation
    | some first =>
        rw [firstEquation] at retained
        cases secondEquation : right.upperBound with
        | none =>
            rw [secondEquation] at retained
            have readback := Option.some.inj retained
            rewrite [← readback]
            exact leftBounds.2 first firstEquation
        | some second =>
            rw [secondEquation] at retained
            change some (if first ≤ second then first else second) = some upper at retained
            by_cases selected : first ≤ second
            · rw [if_pos selected] at retained
              have readback := Option.some.inj retained
              rewrite [← readback]
              exact leftBounds.2 first firstEquation
            · rw [if_neg selected] at retained
              have readback := Option.some.inj retained
              rewrite [← readback]
              exact rightBounds.2 second secondEquation

/-- A nonnegative affine evaluation certifies its retained lower-bound constraint.

The original natural additive difference moves the constant to the lower
endpoint by scalar cancellation. The original coefficient vector and value
owner then satisfy the same one-sided constraint. -/
public theorem addInequality_sat (constant : Int) (source values : Coeffs)
    (nonnegative : 0 ≤ constant + Coeffs.dot source values) :
    (Lean.Omega.Constraint.mk (some (-constant)) none).sat' source values := by
  obtain ⟨difference, equation⟩ := Order.le_dest nonnegative
  rw [Arithmetic.zero_add] at equation
  have translated : -constant ≤ Coeffs.dot source values := by
    apply Order.le_intro difference
    calc
      -constant + (difference : Int) =
          -constant + (constant + Coeffs.dot source values) :=
        congrArg (-constant + ·) equation
      _ = Coeffs.dot source values := by
        rw [← Arithmetic.add_assoc, Arithmetic.neg_add_cancel, Arithmetic.zero_add]
  apply sat_of_bounds
  · intro lower retained
    have readback : -constant = lower := Option.some.inj retained
    rewrite [← readback]
    exact translated
  · intro upper retained
    nomatch retained

/-- A vanishing affine evaluation certifies its exact retained bound constraint.

The original scalar equality identifies the coefficient dot product with the
negated constant. Both retained endpoints therefore hold at that same value,
without changing either coefficient vector or its value owner. -/
public theorem addEquality_sat (constant : Int) (source values : Coeffs)
    (vanishes : constant + Coeffs.dot source values = 0) :
    (Lean.Omega.Constraint.mk (some (-constant)) (some (-constant))).sat'
      source values := by
  have recovered : -constant = Coeffs.dot source values :=
    Arithmetic.neg_eq_of_add_eq_zero vanishes
  apply sat_of_bounds
  · intro lower retained
    have readback : -constant = lower := Option.some.inj retained
    rewrite [← readback, ← recovered]
    exact Order.le_refl (-constant)
  · intro upper retained
    have readback : -constant = upper := Option.some.inj retained
    rewrite [← readback, ← recovered]
    exact Order.le_refl (-constant)

/-- A retained lower bound strictly above a retained upper bound excludes satisfaction.

The original constraint fields identify both displayed integer bounds. Any
satisfaction witness would place the original dot product between them, giving
the weak comparison forbidden by their supplied strict order. -/
public theorem not_sat'_of_bounds (constraint : Lean.Omega.Constraint)
    (source values : Coeffs) (lower upper : Int)
    (retainedLower : constraint.lowerBound = some lower)
    (retainedUpper : constraint.upperBound = some upper)
    (incompatible : upper < lower) : ¬constraint.sat' source values := by
  intro satisfies
  have bounds := bounds_of_sat constraint (Coeffs.dot source values) satisfies
  have ordered := Order.le_trans (bounds.1 lower retainedLower)
    (bounds.2 upper retainedUpper)
  exact (Order.lt_iff_le_and_not_ge.mp incompatible).2 ordered

end Purelib.Tactic.Omega.Constraint

end

section

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

public section

section

open Lean.Omega
open Purelib.Tactic.Omega
open Purelib.Data.Int

namespace Purelib.Tactic.QuotientFreeOmega

/-- Reduce a finite coordinate evaluation by its explicit list and integer equations.

This local tactic unfolds only the displayed coefficient constructors, dot product and scalar zero/one identities. -/
local macro "coordinate_rfl" : tactic =>
  `(tactic|
    simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith, Int.one_mul, Int.zero_mul, Int.add_zero,
      Int.zero_add])

end Purelib.Tactic.QuotientFreeOmega

section
open Purelib.Tactic

namespace Purelib.Tactic.Omega.Constraint

/-- Soundness of combining two finite Omega constraints, using the direct
coefficient identities above.

The two original constraint-satisfaction witnesses and their displayed integer
factors certify the combined finite constraint through the retained coefficient
identities. -/
theorem combo_sat' (leftConstraint rightConstraint : Constraint)
    (leftScale : Int) (leftCoefficients : Coeffs)
    (rightScale : Int) (rightCoefficients values : Coeffs)
    (leftSatisfies : leftConstraint.sat' leftCoefficients values)
    (rightSatisfies : rightConstraint.sat' rightCoefficients values) :
    (combo leftScale leftConstraint rightScale rightConstraint).sat'
      (Coeffs.combo leftScale leftCoefficients rightScale rightCoefficients)
      values := by
  rw [Constraint.sat']
  change (combo leftScale leftConstraint rightScale rightConstraint).sat
      (IntList.dot
        (IntList.combo leftScale leftCoefficients rightScale rightCoefficients)
        values) = true
  rw [
    Omega.Coefficients.intList_combo_eq_smul_add_smul,
    Omega.Coefficients.intList_dot_distrib_left,
    Coefficients.intList_dot_smul_left, Coefficients.intList_dot_smul_left]
  exact add_sat _ _ _ _
    (scale_sat leftScale leftConstraint _ leftSatisfies)
    (scale_sat rightScale rightConstraint _ rightSatisfies)

/-- A retained finite quotient decomposition certifies modular elimination.

The coefficient and remainder equations retain exact integer quotient witnesses.
The supplied coordinate equation identifies the original added variable, while
its coefficient replaces an explicitly zero coordinate in the reduced vector.
These finite certificates imply the balanced-remainder constraint directly. -/
theorem bmod_sat
    (modulus : Nat) (remainder : Int) (index : Nat)
    (source reduced quotients values : Coeffs) (remainderQuotient : Int)
    (coefficientEquation : source = (modulus : Int) * quotients + reduced)
    (remainderEquation :
      remainder = (modulus : Int) * remainderQuotient + Int.bmod remainder modulus)
    (unusedCoordinate : Omega.Coefficients.get reduced index = 0)
    (newCoordinate : Omega.Coefficients.get values index =
      (Int.bmod (Coeffs.dot source values) modulus - Coeffs.dot reduced values) /
        (modulus : Int))
    (sourceSatisfies : (Constraint.exact remainder).sat' source values) :
    (Constraint.exact (Int.bmod remainder modulus)).sat'
      (Coeffs.set reduced index (modulus : Int)) values := by
  have bounds := bounds_of_sat (Constraint.exact remainder)
    (Coeffs.dot source values) sourceSatisfies
  have evaluated : Coeffs.dot source values = remainder :=
    Order.le_antisymm (bounds.2 remainder rfl) (bounds.1 remainder rfl)
  have decomposed : Coeffs.dot source values =
      (modulus : Int) * Coeffs.dot quotients values + Coeffs.dot reduced values := by
    rw [coefficientEquation]
    change IntList.dot ((modulus : Int) * quotients + reduced) values =
      (modulus : Int) * IntList.dot quotients values + IntList.dot reduced values
    rw [Coefficients.intList_dot_distrib_left, Coefficients.intList_dot_smul_left]
  have same : (modulus : Int) * Coeffs.dot quotients values + Coeffs.dot reduced values =
      (modulus : Int) * remainderQuotient + Int.bmod remainder modulus :=
    decomposed.symm.trans (evaluated.trans remainderEquation)
  have differenceEquation :
      Int.bmod remainder modulus - Coeffs.dot reduced values =
        (modulus : Int) * (Coeffs.dot quotients values - remainderQuotient) := by
    have transported := congrArg (fun term : Int =>
      term - (modulus : Int) * remainderQuotient - Coeffs.dot reduced values) same
    calc
      Int.bmod remainder modulus - Coeffs.dot reduced values =
          ((modulus : Int) * remainderQuotient + Int.bmod remainder modulus) -
            (modulus : Int) * remainderQuotient - Coeffs.dot reduced values := by ring1
      _ = ((modulus : Int) * Coeffs.dot quotients values + Coeffs.dot reduced values) -
            (modulus : Int) * remainderQuotient - Coeffs.dot reduced values :=
        transported.symm
      _ = (modulus : Int) * (Coeffs.dot quotients values - remainderQuotient) := by ring1
  have divisible : (modulus : Int) ∣
      Int.bmod remainder modulus - Coeffs.dot reduced values :=
    ⟨Coeffs.dot quotients values - remainderQuotient, differenceEquation⟩
  have cancelled := Division.ediv_mul_cancel divisible
  have coordinateProduct : (modulus : Int) * Omega.Coefficients.get values index =
      Int.bmod remainder modulus - Coeffs.dot reduced values := by
    rw [newCoordinate, evaluated]
    exact (Arithmetic.mul_comm _ _).trans cancelled
  have targetValue : Coeffs.dot (Coeffs.set reduced index (modulus : Int)) values =
      Int.bmod remainder modulus := by
    rw [Coefficients.coeffs_dot_set_left, unusedCoordinate,
      Arithmetic.sub_zero, coordinateProduct]
    ring1
  change (Constraint.exact (Int.bmod remainder modulus)).sat
    (Coeffs.dot (Coeffs.set reduced index (modulus : Int)) values) = true
  rw [targetValue]
  apply sat_of_bounds
  · intro lower retained
    have readback : Int.bmod remainder modulus = lower := Option.some.inj retained
    rewrite [← readback]
    exact Order.le_refl _
  · intro upper retained
    have readback : Int.bmod remainder modulus = upper := Option.some.inj retained
    rewrite [← readback]
    exact Order.le_refl _

end Purelib.Tactic.Omega.Constraint

end

namespace Purelib.Tactic.Omega.Constraint

/-- Division of a displayed constraint is sound when the old finite
coefficient vector is explicitly certified to be the divisor times the new
one.

The supplied scaling equation identifies the original coefficient vector with the
displayed divisor times the new vector. The original satisfaction witness then
certifies the divided constraint. -/
theorem div_sat_of_scaled (constraint : Constraint)
    (source target values : Coeffs) (divisor : Nat)
    (divisorNonzero : divisor ≠ 0)
    (scaled : source = (divisor : Int) * target)
    (sourceSatisfies : constraint.sat' source values) :
    (constraint.div divisor).sat' target values := by
  have divisorPositive : 0 < divisor := Nat.pos_of_ne_zero divisorNonzero
  have divisorCastNonzero : (divisor : Int) ≠ 0 := by
    intro castZero
    exact divisorNonzero (Int.ofNat.inj castZero)
  have dotScale : IntList.dot source values =
      (divisor : Int) * IntList.dot target values := by
    rw [scaled, Coefficients.intList_dot_smul_left]
  have bounds := bounds_of_sat constraint
    (IntList.dot source values) sourceSatisfies
  apply sat_of_bounds (constraint.div divisor)
    (IntList.dot target values)
  · intro lower retained
    change constraint.lowerBound.map
      (fun bound => -((-bound) / (divisor : Int))) = some lower at retained
    cases original : constraint.lowerBound with
    | none => rw [original] at retained; nomatch retained
    | some originalLower =>
        rw [original] at retained
        have readback : -((-originalLower) / (divisor : Int)) = lower :=
          Option.some.inj retained
        have bound := bounds.1 originalLower original
        rw [dotScale] at bound
        have reversed := Order.neg_le_neg bound
        have negatedProduct :
            -((divisor : Int) * IntList.dot target values) =
              (divisor : Int) * (-IntList.dot target values) := by
          calc
            -((divisor : Int) * IntList.dot target values) =
                -(IntList.dot target values * (divisor : Int)) :=
              congrArg Int.neg (Arithmetic.mul_comm _ _)
            _ = (-IntList.dot target values) * (divisor : Int) :=
              (Arithmetic.neg_mul _ _).symm
            _ = (divisor : Int) * (-IntList.dot target values) :=
              Arithmetic.mul_comm _ _
        rw [negatedProduct] at reversed
        have divided := Division.ediv_le_ediv_right reversed divisorPositive
        rw [Division.mul_ediv_cancel_left _ divisorCastNonzero] at divided
        have restored := Order.neg_le_neg divided
        rw [Int.neg_neg] at restored
        rw [← readback]
        exact restored
  · intro upper retained
    change constraint.upperBound.map
      (fun bound => bound / (divisor : Int)) = some upper at retained
    cases original : constraint.upperBound with
    | none => rw [original] at retained; nomatch retained
    | some originalUpper =>
        rw [original] at retained
        have readback : originalUpper / (divisor : Int) = upper :=
          Option.some.inj retained
        have bound := bounds.2 originalUpper original
        rw [dotScale] at bound
        have divided := Division.ediv_le_ediv_right bound divisorPositive
        rw [Division.mul_ediv_cancel_left _ divisorCastNonzero] at divided
        rw [← readback]
        exact divided

/-- Negating both the constraint and its displayed coefficient vector preserves satisfaction.

The original upper and lower comparison certificates reverse under integer
negation. They certify the same flipped optional bounds and the negated
dot product, with both displayed coefficient owners retained. -/
theorem neg_sat_coeffs (constraint : Constraint) (source values : Coeffs)
    (sourceSatisfies : constraint.sat' source values) :
    constraint.neg.sat' (-source) values := by
  change constraint.neg.sat (IntList.dot (-source) values) = true
  rw [Coefficients.intList_dot_neg_left]
  have bounds := bounds_of_sat constraint
    (IntList.dot source values) sourceSatisfies
  apply sat_of_bounds constraint.neg (-IntList.dot source values)
  · intro lower retained
    change constraint.upperBound.map Int.neg = some lower at retained
    cases original : constraint.upperBound with
    | none => rw [original] at retained; nomatch retained
    | some originalUpper =>
        rw [original] at retained
        have readback : -originalUpper = lower := Option.some.inj retained
        rw [← readback]
        exact Order.neg_le_neg (bounds.2 originalUpper original)
  · intro upper retained
    change constraint.lowerBound.map Int.neg = some upper at retained
    cases original : constraint.lowerBound with
    | none => rw [original] at retained; nomatch retained
    | some originalLower =>
        rw [original] at retained
        have readback : -originalLower = upper := Option.some.inj retained
        rw [← readback]
        exact Order.neg_le_neg (bounds.1 originalLower original)

open Purelib.Tactic in
/-- The negative-leading branch followed by certified division. -/
theorem neg_div_sat_of_scaled (constraint : Constraint)
    (source target values : Coeffs) (divisor : Nat)
    (divisorNonzero : divisor ≠ 0)
    (scaled : -source = (divisor : Int) * target)
    (sourceSatisfies : constraint.sat' source values) :
    ((constraint.neg).div divisor).sat' target values :=
  div_sat_of_scaled constraint.neg (-source) target values divisor
    divisorNonzero scaled
    (neg_sat_coeffs constraint source values sourceSatisfies)

/-- Soundness of Omega's all-zero normalization branch.

The retained zero-vector, leading-entry and GCD certificates select the
original trivial-constraint branch of the finite normalization procedure. -/
theorem tidy_sat_of_zero (constraint : Constraint) (source values : Coeffs)
    (sourceZero : source.isZero) (leadingZero : source.leading = 0)
    (gcdZero : source.gcd = 0)
    (sourceSatisfies : constraint.sat' source values) :
    (tidyConstraint constraint source).sat'
      (tidyCoeffs constraint source) values := by
  have dotZero : IntList.dot source values = 0 :=
    Omega.Coefficients.intList_dot_eq_zero_of_isZero source values sourceZero
  have satisfiesZero : constraint.sat 0 := by
    change constraint.sat (IntList.dot source values) at sourceSatisfies
    rw [dotZero] at sourceSatisfies
    exact sourceSatisfies
  have positivizeNone : positivize? (constraint, source) = none := by
    unfold positivize?
    change (if 0 ≤ source.leading then none
      else some (constraint.neg, source.smul (-1))) = none
    rw [leadingZero]
    rfl
  have normalizeSome :
      normalize? (constraint, source) = some (Constraint.trivial, source) := by
    unfold normalize?
    change (if source.gcd = 0 then
        if constraint.sat 0 then some (Constraint.trivial, source)
        else some (Constraint.impossible, source)
      else if source.gcd = 1 then none
      else some (constraint.div source.gcd, source.sdiv source.gcd)) =
        some (Constraint.trivial, source)
    rw [gcdZero]
    rw [if_pos rfl, if_pos satisfiesZero]
  have tidyResult : tidy (constraint, source) = (Constraint.trivial, source) := by
    unfold tidy tidy?
    dsimp only
    rw [positivizeNone, normalizeSome]
    rfl
  change ((tidy (constraint, source)).1).sat'
    ((tidy (constraint, source)).2) values
  rw [tidyResult]
  rfl

end Purelib.Tactic.Omega.Constraint

end

end

end
