module

public import Purelib.Polynomial.Dense.Rational.Denominator
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Sign.Basic
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Init.Data.Fin.Lemmas
import Init.Core
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.Polynomial.Dense.Rational.Evaluation

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial.Dense
open Purelib.Algebra

/-- A positive natural embeds as a nonzero canonical rational. -/
private theorem natCast_nonzero {value : Nat} (positive : 0 < value) :
    (value : Fraction.Rational) ≠ 0 := by
  intro equal
  exact (Nat.ne_of_gt positive)
    (Fraction.Cast.Compatibility.natCast_injective_direct equal)

/-- Homogeneous integer evaluation vanishes exactly when its original rational evaluation vanishes. -/
private theorem homogeneous_zero_iff (point : Fraction.Rational) (coefficients : List Int) :
    Integer.Homogeneous.homogeneousEval (Fraction.Basic.representative point).num
        (Fraction.Basic.representative point).den coefficients = 0 ↔
      Integer.Homogeneous.evalIntegers point coefficients = 0 := by
  cases coefficients with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons coefficient remaining =>
      have scaled := Integer.Homogeneous.homogeneousEval_cons_eq_scaled
        (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den_pos
        coefficient remaining
      rewrite [← Fraction.Cast.representative_eq_num_div_den point] at scaled
      have denominatorNonzero := natCast_nonzero (Fraction.Basic.representative point).den_pos
      have powerNonzero := Fraction.Field.pow_ne_zero_direct _ denominatorNonzero remaining.length
      constructor
      · intro zero
        rewrite [zero, Ring.IntCast.cast_zero] at scaled
        exact Field.ExplicitField.eq_zero_of_mul_eq_zero_left powerNonzero scaled.symm
      · intro zero
        rewrite [zero, mul_zero] at scaled
        exact Fraction.Cast.Compatibility.intCast_injective_direct scaled

set_option genInjectivity false in
/-- The complete denominator-clearance record for one original rational coefficient list.

The retained integer table and positive common denominator are exactly the
original structural clearance. They are reused for every subsequent point.
-/
public structure Prepared (coefficients : List Fraction.Rational) where
  /-- The retained ordered integer table and its same positive denominator. -/ cleared : Denominator.ClearedCoefficients
  /-- Complete original coefficient-clearance readback. -/ cleared_eq : cleared = Denominator.clear coefficients

constructive_injectivity Prepared

/-- Prepare the original coefficient table once for exact integer zero discrimination. -/
@[expose] public def prepare (coefficients : List Fraction.Rational) : Prepared coefficients :=
  ⟨Denominator.clear coefficients, rfl⟩

/-- Evaluate the homogeneous numerator using the same retained integer table and rational representative. -/
@[expose] public def Prepared.numerator {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) : Int :=
  Integer.Homogeneous.homogeneousEval (Fraction.Basic.representative point).num
    (Fraction.Basic.representative point).den prepared.cleared.coefficients

/-- Exact integer zero discrimination agrees with evaluation of every original rational coefficient list. -/
public theorem Prepared.numerator_zero_iff {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    prepared.numerator point = 0 ↔ Basic.DensePolynomial.evalCoeffs point coefficients = 0 := by
  have original := homogeneous_zero_iff point prepared.cleared.coefficients
  change prepared.numerator point = 0 ↔ _ at original
  have cleared := Denominator.eval_clear point coefficients
  rewrite [← prepared.cleared_eq] at cleared
  constructor
  · intro zero
    have clearedZero := original.mp zero
    rewrite [cleared] at clearedZero
    exact Field.ExplicitField.eq_zero_of_mul_eq_zero_left
      (natCast_nonzero prepared.cleared.denominatorPositive) clearedZero
  · intro zero
    apply original.mpr
    rewrite [cleared, zero]
    exact mul_zero _

/-- Read the exact original rational value from its certified retained integer numerator.

The supplied equality identifies the actual homogeneous numerator at the
original point and coefficient table. Its zero branch needs no denominator
power; otherwise one quotient consumes that same numerator and the original
positive coefficient and point denominators.
-/
@[expose] public def Prepared.evaluateNumerator {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) (numerator : Int)
    (_correct : numerator = prepared.numerator point) : Fraction.Rational :=
  if numerator = 0 then 0
  else
    let denominator := (Fraction.Basic.representative point).den ^
      (prepared.cleared.coefficients.length - 1) * prepared.cleared.denominator
    Fraction.Cast.fromInt numerator / Fraction.Cast.fromInt (Int.ofNat denominator)

/-- Evaluate at the original point using one retained homogeneous integer numerator. -/
@[expose] public def Prepared.evaluate {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) : Fraction.Rational :=
  prepared.evaluateNumerator point (prepared.numerator point) rfl

/-- The retained homogeneous numerator clears the exact original evaluation by its positive total denominator. -/
private theorem numerator_eq_scaled {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    (prepared.numerator point : Fraction.Rational) =
      (((Fraction.Basic.representative point).den ^ (prepared.cleared.coefficients.length - 1) *
          prepared.cleared.denominator : Nat) : Fraction.Rational) *
        Basic.DensePolynomial.evalCoeffs point coefficients := by
  have homogeneous : (prepared.numerator point : Fraction.Rational) =
      ((Fraction.Basic.representative point).den : Fraction.Rational) ^
          (prepared.cleared.coefficients.length - 1) *
        Integer.Homogeneous.evalIntegers point prepared.cleared.coefficients := by
    unfold Prepared.numerator
    cases prepared.cleared.coefficients with
    | nil =>
        change (0 : Fraction.Rational) = (Fraction.Basic.representative point).den ^ 0 * 0
        rw [mul_zero]
    | cons coefficient remaining =>
        have scaled := Integer.Homogeneous.homogeneousEval_cons_eq_scaled
          (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den_pos
          coefficient remaining
        rw [← Fraction.Cast.representative_eq_num_div_den point] at scaled
        exact scaled
  have cleared := Denominator.eval_clear point coefficients
  rw [← prepared.cleared_eq] at cleared
  rw [NatCast.mul, NatCast.pow, homogeneous, cleared, mul_assoc]

/-- The retained homogeneous integer numerator has the original rational evaluation's exact sign.

Its positive total denominator scales the original value without changing its
sign. Reading the numerator as a denominator-one rational requires no quotient
normalization, including for zero, negative values and leading-zero tables.
-/
public theorem Prepared.numerator_sign_eq {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    Sign.Basic.sign (Fraction.Cast.fromInt (prepared.numerator point)) =
      Sign.Basic.sign (Basic.DensePolynomial.evalCoeffs point coefficients) := by
  have positive : (0 : Fraction.Rational) <
      (((Fraction.Basic.representative point).den ^ (prepared.cleared.coefficients.length - 1) *
          prepared.cleared.denominator : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (n := (Fraction.Basic.representative point).den ^ (prepared.cleared.coefficients.length - 1) *
        prepared.cleared.denominator)
      (Nat.mul_pos (Nat.pow_pos (Fraction.Basic.representative point).den_pos)
        prepared.cleared.denominatorPositive)
  rewrite [← Fraction.Cast.intCast_eq_fromInt, numerator_eq_scaled prepared point,
    Sign.Basic.sign_mul, Sign.Basic.sign_of_pos positive]
  exact Int.one_mul _

/-- Prepared rational evaluation is exactly the original Horner value for every point and coefficient table. -/
public theorem Prepared.evaluate_eq {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    prepared.evaluate point = Basic.DensePolynomial.evalCoeffs point coefficients := by
  rw [Prepared.evaluate, Prepared.evaluateNumerator]
  by_cases zero : prepared.numerator point = 0
  · rw [if_pos zero]
    exact ((prepared.numerator_zero_iff point).mp zero).symm
  · rw [if_neg zero]
    dsimp only
    rw [← Fraction.Cast.intCast_eq_fromInt,
      ← Fraction.Cast.intCast_eq_fromInt (Int.ofNat
        ((Fraction.Basic.representative point).den ^ (prepared.cleared.coefficients.length - 1) *
          prepared.cleared.denominator)), Int.ofNat_eq_natCast, Int.cast_natCast]
    have positive : 0 < (Fraction.Basic.representative point).den ^
        (prepared.cleared.coefficients.length - 1) * prepared.cleared.denominator :=
      Nat.mul_pos (Nat.pow_pos (Fraction.Basic.representative point).den_pos)
        prepared.cleared.denominatorPositive
    apply Fraction.Field.mul_right_cancel_of_ne (natCast_nonzero positive)
    rw [Field.ExplicitField.div_mul_cancel _ (natCast_nonzero positive)]
    exact (numerator_eq_scaled prepared point).trans (mul_comm _ _)

/-- Reading a certified retained numerator gives the same original rational polynomial value. -/
public theorem Prepared.evaluateNumerator_eq {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) (numerator : Int)
    (correct : numerator = prepared.numerator point) :
    prepared.evaluateNumerator point numerator correct =
      Basic.DensePolynomial.evalCoeffs point coefficients := by
  cases correct
  exact prepared.evaluate_eq point

/-- The retained finite table is exactly the signed residue image of the original integer coefficients. -/
@[expose] public def Prepared.ReducesTo {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (modulus : Nat) [NeZero modulus]
    (residues : List (Fin modulus)) : Prop :=
  residues = prepared.cleared.coefficients.map Fin.intCast

/-- Prepare one retained finite-residue table for a consumer of the original coefficients.

The consumer receives its nonzero modulus and the exact original coefficient
map. Both signed casts and the table are computed once, outside any later
point-producing function; the modulus supplies no restriction on the input.
-/
@[expose, specialize 4] public def Prepared.withResidues {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) {Result : Type}
    (finish : ∀ (modulus : Nat) [NeZero modulus] (residues : List (Fin modulus)),
      prepared.ReducesTo modulus residues → Result) : Result :=
  let modulus : Nat := 2147483647
  haveI : NeZero modulus := ⟨by decide⟩
  let residues : List (Fin modulus) := prepared.cleared.coefficients.map Fin.intCast
  finish modulus residues rfl

/-- A consumer independent of the certified residue choice has that same result after preparation. -/
public theorem Prepared.withResidues_result {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) {Result : Type}
    (finish : ∀ (modulus : Nat) [NeZero modulus] (residues : List (Fin modulus)),
      prepared.ReducesTo modulus residues → Result)
    (result : Result)
    (consistent : ∀ (modulus : Nat) [NeZero modulus] (residues : List (Fin modulus))
      (correct : prepared.ReducesTo modulus residues),
      finish modulus residues correct = result) : prepared.withResidues finish = result := by
  unfold Prepared.withResidues
  exact consistent _ _ rfl

/-- A nonzero homogeneous residue certifies the original exact integer numerator is nonzero.

The retained table is the original signed coefficient map. Equality of the
complete homogeneous evaluation with its residue transports a hypothetical
integer zero to the same finite zero, for every nonzero modulus.
-/
public theorem Prepared.numerator_ne_zero_of_modular {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (modulus : Nat) [NeZero modulus]
    (residues : List (Fin modulus))
    (correct : prepared.ReducesTo modulus residues)
    (point : Fraction.Rational)
    (nonzero : Integer.Homogeneous.modularEval modulus
      (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den residues ≠ 0) :
    prepared.numerator point ≠ 0 := by
  intro zero
  apply nonzero
  change residues = prepared.cleared.coefficients.map Fin.intCast at correct
  rewrite [correct, Integer.Homogeneous.modularEval_eq]
  change Fin.intCast (prepared.numerator point) = (0 : Fin modulus)
  rewrite [zero]
  rfl

/-- An exact numerator decision retains its original memoized integer and readback certificate. -/
public abbrev Prepared.NumeratorTest {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :=
  {cached : Thunk Int // cached.get = prepared.numerator point} ×
    Decidable (prepared.numerator point = 0)

/-- Test the exact numerator while retaining its deferred cached value.

A nonzero residue avoids constructing the full integer until the consumer
requests it. A zero residue falls back to the original integer test and retains
that computed integer in the supplied thunk. Neither branch changes the point,
coefficient table or exact zero predicate.
-/
@[expose, inline] public def Prepared.zeroTestUsing
    {coefficients : List Fraction.Rational} (prepared : Prepared coefficients)
    (modulus : Nat) [NeZero modulus] (residues : List (Fin modulus))
    (correct : prepared.ReducesTo modulus residues) (point : Fraction.Rational) :
    prepared.NumeratorTest point :=
  let reduced := Integer.Homogeneous.modularEval modulus
    (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den residues
  if nonzero : reduced ≠ 0 then
    ⟨⟨Thunk.mk (fun _ => prepared.numerator point), rfl⟩,
      .isFalse (prepared.numerator_ne_zero_of_modular modulus residues correct point nonzero)⟩
  else
    let numerator := prepared.numerator point
    if zero : numerator = 0 then
      ⟨⟨Thunk.pure numerator, rfl⟩, .isTrue zero⟩
    else ⟨⟨Thunk.pure numerator, rfl⟩, .isFalse zero⟩

/-- Every certified modular zero test retains the complete original cached integer and exact decision.

Both thunks read back as the same original integer. The exact
decision retains the original zero branch, including when the residue vanishes
but the full integer does not.
-/
public theorem Prepared.zeroTestUsing_eq {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (modulus : Nat) [NeZero modulus]
    (residues : List (Fin modulus))
    (correct : prepared.ReducesTo modulus residues) (point : Fraction.Rational) :
    prepared.zeroTestUsing modulus residues correct point =
      ⟨⟨Thunk.pure (prepared.numerator point), rfl⟩,
        if zero : prepared.numerator point = 0 then .isTrue zero else .isFalse zero⟩ := by
  by_cases nonzero : Integer.Homogeneous.modularEval modulus
      (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den residues ≠ 0
  · rewrite [Prepared.zeroTestUsing, dif_pos nonzero]
    have original := prepared.numerator_ne_zero_of_modular modulus residues correct point nonzero
    rewrite [dif_neg original]
    rfl
  · rewrite [Prepared.zeroTestUsing, dif_neg nonzero]
    by_cases zero : prepared.numerator point = 0
    · rewrite [dif_pos zero, dif_pos zero]
      rfl
    · rewrite [dif_neg zero, dif_neg zero]
      rfl

/-- Decide original rational evaluation zero with one retained modular table and exact fallback. -/
public def Prepared.zeroDecisionMod {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    Decidable (Basic.DensePolynomial.evalCoeffs point coefficients = 0) :=
  prepared.withResidues fun modulus [_modulusInstance : NeZero modulus] residues correct =>
    let tested := prepared.zeroTestUsing modulus residues correct point
    match tested.2 with
    | .isTrue zero => .isTrue ((prepared.numerator_zero_iff point).mp zero)
    | .isFalse nonzero =>
        .isFalse (fun vanished => nonzero ((prepared.numerator_zero_iff point).mpr vanished))

/-- Decide original rational evaluation zero with an exact positive or negative witness.

The decision retains the same point and prepared integer table. Its witness
identifies the corresponding zero or nonzero original rational evaluation.
-/
@[expose, implemented_by Prepared.zeroDecisionMod] public def Prepared.zeroDecision
    {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    Decidable (Basic.DensePolynomial.evalCoeffs point coefficients = 0) :=
  if zero : prepared.numerator point = 0 then
    .isTrue ((prepared.numerator_zero_iff point).mp zero)
  else .isFalse (fun vanished => zero ((prepared.numerator_zero_iff point).mpr vanished))

/-- The modular implementation preserves the complete original rational zero decision for every input. -/
public theorem Prepared.zeroDecisionMod_eq {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    prepared.zeroDecisionMod point = prepared.zeroDecision point := by
  unfold Prepared.zeroDecisionMod
  apply prepared.withResidues_result
  intro modulus modulusInstance residues correct
  rewrite [Prepared.zeroTestUsing_eq]
  by_cases zero : prepared.numerator point = 0
  · rewrite [dif_pos zero, Prepared.zeroDecision, dif_pos zero]
    rfl
  · rewrite [dif_neg zero, Prepared.zeroDecision, dif_neg zero]
    rfl

/-- Compute the zero Boolean from the same prepared integer numerator. -/
@[expose] public def Prepared.isZero {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) : Bool :=
  decide (prepared.numerator point = 0)

/-- The computed Boolean equals the original rational evaluation's decision for every point. -/
public theorem Prepared.isZero_eq_decide {coefficients : List Fraction.Rational}
    (prepared : Prepared coefficients) (point : Fraction.Rational) :
    prepared.isZero point = decide (Basic.DensePolynomial.evalCoeffs point coefficients = 0) := by
  by_cases zero : Basic.DensePolynomial.evalCoeffs point coefficients = 0
  · have numeratorZero := (prepared.numerator_zero_iff point).mpr zero
    exact (decide_eq_true numeratorZero).trans (decide_eq_true zero).symm
  · have numeratorNonzero : prepared.numerator point ≠ 0 := fun vanished =>
      zero ((prepared.numerator_zero_iff point).mp vanished)
    exact (decide_eq_false numeratorNonzero).trans (decide_eq_false zero).symm

end Purelib.Polynomial.Dense.Rational.Evaluation
