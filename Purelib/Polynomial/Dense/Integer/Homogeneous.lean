module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
public import Purelib.Algebra.Monoid.Int
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Map
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Modular.Fin
import Init.Data.Fin.Lemmas

/-!
# Homogeneous readbacks of descending integer coefficient tables

The original integer power recurrence and ordered coefficient list determine
the homogeneous evaluation. Direct scalar transports compare its retained
integer value with the same rational Horner evaluation.
-/

namespace Purelib.Polynomial.Dense.Integer.Homogeneous

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data.Int

/-- Horner evaluation of an integer coefficient list after embedding it in
the constructive rationals.

The original ordered integer table is embedded coefficient by coefficient.
Its unchanged descending Horner evaluation supplies the rational value. -/
@[expose] public def evalIntegers (point : Fraction.Rational) (coefficients : List Int) : Fraction.Rational :=
  Dense.Basic.DensePolynomial.evalCoeffs point (coefficients.map fun (coefficient : Int) =>
    (coefficient : Fraction.Rational))

/-- An empty integer coefficient list evaluates to the constructive rational zero. -/
@[simp] public theorem evalIntegers_nil (point : Fraction.Rational) :
    evalIntegers point [] = 0 := rfl

/-- Split descending integer-coefficient evaluation into the leading monomial and the remaining list.

The retained head contributes its monomial at the original tail length.
The unchanged mapped tail supplies the remaining descending evaluation. -/
public theorem evalIntegers_cons (point : Fraction.Rational) (coefficient : Int)
    (remaining : List Int) :
    evalIntegers point (coefficient :: remaining) =
      (coefficient : Fraction.Rational) * point ^ remaining.length +
        evalIntegers point remaining := by
  change Dense.Basic.DensePolynomial.evalCoeffs point
      ((coefficient : Fraction.Rational) :: remaining.map (fun value : Int => (value : Fraction.Rational))) = _
  rewrite [Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion,
    Map.length_map]
  exact Eq.refl _

/-- Multiplying each integer coefficient by a fixed integer multiplies its rational evaluation by that integer.

The same fixed integer multiplies each original coefficient. Scalar cast
transport and the unchanged descending tail account for the common factor. -/
public theorem evalIntegers_map_mul (point : Fraction.Rational) (initial : Int)
    (coefficients : List Int) :
    evalIntegers point (coefficients.map fun value => initial * value) =
      (initial : Fraction.Rational) * evalIntegers point coefficients := open Purelib.Algebra in by
  induction coefficients with
  | nil => exact (mul_zero (initial : Fraction.Rational)).symm
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.map_cons, evalIntegers_cons, Map.length_map,
        Ring.IntCast.intCast_mul, inductionHypothesis]
      ring1

/-! ## Homogeneous integer evaluation -/

/-- Traverse a descending homogeneous tail with its retained scalar operations.

Exact integers and bounded residues use the same ordered accumulator and power
updates. The final coefficient needs no further denominator multiplication.
-/
@[expose, specialize 2 3] public def evalFromWith {Scalar : Type}
    (multiply add : Scalar → Scalar → Scalar) (num den power accumulator : Scalar) :
    List Scalar → Scalar
  | [] => accumulator
  | [coefficient] => add (multiply accumulator num) (multiply coefficient power)
  | coefficient :: next :: remaining =>
      evalFromWith multiply add num den (multiply power den)
        (add (multiply accumulator num) (multiply coefficient power)) (next :: remaining)

/-- Evaluate an integer tail with the original accumulated value and denominator power. -/
private def evalFrom (num den power accumulator : Int) (coefficients : List Int) : Int :=
  evalFromWith (fun left right : Int => left * right) (fun left right : Int => left + right)
    num den power accumulator coefficients

/-- A scalar map preserving both operations preserves every homogeneous accumulator state.

The same original factors, coefficient order and final-step rule are retained.
Only pointwise scalar operation equalities transport the accumulated values.
-/
private theorem evalFromWith_map {Scalar : Type} (multiply add : Scalar → Scalar → Scalar)
    (map : Int → Scalar)
    (map_mul : ∀ left right, map (left * right) = multiply (map left) (map right))
    (map_add : ∀ left right, map (left + right) = add (map left) (map right))
    (num den power accumulator : Int) (coefficients : List Int) :
    evalFromWith multiply add (map num) (map den) (map power) (map accumulator)
        (coefficients.map map) =
      map (evalFrom num den power accumulator coefficients) := by
  induction coefficients generalizing power accumulator with
  | nil => rfl
  | cons coefficient remaining ih =>
      cases remaining with
      | nil =>
          change add (multiply (map accumulator) (map num)) (multiply (map coefficient) (map power)) =
            map (accumulator * num + coefficient * power)
          rewrite [map_add, map_mul, map_mul]
          rfl
      | cons next remaining =>
          change evalFromWith multiply add (map num) (map den)
              (multiply (map power) (map den))
              (add (multiply (map accumulator) (map num)) (multiply (map coefficient) (map power)))
              ((next :: remaining).map map) =
            map (evalFrom num den (power * den) (accumulator * num + coefficient * power)
              (next :: remaining))
          rewrite [← map_mul, ← map_mul, ← map_mul, ← map_add]
          exact ih (power * den) (accumulator * num + coefficient * power)

/-- Execute homogeneous evaluation with one forward integer accumulator and denominator-power cache.

The original leading coefficient initializes the accumulator. The unchanged
ordered tail consumes successive powers by multiplication, without retaining
a separate numerator power at every recursive head.
-/
public def eval (num : Int) (den : Nat) : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      let denominator : Int := den
      evalFrom num denominator denominator coefficient remaining

/-- High-to-low homogeneous evaluation.  For `m+1` coefficients it is the
ordinary rational evaluation at `num/den`, multiplied by `den^m`.

Each original head contributes its numerator power at the retained tail length.
The original natural denominator multiplies the recursive evaluation of that tail. -/
@[expose, implemented_by eval] public def homogeneousEval (num : Int) (den : Nat) : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      coefficient * num ^ remaining.length +
        (den : Int) * homogeneousEval num den remaining

/-- The forward accumulator contributes its exact numerator power beside the original homogeneous tail.

Both factors and the remaining coefficient order are arbitrary, including
zero denominators and negative numerators. The invariant identifies the whole
integer value before any rational denominator interpretation is required.
-/
private theorem evalFrom_eq (num : Int) (den : Nat) (power accumulator : Int) (coefficients : List Int) :
    evalFrom num (den : Int) power accumulator coefficients =
      accumulator * num ^ coefficients.length + power * homogeneousEval num den coefficients := by
  induction coefficients generalizing power accumulator with
  | nil =>
      change accumulator = accumulator * num ^ 0 + power * 0
      rewrite [Arithmetic.pow_zero, Arithmetic.mul_one, Int.mul_zero, Int.add_zero]
      rfl
  | cons coefficient remaining ih =>
      cases remaining with
      | nil =>
          change accumulator * num + coefficient * power =
            accumulator * num ^ 1 + power * (coefficient * num ^ 0 + (den : Int) * 0)
          rewrite [Arithmetic.pow_succ, Arithmetic.pow_zero]
          ring1
      | cons next remaining =>
          change evalFrom num (den : Int) (power * (den : Int))
              (accumulator * num + coefficient * power) (next :: remaining) = _
          rewrite [ih]
          change (accumulator * num + coefficient * power) * num ^ (next :: remaining).length +
              (power * (den : Int)) * homogeneousEval num den (next :: remaining) =
            accumulator * num ^ ((next :: remaining).length + 1) +
              power * (coefficient * num ^ (next :: remaining).length +
                (den : Int) * homogeneousEval num den (next :: remaining))
          rewrite [Arithmetic.pow_succ]
          ring1

/-- The executable accumulator returns the complete original homogeneous integer for every input.

The original recursive definition remains the logical unfolding contract.
This pointwise equality also retains the executable target in the mathematical
proof closure independently of its compiler replacement attribute.
-/
private theorem eval_eq (num : Int) (den : Nat) (coefficients : List Int) :
    eval num den coefficients = homogeneousEval num den coefficients := by
  cases coefficients with
  | nil => rfl
  | cons coefficient remaining =>
      exact evalFrom_eq num den (den : Int) coefficient remaining

/-- Evaluate a retained residue table with the same homogeneous accumulator.

The original signed numerator and natural denominator are reduced directly.
Every subsequent scalar operation stays in the supplied finite residue carrier;
no large integer power or recursive numerical cast is constructed.
-/
@[expose] public def modularEval (modulus : Nat) [NeZero modulus] (num : Int) (den : Nat) :
    List (Fin modulus) → Fin modulus
  | [] => 0
  | coefficient :: remaining =>
      let numerator : Fin modulus := Fin.intCast num
      let denominator := Fin.ofNat modulus den
      evalFromWith Fin.mul Fin.add numerator denominator denominator coefficient remaining

/-- Reducing the original coefficient table preserves the complete homogeneous value in finite residues.

The original finite-ring operations and casts are retained. Direct signed casts
agree with that ring, and the shared accumulator transports each scalar update.
-/
public theorem modularEval_eq (modulus : Nat) [NeZero modulus] (num : Int) (den : Nat)
    (coefficients : List Int) :
    modularEval modulus num den (coefficients.map Fin.intCast) =
      Fin.intCast (homogeneousEval num den coefficients) := by
  letI := Modular.Fin.finCommRing modulus
  have map_mul (left right : Int) :
      Fin.intCast (left * right) = (Fin.intCast left : Fin modulus) * Fin.intCast right := by
    rewrite [Modular.Fin.intCast_eq modulus, Ring.IntCast.intCast_mul,
      Modular.Fin.intCast_eq modulus, Modular.Fin.intCast_eq modulus]
    rfl
  have map_add (left right : Int) :
      Fin.intCast (left + right) = (Fin.intCast left : Fin modulus) + Fin.intCast right := by
    rewrite [Modular.Fin.intCast_eq modulus, Ring.IntCast.add,
      Modular.Fin.intCast_eq modulus, Modular.Fin.intCast_eq modulus]
    rfl
  cases coefficients with
  | nil => rfl
  | cons coefficient remaining =>
      have mapped := evalFromWith_map Fin.mul Fin.add (fun value : Int => (Fin.intCast value : Fin modulus))
        map_mul map_add num (den : Int) (den : Int) coefficient remaining
      exact mapped.trans (congrArg (fun value : Int => (Fin.intCast value : Fin modulus))
        (eval_eq num den (coefficient :: remaining)))

/-- Last high-to-low coefficient, with zero only for the empty list. -/
@[expose] public def constantCoefficient : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

/-- A singleton descending coefficient list has its sole entry as constant coefficient. -/
@[simp] public theorem constantCoefficient_singleton (coefficient : Int) :
    constantCoefficient [coefficient] = coefficient := rfl

/-- Removing a leading entry from a list with at least two coefficients preserves the constant coefficient.

The last-entry accumulator overwrites the first retained coefficient with
the next one before scanning the unchanged remaining table. -/
@[simp] public theorem constantCoefficient_cons_cons
    (leading next : Int) (remaining : List Int) :
    constantCoefficient (leading :: next :: remaining) =
      constantCoefficient (next :: remaining) := rfl

/-- Every term below the leading term contains the displayed denominator.

The exact recursive tail evaluation is the retained integer divisibility
witness after removing the displayed leading monomial. -/
public theorem denominator_dvd_homogeneousEval_sub_leading
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    (den : Int) ∣
      homogeneousEval num den (leading :: remaining) -
        leading * num ^ remaining.length := by
  refine ⟨homogeneousEval num den remaining, ?_⟩
  simp only [homogeneousEval]
  ring1

/-- Every term above the constant term contains the displayed numerator.

Structural recursion retains the original constant coefficient and denominator
power. Each preceding original head contributes to the explicit integer factor. -/
public theorem numerator_dvd_homogeneousEval_sub_constant
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    num ∣
      homogeneousEval num den (leading :: remaining) -
        constantCoefficient (leading :: remaining) *
          (den : Int) ^ remaining.length := by
  induction remaining generalizing leading with
  | nil =>
      refine ⟨0, ?_⟩
      rewrite [homogeneousEval, homogeneousEval, constantCoefficient_singleton,
        List.length_nil, Arithmetic.pow_zero]
      ring1
  | cons next remaining inductionHypothesis =>
      rcases inductionHypothesis next with ⟨factor, factorization⟩
      refine ⟨leading * num ^ remaining.length + (den : Int) * factor, ?_⟩
      simp only [homogeneousEval, constantCoefficient_cons_cons,
        List.length_cons, pow_succ]
      calc
        leading * (num ^ remaining.length * num) +
              (den : Int) * homogeneousEval num den (next :: remaining) -
            constantCoefficient (next :: remaining) *
              ((den : Int) ^ remaining.length * den) =
            num * (leading * num ^ remaining.length) +
              (den : Int) *
                (homogeneousEval num den (next :: remaining) -
                  constantCoefficient (next :: remaining) *
                    (den : Int) ^ remaining.length) := by
          ring1
        _ = num *
            (leading * num ^ remaining.length + (den : Int) * factor) := by
          rw [factorization]
          ring1

/-- Homogeneous integer evaluation clears the denominator power of rational evaluation.

For a nonempty coefficient list and positive natural denominator, its integer value embeds as the ordinary rational
evaluation multiplied by the denominator raised to the tail length. -/
public theorem homogeneousEval_cons_eq_scaled
    (num : Int) {den : Nat} (denPositive : 0 < den)
    (coefficient : Int) (remaining : List Int) :
    ((homogeneousEval num den (coefficient :: remaining) : Int) : Fraction.Rational) =
      (den : Fraction.Rational) ^ remaining.length *
        evalIntegers ((num : Fraction.Rational) / (den : Fraction.Rational))
          (coefficient :: remaining) := open Purelib.Algebra.Field in open Purelib.Algebra in by
  induction remaining generalizing coefficient with
  | nil =>
      rewrite [homogeneousEval, homogeneousEval, evalIntegers_cons, evalIntegers_nil,
        List.length_nil, Arithmetic.pow_zero, pow_zero, pow_zero,
        Arithmetic.mul_one, Int.mul_zero, Int.add_zero,
        mul_one, add_zero, one_mul]
      exact Eq.refl _
  | cons next remaining inductionHypothesis =>
      let denominator : Fraction.Rational := den
      let numerator : Fraction.Rational := num
      let point : Fraction.Rational := numerator / denominator
      have denominatorNonzero : denominator ≠ 0 := by
        change (den : Fraction.Rational) ≠ 0
        intro equal
        have denZero : den = 0 :=
          Fraction.Cast.Compatibility.natCast_injective_direct
            (equal.trans (Nat.cast_zero).symm)
        exact (Nat.ne_of_gt denPositive) denZero
      have pointClear : denominator * point = numerator := by
        change (den : Fraction.Rational) * ((num : Fraction.Rational) / (den : Fraction.Rational)) =
          (num : Fraction.Rational)
        rw [Fraction.Field.mul_comm]
        exact ExplicitField.div_mul_cancel _ denominatorNonzero
      have powerClear :
          denominator ^ (List.length (next :: remaining)) *
              point ^ (List.length (next :: remaining)) =
            numerator ^ (List.length (next :: remaining)) := by
        rewrite [← Semiring.Normalization.product_pow, pointClear]
        exact Eq.refl _
      change
        ((coefficient * num ^ (next :: remaining).length +
            (den : Int) * homogeneousEval num den (next :: remaining) : Int) :
            Fraction.Rational) =
          denominator ^ (List.length (next :: remaining)) *
            evalIntegers point (coefficient :: next :: remaining)
      rw [Ring.IntCast.add, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_pow,
        Int.cast_natCast, inductionHypothesis]
      conv_rhs =>
        rw [evalIntegers_cons point coefficient (next :: remaining)]
      change
        (coefficient : Fraction.Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
          denominator ^ (List.length (next :: remaining)) *
            ((coefficient : Fraction.Rational) *
                point ^ (List.length (next :: remaining)) +
              evalIntegers point (next :: remaining))
      calc
        (coefficient : Fraction.Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
            (coefficient : Fraction.Rational) *
                (denominator ^ (List.length (next :: remaining)) *
                  point ^ (List.length (next :: remaining))) +
              (denominator * denominator ^ remaining.length) *
                evalIntegers point (next :: remaining) := by
          rw [powerClear]
          ring1
        _ = _ := by
          rw [List.length_cons, pow_succ]
          ring1

end Purelib.Polynomial.Dense.Integer.Homogeneous
