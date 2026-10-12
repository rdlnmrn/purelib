module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Root bounds from retained finite synthetic division

Synthetic division keeps the original coefficient list, quotient and remainder.
Removing one displayed zero decreases the retained normalized coefficient count
and preserves all remaining distinct zero witnesses. This gives a finite root
bound over explicit fields and the retained Gaussian rational realization.
-/

namespace Purelib.Polynomial.Dense.RootBound

open Purelib.Polynomial.Dense
open Purelib.Algebra.Field
open Purelib.Data.List
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The descending dense polynomial representation over the given coefficient type. -/
public abbrev CoefficientPolynomial (K : Type*) :=
  Basic.DensePolynomial K

namespace Extensionality

/-- Synthetic division through one displayed root.

Each original coefficient updates the retained Horner accumulator and emits
its previous value as the next quotient coefficient. The final accumulator
is the remainder at the supplied root. -/
@[expose] public def syntheticAux (root leading : K) : List K → List K × K
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := Purelib.Polynomial.Dense.RootBound.Extensionality.syntheticAux root (leading * root + coefficient)
        remaining
      (leading :: result.1, result.2)

omit [DecidableEq K] in
/-- Split descending Horner evaluation into the leading monomial and the remaining coefficients.

The original finite Horner fold contributes the displayed leading coefficient
at the power determined by the retained tail length; the tail contributes its
unchanged own evaluation. -/
private theorem evalCoeffs_cons_power (x leading : K)
    (remaining : List K) :
    Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
      leading * x ^ remaining.length + Basic.DensePolynomial.evalCoeffs x remaining := by
  induction remaining generalizing leading with
  | nil =>
      simp only [Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil, List.length_nil, pow_zero,
        Basic.DensePolynomial.evalCoeffs_nil]
      ring0
  | cons coefficient remaining inductionHypothesis =>
      rw [Basic.DensePolynomial.evalCoeffs_cons]
      simp only [List.foldl_cons]
      rw [← Basic.DensePolynomial.evalCoeffs_cons x (leading * x + coefficient) remaining,
        inductionHypothesis (leading * x + coefficient),
        inductionHypothesis coefficient]
      simp only [List.length_cons, pow_succ]
      ring0

omit [DecidableEq K] in
/-- Certify the quotient length, remainder evaluation and synthetic-division identity.

For each displayed point, the original list evaluates as the linear factor times the quotient plus the retained
remainder. -/
private theorem syntheticAux_spec (root leading : K) (remaining : List K) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = Basic.DensePolynomial.evalCoeffs root (leading :: remaining) ∧
      ∀ x : K,
        Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
          (x - root) * Basic.DensePolynomial.evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      change
        [].length = [].length ∧
          leading = Basic.DensePolynomial.evalCoeffs root [leading] ∧
          ∀ x : K, Basic.DensePolynomial.evalCoeffs x [leading] =
            (x - root) * Basic.DensePolynomial.evalCoeffs x [] + leading
      constructor
      · exact rfl
      constructor
      · rewrite [Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil]
        exact Eq.refl _
      · intro x
        rewrite [Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil,
          Basic.DensePolynomial.evalCoeffs_nil, mul_zero, zero_add]
        exact Eq.refl _
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = Basic.DensePolynomial.evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : K,
          Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) =
            (x - root) * Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 = Basic.DensePolynomial.evalCoeffs root
            (leading :: coefficient :: remaining) ∧
          ∀ x : K,
            Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [Basic.DensePolynomial.evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← Basic.DensePolynomial.evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                  Basic.DensePolynomial.evalCoeffs x remaining := by
            rw [evalCoeffs_cons_power x leading (coefficient :: remaining),
              evalCoeffs_cons_power x coefficient remaining]
            simp only [List.length_cons]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) := by
            rw [evalCoeffs_cons_power x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * Basic.DensePolynomial.evalCoeffs x recursive.1 +
                  recursive.2) := by rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  Basic.DensePolynomial.evalCoeffs x recursive.1) + recursive.2 := by ring0
          _ = (x - root) * Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

/-- A nonzero finite dense polynomial has fewer displayed distinct roots than coefficient slots.

Synthetic division retains the original quotient coefficients and remainder.
Removing one displayed root decreases the normalized coefficient count while
preserving the remaining distinct zero witnesses. -/
public theorem nodup_zeros_length_lt_degreeCount
    (polynomial : CoefficientPolynomial K) (nonzero : polynomial.isZero = false)
    (points : List K) (nodup : points.Nodup)
    (zeros : ∀ point ∈ points, polynomial.eval point = 0) :
    points.length < polynomial.degreeCount := by
  generalize degreeEquation : polynomial.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing polynomial points with
  | h degree inductionHypothesis =>
      have degreePositive := Basic.DensePolynomial.degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil => exact degreePositive
      | cons root otherPoints =>
          have rootFresh : ∀ point ∈ otherPoints, root ≠ point := by
            cases nodup with
            | cons fresh _ => exact fresh
          have otherNodup : otherPoints.Nodup := by
            cases nodup with
            | cons _ tail => exact tail
          cases coefficientsEquation : polynomial.normalize.coeffs with
          | nil =>
              change polynomial.normalize.coeffs.isEmpty = false at nonzero
              rw [coefficientsEquation] at nonzero
              exact Bool.noConfusion nonzero
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have canonical := Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
                change polynomial.normalize.coeffs.headD 0 ≠ 0 at canonical
                rw [coefficientsEquation] at canonical
                exact canonical
              cases remaining with
              | nil =>
                  have rootZero := zeros root List.mem_cons_self
                  have normalizedRootZero : polynomial.normalize.eval root = 0 := by
                    rewrite [Basic.DensePolynomial.eval_normalize]
                    exact rootZero
                  change Basic.DensePolynomial.evalCoeffs root polynomial.normalize.coeffs = 0 at normalizedRootZero
                  rw [coefficientsEquation] at normalizedRootZero
                  simp only [Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil] at normalizedRootZero
                  exact (leadingNonzero normalizedRootZero).elim
              | cons coefficient remaining =>
                  let division := syntheticAux root leading
                    (coefficient :: remaining)
                  let quotient : CoefficientPolynomial K := ⟨division.1⟩
                  have divisionSpec := syntheticAux_spec root leading
                    (coefficient :: remaining)
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (syntheticAux root
                          (leading * root + coefficient) remaining).1 := rfl
                  have quotientNonzero : quotient.isZero = false := by
                    change quotient.normalize.coeffs.isEmpty = false
                    rewrite [Basic.DensePolynomial.normalize_coeffs, quotientCoefficients,
                      DropWhile.cons_of_false (fun value : K => decide (value = 0))
                        leading _ (decide_eq_false leadingNonzero)]
                    exact Eq.refl _
                  have quotientDegree : quotient.degreeCount =
                      (coefficient :: remaining).length := by
                    calc
                      quotient.degreeCount = quotient.normalize.coeffs.length :=
                        rfl
                      _ = quotient.coeffs.length := by
                        rw [Basic.DensePolynomial.normalize_coeffs, quotientCoefficients,
                          DropWhile.cons_of_false _ leading _
                            (decide_eq_false leadingNonzero)]
                      _ = division.1.length := rfl
                      _ = (coefficient :: remaining).length := divisionSpec.1
                  have originalDegree : polynomial.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    change polynomial.normalize.coeffs.length = _
                    rewrite [coefficientsEquation]
                    exact Eq.refl _
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    exact Nat.lt_succ_self _
                  have remainderZero : division.2 = 0 := by
                    rw [divisionSpec.2.1, ← coefficientsEquation]
                    change polynomial.normalize.eval root = 0
                    rw [Basic.DensePolynomial.eval_normalize]
                    exact zeros root List.mem_cons_self
                  have otherZeros : ∀ point ∈ otherPoints,
                      quotient.eval point = 0 := by
                    intro point member
                    have originalZero := zeros point (List.mem_cons_of_mem root member)
                    have factor := divisionSpec.2.2 point
                    rw [← coefficientsEquation] at factor
                    change polynomial.normalize.eval point =
                      (point - root) * quotient.eval point + division.2 at factor
                    rw [Basic.DensePolynomial.eval_normalize, originalZero, remainderZero] at factor
                    have productZero :
                        (point - root) * quotient.eval point = 0 := by
                      calc
                        (point - root) * quotient.eval point =
                            (point - root) * quotient.eval point + 0 := by ring0
                        _ = 0 := factor.symm
                    have distinct : point ≠ root := fun equal =>
                      rootFresh point member equal.symm
                    have differenceNonzero : point - root ≠ 0 := by
                      intro zero
                      apply distinct
                      calc
                        point = (point - root) + root := by
                          rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
                        _ = root := by rw [zero, zero_add]
                    by_cases quotientZero : quotient.eval point = 0
                    · exact quotientZero
                    · exact (ExplicitField.mul_ne_zero
                        differenceNonzero quotientZero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    otherNodup otherZeros rfl
                  simp only [List.length_cons]
                  exact (Nat.succ_le_of_lt recursive).trans_lt quotientSmaller
end Extensionality

end Purelib.Polynomial.Dense.RootBound

/-!
# Finite root bounds over constructive Gaussian rationals

A nonzero dense polynomial cannot vanish at as many distinct displayed
Gaussian rationals as it has normalized coefficient slots.  Synthetic
division proves this directly.  The resulting bounded scan supplies one
explicit nonzero evaluation without forming or quantifying over a root set.
-/

namespace Purelib.Polynomial.Dense.RootBound.Roots

open Purelib.Polynomial
open Purelib.Data
open Purelib.Algebra.Field
open Purelib.Data.List
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- Perform synthetic division of a descending Gaussian coefficient list.

The supplied leading accumulator starts the scan; each step emits one quotient coefficient and updates the accumulator,
ending with the remainder. -/
@[expose] public def syntheticAux (root leading : Gaussian.Basic.Canonical) :
    List Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical × Gaussian.Basic.Canonical
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := Purelib.Polynomial.Dense.RootBound.Roots.syntheticAux root (leading * root + coefficient) remaining
      (leading :: result.1, result.2)

/-- Split descending Horner evaluation into the leading monomial and the remaining coefficients.

The original finite Horner fold contributes the displayed leading coefficient
at the power determined by the retained tail length; the tail contributes its
unchanged own evaluation. -/
private theorem evalCoeffs_cons_power (x leading : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) :
    Dense.Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
      leading * x ^ remaining.length + Dense.Basic.DensePolynomial.evalCoeffs x remaining := by
  induction remaining generalizing leading with
  | nil =>
      simp only [Dense.Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil, List.length_nil, pow_zero,
        Dense.Basic.DensePolynomial.evalCoeffs_nil]
      ring1
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.Basic.DensePolynomial.evalCoeffs_cons]
      simp only [List.foldl_cons]
      rw [← Dense.Basic.DensePolynomial.evalCoeffs_cons x (leading * x + coefficient) remaining,
        inductionHypothesis (leading * x + coefficient),
        inductionHypothesis coefficient]
      simp only [List.length_cons, pow_succ]
      ring1

/-- Certify the quotient length, remainder evaluation and synthetic-division identity.

For each displayed point, the original list evaluates as the linear factor times the quotient plus the retained
remainder. -/
private theorem syntheticAux_spec (root leading : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = Dense.Basic.DensePolynomial.evalCoeffs root (leading :: remaining) ∧
      ∀ x : Gaussian.Basic.Canonical,
        Dense.Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
          (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      constructor
      · rfl
      constructor
      · change leading = Dense.Basic.DensePolynomial.evalCoeffs root [leading]
        rewrite [Dense.Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil]
        exact Eq.refl _
      · intro x
        change Dense.Basic.DensePolynomial.evalCoeffs x [leading] =
          (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x [] + leading
        rewrite [Dense.Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil,
          Dense.Basic.DensePolynomial.evalCoeffs_nil, mul_zero, zero_add]
        exact Eq.refl _
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = Dense.Basic.DensePolynomial.evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : Gaussian.Basic.Canonical,
          Dense.Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) =
            (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 =
            Dense.Basic.DensePolynomial.evalCoeffs root (leading :: coefficient :: remaining) ∧
          ∀ x : Gaussian.Basic.Canonical,
            Dense.Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [Dense.Basic.DensePolynomial.evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← Dense.Basic.DensePolynomial.evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          Dense.Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                  Dense.Basic.DensePolynomial.evalCoeffs x remaining := by
            rw [evalCoeffs_cons_power x leading (coefficient :: remaining),
              evalCoeffs_cons_power x coefficient remaining]
            simp only [List.length_cons]
            ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                Dense.Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) := by
            rw [evalCoeffs_cons_power x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            let power := x ^ remaining.length
            change leading * (power * x) + coefficient * power +
                Dense.Basic.DensePolynomial.evalCoeffs x remaining =
              (x - root) * (leading * power) +
                ((leading * root + coefficient) * power +
                  Dense.Basic.DensePolynomial.evalCoeffs x remaining)
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.add_re,
                Gaussian.Basic.add_im,
                Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im] <;>
              ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * Dense.Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2) := by
            rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  Dense.Basic.DensePolynomial.evalCoeffs x recursive.1) + recursive.2 := by ring1
          _ = (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

/-- A nonzero Gaussian polynomial has fewer displayed distinct roots than coefficient slots.

The original synthetic quotient preserves the remaining zero witnesses after
one displayed root is removed. Its leading nonzero coefficient makes the
retained coefficient count strictly smaller. -/
public theorem nodup_zeros_length_lt_degreeCount
    (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : p.isZero = false)
    (points : List Gaussian.Basic.Canonical) (nodup : points.Nodup)
    (zeros : ∀ x ∈ points, p.eval x = 0) :
    points.length < p.degreeCount := by
  generalize degreeEquation : p.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p points with
  | h degree inductionHypothesis =>
      have degreePositive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil => exact degreePositive
      | cons root otherPoints =>
          have rootFresh : ∀ point ∈ otherPoints, root ≠ point := by
            cases nodup with
            | cons fresh _ => exact fresh
          have otherNodup : otherPoints.Nodup := by
            cases nodup with
            | cons _ tail => exact tail
          cases coefficientsEquation : p.normalize.coeffs with
          | nil =>
              change p.normalize.coeffs.isEmpty = false at nonzero
              rw [coefficientsEquation] at nonzero
              exact Bool.noConfusion nonzero
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have canonical := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
                change p.normalize.coeffs.headD 0 ≠ 0 at canonical
                rw [coefficientsEquation] at canonical
                exact canonical
              cases remaining with
              | nil =>
                  have rootZero := zeros root List.mem_cons_self
                  have normalizedRootZero : p.normalize.eval root = 0 := by
                    rewrite [Dense.Basic.DensePolynomial.eval_normalize]
                    exact rootZero
                  change Dense.Basic.DensePolynomial.evalCoeffs root p.normalize.coeffs = 0 at normalizedRootZero
                  rw [coefficientsEquation] at normalizedRootZero
                  simp only [Dense.Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil] at normalizedRootZero
                  exact (leadingNonzero normalizedRootZero).elim
              | cons coefficient remaining =>
                  let division := syntheticAux root leading
                    (coefficient :: remaining)
                  let quotient : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨division.1⟩
                  have divisionSpec := syntheticAux_spec root leading
                    (coefficient :: remaining)
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (syntheticAux root
                          (leading * root + coefficient) remaining).1 := rfl
                  have quotientNonzero : quotient.isZero = false := by
                    change quotient.normalize.coeffs.isEmpty = false
                    rewrite [Dense.Basic.DensePolynomial.normalize_coeffs, quotientCoefficients,
                      DropWhile.cons_of_false
                        (fun value : Gaussian.Basic.Canonical => decide (value = 0))
                        leading _ (decide_eq_false leadingNonzero)]
                    exact Eq.refl _
                  have quotientDegree : quotient.degreeCount =
                      (coefficient :: remaining).length := by
                    calc
                      quotient.degreeCount = quotient.normalize.coeffs.length :=
                        rfl
                      _ = quotient.coeffs.length := by
                        rw [Dense.Basic.DensePolynomial.normalize_coeffs, quotientCoefficients,
                          DropWhile.cons_of_false _ leading _
                            (decide_eq_false leadingNonzero)]
                      _ = division.1.length := rfl
                      _ = (coefficient :: remaining).length := divisionSpec.1
                  have originalDegree : p.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    change p.normalize.coeffs.length = _
                    rewrite [coefficientsEquation]
                    exact Eq.refl _
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    exact Nat.lt_succ_self _
                  have remainderZero : division.2 = 0 := by
                    rw [divisionSpec.2.1]
                    rw [← coefficientsEquation]
                    change p.normalize.eval root = 0
                    rw [Dense.Basic.DensePolynomial.eval_normalize]
                    exact zeros root List.mem_cons_self
                  have otherZeros : ∀ x ∈ otherPoints,
                      quotient.eval x = 0 := by
                    intro x member
                    have originalZero := zeros x (List.mem_cons_of_mem root member)
                    have factor := divisionSpec.2.2 x
                    rw [← coefficientsEquation] at factor
                    change p.normalize.eval x =
                      (x - root) * quotient.eval x + division.2 at factor
                    rw [Dense.Basic.DensePolynomial.eval_normalize, originalZero, remainderZero] at factor
                    have productZero : (x - root) * quotient.eval x = 0 := by
                      calc
                        (x - root) * quotient.eval x =
                            (x - root) * quotient.eval x + 0 := by ring1
                        _ = 0 := factor.symm
                    have distinct : x ≠ root := fun equal =>
                      rootFresh x member equal.symm
                    have differenceNonzero : x - root ≠ 0 := by
                      intro zero
                      apply distinct
                      calc
                        x = (x - root) + root := by
                          rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
                        _ = root := by rw [zero, zero_add]
                    by_cases quotientZero : quotient.eval x = 0
                    · exact quotientZero
                    · exact
                        (Gaussian.Field.mul_ne_zero_direct
                          differenceNonzero quotientZero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    otherNodup otherZeros rfl
                  simp only [List.length_cons]
                  exact (Nat.succ_le_of_lt recursive).trans_lt quotientSmaller
end Purelib.Polynomial.Dense.RootBound.Roots
