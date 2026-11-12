module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.DropWhile.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Synthetic
public import Purelib.Polynomial.Dense.Evaluation
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
                  let division := Division.Synthetic.divide ⟨leading :: coefficient :: remaining⟩ root
                  let quotient := division.quotient
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (Division.Synthetic.divide
                          ⟨(leading * root + coefficient) :: remaining⟩ root).quotient.coeffs :=
                    Division.Synthetic.divide_cons_cons root leading coefficient remaining
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
                      _ = division.quotient.coeffs.length := rfl
                      _ = (coefficient :: remaining).length := division.quotient_length
                  have originalDegree : polynomial.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    change polynomial.normalize.coeffs.length = _
                    rewrite [coefficientsEquation]
                    exact Eq.refl _
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    exact Nat.lt_succ_self _
                  have remainderZero : division.remainder = 0 := by
                    rw [division.remainder_eval, ← coefficientsEquation]
                    change polynomial.normalize.eval root = 0
                    rw [Basic.DensePolynomial.eval_normalize]
                    exact zeros root List.mem_cons_self
                  have otherZeros : ∀ point ∈ otherPoints,
                      quotient.eval point = 0 := by
                    intro point member
                    have originalZero := zeros point (List.mem_cons_of_mem root member)
                    have factor : polynomial.normalize.eval point =
                        (point - root) * quotient.eval point + division.remainder :=
                      (congrArg (Basic.DensePolynomial.evalCoeffs point) coefficientsEquation).trans
                        (division.eval_eq point)
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
