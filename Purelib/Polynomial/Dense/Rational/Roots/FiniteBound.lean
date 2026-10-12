module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.DropWhile.Basic
import Purelib.Algebra.Group.Negation
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Division.Synthetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite root bounds for descending rational polynomials

Synthetic division removes one displayed root while retaining the original
quotient and remainder. The quotient's strictly shorter normalized coefficient
list bounds every remaining distinct root by induction on coefficient count.
-/

open Purelib
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Polynomial.Dense.Rational.Roots.FiniteBound

/-- A nonzero rational polynomial has fewer distinct displayed roots than normalized coefficient slots.

The original duplicate-free root list and its pointwise zero evaluations
are retained. Synthetic division at its head keeps the same quotient,
remainder and factor identity while strictly decreasing coefficient count. -/
public theorem nodup_zeros_length_lt_degreeCount (p : Dense.Rational.Basic.CoordinatePolynomial)
    (nonzero : p.isZero = false) (points : List Fraction.Rational)
    (nodup : points.Nodup)
    (zeros : ∀ x ∈ points, p.eval x = 0) :
    points.length < p.degreeCount := by
  generalize degreeEquation : p.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p points with
  | h degree inductionHypothesis =>
      have degreePositive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil =>
          simp only [List.length_nil]
          exact degreePositive
      | cons root otherPoints =>
          have distinctFields : (∀ value ∈ otherPoints, root ≠ value) ∧
              otherPoints.Nodup := by
            cases nodup with
            | cons headDistinct tailDistinct => exact ⟨headDistinct, tailDistinct⟩
          rcases distinctFields with ⟨headDistinct, tailNodup⟩
          have normalizedNonempty : p.normalize.coeffs ≠ [] := by
            intro empty
            have normalizedNonzero := nonzero
            change p.normalize.coeffs.isEmpty = false at normalizedNonzero
            rw [empty] at normalizedNonzero
            exact Bool.noConfusion normalizedNonzero
          cases coefficientsEquation : p.normalize.coeffs with
          | nil => exact (normalizedNonempty coefficientsEquation).elim
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have headNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
                change p.normalize.coeffs.headD 0 ≠ 0 at headNonzero
                rw [coefficientsEquation] at headNonzero
                exact headNonzero
              cases remaining with
              | nil =>
                  have rootZero := zeros root (List.Mem.head otherPoints)
                  have normalizedRootZero : p.normalize.eval root = 0 := by
                    rw [Dense.Basic.DensePolynomial.eval_normalize]
                    exact rootZero
                  change Dense.Basic.DensePolynomial.evalCoeffs root p.normalize.coeffs = 0 at normalizedRootZero
                  rw [coefficientsEquation] at normalizedRootZero
                  rw [Dense.Basic.DensePolynomial.evalCoeffs_cons] at normalizedRootZero
                  exact (leadingNonzero normalizedRootZero).elim
              | cons coefficient remaining =>
                  let division := Dense.Rational.Division.Synthetic.syntheticAux root leading
                    (coefficient :: remaining)
                  let quotient : (Dense.Basic.DensePolynomial Fraction.Rational) := ⟨division.1⟩
                  have divisionSpec := Dense.Rational.Division.Synthetic.syntheticAux_spec root leading
                    (coefficient :: remaining)
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (Dense.Rational.Division.Synthetic.syntheticAux root
                          (leading * root + coefficient) remaining).1 := rfl
                  have leadingRetained : decide (leading = 0) = false := by
                    cases selected : decide (leading = 0) with
                    | false => rfl
                    | true =>
                        exact (leadingNonzero (of_decide_eq_true selected)).elim
                  have quotientNormalizedCoefficients :
                      quotient.normalize.coeffs = quotient.coeffs := by
                    rw [Dense.Basic.DensePolynomial.normalize_coeffs,
                      quotientCoefficients]
                    exact DropWhile.cons_of_false
                      (fun value : Fraction.Rational => decide (value = 0)) leading
                      (Dense.Rational.Division.Synthetic.syntheticAux root
                        (leading * root + coefficient) remaining).1 leadingRetained
                  have quotientNonzero : quotient.isZero = false := by
                    calc
                      quotient.isZero = quotient.normalize.coeffs.isEmpty := rfl
                      _ = quotient.coeffs.isEmpty :=
                        congrArg List.isEmpty quotientNormalizedCoefficients
                      _ = false := by
                        rw [quotientCoefficients]
                        rfl
                  have quotientDegree : quotient.degreeCount =
                      (coefficient :: remaining).length := by
                    calc
                      quotient.degreeCount = quotient.normalize.coeffs.length :=
                        rfl
                      _ = quotient.coeffs.length :=
                        congrArg List.length quotientNormalizedCoefficients
                      _ = division.1.length := rfl
                      _ = (coefficient :: remaining).length := divisionSpec.1
                  have originalDegree : p.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    exact congrArg List.length coefficientsEquation
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    exact Nat.lt_succ_self _
                  have remainderZero : division.2 = 0 := by
                    rw [divisionSpec.2.1]
                    rw [← coefficientsEquation]
                    change p.normalize.eval root = 0
                    rw [Dense.Basic.DensePolynomial.eval_normalize]
                    exact zeros root (List.Mem.head otherPoints)
                  have otherZeros : ∀ x ∈ otherPoints,
                      quotient.eval x = 0 := by
                    intro x member
                    have originalZero := zeros x (List.Mem.tail root member)
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
                    have distinct : x ≠ root := by
                      intro equal
                      exact headDistinct x member equal.symm
                    have differenceNonzero : x - root ≠ 0 := by
                      intro equal
                      apply distinct
                      calc
                        x = (x - root) + root := by ring1
                        _ = 0 + root :=
                          congrArg (fun value : Fraction.Rational => value + root) equal
                        _ = root := by ring1
                    by_cases quotientZero : quotient.eval x = 0
                    · exact quotientZero
                    · have productNonzero :
                          (x - root) * quotient.eval x ≠ 0 :=
                        Fraction.Field.mul_ne_zero_direct
                          differenceNonzero quotientZero
                      exact (productNonzero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    tailNodup otherZeros rfl
                  simp only [List.length_cons]
                  exact (Nat.succ_le_of_lt recursive).trans_lt quotientSmaller

end Purelib.Polynomial.Dense.Rational.Roots.FiniteBound
