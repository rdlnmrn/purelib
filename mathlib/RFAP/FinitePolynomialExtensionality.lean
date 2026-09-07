import mathlib.RFAP.ComputablePolynomial
import mathlib.RFAP.ConstructiveFraction
import mathlib.RFAP.FiniteTotient
import mathlib.Tactic.QuotientFreeOmega

/-!
# Finite extensionality for executable dense polynomials

This module proves the coefficient extensionality needed by the finite
cyclotomic construction.  A nonzero dense polynomial cannot vanish at as
many explicitly listed points as it has normalized coefficient slots.  For
the project's constructive rationals, the bounded list `0, ..., d-1`
therefore decides equality of two normalized polynomials of coefficient
count at most `d`.

Every construction is a recursion over coefficient or point lists.  No
carrier-wide root set or infinite evaluation principle is used.
-/

namespace RFAP.FinitePolynomialExtensionality

open RFAP.ComputablePolynomial.DensePolynomial

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

abbrev Polynomial (K : Type*) :=
  RFAP.ComputablePolynomial.DensePolynomial K

/-- Synthetic division through one displayed root. -/
def syntheticAux (root leading : K) : List K → List K × K
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := syntheticAux root (leading * root + coefficient) remaining
      (leading :: result.1, result.2)

omit [DecidableEq K] in
private theorem evalCoeffs_cons_power (x leading : K)
    (remaining : List K) :
    evalCoeffs x (leading :: remaining) =
      leading * x ^ remaining.length + evalCoeffs x remaining := by
  induction remaining generalizing leading with
  | nil =>
      simp only [evalCoeffs_cons, List.foldl_nil, List.length_nil, pow_zero,
        evalCoeffs_nil]
      ring0
  | cons coefficient remaining inductionHypothesis =>
      rw [evalCoeffs_cons]
      simp only [List.foldl_cons]
      rw [← evalCoeffs_cons x (leading * x + coefficient) remaining,
        inductionHypothesis (leading * x + coefficient),
        inductionHypothesis coefficient]
      simp only [List.length_cons, pow_succ]
      ring0

omit [DecidableEq K] in
private theorem syntheticAux_spec (root leading : K) (remaining : List K) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = evalCoeffs root (leading :: remaining) ∧
      ∀ x : K,
        evalCoeffs x (leading :: remaining) =
          (x - root) * evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      change
        [].length = [].length ∧
          leading = evalCoeffs root [leading] ∧
          ∀ x : K, evalCoeffs x [leading] =
            (x - root) * evalCoeffs x [] + leading
      constructor
      · exact rfl
      constructor
      · simp only [evalCoeffs_cons, List.foldl_nil]
      · intro x
        simp only [evalCoeffs_cons, List.foldl_nil, evalCoeffs_nil,
          mul_zero, zero_add]
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : K,
          evalCoeffs x (nextLeading :: remaining) =
            (x - root) * evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 = evalCoeffs root
            (leading :: coefficient :: remaining) ∧
          ∀ x : K,
            evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                  evalCoeffs x remaining := by
            rw [evalCoeffs_cons_power x leading (coefficient :: remaining),
              evalCoeffs_cons_power x coefficient remaining]
            simp only [List.length_cons]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                evalCoeffs x (nextLeading :: remaining) := by
            rw [evalCoeffs_cons_power x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * evalCoeffs x recursive.1 +
                  recursive.2) := by rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  evalCoeffs x recursive.1) + recursive.2 := by ring0
          _ = (x - root) * evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

/-- A nonzero finite dense polynomial has fewer displayed distinct roots
than normalized coefficient slots. -/
theorem nodup_zeros_length_lt_degreeCount
    (polynomial : Polynomial K) (nonzero : polynomial.isZero = false)
    (points : List K) (nodup : points.Nodup)
    (zeros : ∀ point ∈ points, polynomial.eval point = 0) :
    points.length < polynomial.degreeCount := by
  generalize degreeEquation : polynomial.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing polynomial points with
  | h degree inductionHypothesis =>
      have degreePositive := degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil => exact degreePositive
      | cons root otherPoints =>
          cases coefficientsEquation : polynomial.normalize.coeffs with
          | nil =>
              change polynomial.normalize.coeffs.isEmpty = false at nonzero
              rw [coefficientsEquation] at nonzero
              exact Bool.noConfusion nonzero
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have canonical := leadingCoeff_ne_zero nonzero
                change polynomial.normalize.coeffs.headD 0 ≠ 0 at canonical
                rw [coefficientsEquation] at canonical
                simpa only [List.headD_cons] using canonical
              cases remaining with
              | nil =>
                  have rootZero := zeros root (by simp)
                  have normalizedRootZero : polynomial.normalize.eval root = 0 := by
                    simpa only [eval_normalize] using rootZero
                  change evalCoeffs root polynomial.normalize.coeffs = 0 at normalizedRootZero
                  rw [coefficientsEquation] at normalizedRootZero
                  simp only [evalCoeffs_cons, List.foldl_nil] at normalizedRootZero
                  exact (leadingNonzero normalizedRootZero).elim
              | cons coefficient remaining =>
                  let division := syntheticAux root leading
                    (coefficient :: remaining)
                  let quotient : Polynomial K := ⟨division.1⟩
                  have divisionSpec := syntheticAux_spec root leading
                    (coefficient :: remaining)
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (syntheticAux root
                          (leading * root + coefficient) remaining).1 := rfl
                  have quotientNonzero : quotient.isZero = false := by
                    simp [isZero, normalize, quotientCoefficients,
                      leadingNonzero]
                  have quotientDegree : quotient.degreeCount =
                      (coefficient :: remaining).length := by
                    calc
                      quotient.degreeCount = quotient.normalize.coeffs.length :=
                        rfl
                      _ = quotient.coeffs.length := by
                        rw [normalize_coeffs, quotientCoefficients,
                          List.dropWhile_cons_of_neg
                            (by simp [leadingNonzero])]
                      _ = division.1.length := rfl
                      _ = (coefficient :: remaining).length := divisionSpec.1
                  have originalDegree : polynomial.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    simp only [degreeCount, coefficientsEquation]
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    simp only [List.length_cons]
                    omega0
                  have remainderZero : division.2 = 0 := by
                    rw [divisionSpec.2.1, ← coefficientsEquation]
                    change polynomial.normalize.eval root = 0
                    rw [eval_normalize]
                    exact zeros root (by simp)
                  have otherZeros : ∀ point ∈ otherPoints,
                      quotient.eval point = 0 := by
                    intro point member
                    have originalZero := zeros point (by simp [member])
                    have factor := divisionSpec.2.2 point
                    rw [← coefficientsEquation] at factor
                    change polynomial.normalize.eval point =
                      (point - root) * quotient.eval point + division.2 at factor
                    rw [eval_normalize, originalZero, remainderZero] at factor
                    have productZero :
                        (point - root) * quotient.eval point = 0 := by
                      calc
                        (point - root) * quotient.eval point =
                            (point - root) * quotient.eval point + 0 := by ring0
                        _ = 0 := factor.symm
                    have distinct : point ≠ root := by
                      intro equal
                      subst point
                      exact (List.nodup_cons.mp nodup).1 member
                    have differenceNonzero : point - root ≠ 0 :=
                      sub_ne_zero.mpr distinct
                    by_cases quotientZero : quotient.eval point = 0
                    · exact quotientZero
                    · exact (RFAP.ExplicitField.mul_ne_zero
                        differenceNonzero quotientZero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    (List.nodup_cons.mp nodup).2 otherZeros rfl
                  simp only [List.length_cons]
                  omega0

private theorem eq_of_subtraction_dropWhile_eq_nil
    {A : Type*} [AddCommGroup A] [DecidableEq A] :
    ∀ left right : List A,
      left.length = right.length →
      (List.zipWith (· + ·) left (right.map (-·))).dropWhile (· = 0) = [] →
      left = right
  | [], [], _, _ => rfl
  | [], _ :: _, length, _ => by
      exact Nat.noConfusion length
  | _ :: _, [], length, _ => by
      exact Nat.noConfusion length
  | left :: leftTail, right :: rightTail, length, zero => by
      simp only [List.length_cons, Nat.succ.injEq] at length
      simp only [List.map_cons, List.zipWith_cons_cons] at zero
      by_cases headZero : left + -right = 0
      · rw [List.dropWhile_cons_of_pos (by simpa using headZero)] at zero
        have headEqual : left = right := by
          calc
            left = (left + -right) + right := by simp
            _ = right := by rw [headZero, zero_add]
        rw [headEqual, eq_of_subtraction_dropWhile_eq_nil leftTail rightTail
          length zero]
      · rw [List.dropWhile_cons_of_neg (by simpa using headZero)] at zero
        exact (List.cons_ne_nil (left + -right) _ zero).elim

private theorem dropWhile_replicate_zero_append
    {A : Type*} [Zero A] [DecidableEq A] (count : Nat) (values : List A) :
    (List.replicate count 0 ++ values).dropWhile (· = 0) =
      values.dropWhile (· = 0) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.cons_append,
        List.dropWhile_cons_of_pos (by simp), inductionHypothesis]

/-- An exactly zero coefficient difference identifies two normalized dense
polynomials without evaluating over a carrier. -/
theorem normalized_eq_of_sub_isZero
    {left right : Polynomial K}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (differenceZero : (left - right).isZero = true) : left = right := by
  have differenceEmpty : (left - right).coeffs = [] := by
    have normalizedEmpty : (left - right).normalize.coeffs = [] := by
      unfold isZero at differenceZero
      cases coefficients : (left - right).normalize.coeffs with
      | nil => rfl
      | cons coefficient remaining =>
          rw [coefficients] at differenceZero
          exact Bool.noConfusion differenceZero
    rw [normalize_sub] at normalizedEmpty
    exact normalizedEmpty
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  let count := max left.coeffs.length right.coeffs.length
  let leftPadded := padLeft (count - left.coeffs.length) left.coeffs
  let rightPadded := padLeft (count - right.coeffs.length) right.coeffs
  have leftLength : left.coeffs.length ≤ count := le_max_left _ _
  have rightLength : right.coeffs.length ≤ count := le_max_right _ _
  have paddedLength : leftPadded.length = rightPadded.length := by
    dsimp only [leftPadded, rightPadded, padLeft]
    simp only [List.length_append, List.length_replicate]
    rw [Nat.sub_add_cancel leftLength, Nat.sub_add_cancel rightLength]
  have rightNegCoefficients : (-right).coeffs = right.coeffs.map (-·) := by
    rw [neg_coeffs, rightNormalized]
  have rightNegLength : (-right).coeffs.length = right.coeffs.length := by
    rw [rightNegCoefficients, List.length_map]
  have paddedNeg :
      padLeft (count - right.coeffs.length) (-right).coeffs =
        rightPadded.map (-·) := by
    rw [rightNegCoefficients]
    dsimp only [rightPadded, padLeft]
    simp only [List.map_append, List.map_replicate, neg_zero]
  have paddedDifference :
      (List.zipWith (· + ·) leftPadded (rightPadded.map (-·))).dropWhile
          (· = 0) = [] := by
    change (add left (-right)).coeffs = [] at differenceEmpty
    simp only [add] at differenceEmpty
    rw [rightNegLength] at differenceEmpty
    change
      (List.zipWith (· + ·)
        (padLeft (count - left.coeffs.length) left.coeffs)
        (padLeft (count - right.coeffs.length) (-right).coeffs)).dropWhile
          (· = 0) = [] at differenceEmpty
    rw [paddedNeg] at differenceEmpty
    exact differenceEmpty
  have paddedEqual : leftPadded = rightPadded :=
    eq_of_subtraction_dropWhile_eq_nil leftPadded rightPadded paddedLength
      paddedDifference
  dsimp only [leftPadded, rightPadded, padLeft] at paddedEqual
  have trimmedEqual := congrArg (List.dropWhile (· = (0 : K))) paddedEqual
  rw [dropWhile_replicate_zero_append,
    dropWhile_replicate_zero_append] at trimmedEqual
  have leftTrim : left.coeffs.dropWhile (· = 0) = left.coeffs := by
    exact congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      leftNormalized
  have rightTrim : right.coeffs.dropWhile (· = 0) = right.coeffs := by
    exact congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      rightNormalized
  rw [leftTrim, rightTrim] at trimmedEqual
  exact trimmedEqual

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev RationalPolynomial := Polynomial Rational

/-- The bounded rational points used by coefficient extensionality. -/
def rationalPoints (count : Nat) : List Rational :=
  List.map (fun value : Nat => (value : Rational)) (List.range count)

theorem rationalPoints_nodup (count : Nat) :
    (rationalPoints count).Nodup := by
  change ((List.range count).map
    (fun value : Nat => (value : Rational))).Nodup
  apply QuotientFreeList.nodup_map_of_injective
  · intro left right equal
    exact RFAP.ConstructiveFraction.natCast_injective_direct equal
  · exact RFAP.finiteRange_nodup count

@[simp] theorem rationalPoints_length (count : Nat) :
    (rationalPoints count).length = count := by
  change ((List.range count).map
    (fun value : Nat => (value : Rational))).length = count
  rw [List.length_map, List.length_range]

/-- Equality at every constructive rational point identifies normalized
dense coefficient lists.  The proof actually uses only the bounded prefix
whose length is the coefficient count of the difference. -/
theorem rational_normalized_eq_of_eval_eq
    {left right : RationalPolynomial}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (equal : ∀ point : Rational, left.eval point = right.eval point) :
    left = right := by
  have differenceZero : (left - right).isZero = true := by
    by_cases zero : (left - right).isZero = true
    · exact zero
    · have nonzero : (left - right).isZero = false := by simpa using zero
      have zeros : ∀ point ∈ rationalPoints (left - right).degreeCount,
          (left - right).eval point = 0 := by
        intro point member
        rw [eval_sub, equal point]
        ring0
      have tooMany := nodup_zeros_length_lt_degreeCount
        (left - right) nonzero
        (rationalPoints (left - right).degreeCount)
        (rationalPoints_nodup _) zeros
      rw [rationalPoints_length] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim
  exact normalized_eq_of_sub_isZero leftNormalized rightNormalized
    differenceZero

end RFAP.FinitePolynomialExtensionality
