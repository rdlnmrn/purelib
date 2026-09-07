import mathlib.RFAP.FinitePolynomialExtensionality

/-!
# Finite multivariate polynomial avoidance

This module supplies the constructive finite replacement for the usual
"the rationals are infinite" polynomial-identity argument.  A polynomial in
`n + 1` variables is a finite high-to-low list of polynomials in `n`
variables.  No carrier-wide set of points is formed.

The key univariate step multiplies two specialized dense polynomials and
tests the bounded list

`0, 1, ..., degree(product)`.

The existing finite root bound proves that one of those `degree + 1` points
is not a root.  Recursing through the variables gives a rational point where
any two nonzero multivariate polynomials are simultaneously nonzero, and
hence proves the rational-point transfer statement used as Lemma 59 in the
rational-rotations paper.
-/

namespace RFAP.FiniteMultivariatePolynomial

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev DensePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Rational

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.FinitePolynomialExtensionality

/- Finite recursively dense polynomials in exactly the displayed number of
variables.  `Coefficients` is a project-owned finite list constructor so the
kernel sees the mutual recursion directly, without a nested inductive. -/
mutual
  /-- A recursively dense polynomial of finite arity. -/
  inductive Polynomial : Nat → Type
    | constant : Rational → Polynomial 0
    | next {arity : Nat} : Coefficients arity → Polynomial (arity + 1)

  /-- A finite high-to-low coefficient sequence. -/
  inductive Coefficients : Nat → Type
    | nil {arity : Nat} : Coefficients arity
    | cons {arity : Nat} : Polynomial arity → Coefficients arity →
        Coefficients arity
end

/-- Forget the recursive list wrapper after its finiteness has been made
kernel-visible. -/
def Coefficients.toList {arity : Nat} :
    Coefficients arity → List (Polynomial arity)
  | .nil => []
  | .cons coefficient remaining => coefficient :: remaining.toList

/-- Build a recursive coefficient sequence from an ordinary finite list. -/
def Coefficients.ofList {arity : Nat} :
    List (Polynomial arity) → Coefficients arity
  | [] => .nil
  | coefficient :: remaining =>
      .cons coefficient (Coefficients.ofList remaining)

/-- A rational point with exactly the displayed finite number of
coordinates. -/
def Point : Nat → Type
  | 0 => Unit
  | arity + 1 => Point arity × Rational

/- Exact finite zero tests: every recursively displayed coefficient must
vanish.  Representation-only leading zero coefficients do not affect them. -/
mutual
  def Polynomial.isZero : {arity : Nat} → Polynomial arity → Bool
    | 0, .constant coefficient => decide (coefficient = 0)
    | _ + 1, .next coefficients => coefficients.isZero

  def Coefficients.isZero {arity : Nat} : Coefficients arity → Bool
    | .nil => true
    | .cons coefficient remaining =>
        coefficient.isZero && remaining.isZero
end

/- Horner evaluation, inner coordinates first and the last coordinate
outermost. -/
mutual
  def Polynomial.eval : {arity : Nat} →
      Polynomial arity → Point arity → Rational
    | 0, .constant coefficient, _ => coefficient
    | _ + 1, .next coefficients, (inner, outer) =>
        coefficients.eval inner outer 0

  def Coefficients.eval {arity : Nat} : Coefficients arity →
      Point arity → Rational → Rational → Rational
    | .nil, _, _, value => value
    | .cons coefficient remaining, inner, outer, value =>
        remaining.eval inner outer
          (value * outer + coefficient.eval inner)
end

/-- Specialize all inner variables, leaving an ordinary dense polynomial in
the final variable. -/
def specializeOuter {arity : Nat}
    (coefficients : Coefficients arity) (inner : Point arity) :
    DensePolynomial :=
  ⟨coefficients.toList.map (fun coefficient => coefficient.eval inner)⟩

private theorem coefficients_eval_eq_foldl {arity : Nat} :
    ∀ (coefficients : Coefficients arity) (inner : Point arity)
      (outer value : Rational),
      coefficients.eval inner outer value =
        (coefficients.toList.map
          (fun coefficient => coefficient.eval inner)).foldl
            (fun accumulator coefficient =>
              accumulator * outer + coefficient) value
  | .nil, _, _, _ => rfl
  | .cons coefficient remaining, inner, outer, value => by
      simp only [Coefficients.eval, Coefficients.toList, List.map_cons,
        List.foldl_cons]
      exact coefficients_eval_eq_foldl remaining inner outer _
termination_by coefficients _ _ _ => coefficients.toList.length
decreasing_by simp [Coefficients.toList]

@[simp] theorem eval_next {arity : Nat}
    (coefficients : Coefficients arity) (inner : Point arity)
    (outer : Rational) :
    (Polynomial.next coefficients).eval (inner, outer) =
      (specializeOuter coefficients inner).eval outer := by
  rw [Polynomial.eval, coefficients_eval_eq_foldl]
  rfl

private theorem nonzero_coefficient {arity : Nat} :
    ∀ coefficients : Coefficients arity,
      coefficients.isZero = false →
      ∃ coefficient ∈ coefficients.toList, coefficient.isZero = false
  | .nil, nonzero => Bool.noConfusion nonzero
  | .cons coefficient remaining, nonzero => by
      cases coefficientZero : coefficient.isZero with
      | false =>
          exact ⟨coefficient, List.mem_cons_self, coefficientZero⟩
      | true =>
          have remainingNonzero : remaining.isZero = false := by
            simpa only [Coefficients.isZero, coefficientZero,
              Bool.true_and] using nonzero
          obtain ⟨entry, member, entryNonzero⟩ :=
            nonzero_coefficient remaining remainingNonzero
          exact ⟨entry, List.mem_cons_of_mem _ member, entryNonzero⟩

private theorem all_zero_of_dropWhile_eq_nil :
    ∀ coefficients : List Rational,
      coefficients.dropWhile (fun coefficient => decide (coefficient = 0)) = [] →
      ∀ coefficient ∈ coefficients, coefficient = 0
  | [], _, _, member => by simp only [List.not_mem_nil] at member
  | first :: remaining, dropped, coefficient, member => by
      by_cases firstZero : first = 0
      · simp [List.dropWhile, firstZero] at dropped
        simp only [List.mem_cons] at member
        rcases member with equal | later
        · simpa only [equal] using firstZero
        · exact all_zero_of_dropWhile_eq_nil remaining dropped coefficient
            later
      · simp [List.dropWhile, firstZero] at dropped

private theorem dense_isZero_false_of_member_ne_zero
    (polynomial : DensePolynomial) {coefficient : Rational}
    (member : coefficient ∈ polynomial.coeffs)
    (nonzero : coefficient ≠ 0) :
    polynomial.isZero = false := by
  cases zero : polynomial.isZero with
  | false => rfl
  | true =>
      have dropped : polynomial.coeffs.dropWhile
          (fun entry => decide (entry = 0)) = [] := by
        change (polynomial.coeffs.dropWhile
          (fun entry => decide (entry = 0))).isEmpty = true at zero
        exact List.isEmpty_iff.mp zero
      exact (nonzero
        (all_zero_of_dropWhile_eq_nil polynomial.coeffs dropped coefficient
          member)).elim

private theorem specializeOuter_nonzero_of_coefficient
    {arity : Nat} {coefficients : Coefficients arity}
    {coefficient : Polynomial arity} {inner : Point arity}
    (member : coefficient ∈ coefficients.toList)
    (nonzero : coefficient.eval inner ≠ 0) :
    (specializeOuter coefficients inner).isZero = false := by
  apply dense_isZero_false_of_member_ne_zero
    (specializeOuter coefficients inner)
  · exact QuotientFreeList.mem_map.mpr
      ⟨coefficient, member, rfl⟩
  · exact nonzero

private theorem exists_member_ne_zero_of_not_all_zero
    (values : List Rational) (evaluation : Rational → Rational)
    (notAllZero : ¬ ∀ point ∈ values, evaluation point = 0) :
    ∃ point ∈ values, evaluation point ≠ 0 := by
  induction values with
  | nil =>
      exact (notAllZero (fun point member => by
        simp only [List.not_mem_nil] at member)).elim
  | cons first remaining inductionHypothesis =>
      by_cases firstZero : evaluation first = 0
      · have tailNotAllZero :
            ¬ ∀ point ∈ remaining, evaluation point = 0 := by
          intro tailAllZero
          apply notAllZero
          intro point member
          simp only [List.mem_cons] at member
          rcases member with equal | later
          · simpa only [equal] using firstZero
          · exact tailAllZero point later
        obtain ⟨point, member, nonzero⟩ := inductionHypothesis tailNotAllZero
        exact ⟨point, List.mem_cons_of_mem _ member, nonzero⟩
      · exact ⟨first, List.mem_cons_self, firstZero⟩

/-- Two nonzero univariate rational polynomials have a common non-root among
the explicitly tested points `0, ..., degree(left * right)`.  Since
`degreeCount = degree + 1` for a nonzero dense polynomial, this is precisely
the finite `d + 1` test for their product. -/
theorem exists_rational_not_root_of_product
    (left right : DensePolynomial)
    (leftNonzero : left.isZero = false)
    (rightNonzero : right.isZero = false) :
    ∃ point ∈ rationalPoints (left * right).degreeCount,
      left.eval point ≠ 0 ∧ right.eval point ≠ 0 := by
  have productNonzero : (left * right).isZero = false :=
    isZero_mul_eq_false leftNonzero rightNonzero
  have notAllProductZero :
      ¬ ∀ point ∈ rationalPoints (left * right).degreeCount,
        (left * right).eval point = 0 := by
    intro allProductZero
    have tooMany := nodup_zeros_length_lt_degreeCount
      (left * right) productNonzero
      (rationalPoints (left * right).degreeCount)
      (rationalPoints_nodup _) allProductZero
    rw [rationalPoints_length] at tooMany
    exact Nat.lt_irrefl _ tooMany
  obtain ⟨point, member, productValueNonzero⟩ :=
    exists_member_ne_zero_of_not_all_zero
      (rationalPoints (left * right).degreeCount)
      (fun value => (left * right).eval value) notAllProductZero
  refine ⟨point, member, ?_, ?_⟩
  · intro leftZero
    apply productValueNonzero
    rw [eval_mul, leftZero, zero_mul]
  · intro rightZero
    apply productValueNonzero
    rw [eval_mul, rightZero, mul_zero]

/-- Constructively, two nonzero finite multivariate rational polynomials
are simultaneously nonzero at some rational point.  Each recursive outer
coordinate is selected from a finite `degree(product) + 1` list. -/
theorem exists_common_nonzero :
    ∀ {arity : Nat} (left right : Polynomial arity),
      left.isZero = false → right.isZero = false →
      ∃ point : Point arity,
        left.eval point ≠ 0 ∧ right.eval point ≠ 0
  | 0, .constant left, .constant right, leftNonzero, rightNonzero => by
      have leftNe : left ≠ 0 := by
        intro leftZero
        subst left
        simp [Polynomial.isZero] at leftNonzero
      have rightNe : right ≠ 0 := by
        intro rightZero
        subst right
        simp [Polynomial.isZero] at rightNonzero
      exact ⟨(), leftNe, rightNe⟩
  | _ + 1, .next leftCoefficients, .next rightCoefficients,
      leftNonzero, rightNonzero => by
      obtain ⟨leftCoefficient, leftMember, leftCoefficientNonzero⟩ :=
        nonzero_coefficient leftCoefficients leftNonzero
      obtain ⟨rightCoefficient, rightMember, rightCoefficientNonzero⟩ :=
        nonzero_coefficient rightCoefficients rightNonzero
      obtain ⟨inner, leftValueNonzero, rightValueNonzero⟩ :=
        exists_common_nonzero leftCoefficient rightCoefficient
          leftCoefficientNonzero rightCoefficientNonzero
      have leftSpecializationNonzero :
          (specializeOuter leftCoefficients inner).isZero = false :=
        specializeOuter_nonzero_of_coefficient leftMember leftValueNonzero
      have rightSpecializationNonzero :
          (specializeOuter rightCoefficients inner).isZero = false :=
        specializeOuter_nonzero_of_coefficient rightMember rightValueNonzero
      obtain ⟨outer, _, leftOuterNonzero, rightOuterNonzero⟩ :=
        exists_rational_not_root_of_product
          (specializeOuter leftCoefficients inner)
          (specializeOuter rightCoefficients inner)
          leftSpecializationNonzero rightSpecializationNonzero
      exact ⟨(inner, outer), by simpa using leftOuterNonzero,
        by simpa using rightOuterNonzero⟩

/-- Finite constructive form of Lemma 59: if `right` is nonzero and `left`
vanishes at every rational point where `right` does not, then `left` is the
zero polynomial. -/
theorem isZero_of_vanishes_where_second_nonzero
    {arity : Nat} (left right : Polynomial arity)
    (rightNonzero : right.isZero = false)
    (vanishes : ∀ point : Point arity,
      right.eval point ≠ 0 → left.eval point = 0) :
    left.isZero = true := by
  cases leftZero : left.isZero with
  | true => rfl
  | false =>
      obtain ⟨point, leftValueNonzero, rightValueNonzero⟩ :=
        exists_common_nonzero left right leftZero rightNonzero
      exact (leftValueNonzero (vanishes point rightValueNonzero)).elim

end RFAP.FiniteMultivariatePolynomial
