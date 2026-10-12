module
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Extensionality
public import Purelib.Polynomial.RecursiveDense.Rational.Basic
import Purelib.Polynomial.RecursiveDense.Rational.Specialization
import Purelib.Data.List.Search
import Purelib.Polynomial.Dense.Rational.Roots.FiniteBound
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib

open Purelib.Polynomial

section
public section

/-!
# Common finite nonzero points for rational polynomials

Two recursively dense polynomials with failed zero tests admit one common
rational point where both evaluations are nonzero. Each outer coordinate
comes from the retained finite degree-bound point list for the product of
the two specialized polynomials; the original coefficient witnesses determine
the inner recursive point.
-/

namespace Purelib.Polynomial.RecursiveDense.Rational.Avoidance

/- Finite recursively dense polynomials in exactly the displayed number of
variables.  `Coefficients` is a project-owned finite list constructor so the
kernel sees the mutual recursion directly, without a nested inductive. -/

/- Horner evaluation, inner coordinates first and the last coordinate
outermost. -/

/-- Two nonzero univariate rational polynomials have a common non-root among
the explicitly tested points `0, ..., degree(left * right)`.  Since
`degreeCount = degree + 1` for a nonzero dense polynomial, this is precisely
the finite `d + 1` test for their product. -/
theorem exists_rational_not_root_of_product
    (left right : Basic.DensePolynomial)
    (leftNonzero : left.isZero = false)
    (rightNonzero : right.isZero = false) :
    ∃ point ∈ Dense.Rational.Extensionality.rationalPoints (left * right).degreeCount,
      left.eval point ≠ 0 ∧ right.eval point ≠ 0 := by
  have productNonzero : (left * right).isZero = false :=
    DensePolynomial.isZero_mul_eq_false leftNonzero rightNonzero
  have notAllProductZero :
      ¬ ∀ point ∈ Dense.Rational.Extensionality.rationalPoints (left * right).degreeCount,
        (left * right).eval point = 0 := by
    intro allProductZero
    have tooMany := Dense.Rational.Roots.FiniteBound.nodup_zeros_length_lt_degreeCount
      (left * right) productNonzero
      (Dense.Rational.Extensionality.rationalPoints (left * right).degreeCount)
      (Dense.Rational.Extensionality.rationalPoints_nodup _) allProductZero
    rw [Dense.Rational.Extensionality.rationalPoints_length] at tooMany
    exact Nat.lt_irrefl _ tooMany
  obtain ⟨point, member, productValueNonzero⟩ :=
    Data.List.Search.exists_member_ne_zero_of_not_all_zero
      (Dense.Rational.Extensionality.rationalPoints (left * right).degreeCount)
      (fun value => (left * right).eval value) notAllProductZero
  refine ⟨point, member, ?_, ?_⟩
  · intro leftZero
    apply productValueNonzero
    rw [DensePolynomial.eval_mul, leftZero, zero_mul]
  · intro rightZero
    apply productValueNonzero
    rw [DensePolynomial.eval_mul, rightZero, mul_zero]

/-- Constructively, two nonzero finite multivariate rational polynomials
are simultaneously nonzero at some rational point.  Each recursive outer
coordinate is selected from a finite `degree(product) + 1` list. -/
theorem exists_common_nonzero :
    ∀ {arity : Nat} (left right : Basic.Expression arity),
      left.isZero = false → right.isZero = false →
      ∃ point : Basic.Point arity,
        left.eval point ≠ 0 ∧ right.eval point ≠ 0
 := by
  intro arity
  induction arity with
  | zero =>
      intro left right leftNonzero rightNonzero
      cases left with
      | constant left =>
        cases right with
        | constant right =>
          have leftNe : left ≠ 0 := by
            intro leftZero
            subst left
            change decide ((0 : Purelib.Data.Rat.Fraction.Rational) = 0) = false at leftNonzero
            exact Bool.noConfusion leftNonzero
          have rightNe : right ≠ 0 := by
            intro rightZero
            subst right
            change decide ((0 : Purelib.Data.Rat.Fraction.Rational) = 0) = false at rightNonzero
            exact Bool.noConfusion rightNonzero
          exact ⟨(), leftNe, rightNe⟩
  | succ arity inductionHypothesis =>
      intro left right leftNonzero rightNonzero
      have nextRepresentation : ∀ {index : Nat} (polynomial : Basic.Expression index)
          (indexEqual : index = arity + 1),
          ∃ coefficients : Basic.Coefficients arity,
            polynomial = indexEqual.symm ▸ Basic.Expression.next coefficients := by
        intro index polynomial
        cases polynomial with
        | constant coefficient =>
            intro indexEqual
            exact Nat.noConfusion indexEqual
        | @next index coefficients =>
            intro indexEqual
            have predecessorEqual : index = arity := Nat.succ.inj indexEqual
            cases predecessorEqual
            cases indexEqual
            exact ⟨coefficients, rfl⟩
      obtain ⟨leftCoefficients, leftIdentity⟩ := nextRepresentation left rfl
      obtain ⟨rightCoefficients, rightIdentity⟩ := nextRepresentation right rfl
      cases leftIdentity
      cases rightIdentity
      obtain ⟨leftCoefficient, leftMember, leftCoefficientNonzero⟩ :=
        Specialization.nonzero_coefficient leftCoefficients leftNonzero
      obtain ⟨rightCoefficient, rightMember, rightCoefficientNonzero⟩ :=
        Specialization.nonzero_coefficient rightCoefficients rightNonzero
      obtain ⟨inner, leftValueNonzero, rightValueNonzero⟩ :=
        inductionHypothesis leftCoefficient rightCoefficient
          leftCoefficientNonzero rightCoefficientNonzero
      have leftSpecializationNonzero :
          (Specialization.specializeOuter leftCoefficients inner).isZero = false :=
        Specialization.specializeOuter_nonzero_of_coefficient leftMember leftValueNonzero
      have rightSpecializationNonzero :
          (Specialization.specializeOuter rightCoefficients inner).isZero = false :=
        Specialization.specializeOuter_nonzero_of_coefficient rightMember rightValueNonzero
      obtain ⟨outer, _, leftOuterNonzero, rightOuterNonzero⟩ :=
        exists_rational_not_root_of_product
          (Specialization.specializeOuter leftCoefficients inner)
          (Specialization.specializeOuter rightCoefficients inner)
          leftSpecializationNonzero rightSpecializationNonzero
      refine ⟨(inner, outer), ?_, ?_⟩
      · rewrite [Specialization.eval_next]
        exact leftOuterNonzero
      · rewrite [Specialization.eval_next]
        exact rightOuterNonzero

/-- Finite constructive form of Lemma 59: if `right` is nonzero and `left`
vanishes at every rational point where `right` does not, then `left` is the
zero polynomial. -/
theorem isZero_of_vanishes_where_second_nonzero
    {arity : Nat} (left right : Basic.Expression arity)
    (rightNonzero : right.isZero = false)
    (vanishes : ∀ point : Basic.Point arity,
      right.eval point ≠ 0 → left.eval point = 0) :
    left.isZero = true := by
  cases leftZero : left.isZero with
  | true => rfl
  | false =>
      obtain ⟨point, leftValueNonzero, rightValueNonzero⟩ :=
        exists_common_nonzero left right leftZero rightNonzero
      exact (leftValueNonzero (vanishes point rightValueNonzero)).elim

end Purelib.Polynomial.RecursiveDense.Rational.Avoidance

end
