module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Nat.FiniteSum
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Divisibility

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Products of retained finite rational polynomial families

The indexed product retains each original factor in order, multiplying the
previous prefix by the final factor. Normalization, nonzero values, degrees,
divisibility and displayed Bezout certificates follow the same finite spine
without identifying the indexing functions or replacing factor witnesses.
-/

namespace Purelib.Polynomial.Dense.Rational.FiniteProduct

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Rational
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- Multiply a retained rational polynomial family along its original finite index spine.

The empty prefix is the constant-one polynomial. Each successor retains the
same earlier factors and multiplies their completed product by its final
factor, preserving the original order and selected polynomial values. -/
@[expose] public def productFin : (count : Nat) → (Fin count → Divisibility.CoefficientPolynomial) →
  Divisibility.CoefficientPolynomial
  | 0, _ => Basic.DensePolynomial.constant 1
  | count + 1, factor =>
      Purelib.Polynomial.Dense.Rational.FiniteProduct.productFin count (fun index => factor index.castSucc) *
        factor (Fin.last count)

/-- The empty indexed polynomial product is the constant-one polynomial. -/
@[simp] public theorem productFin_zero (factor : Fin 0 → Divisibility.CoefficientPolynomial) :
    productFin 0 factor = Basic.DensePolynomial.constant 1 := rfl

/-- Extend the indexed polynomial product by its last factor. -/
@[simp] public theorem productFin_succ (factor : Fin (count + 1) → Divisibility.CoefficientPolynomial) :
    productFin (count + 1) factor =
      productFin count (fun index => factor index.castSucc) *
        factor (Fin.last count) := rfl

/-- Pointwise equality of a finite indexed family preserves its displayed product.

Each scalar polynomial equality transports its original indexed factor. The
finite recursion compares the two retained product spines without identifying
the indexing functions themselves. -/
public theorem productFin_congr : ∀ (count : Nat)
    (left right : Fin count → Divisibility.CoefficientPolynomial),
    (∀ index, left index = right index) →
      productFin count left = productFin count right
  | 0, left, right, pointwise => rfl
  | count + 1, left, right, pointwise => by
      rw [productFin_succ, productFin_succ,
        productFin_congr count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc)
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]

/-- Every finite indexed polynomial product is already normalized.

The constant-one base is normalized. Each subsequent multiplication returns
normalized retained coefficients regardless of the individual factor forms. -/
public theorem productFin_normalized : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial),
    (productFin count factor).normalize = productFin count factor
  | 0, factor =>
      Basic.DensePolynomial.normalize_constant_of_ne Fraction.Field.zero_ne_one.symm
  | count + 1, factor => by
      rw [productFin_succ, Basic.DensePolynomial.normalize_mul]

/-- A finite product of represented nonzero rational polynomials is represented as nonzero.

The supplied certificate excludes zero for each original indexed factor.
Finite multiplication preserves those nonzero certificates along the same
completed prefix products. -/
public theorem productFin_nonzero : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial),
    (∀ index, (factor index).isZero = false) →
    (productFin count factor).isZero = false
  | 0, factor, allNonzero => by
      exact Basic.DensePolynomial.isZero_false_of_eval_ne (x := 0) (by
        change (Basic.DensePolynomial.constant (1 : Fraction.Rational)).eval 0 ≠ 0
        rw [Basic.DensePolynomial.eval_constant]
        exact Fraction.Field.zero_ne_one.symm)
  | count + 1, factor, allNonzero => by
      rw [productFin_succ]
      exact Basic.DensePolynomial.isZero_mul_eq_false
        (productFin_nonzero count (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc))
        (allNonzero (Fin.last count))

/-- Combine the displayed coprimality of each finite factor with a fixed right polynomial.

The finite product inherits a Bezout certificate by recursively multiplying the left-side certificates. -/
public theorem evalCoprime_productFin_left : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial) (right : Divisibility.CoefficientPolynomial),
    (∀ index, Divisibility.EvalCoprime (factor index) right) →
    Divisibility.EvalCoprime (productFin count factor) right
  | 0, factor, right, allCoprime => Divisibility.evalCoprime_one_left right
  | count + 1, factor, right, allCoprime => by
      rw [productFin_succ]
      exact Divisibility.evalCoprime_mul_left
        (evalCoprime_productFin_left count
          (fun index => factor index.castSucc) right
          (fun index => allCoprime index.castSucc))
        (allCoprime (Fin.last count))

/-- A finite family of pairwise Bezout-coprime divisors has product dividing the same dividend.

The finite recursion combines the supplied quotient witnesses and coprimality certificates without identifying indexing
functions. -/
public theorem evalDvd_productFin_of_pairwise : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial) (dividend : Divisibility.CoefficientPolynomial),
    (∀ index, Divisibility.EvalDvd (factor index) dividend) →
    (∀ first second, first ≠ second →
      Divisibility.EvalCoprime (factor first) (factor second)) →
    Divisibility.EvalDvd (productFin count factor) dividend
  | 0, factor, dividend, allDivide, pairwise => by
      refine ⟨dividend, ?_⟩
      intro point
      rewrite [productFin_zero, Basic.DensePolynomial.eval_mul,
        Basic.DensePolynomial.eval_constant, one_mul]
      exact Eq.refl _
  | count + 1, factor, dividend, allDivide, pairwise => by
      rw [productFin_succ]
      apply Divisibility.evalDvd_mul_of_coprime
      · exact evalDvd_productFin_of_pairwise count
          (fun index => factor index.castSucc) dividend
          (fun index => allDivide index.castSucc)
          (fun first second different => pairwise first.castSucc second.castSucc
            (fun equal => by
              apply different
              apply Fin.ext
              exact congrArg (fun index : Fin (count + 1) => index.val) equal))
      · exact allDivide (Fin.last count)
      · apply evalCoprime_productFin_left
        intro index
        exact pairwise index.castSucc (Fin.last count)
          (fun equal => by
            have values := congrArg Fin.val equal
            simp only [Fin.val_castSucc, Fin.val_last] at values
            omega0)

/-- The degree of a nonzero finite product is the finite sum of its factor degrees.

Every original indexed factor has a retained nonzero certificate. Degree
additivity follows the same product recursion and the original finite sum
indices, including the empty constant-one product. -/
public theorem natDegree_productFin : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial),
    (∀ index, (factor index).isZero = false) →
    (productFin count factor).natDegree =
      FiniteSum.sumFinNat count (fun index => (factor index).natDegree)
  | 0, factor, allNonzero => by
      simp only [productFin_zero, FiniteSum.sumFinNat]
      rfl
  | count + 1, factor, allNonzero => by
      rw [productFin_succ, FiniteSum.sumFinNat,
        Basic.DensePolynomial.natDegree_mul
          (productFin_nonzero count (fun index => factor index.castSucc)
            (fun index => allNonzero index.castSucc))
          (allNonzero (Fin.last count)),
        natDegree_productFin count (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc)]

/-- Every displayed slot divides its literal finite product.

The original index either selects the final factor or retains its exact bound
in the earlier prefix. Transitive divisibility carries that selected factor
through the unchanged finite multiplication spine. -/
public theorem evalDvd_factor_productFin : ∀ (count : Nat)
    (factor : Fin count → Divisibility.CoefficientPolynomial) (index : Fin count),
    Divisibility.EvalDvd (factor index) (productFin count factor)
  | 0, factor, index => Fin.elim0 index
  | count + 1, factor, index => by
      by_cases final : index.val = count
      · have indexLast : index = Fin.last count := Fin.ext final
        subst index
        rw [productFin_succ]
        exact Divisibility.evalDvd_mul_left _ _
      · have indexBelow : index.val < count := by
          have := index.isLt
          omega0
        let earlier : Fin count := ⟨index.val, indexBelow⟩
        apply Divisibility.evalDvd_trans
          (evalDvd_factor_productFin count
            (fun earlierIndex => factor earlierIndex.castSucc) earlier)
        exact Divisibility.evalDvd_mul_right _ _
end Purelib.Polynomial.Dense.Rational.FiniteProduct
