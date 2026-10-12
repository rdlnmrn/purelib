module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
public import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Constants
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Product
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Leading (LeadingTerm)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Parity-aware finite square-factor reduction

An exact multiplicity basis gives `p = s * s * q`: half of each
multiplicity goes into `s`, and only odd multiplicities remain in `q`.
The scalar stays in `q`, without extracting a square root in the coefficient
field.  This is not the squarefree radical, which would retain even factors.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Products

/-- The displayed square factor, with half of each exact multiplicity. -/
def halfProduct : List
  PositiveEntry →
    CoefficientPolynomial
  | [] => DensePolynomial.constant 1
  | entry :: entries =>
      Dense.Gaussian.Power.polynomialPower entry.part.polynomial (entry.multiplicity / 2) *
        halfProduct entries

/-- Retain a factor once precisely when its multiplicity is odd. -/
def oddProduct : List
  PositiveEntry →
    CoefficientPolynomial
  | [] => DensePolynomial.constant 1
  | entry :: entries =>
      if entry.multiplicity % 2 = 0 then oddProduct
        entries
      else entry.part.polynomial * oddProduct entries

/-- The product formed from half multiplicities is nonzero. -/
theorem halfProduct_nonzero : ∀ entries : List
  PositiveEntry,
    (halfProduct entries).isZero = false
  | [] => (LeadingTerm.constant one_ne_zero).nonzero
  | entry :: entries =>
      DensePolynomial.isZero_mul_eq_false (Dense.Gaussian.Power.polynomialPower_nonzero entry.part.nonzero
        _)
        (halfProduct_nonzero entries)

/-- The product of factors with odd multiplicity is nonzero. -/
theorem oddProduct_nonzero : ∀ entries : List
  PositiveEntry,
    (oddProduct entries).isZero = false
  | [] => (LeadingTerm.constant one_ne_zero).nonzero
  | entry :: entries => by
      by_cases even : entry.multiplicity % 2 = 0
      · have equal : oddProduct (entry :: entries) =
          oddProduct entries := if_pos even
        exact (congrArg (fun p : CoefficientPolynomial => p.isZero)
          equal).trans
          (oddProduct_nonzero entries)
      · have equal : oddProduct (entry :: entries) =
            entry.part.polynomial * oddProduct entries := if_neg even
        exact (congrArg (fun p : CoefficientPolynomial => p.isZero)
          equal).trans
          (DensePolynomial.isZero_mul_eq_false entry.part.nonzero
            (oddProduct_nonzero entries))

/-- The half-multiplicity product is already normalized. -/
theorem halfProduct_normalized : ∀ entries :
  List PositiveEntry,
    (halfProduct entries).normalize =
      halfProduct entries
  | [] => (LeadingTerm.constant one_ne_zero).normalized
  | _ :: _ => DensePolynomial.normalize_mul _ _

/-- The parity-selected product is already normalized. -/
theorem oddProduct_normalized : ∀ entries :
  List PositiveEntry,
    (oddProduct entries).normalize =
      oddProduct entries
  | [] => (LeadingTerm.constant one_ne_zero).normalized
  | entry :: entries => by
      rw [oddProduct]
      split
      · exact oddProduct_normalized entries
      · exact DensePolynomial.normalize_mul _ _

/-- Coprimality with every retained factor gives coprimality with their
product.  The input relation comes from the computed multiplicity basis. -/
def coprimeOddProduct (external :
  Dense.Gaussian.Squarefree.Part) :
    (entries : List PositiveEntry) →
    (∀ entry ∈ entries, Dense.Gaussian.Multiplicity.CoprimeRelation external entry.part) →
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate external.polynomial
      (oddProduct entries)
  | [], _ => Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight external.nonzero
  | entry :: entries, coprime => by
      rw [oddProduct]
      split
      · exact coprimeOddProduct external entries
          (fun found member => coprime found (List.mem_cons_of_mem entry member))
      · exact Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight external.nonzero
          (Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeCertificateOfRelation external entry.part
            (coprime entry List.mem_cons_self))
          (coprimeOddProduct external entries
            (fun found member => coprime found (List.mem_cons_of_mem entry member)))

/-- The parity-selected product is squarefree, including the empty product. -/
def oddProductSquarefree : (entries : List
  PositiveEntry) →
    entries.Pairwise (fun left right => Dense.Gaussian.Multiplicity.CoprimeRelation left.part
      right.part) →
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (oddProduct entries)
  | [], _ => Dense.Gaussian.Squarefree.Constants.constant 1 one_ne_zero
  | entry :: entries, pairwise => by
      have parts := List.pairwise_cons.mp pairwise
      rw [oddProduct]
      split
      · exact oddProductSquarefree entries parts.2
      · exact Dense.Gaussian.Squarefree.Product.product entry.part.nonzero
          (oddProduct_nonzero entries) entry.part.squarefree
          (oddProductSquarefree entries parts.2)
          (coprimeOddProduct entry.part entries parts.1)

/-- Exact reconstruction at any displayed finite coefficient point.

The original finite multiplicities split into twice their natural halves and their parity bits, so the retained square
factor and parity-selected factor reconstruct the same value. -/
theorem parityIdentity (entries : List
  PositiveEntry) (point : Gaussian.Basic.Canonical) :
    Basis.Positive.positiveValue entries point =
      (halfProduct entries).eval point *
        (halfProduct entries).eval point *
        (oddProduct entries).eval point := by
  have powerAddLocal (value : Gaussian.Basic.Canonical) (left right : Nat) :
      value ^ (left + right) = value ^ left * value ^ right := by
    induction right with
    | zero =>
        simp only [Nat.add_zero, pow_zero, mul_one, -eq_self, -iff_self]
        rfl
    | succ right ih =>
        rw [Nat.add_succ, pow_succ, ih, pow_succ]
        exact Gaussian.Basic.mul_assoc _ _ _
  have powerParityLocal (value : Gaussian.Basic.Canonical) (exponent : Nat) :
      value ^ exponent = value ^ (exponent / 2) * value ^ (exponent / 2) *
        (if exponent % 2 = 0 then 1 else value) := by
    have balance : exponent = exponent / 2 + exponent / 2 + exponent % 2 := by omega
    calc
      value ^ exponent = value ^ (exponent / 2 + exponent / 2 + exponent % 2) :=
        congrArg (fun n => value ^ n) balance
      _ = value ^ (exponent / 2) * value ^ (exponent / 2) *
          value ^ (exponent % 2) := by
        rw [powerAddLocal, powerAddLocal]
      _ = _ := by
        by_cases even : exponent % 2 = 0
        · rw [if_pos even, even, pow_zero]
        · have odd : exponent % 2 = 1 := by omega
          rw [if_neg even, odd, pow_one]
  induction entries with
  | nil =>
      simp only [Basis.Positive.positiveValue,
        halfProduct,
        oddProduct, DensePolynomial.eval_constant, mul_one,
        -eq_self, -iff_self]
      rfl
  | cons entry entries ih =>
      rw [Basis.Positive.positiveValue,
        halfProduct,
        oddProduct]
      simp only [DensePolynomial.eval_mul, Dense.Gaussian.Power.eval_polynomialPower, -eq_self, -iff_self]
      rw [powerParityLocal, ih]
      split
      · simp only [mul_one, -eq_self, -iff_self]
        ring1
      · simp only [DensePolynomial.eval_mul, -eq_self, -iff_self]
        ring1
end Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Products

end
