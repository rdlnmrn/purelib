module

public import Purelib.Polynomial.Laurent.Normalization
public import Purelib.Polynomial.Laurent.Arithmetic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Zero
import Purelib.Polynomial.Dense.Leading
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Actual normalized products of original Laurent symbols

The same computed raw cross-product receives its automatic normalization.
Positive finite Gaussian probes compare its original coefficient tables,
while exact zero-root and degree balances determine both support endpoints
and the extra zero roots of a common nonminimal polynomializing shift.
-/

namespace Purelib.Polynomial.Laurent.Arithmetic.Product

open Purelib.Data
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Leading
open Purelib.Polynomial.Laurent.Basic
open Purelib.Polynomial.Laurent.Normalization

/-- Nonzero normalized inputs cannot produce a computed zero original Laurent product. -/
public theorem zero_obstruction_impossible {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (obstruction : ZeroSymbol product.symbol) : False := by
  let polynomial := leftResult.polynomial * rightResult.polynomial
  have nonzero : polynomial.isZero = false :=
    DensePolynomial.isZero_mul_eq_false leftResult.polynomial_nonzero rightResult.polynomial_nonzero
  have zero : polynomial.isZero = true :=
    Dense.Gaussian.Extensionality.isZero_of_positive_grid_zero polynomial (fun point member => by
      have pointNonzero := Dense.Gaussian.Extensionality.positiveProbePoints_nonzero _ point member
      have leftDefined := left.definedAt_of_nonzero pointNonzero
      have rightDefined := right.definedAt_of_nonzero pointNonzero
      have sourceZero := obstruction.eval_zero point (product.symbol.definedAt_of_nonzero pointNonzero)
      have sourceProduct := product.eval_eq_mul point ⟨leftDefined, rightDefined⟩
      change product.symbol.eval point = left.eval point * right.eval point at sourceProduct
      have productZero : left.eval point * right.eval point = 0 := sourceProduct.symm.trans sourceZero
      change (leftResult.polynomial * rightResult.polynomial).eval point = 0
      rewrite [DensePolynomial.eval_mul, leftResult.polynomial_eval point leftDefined,
        rightResult.polynomial_eval point rightDefined]
      calc
        (point ^ leftResult.poleOrder * left.eval point) *
            (point ^ rightResult.poleOrder * right.eval point) =
            (point ^ leftResult.poleOrder * point ^ rightResult.poleOrder) *
              (left.eval point * right.eval point) := by ring1
        _ = 0 := by rewrite [productZero, Gaussian.Basic.mul_zero]; rfl)
  exact Bool.noConfusion (nonzero.symm.trans zero)

/-- Automatically normalize the retained raw product of two nonzero normalized original inputs. -/
@[expose] public def normalize {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right) : Normalized product.symbol :=
  match product.symbol.prepare with
  | .zero obstruction => (product.zero_obstruction_impossible leftResult rightResult obstruction).elim
  | .normalized result => result

/-- Common polynomializing shifts identify the actual original dense product coefficient tables. -/
public theorem commonShift_identity {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) :
    DensePolynomial.shift result.poleOrder (leftResult.polynomial * rightResult.polynomial) =
      DensePolynomial.shift (leftResult.poleOrder + rightResult.poleOrder) result.polynomial := by
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_shift _ _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have leftDefined := left.definedAt_of_nonzero nonzero
  have rightDefined := right.definedAt_of_nonzero nonzero
  have sourceProduct := product.eval_eq_mul point ⟨leftDefined, rightDefined⟩
  change product.symbol.eval point = left.eval point * right.eval point at sourceProduct
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_shift, DensePolynomial.eval_mul,
    leftResult.polynomial_eval point leftDefined, rightResult.polynomial_eval point rightDefined,
    result.polynomial_eval point (product.symbol.definedAt_of_nonzero nonzero), sourceProduct, pow_add]
  ring1

/-- Common-shift comparison retains the exact original zero-root compensation. -/
public theorem zeroMultiplicity_balance {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) :
    leftResult.zeroMultiplicity + rightResult.zeroMultiplicity + result.poleOrder =
      result.zeroMultiplicity + (leftResult.poleOrder + rightResult.poleOrder) := by
  have identity := congrArg DensePolynomial.zeroMultiplicity
    (product.commonShift_identity leftResult rightResult result)
  rewrite [DensePolynomial.zeroMultiplicity_shift _
      (DensePolynomial.isZero_mul_eq_false leftResult.polynomial_nonzero rightResult.polynomial_nonzero),
    DensePolynomial.zeroMultiplicity_shift _ result.polynomial_nonzero,
    Dense.Gaussian.Multiplicity.Zero.product _ _ leftResult.polynomial_nonzero rightResult.polynomial_nonzero,
    leftResult.polynomial_zeroMultiplicity, rightResult.polynomial_zeroMultiplicity,
    result.polynomial_zeroMultiplicity] at identity
  exact identity

/-- The actual lowest normalized support exponents add under multiplication. -/
public theorem lower_add {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) : result.lower = leftResult.lower + rightResult.lower := by
  have balance := product.zeroMultiplicity_balance leftResult rightResult result
  have leftZero := leftResult.zeroMultiplicity_eq
  have rightZero := rightResult.zeroMultiplicity_eq
  have resultZero := result.zeroMultiplicity_eq
  omega0

/-- The actual highest normalized support exponents add under multiplication. -/
public theorem upper_add {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) : result.upper = leftResult.upper + rightResult.upper := by
  have identity := congrArg DensePolynomial.natDegree
    (product.commonShift_identity leftResult rightResult result)
  have productLeading := LeadingTerm.mul
    (LeadingTerm.ofNormalized leftResult.polynomial_nonzero leftResult.polynomial_normalized)
    (LeadingTerm.ofNormalized rightResult.polynomial_nonzero rightResult.polynomial_normalized)
  have leftDegree := (LeadingTerm.shift result.poleOrder productLeading).degree_eq
  have rightDegree := (LeadingTerm.shift (leftResult.poleOrder + rightResult.poleOrder)
    (LeadingTerm.ofNormalized result.polynomial_nonzero result.polynomial_normalized)).degree_eq
  have leftBalance := leftResult.polynomial_degree
  have rightBalance := rightResult.polynomial_degree
  have resultBalance := result.polynomial_degree
  omega0

/-- The sum of actual input pole orders is a sufficient common polynomializing shift for their product. -/
public theorem poleOrder_le {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) : result.poleOrder ≤ leftResult.poleOrder + rightResult.poleOrder := by
  have balance := product.zeroMultiplicity_balance leftResult rightResult result
  cases result.poleOrder_zero_or_zeroMultiplicity_zero with
  | inl zero => rewrite [zero]; exact Nat.zero_le _
  | inr zero => rewrite [zero] at balance; omega0

/-- The actual normalized product polynomial differs from the dense product by exactly the extra common shift. -/
public theorem polynomial_identity {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) :
    leftResult.polynomial * rightResult.polynomial =
      DensePolynomial.shift (leftResult.poleOrder + rightResult.poleOrder - result.poleOrder) result.polynomial := by
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_mul _ _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have leftDefined := left.definedAt_of_nonzero nonzero
  have rightDefined := right.definedAt_of_nonzero nonzero
  have sourceProduct := product.eval_eq_mul point ⟨leftDefined, rightDefined⟩
  change product.symbol.eval point = left.eval point * right.eval point at sourceProduct
  have exponentBalance : leftResult.poleOrder + rightResult.poleOrder = result.poleOrder +
      (leftResult.poleOrder + rightResult.poleOrder - result.poleOrder) := by
    have sufficient := product.poleOrder_le leftResult rightResult result
    omega0
  calc
    (leftResult.polynomial * rightResult.polynomial).eval point =
        point ^ (leftResult.poleOrder + rightResult.poleOrder) * (left.eval point * right.eval point) := by
      rewrite [DensePolynomial.eval_mul, leftResult.polynomial_eval point leftDefined,
        rightResult.polynomial_eval point rightDefined, pow_add]
      ring1
    _ = point ^ (result.poleOrder + (leftResult.poleOrder + rightResult.poleOrder - result.poleOrder)) *
        (left.eval point * right.eval point) := congrArg
      (fun exponent : Nat => point ^ exponent * (left.eval point * right.eval point)) exponentBalance
    _ = (DensePolynomial.shift
        (leftResult.poleOrder + rightResult.poleOrder - result.poleOrder) result.polynomial).eval point := by
      rewrite [DensePolynomial.eval_shift,
        result.polynomial_eval point (product.symbol.definedAt_of_nonzero nonzero), sourceProduct, pow_add]
      ring1

/-- The common polynomializing shift introduces exactly its retained extra zero-root count. -/
public theorem nonminimal_zeroMultiplicity {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) :
    (leftResult.polynomial * rightResult.polynomial).zeroMultiplicity = result.zeroMultiplicity +
      (leftResult.poleOrder + rightResult.poleOrder - result.poleOrder) := by
  rewrite [product.polynomial_identity leftResult rightResult result]
  exact result.nonminimal_zeroMultiplicity _

/-- The actual normalized product polynomial has the product of the same two input quadrances on the unit boundary.

The extra common polynomializing shift has exact unit quadrance. Its zero
roots therefore change neither this boundary payment nor either original
Laurent input's guarded domain.
-/
public theorem polynomial_normSq {left right : LaurentPolynomial} (product : Product left right)
    (leftResult : Normalized left) (rightResult : Normalized right)
    (result : Normalized product.symbol) (point : Gaussian.Basic.Canonical) (unit : point.normSq = 1) :
    Gaussian.Norm.Basic.normSq (result.polynomial.eval point) =
      Gaussian.Norm.Basic.normSq (leftResult.polynomial.eval point) *
        Gaussian.Norm.Basic.normSq (rightResult.polynomial.eval point) := by
  have same := congrArg (fun polynomial : DensePolynomial Gaussian.Basic.Canonical =>
    Gaussian.Norm.Basic.normSq (polynomial.eval point))
    (product.polynomial_identity leftResult rightResult result)
  have normUnit : Gaussian.Norm.Basic.normSq point = 1 :=
    (Gaussian.Norm.Basic.normSq_eq_canonical point).trans unit
  rewrite [DensePolynomial.eval_mul, Gaussian.Norm.Basic.normSq_mul, DensePolynomial.eval_shift,
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, normUnit, one_pow, mul_one] at same
  exact same.symm

end Purelib.Polynomial.Laurent.Arithmetic.Product
