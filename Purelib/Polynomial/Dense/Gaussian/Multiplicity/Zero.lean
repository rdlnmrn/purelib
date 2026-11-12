module

public import Purelib.Polynomial.Dense.ZeroMultiplicity
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Zero-root multiplicity of Gaussian polynomial products

The original dense product is factored through the two retained zero cores.
Their actual nonzero constant values certify that no further zero root is
introduced, while the original shifts add their exact trailing-zero counts.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Zero

open Purelib.Data
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic

/-- The original dense product adds the actual zero-root multiplicities of its nonzero inputs. -/
public theorem product (left right : DensePolynomial Gaussian.Basic.Canonical)
    (leftNonzero : left.isZero = false) (rightNonzero : right.isZero = false) :
    (left * right).zeroMultiplicity = left.zeroMultiplicity + right.zeroMultiplicity := by
  let core := left.zeroCore * right.zeroCore
  have coreNonzero : core.isZero = false := DensePolynomial.isZero_mul_eq_false
    (DensePolynomial.zeroCore_nonzero leftNonzero) (DensePolynomial.zeroCore_nonzero rightNonzero)
  have coreAtZero : core.eval 0 ≠ 0 := by
    change (left.zeroCore * right.zeroCore).eval 0 ≠ 0
    rewrite [DensePolynomial.eval_mul]
    exact Gaussian.Field.mul_ne_zero_direct
      (DensePolynomial.zeroCore_eval_zero_nonzero leftNonzero)
      (DensePolynomial.zeroCore_eval_zero_nonzero rightNonzero)
  have coreMultiplicity := DensePolynomial.zeroMultiplicity_eq_zero_of_eval_zero_nonzero core coreAtZero
  have identity : left * right =
      DensePolynomial.shift (left.zeroMultiplicity + right.zeroMultiplicity) core := by
    apply Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq
      (DensePolynomial.normalize_mul _ _) (DensePolynomial.normalize_shift _ _)
    intro point
    change (left * right).eval point =
      (DensePolynomial.shift (left.zeroMultiplicity + right.zeroMultiplicity)
        (left.zeroCore * right.zeroCore)).eval point
    rewrite [DensePolynomial.eval_mul, DensePolynomial.eval_shift, DensePolynomial.eval_mul,
      DensePolynomial.eval_zeroCore_mul_power left point,
      DensePolynomial.eval_zeroCore_mul_power right point, pow_add]
    ring1
  rewrite [identity, DensePolynomial.zeroMultiplicity_shift _ coreNonzero, coreMultiplicity]
  exact Nat.zero_add _

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Zero
