module

public import Purelib.Polynomial.Dense.TrimTrailing
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.DropWhile.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Exact zero-root multiplicity in the original dense coefficient table

Leading normalization and the original trailing-zero scan retain the factor
left after removing every zero root. The suffix length is an executable
natural multiplicity and its original coefficient decomposition is exact.
-/

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense
open Purelib.Data.List

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Count the original normalized polynomial's trailing zero coefficients.

For the zero polynomial the retained count is zero. For a nonzero polynomial
the removed finite zero block gives its exact zero-root multiplicity. -/
@[expose] public def zeroMultiplicity (polynomial : DensePolynomial K) : Nat :=
  (TrimTrailing.trailingPart polynomial.normalize.coeffs).length

/-- Remove the original normalized polynomial's trailing zero coefficients. -/
@[expose] public def zeroCore (polynomial : DensePolynomial K) : DensePolynomial K :=
  ⟨TrimTrailing.trimTrailing polynomial.normalize.coeffs⟩

/-- The retained zero core and its exact zero block reconstruct the normalized coefficients. -/
public theorem zeroCore_coefficients (polynomial : DensePolynomial K) :
    polynomial.zeroCore.coeffs ++ List.replicate polynomial.zeroMultiplicity 0 =
      polynomial.normalize.coeffs := by
  change TrimTrailing.trimTrailing polynomial.normalize.coeffs ++
    List.replicate (TrimTrailing.trailingPart polynomial.normalize.coeffs).length 0 = _
  rewrite [← TrimTrailing.trailingPart_eq_replicate]
  exact TrimTrailing.trimTrailing_append_trailingPart _

/-- The zero core of a nonzero polynomial retains its original nonzero leading coefficient. -/
private theorem zeroCore_shape {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) :
    ∃ remaining, polynomial.zeroCore.coeffs = polynomial.leadingCoeff :: remaining := by
  obtain ⟨remaining, shape, _⟩ := normalized_coeffs_shape nonzero
  change ∃ tail, TrimTrailing.trimTrailing polynomial.normalize.coeffs = _
  rewrite [shape]
  exact TrimTrailing.trimTrailing_cons_of_leading_nonzero _ _ (leadingCoeff_ne_zero nonzero)

/-- Removing zero roots preserves an already normalized nonzero leading coefficient. -/
public theorem zeroCore_normalized {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) : polynomial.zeroCore.normalize = polynomial.zeroCore := by
  obtain ⟨remaining, shape⟩ := zeroCore_shape nonzero
  apply ext
  change polynomial.zeroCore.coeffs.dropWhile (· = 0) = polynomial.zeroCore.coeffs
  rewrite [shape]
  exact DropWhile.cons_of_false (fun value : K => decide (value = 0)) _ _
    (decide_eq_false (leadingCoeff_ne_zero nonzero))

/-- A nonzero polynomial retains a nonzero zero core. -/
public theorem zeroCore_nonzero {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) : polynomial.zeroCore.isZero = false := by
  obtain ⟨remaining, shape⟩ := zeroCore_shape nonzero
  change polynomial.zeroCore.normalize.coeffs.isEmpty = false
  rewrite [zeroCore_normalized nonzero, shape]
  exact Eq.refl _

/-- A nonzero zero core has a nonzero original constant coefficient. -/
public theorem zeroCore_constant_nonzero {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) :
    Coefficients.constantCoefficient polynomial.zeroCore.coeffs ≠ 0 := by
  obtain ⟨remaining, shape⟩ := zeroCore_shape nonzero
  have endpoint := TrimTrailing.trimTrailing_constant_nonzero polynomial.normalize.coeffs
    polynomial.leadingCoeff remaining shape
  rewrite [shape]
  exact endpoint

/-- The original polynomial value factors by its exact zero-root multiplicity. -/
public theorem eval_zeroCore_mul_power (polynomial : DensePolynomial K) (point : K) :
    polynomial.eval point = polynomial.zeroCore.eval point * point ^ polynomial.zeroMultiplicity :=
  (eval_normalize polynomial point).symm.trans
    (TrimTrailing.eval_trimTrailing_mul_power point polynomial.normalize.coeffs)

/-- Reattach the exact removed zero block to recover the normalized original polynomial. -/
public theorem shift_zeroCore {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) :
    shift polynomial.zeroMultiplicity polynomial.zeroCore = polynomial.normalize := by
  apply ext
  rewrite [shift, if_neg (fun zero =>
    Bool.noConfusion ((zeroCore_nonzero nonzero).symm.trans zero)),
    zeroCore_normalized nonzero]
  exact zeroCore_coefficients polynomial

omit [DecidableEq K] in
/-- Evaluation at zero retains the original last-coefficient accumulator. -/
private theorem foldl_zero_eval (coefficients : List K) (accumulator : K) :
    coefficients.foldl (fun value coefficient => value * 0 + coefficient) accumulator =
      coefficients.foldl (fun _ coefficient => coefficient) accumulator := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change remaining.foldl (fun value coefficient => value * 0 + coefficient)
        (accumulator * 0 + coefficient) =
          remaining.foldl (fun _ coefficient => coefficient) coefficient
      rewrite [mul_zero, zero_add]
      exact inductionHypothesis coefficient

omit [DecidableEq K] in
/-- Horner evaluation at zero equals the original constant-coefficient readback. -/
public theorem eval_zero_eq_constantCoefficient (polynomial : DensePolynomial K) :
    polynomial.eval 0 = Coefficients.constantCoefficient polynomial.coeffs := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => rfl
      | cons coefficient remaining =>
          change remaining.foldl (fun value coefficient => value * 0 + coefficient)
            ((0 : K) * 0 + coefficient) = remaining.foldl (fun _ coefficient => coefficient) coefficient
          rewrite [mul_zero, zero_add]
          exact foldl_zero_eval remaining coefficient

/-- A nonzero zero core evaluates nontrivially at zero. -/
public theorem zeroCore_eval_zero_nonzero {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) : polynomial.zeroCore.eval 0 ≠ 0 := by
  rewrite [eval_zero_eq_constantCoefficient]
  exact zeroCore_constant_nonzero nonzero

/-- Prefixing a zero block extends the original zero-prefix scan by that exact block. -/
private theorem takeWhile_replicate_zero_append (count : Nat) (coefficients : List K) :
    (List.replicate count 0 ++ coefficients).takeWhile (· = 0) =
      List.replicate count 0 ++ coefficients.takeWhile (· = 0) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (0 :: (List.replicate count 0 ++ coefficients)).takeWhile (· = 0) =
        0 :: (List.replicate count 0 ++ coefficients.takeWhile (· = 0))
      rewrite [List.takeWhile, decide_eq_true (Eq.refl (0 : K))]
      exact congrArg (List.cons (0 : K)) inductionHypothesis

/-- Appending a zero block adds its length to the retained trailing-zero count. -/
private theorem trailingPart_length_append_replicate (coefficients : List K) (count : Nat) :
    (TrimTrailing.trailingPart (coefficients ++ List.replicate count 0)).length =
      (TrimTrailing.trailingPart coefficients).length + count := by
  unfold TrimTrailing.trailingPart
  rewrite [Reverse.length_reverse, Reverse.length_reverse, Reverse.reverse_append,
    Reverse.reverse_replicate, takeWhile_replicate_zero_append,
    Append.length_append, Replicate.length_replicate]
  exact Nat.add_comm _ _

/-- A natural degree shift adds exactly that many zero roots to a nonzero polynomial. -/
public theorem zeroMultiplicity_shift (polynomial : DensePolynomial K)
    (nonzero : polynomial.isZero = false) (count : Nat) :
    (shift count polynomial).zeroMultiplicity = polynomial.zeroMultiplicity + count := by
  change (TrimTrailing.trailingPart (shift count polynomial).normalize.coeffs).length = _
  rewrite [normalize_shift, shift, if_neg (fun zero => Bool.noConfusion (nonzero.symm.trans zero))]
  exact trailingPart_length_append_replicate polynomial.normalize.coeffs count

/-- A coefficient table with a nonzero constant has no trailing zero coefficients. -/
private theorem trailingPart_length_zero_of_constant_nonzero (coefficients : List K)
    (nonzero : Coefficients.constantCoefficient coefficients ≠ 0) :
    (TrimTrailing.trailingPart coefficients).length = 0 := by
  have reconstruction := TrimTrailing.trimTrailing_append_trailingPart coefficients
  have zeros := TrimTrailing.trailingPart_eq_replicate coefficients
  cases countEq : (TrimTrailing.trailingPart coefficients).length with
  | zero => rfl
  | succ amount =>
      have lastZero : Coefficients.constantCoefficient coefficients = 0 := by
        rewrite [← reconstruction, zeros, countEq, Replicate.replicate_add amount 1 (0 : K),
          ← Append.append_assoc]
        exact Coefficients.constantCoefficient_append_singleton _ 0
      exact (nonzero lastZero).elim

/-- A polynomial nonzero at zero has no zero-root multiplicity. -/
public theorem zeroMultiplicity_eq_zero_of_eval_zero_nonzero (polynomial : DensePolynomial K)
    (nonzero : polynomial.eval 0 ≠ 0) : polynomial.zeroMultiplicity = 0 := by
  apply trailingPart_length_zero_of_constant_nonzero polynomial.normalize.coeffs
  intro constantZero
  apply nonzero
  calc
    polynomial.eval 0 = polynomial.normalize.eval 0 := (eval_normalize polynomial 0).symm
    _ = Coefficients.constantCoefficient polynomial.normalize.coeffs := eval_zero_eq_constantCoefficient _
    _ = 0 := constantZero

/-- Removing all zero roots leaves zero multiplicity exactly zero. -/
public theorem zeroMultiplicity_zeroCore {polynomial : DensePolynomial K}
    (nonzero : polynomial.isZero = false) : polynomial.zeroCore.zeroMultiplicity = 0 := by
  unfold zeroMultiplicity
  rewrite [zeroCore_normalized nonzero]
  exact trailingPart_length_zero_of_constant_nonzero _ (zeroCore_constant_nonzero nonzero)

end Purelib.Polynomial.Dense.Basic.DensePolynomial
