module

public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.List.Map
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Reverse
import Purelib.Data.List.GetD

/-!
# Maps of original dense coefficient tables

The same structural coefficient map visits every descending entry in order.
It does not require a field. Scalar operation certificates transport the
original Horner scan, while preservation of zero alone transports evaluation
past the original leading-zero normalization.
-/

namespace Purelib.Polynomial.Dense.Map

open Purelib.Polynomial.Dense.Basic
open Purelib.Data
open Purelib.Data.List (getD getD_map)
open Purelib.Algebra.FiniteSum.Fin

/-- The original descending coefficient representation on either side of a map. -/
public abbrev CoefficientPolynomial (K : Type*) := DensePolynomial K

/-- Apply the supplied scalar function to each original descending coefficient. -/
@[expose] public def map {K L : Type*} (function : K → L) (polynomial : CoefficientPolynomial K) :
    CoefficientPolynomial L := ⟨polynomial.coeffs.map function⟩

/-- Coefficient mapping retains the same original ordered list map. -/
@[simp] public theorem map_coeffs {K L : Type*} (function : K → L) (polynomial : CoefficientPolynomial K) :
    (map function polynomial).coeffs = polynomial.coeffs.map function := rfl

/-- Coefficient mapping retains exactly the original number of coefficient slots. -/
public theorem map_length {K L : Type*} (function : K → L) (polynomial : CoefficientPolynomial K) :
    (map function polynomial).coeffs.length = polynomial.coeffs.length :=
  List.Map.length_map function polynomial.coeffs

/-- Two successive coefficient maps compose on the same original coefficient spine. -/
public theorem map_map {K L M : Type*} (second : L → M) (first : K → L)
    (polynomial : CoefficientPolynomial K) :
    map second (map first polynomial) = map (second ∘ first) polynomial :=
  DensePolynomial.ext (List.Map.map_map second first polynomial.coeffs)

/-- Mapping the identity function preserves the original polynomial data. -/
public theorem map_id {K : Type*} (polynomial : CoefficientPolynomial K) : map id polynomial = polynomial :=
  DensePolynomial.ext (List.Map.map_id polynomial.coeffs)

section Leading

variable {K L : Type*} [Zero K] [DecidableEq K] [Zero L] [DecidableEq L]

/-- A zero-preserving coefficient reading retains the leading-zero scan when its first retained head stays nonzero. -/
private theorem map_dropWhile_of_head_nonzero (function : K → L) (mapZero : function 0 = 0) :
    ∀ coefficients : List K,
      function ((coefficients.dropWhile (· = 0)).headD 0) ≠ 0 →
        (coefficients.dropWhile (· = 0)).map function =
          (coefficients.map function).dropWhile (· = 0)
  | [], nonzero => False.elim (nonzero mapZero)
  | coefficient :: remaining, nonzero => by
      by_cases zero : coefficient = 0
      · have source := List.DropWhile.cons_of_true (fun value : K => decide (value = 0))
          coefficient remaining (decide_eq_true zero)
        rewrite [source] at nonzero
        rewrite [source, List.map_cons, zero, mapZero,
          List.DropWhile.cons_of_true (fun value : L => decide (value = 0)) 0
            (remaining.map function) (decide_eq_true rfl)]
        exact map_dropWhile_of_head_nonzero function mapZero remaining nonzero
      · have source := List.DropWhile.cons_of_false (fun value : K => decide (value = 0))
          coefficient remaining (decide_eq_false zero)
        rewrite [source] at nonzero
        have imageNonzero : function coefficient ≠ 0 := nonzero
        rewrite [source, List.map_cons,
          List.DropWhile.cons_of_false (fun value : L => decide (value = 0)) (function coefficient)
            (remaining.map function) (decide_eq_false imageNonzero)]
        rfl

/-- A zero-preserving reading commutes with normalization when the original leading coefficient has nonzero image.

Later nonzero coefficients may map to zero. Only the same first retained
coefficient determines where both original leading-zero scans stop.
-/
public theorem map_normalize_of_leading_nonzero (function : K → L) (mapZero : function 0 = 0)
    (polynomial : CoefficientPolynomial K) (leadingNonzero : function polynomial.leadingCoeff ≠ 0) :
    map function polynomial.normalize = (map function polynomial).normalize :=
  DensePolynomial.ext (map_dropWhile_of_head_nonzero function mapZero polynomial.coeffs leadingNonzero)

/-- Retaining the nonzero image of the original leading coefficient preserves the same natural degree. -/
public theorem map_natDegree_of_leading_nonzero (function : K → L) (mapZero : function 0 = 0)
    (polynomial : CoefficientPolynomial K) (leadingNonzero : function polynomial.leadingCoeff ≠ 0) :
    (map function polynomial).natDegree = polynomial.natDegree := by
  change (map function polynomial).normalize.coeffs.length - 1 = polynomial.normalize.coeffs.length - 1
  rewrite [← map_normalize_of_leading_nonzero function mapZero polynomial leadingNonzero]
  exact congrArg (fun count => count - 1) (map_length function polynomial.normalize)

/-- A locally retained leading image is the exact leading coefficient of the mapped original table. -/
public theorem map_leadingCoeff_of_leading_nonzero (function : K → L) (mapZero : function 0 = 0)
    (polynomial : CoefficientPolynomial K) (leadingNonzero : function polynomial.leadingCoeff ≠ 0) :
    (map function polynomial).leadingCoeff = function polynomial.leadingCoeff := by
  change (map function polynomial).normalize.coeffs.headD 0 = function (polynomial.normalize.coeffs.headD 0)
  rewrite [← map_normalize_of_leading_nonzero function mapZero polynomial leadingNonzero]
  change (polynomial.normalize.coeffs.map function).headD 0 = function (polynomial.normalize.coeffs.headD 0)
  cases polynomial.normalize.coeffs with
  | nil => exact mapZero.symm
  | cons _ _ => rfl

end Leading

variable {K L : Type*} [CommRing K] [CommRing L]

/-- Scalar multiplication and addition certificates transport one retained Horner accumulator. -/
private theorem map_evalCoeffs_from (function : K → L)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (point : K) : ∀ (coefficients : List K) (accumulator : K),
      function (coefficients.foldl (fun current coefficient => current * point + coefficient) accumulator) =
        (coefficients.map function).foldl
          (fun current coefficient => current * function point + coefficient) (function accumulator)
  | [], _ => rfl
  | coefficient :: remaining, accumulator => by
      change function (remaining.foldl _ (accumulator * point + coefficient)) =
        (remaining.map function).foldl _ (function accumulator * function point + function coefficient)
      have retained := map_evalCoeffs_from function mapAdd mapMul point remaining
        (accumulator * point + coefficient)
      rewrite [mapAdd, mapMul] at retained
      exact retained

/-- A scalar map preserving zero, addition and multiplication commutes with original Horner evaluation. -/
public theorem map_eval (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (polynomial : CoefficientPolynomial K) (point : K) :
    function (polynomial.eval point) = (map function polynomial).eval (function point) := by
  unfold DensePolynomial.eval DensePolynomial.evalCoeffs map
  rewrite [← mapZero]
  exact map_evalCoeffs_from function mapAdd mapMul point polynomial.coeffs 0

/-- A zero-preserving coefficient map retains evaluation after the original leading-zero scan. -/
private theorem eval_map_dropWhile_zero [DecidableEq K]
    (function : K → L) (mapZero : function 0 = 0) (point : L) : ∀ coefficients : List K,
    DensePolynomial.evalCoeffs point ((coefficients.dropWhile (· = 0)).map function) =
      DensePolynomial.evalCoeffs point (coefficients.map function)
  | [] => rfl
  | coefficient :: remaining => by
      by_cases zero : coefficient = 0
      · rewrite [List.DropWhile.cons_of_true _ coefficient remaining (decide_eq_true zero),
          List.map_cons, zero, mapZero, DensePolynomial.evalCoeffs_cons_zero]
        exact eval_map_dropWhile_zero function mapZero point remaining
      · rewrite [List.DropWhile.cons_of_false _ coefficient remaining (decide_eq_false zero)]
        rfl

/-- Mapping the original normalized table preserves every target evaluation when scalar zero is preserved.

No injectivity, inverse or field structure is required. The target point need
not be the image of a source scalar.
-/
public theorem map_normalize_eval [DecidableEq K]
    (function : K → L) (mapZero : function 0 = 0) (polynomial : CoefficientPolynomial K) (point : L) :
    (map function polynomial.normalize).eval point = (map function polynomial).eval point :=
  eval_map_dropWhile_zero function mapZero point polynomial.coeffs

/-- Reversing and mapping an ascending table retains its original coefficient-power sum. -/
public theorem evalCoeffs_reverse_sum (function : K → L) (mapZero : function 0 = 0)
    (point : L) (coefficients : List K) :
    DensePolynomial.evalCoeffs point (coefficients.reverse.map function) =
      sumFin (fun index : Fin coefficients.length =>
        function (getD coefficients index.val 0) * point ^ index.val) := by
  rewrite [Purelib.Data.List.Reverse.map_reverse, DensePolynomial.evalCoeffs_reverse_sum]
  apply sumFin_congr_size (List.Map.length_map function coefficients)
  intro first second same
  have entry := getD_map function coefficients first.val 0
  rewrite [mapZero] at entry
  rewrite [entry, same]
  rfl

end Purelib.Polynomial.Dense.Map
