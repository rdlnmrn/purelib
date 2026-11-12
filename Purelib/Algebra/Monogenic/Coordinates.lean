module

public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.Polynomial.Dense.Map.Basic
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Reverse
import Purelib.Tactic.Ring

/-!
# Polynomial coordinates of the original cyclic matrix algebra

The original distinguished column supplies the finite coefficients in its
original cyclic basis. Reversing that same bounded table gives an original
dense polynomial. Its Horner evaluation at the retained generator recovers
the entire original matrix, while arbitrary coefficient readings give its
corresponding finite weighted evaluation.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.List

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}
variable {cyclic : Cyclic generator}

/-- Read the same original distinguished column as descending polynomial coefficients. -/
@[expose] def polynomial (value : Element cyclic) : DensePolynomial K :=
  ⟨(List.ofFn (fun index => value.matrix index cyclic.origin)).reverse⟩

/-- The original coordinate polynomial has exactly the original cyclic dimension's slots. -/
theorem polynomial_length (value : Element cyclic) : value.polynomial.coeffs.length = dimension :=
  (Reverse.length_reverse _).trans OfFn.Basic.length_ofFn

/-- Mapping and evaluating the coordinate polynomial reads the same original finite weighted column. -/
theorem eval_map_polynomial {L : Type*} [CommRing L] (function : K → L) (mapZero : function 0 = 0)
    (value : Element cyclic) (point : L) :
    (Map.map function value.polynomial).eval point =
      sumFin (fun index : Fin dimension => function (value.matrix index cyclic.origin) * point ^ index.val) := by
  change DensePolynomial.evalCoeffs point
    ((List.ofFn (fun index => value.matrix index cyclic.origin)).reverse.map function) = _
  apply (Map.evalCoeffs_reverse_sum function mapZero point
    (List.ofFn (fun index => value.matrix index cyclic.origin))).trans
  apply sumFin_congr_size OfFn.Basic.length_ofFn
  intro first second same
  rewrite [same, OfFn.Basic.getD_ofFn]
  rfl

/-- Evaluating the original coordinate polynomial at the retained generator recovers the same algebra element. -/
theorem polynomial_root (value : Element cyclic) :
    (Map.map (scalar cyclic) value.polynomial).eval (root cyclic) = value := by
  apply eq_of_column
  intro row
  rewrite [eval_map_polynomial (scalar cyclic) (scalar_zero cyclic), sumFin_apply]
  calc
    _ = sumFin (fun index => if index = row then value.matrix index cyclic.origin else 0) := by
      apply sumFin_congr
      intro index
      rewrite [scalar_mul_apply, pow_matrix, root_matrix, ← cyclic.powers_eq index, cyclic.coordinate]
      by_cases same : index = row
      · rewrite [if_pos same, if_pos same.symm, mul_one]
        rfl
      · rewrite [if_neg same, if_neg (fun equal => same equal.symm), mul_zero]
        rfl
    _ = value.matrix row cyclic.origin := sumFin_ite_eq row (fun index => value.matrix index cyclic.origin)

variable {L : Type*} [CommRing L]

/-- Read the original coordinate polynomial by the original mapped Horner evaluator. -/
@[expose] def evaluate (function : K → L) (point : L) (value : Element cyclic) : L :=
  (Map.map function value.polynomial).eval point

/-- A zero-preserving coefficient reading sends the original algebra zero to target zero. -/
theorem evaluate_zero (function : K → L) (mapZero : function 0 = 0) (point : L) :
    evaluate function point (0 : Element cyclic) = 0 := by
  unfold evaluate
  rewrite [eval_map_polynomial function mapZero]
  apply (sumFin_congr (right := fun _ => (0 : L)) ?_).trans sumFin_zero
  intro index
  change function (Arithmetic.zero index cyclic.origin) * point ^ index.val = 0
  rewrite [Arithmetic.zero_apply, mapZero, zero_mul]
  rfl

/-- An additive coefficient reading preserves addition of the original algebra elements. -/
theorem evaluate_add (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (left right : Element cyclic) :
    evaluate function point (left + right) = evaluate function point left + evaluate function point right := by
  unfold evaluate
  repeat rewrite [eval_map_polynomial function mapZero]
  apply (sumFin_congr ?_).trans (sumFin_add _ _)
  intro index
  rewrite [add_matrix, Arithmetic.add_apply, mapAdd, add_mul]
  rfl

/-- A negation-preserving coefficient reading preserves original algebra negation. -/
theorem evaluate_neg (function : K → L) (mapZero : function 0 = 0)
    (mapNeg : ∀ value, function (-value) = -function value) (point : L) (value : Element cyclic) :
    evaluate function point (-value) = -evaluate function point value := by
  unfold evaluate
  repeat rewrite [eval_map_polynomial function mapZero]
  apply (sumFin_congr ?_).trans (sumFin_neg _)
  intro index
  have negativeEntry : (-1 : K) * value.matrix index cyclic.origin = -value.matrix index cyclic.origin := by
    ring0
  rewrite [neg_matrix, Arithmetic.scale_apply, negativeEntry, mapNeg, neg_mul]
  rfl

/-- A bounded original generator power reads its same rational power with its original coefficient reading.

Only the retained power-column identity is used. The coefficient reading need
not preserve multiplication, and no reduction by the source relation occurs
below the original cyclic dimension.
-/
theorem evaluate_scalar_power (function : K → L) (mapZero : function 0 = 0) (point : L)
    (coefficient : K) (power : Fin dimension) :
    evaluate function point (scalar cyclic coefficient * root cyclic ^ power.val) =
      function coefficient * point ^ power.val := by
  unfold evaluate
  rewrite [eval_map_polynomial function mapZero]
  calc
    _ = sumFin (fun index => if index = power then function coefficient * point ^ index.val else 0) := by
      apply sumFin_congr
      intro index
      rewrite [scalar_mul_apply, pow_matrix, root_matrix, ← cyclic.powers_eq power, cyclic.coordinate]
      by_cases same : index = power
      · rewrite [if_pos same, if_pos same, mul_one]
        rfl
      · rewrite [if_neg same, if_neg same, mul_zero, mapZero, zero_mul]
        rfl
    _ = function coefficient * point ^ power.val :=
      sumFin_ite_eq power (fun index => function coefficient * point ^ index.val)

/-- Reading an original embedded scalar returns its unchanged original coefficient reading. -/
theorem evaluate_scalar (function : K → L) (mapZero : function 0 = 0) (point : L) (coefficient : K) :
    evaluate function point (scalar cyclic coefficient) = function coefficient := by
  let zeroIndex : Fin dimension := ⟨0, Nat.zero_lt_of_lt cyclic.origin.isLt⟩
  have retained := evaluate_scalar_power (cyclic := cyclic) function mapZero point coefficient zeroIndex
  change evaluate function point (scalar cyclic coefficient * root cyclic ^ 0) = function coefficient * point ^ 0
    at retained
  rewrite [pow_zero, mul_one, pow_zero, mul_one] at retained
  exact retained

/-- In dimension at least two, reading the original generator returns the supplied target point. -/
theorem evaluate_root (function : K → L) (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (point : L) (bounded : 1 < dimension) : evaluate function point (root cyclic) = point := by
  have retained := evaluate_scalar_power (cyclic := cyclic) function mapZero point (1 : K) ⟨1, bounded⟩
  change evaluate function point (scalar cyclic 1 * root cyclic ^ 1) = function 1 * point ^ 1 at retained
  rewrite [scalar_one, pow_one, one_mul, mapOne, pow_one, one_mul] at retained
  exact retained

/-- A coefficient reading that respects one scalar action retains that same scalar action after evaluation. -/
theorem evaluate_scalar_mul (function : K → L) (mapZero : function 0 = 0) (point : L)
    (coefficient : K) (image : L) (mapScale : ∀ value, function (coefficient * value) = image * function value)
    (value : Element cyclic) :
    evaluate function point (scalar cyclic coefficient * value) = image * evaluate function point value := by
  unfold evaluate
  repeat rewrite [eval_map_polynomial function mapZero]
  apply (sumFin_congr ?_).trans (sumFin_mul_left image _)
  intro index
  rewrite [scalar_mul_apply, mapScale, mul_assoc]
  rfl

/-- The scalar-action discrepancy is the same original coordinate reading of the coefficient discrepancies.

Only preservation of zero is required. The original scalar product reads
the same retained distinguished column, and both finite sums retain their
original bounded indices.
-/
theorem evaluate_scalar_mul_sub (function : K → L) (mapZero : function 0 = 0) (point : L)
    (coefficient : K) (value : Element cyclic) :
    evaluate function point (scalar cyclic coefficient * value) - function coefficient * evaluate function point value =
      evaluate (fun entry => function (coefficient * entry) - function coefficient * function entry) point value := by
  have errorZero : function (coefficient * 0) - function coefficient * function 0 = 0 := by
    rewrite [mul_zero, mapZero, mul_zero, sub_self]
    rfl
  unfold evaluate
  repeat rewrite [eval_map_polynomial function mapZero]
  rewrite [eval_map_polynomial _ errorZero]
  have first : sumFin (fun index =>
      function ((scalar cyclic coefficient * value).matrix index cyclic.origin) * point ^ index.val) =
      sumFin (fun index => function (coefficient * value.matrix index cyclic.origin) * point ^ index.val) := by
    apply sumFin_congr
    intro index
    rewrite [scalar_mul_apply]
    rfl
  have second : function coefficient *
      sumFin (fun index => function (value.matrix index cyclic.origin) * point ^ index.val) =
      sumFin (fun index => (function coefficient * function (value.matrix index cyclic.origin)) *
        point ^ index.val) := by
    apply Eq.symm
    apply (sumFin_congr (fun _ => mul_assoc _ _ _)).trans
    exact sumFin_mul_left _ _
  apply (congrArg₂ (· - ·) first second).trans
  apply (sumFin_sub _ _).symm.trans
  apply sumFin_congr
  intro index
  ring0

/-- An additive zero-preserving coefficient reading retains original finite algebra sums. -/
theorem evaluate_sumFin (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) {count : Nat} (values : Fin count → Element cyclic) :
    evaluate function point (sumFin values) = sumFin (fun index => evaluate function point (values index)) := by
  exact map_sumFin (evaluate function point) (evaluate_zero function mapZero point)
    (evaluate_add function mapZero mapAdd point) values

/-- An additive coefficient reading expands the original matrix product through its same two finite indices. -/
theorem evaluate_mul_sums (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (left right : Element cyclic) :
    evaluate function point (left * right) = sumFin (fun row => sumFin (fun middle =>
      function (left.matrix row middle * right.matrix middle cyclic.origin) * point ^ row.val)) := by
  unfold evaluate
  rewrite [eval_map_polynomial function mapZero]
  apply sumFin_congr
  intro row
  rewrite [mul_matrix, Multiplication.mul_apply, map_sumFin function mapZero mapAdd]
  exact (sumFin_mul_right _ _).symm

/-- The original generator-action discrepancy separates exact column residuals and coefficient-product errors.

Every residual uses the same original generator column and candidate powers.
The remaining term contains precisely the original coefficient reading's
multiplication discrepancies; no multiplicativity is assumed.
-/
theorem evaluate_root_mul_sub (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (value : Element cyclic) :
    evaluate function point (root cyclic * value) - point * evaluate function point value =
      sumFin (fun column => function (value.matrix column cyclic.origin) *
        (sumFin (fun row => function (generator row column) * point ^ row.val) - point * point ^ column.val)) +
      sumFin (fun row => sumFin (fun column =>
        (function (generator row column * value.matrix column cyclic.origin) -
          function (generator row column) * function (value.matrix column cyclic.origin)) * point ^ row.val)) := by
  let errors := sumFin (fun row => sumFin (fun column =>
    (function (generator row column * value.matrix column cyclic.origin) -
      function (generator row column) * function (value.matrix column cyclic.origin)) * point ^ row.val))
  let main := sumFin (fun column => function (value.matrix column cyclic.origin) *
    sumFin (fun row => function (generator row column) * point ^ row.val))
  let scaledTerm := sumFin (fun column =>
    function (value.matrix column cyclic.origin) * (point * point ^ column.val))
  have original := evaluate_mul_sums function mapZero mapAdd point (root cyclic) value
  have expanded : evaluate function point (root cyclic * value) =
      sumFin (fun row => sumFin (fun column =>
        (function (generator row column) * function (value.matrix column cyclic.origin)) * point ^ row.val)) +
          errors := by
    apply original.trans
    apply Eq.trans ?_ (sumFin_add _ _)
    apply sumFin_congr
    intro row
    apply Eq.trans ?_ (sumFin_add _ _)
    apply sumFin_congr
    intro column
    rewrite [root_matrix]
    ring0
  have collected : sumFin (fun row => sumFin (fun column =>
        (function (generator row column) * function (value.matrix column cyclic.origin)) * point ^ row.val)) =
      sumFin (fun column => function (value.matrix column cyclic.origin) *
        sumFin (fun row => function (generator row column) * point ^ row.val)) := by
    apply (sumFin_swap _).trans
    apply sumFin_congr
    intro column
    apply (sumFin_congr (right := fun row => function (value.matrix column cyclic.origin) *
      (function (generator row column) * point ^ row.val)) ?_).trans (sumFin_mul_left _ _)
    intro row
    ring0
  have scaled : point * evaluate function point value =
      sumFin (fun column => function (value.matrix column cyclic.origin) * (point * point ^ column.val)) := by
    unfold evaluate
    rewrite [eval_map_polynomial function mapZero]
    apply Eq.symm
    apply (sumFin_congr (right := fun column => point *
      (function (value.matrix column cyclic.origin) * point ^ column.val)) ?_).trans (sumFin_mul_left _ _)
    intro column
    ring0
  have decomposition : evaluate function point (root cyclic * value) - point * evaluate function point value =
      (main - scaledTerm) + errors := by
    rewrite [expanded, collected, scaled]
    change (main + errors) - scaledTerm = (main - scaledTerm) + errors
    ring0
  apply decomposition.trans
  apply congrArg (· + errors)
  apply (sumFin_sub _ _).symm.trans
  apply sumFin_congr
  intro column
  ring0

/-- The original product-reading error splits into scalar-action and bounded power-action errors.

The finite coordinate sum is reconstructed from the same distinguished
column. Only additivity is required of the coefficient reading; the two
displayed discrepancies retain every failure of multiplication explicitly.
-/
theorem evaluate_mul_sub (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (left right : Element cyclic) :
    evaluate function point (left * right) - evaluate function point left * evaluate function point right =
      sumFin (fun index : Fin dimension =>
        (evaluate function point (scalar cyclic (left.matrix index cyclic.origin) *
            (root cyclic ^ index.val * right)) -
          function (left.matrix index cyclic.origin) * evaluate function point (root cyclic ^ index.val * right)) +
        function (left.matrix index cyclic.origin) *
          (evaluate function point (root cyclic ^ index.val * right) -
            point ^ index.val * evaluate function point right)) := by
  have reconstructed : left = sumFin (fun index : Fin dimension =>
      scalar cyclic (left.matrix index cyclic.origin) * root cyclic ^ index.val) :=
    (polynomial_root left).symm.trans (eval_map_polynomial (scalar cyclic) (scalar_zero cyclic) left (root cyclic))
  have originalProduct := (congrArg (· * right) reconstructed).trans (sumFin_mul_right _ _).symm
  have expanded := congrArg (evaluate function point) originalProduct
  rewrite [evaluate_sumFin function mapZero mapAdd] at expanded
  have targetProduct : evaluate function point left * evaluate function point right =
      sumFin (fun index : Fin dimension => function (left.matrix index cyclic.origin) *
        (point ^ index.val * evaluate function point right)) := by
    unfold evaluate
    rewrite [eval_map_polynomial function mapZero]
    apply (sumFin_mul_right _ _).symm.trans
    apply sumFin_congr
    intro index
    exact mul_assoc _ _ _
  apply Eq.trans ((congrArg₂ (· - ·) expanded targetProduct).trans (sumFin_sub _ _).symm)
  apply sumFin_congr
  intro index
  rewrite [mul_assoc]
  ring0

/-- A bounded original coefficient table reads exactly as its target Horner polynomial.

Its displayed slot count stays within the original cyclic dimension. The
retained power-column identities therefore read every original term before
any source-relation reduction, requiring only additive coefficient readings.
-/
theorem evaluate_polynomial (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (source : DensePolynomial K) (bounded : source.coeffs.length ≤ dimension) :
    evaluate function point ((Map.map (scalar cyclic) source).eval (root cyclic)) =
      (Map.map function source).eval point := by
  have original := Map.evalCoeffs_reverse_sum (scalar cyclic) (scalar_zero cyclic) (root cyclic) source.coeffs.reverse
  rewrite [Reverse.reverse_reverse] at original
  have read := congrArg (evaluate function point) original
  rewrite [evaluate_sumFin function mapZero mapAdd] at read
  have target := Map.evalCoeffs_reverse_sum function mapZero point source.coeffs.reverse
  rewrite [Reverse.reverse_reverse] at target
  apply read.trans
  apply Eq.trans ?_ target.symm
  apply sumFin_congr
  intro index
  have sourceBound : index.val < source.coeffs.length := (Reverse.length_reverse source.coeffs) ▸ index.isLt
  have indexBound : index.val < dimension := Nat.lt_of_lt_of_le sourceBound bounded
  exact evaluate_scalar_power function mapZero point (getD source.coeffs.reverse index.val 0) ⟨index.val, indexBound⟩

end Purelib.Algebra.Monogenic.Cyclic.Element

end
