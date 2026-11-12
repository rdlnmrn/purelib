module

public import Purelib.Algebra.Monogenic.Coordinates
public import Purelib.Polynomial.Dense.Division.Synthetic
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Data.List.Prefix.Take
import Purelib.Tactic.QuotientFreeOmega

/-!
# Exact readings of original synthetic quotient coefficients

Each same quotient coefficient is the original source-prefix Horner reading.
Its prefix fits inside the original cyclic dimension, so the distinguished
column reads it exactly at the target point without any multiplication law
for the coefficient reading.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.List.Prefix

variable {K L : Type*} [CommRing K] [CommRing L]
variable {dimension : Nat} {generator : SquareMatrix K dimension} {cyclic : Cyclic generator}

/-- Reading the actual original synthetic quotient gives the same original quotient at the supplied target point.

The source has at most one more slot than the cyclic dimension. Every
quotient prefix therefore fits the original bounded power-column identities.
Only the parent reading's zero and addition laws are used.
-/
theorem evaluate_synthetic_quotient (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (point : L) (source : DensePolynomial K) (bounded : source.coeffs.length ≤ dimension + 1) :
    Map.map (evaluate function point)
        (Synthetic.divide (Map.map (scalar cyclic) source) (root cyclic)).quotient =
      (Synthetic.divide (Map.map function source) point).quotient := by
  let original := Synthetic.divide (Map.map (scalar cyclic) source) (root cyclic)
  let observed := Synthetic.divide (Map.map function source) point
  have originalCount : original.quotient.coeffs.length = source.coeffs.length - 1 :=
    original.quotient_length.trans (congrArg (fun count => count - 1) (Map.map_length (scalar cyclic) source))
  have observedCount : observed.quotient.coeffs.length = source.coeffs.length - 1 :=
    observed.quotient_length.trans (congrArg (fun count => count - 1) (Map.map_length function source))
  have readZero : evaluate function point (0 : Element cyclic) = 0 := evaluate_zero function mapZero point
  apply DensePolynomial.ext
  apply eq_of_getD (0 : L)
  · exact (List.Map.length_map (evaluate function point) original.quotient.coeffs).trans
      (originalCount.trans observedCount.symm)
  · intro slot
    have read := getD_map (evaluate function point) original.quotient.coeffs slot 0
    rewrite [readZero] at read
    change getD (original.quotient.coeffs.map (evaluate function point)) slot 0 =
      getD observed.quotient.coeffs slot 0
    rewrite [read]
    by_cases within : slot < source.coeffs.length - 1
    · have originalBound : slot < (Map.map (scalar cyclic) source).coeffs.length - 1 := by
        rewrite [Map.map_length]
        exact within
      have observedBound : slot < (Map.map function source).coeffs.length - 1 := by
        rewrite [Map.map_length]
        exact within
      have originalSlot := Synthetic.quotient_getD_eq_eval_take (Map.map (scalar cyclic) source)
        (root cyclic) ⟨slot, originalBound⟩
      have observedSlot := Synthetic.quotient_getD_eq_eval_take (Map.map function source) point
        ⟨slot, observedBound⟩
      change getD original.quotient.coeffs slot 0 =
        (⟨((source.coeffs.map (scalar cyclic)).take (slot + 1))⟩ : DensePolynomial (Element cyclic)).eval
          (root cyclic) at originalSlot
      change getD observed.quotient.coeffs slot 0 =
        (⟨((source.coeffs.map function).take (slot + 1))⟩ : DensePolynomial L).eval point at observedSlot
      have prefixLength : (source.coeffs.take (slot + 1)).length ≤ dimension := by
        have sourceWithin : slot + 1 ≤ source.coeffs.length := by omega0
        rewrite [Take.length_take_of_le sourceWithin]
        omega0
      have exactPrefix := evaluate_polynomial (cyclic := cyclic) function mapZero mapAdd point
        (⟨source.coeffs.take (slot + 1)⟩ : DensePolynomial K) prefixLength
      have sourcePrefix : (⟨(source.coeffs.map (scalar cyclic)).take (slot + 1)⟩ :
          DensePolynomial (Element cyclic)) = Map.map (scalar cyclic) ⟨source.coeffs.take (slot + 1)⟩ :=
        DensePolynomial.ext (List.Map.map_take _ _ _).symm
      have targetPrefix : (⟨(source.coeffs.map function).take (slot + 1)⟩ : DensePolynomial L) =
          Map.map function ⟨source.coeffs.take (slot + 1)⟩ :=
        DensePolynomial.ext (List.Map.map_take _ _ _).symm
      rewrite [originalSlot, observedSlot, sourcePrefix, targetPrefix]
      exact exactPrefix
    · have sourceDefault : getD original.quotient.coeffs slot 0 = 0 :=
        getD_eq_default_of_length_le original.quotient.coeffs slot 0
          (originalCount ▸ Nat.le_of_not_lt within)
      have targetDefault : getD observed.quotient.coeffs slot 0 = 0 :=
        getD_eq_default_of_length_le observed.quotient.coeffs slot 0
          (observedCount ▸ Nat.le_of_not_lt within)
      rewrite [sourceDefault, targetDefault, readZero]
      rfl

end Purelib.Algebra.Monogenic.Cyclic.Element

end
