module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.DropWhile.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Leading

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Data

open Purelib.Polynomial

/-!
# Gaussian coordinate and scalar-constant polynomials

The dense coordinate, normalized scalar constants and doubled parameter retain
their original finite coefficient tables. Scalar evaluation and leading-term
certificates concern those same tables and their executable zero test.
-/

public section
namespace Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants

/-- Retain the Gaussian coordinate polynomial with coefficient table `[1, 0]`.

Its descending table represents the identity coordinate in the original dense
polynomial carrier, with the leading one and trailing zero retained explicitly. -/
@[expose] def coordinate : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨[1, 0]⟩

/-- Construct a normalized dense scalar constant, including zero.

The original Gaussian equality procedure selects the retained zero polynomial
for zero; every other scalar keeps the original one-entry constant table. -/
@[expose] def SeparatedVariables.parameterConstant (a : Gaussian.Basic.Canonical) : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  if a = 0 then 0 else Dense.Basic.DensePolynomial.constant a

/-- A normalized parameter constant evaluates to its retained scalar.

Both branches preserve the original Gaussian scalar independently of the
supplied parameter, using the zero or one-entry constant evaluation certificate. -/
@[simp] theorem eval_parameterConstant (a t : Gaussian.Basic.Canonical) :
    (SeparatedVariables.parameterConstant a).eval t = a := by
  rw [SeparatedVariables.parameterConstant]
  split
  · rename_i zero
    rw [zero, Dense.Basic.DensePolynomial.eval_zero]
  · exact Dense.Basic.DensePolynomial.eval_constant a t

/-- The normalized parameter constant of zero is the zero polynomial.

The original scalar equality selects its existing zero branch directly. No
normalization or new coefficient table is computed by this certificate. -/
@[simp] theorem parameterConstant_zero :
    SeparatedVariables.parameterConstant (0 : Gaussian.Basic.Canonical) = 0 := by
  rewrite [SeparatedVariables.parameterConstant,
    if_pos (Eq.refl (0 : Gaussian.Basic.Canonical))]
  exact Eq.refl _

/-- A normalized parameter constant has degree at most zero.

The same original zero test selects the zero certificate or the retained
nonzero scalar's degree-zero leading-term certificate. -/
theorem parameterConstant_atMost (a : Gaussian.Basic.Canonical) :
    Dense.Leading.DegreeAtMost (SeparatedVariables.parameterConstant a) 0 := by
  by_cases zero : a = 0
  · rw [SeparatedVariables.parameterConstant, if_pos zero]
    exact Dense.Leading.DegreeAtMost.zero 0
  · rw [SeparatedVariables.parameterConstant, if_neg zero]
    exact (Dense.Leading.LeadingTerm.constant zero).atMost

/-- A nonzero parameter constant retains degree zero and its original leading scalar.

The supplied scalar nonzero witness selects the original constant branch and
certifies its unchanged normalized one-entry coefficient table. -/
theorem parameterConstant_leading {a : Gaussian.Basic.Canonical} (nonzero : a ≠ 0) :
    Dense.Leading.LeadingTerm (SeparatedVariables.parameterConstant a) 0 a := by
  rw [SeparatedVariables.parameterConstant, if_neg nonzero]
  exact Dense.Leading.LeadingTerm.constant nonzero

/-- Retain the Gaussian parameter polynomial `2T`.

The original dense descending table `[2, 0]` keeps its leading scalar and
trailing zero explicitly, without computing a replacement normalization. -/
@[expose] def SeparatedVariables.twiceParameter : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨[2, 0]⟩

/-- The polynomial `2T` is normalized with degree one and leading coefficient two.

The retained two-entry table starts with its original nonzero Gaussian two.
Its unchanged leading-prefix scan therefore keeps the same count and head. -/
theorem twiceParameter_leading :
    Dense.Leading.LeadingTerm SeparatedVariables.twiceParameter 1 (2 : Gaussian.Basic.Canonical) := by
  have twoNonzero : (2 : Gaussian.Basic.Canonical) ≠ 0 := by decide
  have retained : decide ((2 : Gaussian.Basic.Canonical) = 0) = false :=
    decide_eq_false twoNonzero
  have coefficients : ([2, 0] : List Gaussian.Basic.Canonical).dropWhile (· = 0) = [2, 0] :=
    Data.List.DropWhile.cons_of_false _ _ _ retained
  refine
    { normalized := ?_
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · apply Dense.Basic.DensePolynomial.ext
    change ([2, 0] : List Gaussian.Basic.Canonical).dropWhile (· = 0) = [2, 0]
    rewrite [coefficients]
    exact Eq.refl _
  · change (([2, 0] : List Gaussian.Basic.Canonical).dropWhile (· = 0)).isEmpty = false
    rewrite [coefficients]
    rfl
  · change (([2, 0] : List Gaussian.Basic.Canonical).dropWhile (· = 0)).length - 1 = 1
    rewrite [coefficients]
    rfl
  · change (([2, 0] : List Gaussian.Basic.Canonical).dropWhile (· = 0)).headD 0 = 2
    rewrite [coefficients]
    rfl
end Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
