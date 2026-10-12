module

import Purelib.Approximation.Gaussian.Name.Coherent.State
public import Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Subtraction

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-!
# Exact coefficient tables for positive-degree power polynomials

The supplied Gaussian parameter and positive root degree determine the original
finite high-to-low coefficient list. Exact coherent states retain that same list,
and its values, degree and squarefree certificate use the original polynomial.
-/

namespace Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients

/-- The displayed non-leading coefficient list of `Z^d-w`.

The positive degree fixes the retained zero prefix. Its final coefficient
is the opposite of the supplied Gaussian parameter, preserving the original
high-to-low order. -/
@[expose] public def coefficientValues (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    List Gaussian.Basic.Canonical :=
  List.replicate (degree.value - 1) 0 ++ [-parameter]

/-- The exact coherent-state table for the displayed power-polynomial coefficients.

Each original coefficient is embedded in its exact coherent state.
The table retains this mapped list in the same order, including every
zero coefficient and its terminal parameter coefficient. -/
@[expose] public def coefficientTable (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable where
  entries := (Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree).map
    Name.Coherent.State.Exact.exactCoefficientState

/-- Every exact coefficient state has allowance below the supplied positive target.

Each retained state is exact and therefore has zero allowance.
The supplied target is strictly positive, so every displayed coefficient
state satisfies the original finite allowance predicate. -/
public theorem coefficientTable_allowances_lt
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree)
    {target : Fraction.Rational} (positive : 0 < target) :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt
      (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).entries target := by
  simp only [Power.Gaussian.Progressive.Coefficients.coefficientTable]
  induction Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree with
  | nil => trivial
  | cons value remaining inductionHypothesis =>
      simp only [List.map_cons,
        Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt,
        Name.Coherent.State.Exact.exactCoefficientState_allowance]
      exact ⟨positive, inductionHypothesis⟩

/-- Reading the exact coefficient table recovers the original non-leading coefficient list.

Projection of each retained exact state recovers its original coefficient.
Structural recursion preserves the entire ordered list without changing
the table construction or its coefficient states. -/
@[simp] public theorem coefficientTable_values
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).values =
      Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree := by
  change List.map Name.Coherent.State.CoefficientState.value
      (List.map Name.Coherent.State.Exact.exactCoefficientState
        (Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree)) = _
  induction Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree with
  | nil => exact Eq.refl _
  | cons value remaining inductionHypothesis =>
      change value ::
          List.map Name.Coherent.State.CoefficientState.value
            (List.map Name.Coherent.State.Exact.exactCoefficientState remaining) =
        value :: remaining
      exact congrArg (List.cons value) inductionHypothesis

/-- The exact coefficient table represents the original displayed power polynomial.

The table polynomial is monic with one followed by its retained values.
The exact value list identifies that same high-to-low coefficient sequence
with the supplied parameter and positive-degree power polynomial. -/
@[simp] public theorem coefficientTable_polynomial
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).polynomial =
      Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree := by
  apply Dense.Basic.DensePolynomial.ext
  change 1 :: (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).values =
    1 :: Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree
  exact congrArg (List.cons (1 : Gaussian.Basic.Canonical))
    (Power.Gaussian.Progressive.Coefficients.coefficientTable_values parameter degree)

/-- The exact coefficient table retains the squarefree certificate at a nonzero parameter.

The supplied parameter is nonzero and the degree is positive.
The exact polynomial equation transports the original squarefree
certificate to the same retained coefficient table. -/
@[expose] public def coefficientTableSquarefree {parameter : Gaussian.Basic.Canonical}
    (parameterNonzero : parameter ≠ 0) (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).polynomial := by
  rw [Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial]
  exact Power.Gaussian.Squarefree.squarefree parameterNonzero degree

/-- The non-leading coefficient list has exactly the displayed positive degree many entries.

The zero prefix has the degree predecessor many entries and the
terminal parameter coefficient adds one. Positivity of the degree
prevents truncation when reconstructing this natural count. -/
@[simp] public theorem coefficientValues_length
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree).length = degree.value := by
  change (List.replicate (degree.value - 1) (0 : Gaussian.Basic.Canonical) ++
    [-parameter]).length = degree.value
  rewrite [List.Append.length_append, List.Replicate.length_replicate]
  change degree.value - 1 + 1 = degree.value
  exact (Nat.add_comm (degree.value - 1) 1).trans
    (Nat.Subtraction.add_sub_of_le degree.positive)

/-- The exact coefficient table retains the displayed positive degree.

Mapping each retained coefficient into its exact state preserves
list length. The original coefficient count is precisely the supplied
positive root degree. -/
@[simp] public theorem coefficientTable_degree
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree = degree.value := by
  change (List.map Name.Coherent.State.Exact.exactCoefficientState
    (Power.Gaussian.Progressive.Coefficients.coefficientValues parameter degree)).length =
      degree.value
  exact (List.Map.length_map Name.Coherent.State.Exact.exactCoefficientState _).trans
    (Power.Gaussian.Progressive.Coefficients.coefficientValues_length parameter degree)

end Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
