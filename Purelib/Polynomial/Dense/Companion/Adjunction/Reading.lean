module

public import Purelib.Polynomial.Dense.Companion.Adjunction
public import Purelib.Polynomial.Dense.Companion.Reading
public import Purelib.Algebra.Monogenic.Coordinates.Division
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Reverse
import Purelib.Tactic.Ring

/-!
# Original adjunction quotients and candidate readings

The retained original source, root and synthetic quotient remain the inputs.
The quotient's bounded prefixes read as the same Gaussian division at a
candidate. The actual generator reading retains the original mapped source
residual in degree one instead of identifying every candidate with a root.
-/

public section

namespace Purelib.Polynomial.Dense.Companion.Adjunction

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix
open Division

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K}

/-- Reading the same retained original quotient is exactly the original division at the supplied target point.

The normalized source has the original companion degree plus one slots.
Its actual cached quotient coefficients therefore read before any reduction
by the source relation, without a multiplication law for the reading.
-/
theorem quotient_reading {L : Type*} [CommRing L] (adjunction : Adjunction polynomial)
    (normalized : polynomial.normalize = polynomial) (function : K → L) (mapZero : function 0 = 0)
    (mapAdd : ∀ left right, function (left + right) = function left + function right) (point : L) :
    Map.map (Cyclic.Element.evaluate function point) adjunction.division.quotient =
      (Synthetic.divide (Map.map function polynomial) point).quotient := by
  have count := congrArg List.length adjunction.companion.source_eq
  rewrite [normalized, List.length_cons, List.Reverse.length_reverse, adjunction.companion.count_eq] at count
  have bounded : polynomial.coeffs.length ≤ polynomial.natDegree + 1 := Nat.le_of_eq count
  rewrite [adjunction.division_eq, adjunction.source_eq, adjunction.root_eq]
  exact Cyclic.Element.evaluate_synthetic_quotient function mapZero mapAdd point polynomial bounded

/-- Reading the retained original generator is the same original first companion-row power sum. -/
theorem root_reading_sum (adjunction : Adjunction polynomial) (function : K → Canonical)
    (mapZero : function 0 = 0) (point : Canonical) :
    Cyclic.Element.evaluate function point adjunction.root =
      sumFin (fun column : Fin polynomial.natDegree =>
        function (adjunction.companion.matrix adjunction.companion.firstIndex column) * point ^ column.val) := by
  rewrite [adjunction.root_eq]
  change (Map.map function (Cyclic.Element.root adjunction.table).polynomial).eval point = _
  apply (Cyclic.Element.eval_map_polynomial function mapZero _ point).trans
  have origin : adjunction.table.origin = adjunction.companion.firstIndex :=
    congrArg (fun table : Table adjunction.companion => table.origin) adjunction.table_eq
  apply sumFin_congr
  intro column
  rewrite [Cyclic.Element.root_matrix, Rectangular.transpose_apply, origin]
  rfl

/-- The same original generator-candidate discrepancy is exactly its actual terminal mapped-source residual. -/
theorem root_reading_error (adjunction : Adjunction polynomial) {function : K → Canonical}
    {inverseImage : Canonical} (reading : Companion.Reading adjunction.companion function inverseImage)
    (mapZero : function 0 = 0) (point : Canonical) :
    Cyclic.Element.evaluate function point adjunction.root - point =
      (if 1 = polynomial.natDegree then -(reading.observed.eval point * inverseImage) else 0) := by
  have action := reading.source_action_error point adjunction.companion.firstIndex
  change sumFin (fun column : Fin polynomial.natDegree =>
      function (adjunction.companion.matrix adjunction.companion.firstIndex column) * point ^ column.val) -
        point * point ^ 0 = _ at action
  rewrite [pow_zero, mul_one] at action
  rewrite [adjunction.root_reading_sum function mapZero point]
  exact action

/-- A nonterminal original generator reads exactly the supplied candidate in degree at least two. -/
theorem root_reading_of_two_le (adjunction : Adjunction polynomial) {function : K → Canonical}
    {inverseImage : Canonical} (reading : Companion.Reading adjunction.companion function inverseImage)
    (mapZero : function 0 = 0) (point : Canonical) (degree : 1 < polynomial.natDegree) :
    Cyclic.Element.evaluate function point adjunction.root = point := by
  have different : ¬1 = polynomial.natDegree := fun same => Nat.ne_of_lt degree same
  have error := adjunction.root_reading_error reading mapZero point
  rewrite [if_neg different] at error
  calc
    _ = (Cyclic.Element.evaluate function point adjunction.root - point) + point := by ring0
    _ = point := by rewrite [error, zero_add]; rfl

/-- In degree one the actual generator retains the candidate's explicit mapped linear residual. -/
theorem root_reading_of_degree_one (adjunction : Adjunction polynomial) {function : K → Canonical}
    {inverseImage : Canonical} (reading : Companion.Reading adjunction.companion function inverseImage)
    (mapZero : function 0 = 0) (point : Canonical) (degree : polynomial.natDegree = 1) :
    Cyclic.Element.evaluate function point adjunction.root = point - reading.observed.eval point * inverseImage := by
  have error := adjunction.root_reading_error reading mapZero point
  rewrite [if_pos degree.symm] at error
  calc
    _ = (Cyclic.Element.evaluate function point adjunction.root - point) + point := by ring0
    _ = point - reading.observed.eval point * inverseImage := by rewrite [error]; ring0

/-- The same cached observed source bounds the actual retained generator's candidate discrepancy. -/
theorem root_reading_error_normSq_le (adjunction : Adjunction polynomial) {function : K → Canonical}
    {inverseImage : Canonical} (reading : Companion.Reading adjunction.companion function inverseImage)
    (mapZero : function 0 = 0) (point : Canonical) (epsilon : Rat.Fraction.Rational)
    (bound : Norm.Basic.normSq (reading.observed.eval point) ≤ epsilon) :
    Norm.Basic.normSq (Cyclic.Element.evaluate function point adjunction.root - point) ≤
      epsilon * Norm.Basic.normSq inverseImage := by
  rewrite [adjunction.root_reading_sum function mapZero point]
  have estimate := reading.source_action_error_normSq_le point adjunction.companion.firstIndex epsilon bound
  change Norm.Basic.normSq (sumFin (fun column : Fin polynomial.natDegree =>
      function (adjunction.companion.matrix adjunction.companion.firstIndex column) * point ^ column.val) -
        point * point ^ 0) ≤ _ at estimate
  rewrite [pow_zero, mul_one] at estimate
  exact estimate

end Purelib.Polynomial.Dense.Companion.Adjunction

end
