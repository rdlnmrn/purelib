module

public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.Polynomial.Dense.Companion.Execution
public import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-!
# Cyclic coefficient algebras of original companion matrices

The transpose of the retained companion has the original coordinate units as
its first iterates of the first column. Its cached finite power table therefore
constructs the executable commutative centralizer algebra without a supplied
basis or a quotient.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Purelib.Algebra.Monogenic
open Purelib.LinearAlgebra.Matrix
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.List

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

/-- Compute the original transposed companion's cyclic table from successive finite matrix products.

The original source degree fixes the whole table. Its coordinate certificate
comes from the same companion's finite initial-state execution theorem.
-/
@[expose] def cyclic (companion : Companion polynomial) : Cyclic (Rectangular.transpose companion.matrix) where
  origin := companion.firstIndex
  powers := Arithmetic.powerTable (Rectangular.transpose companion.matrix) polynomial.natDegree
  powers_eq := Arithmetic.powerTable_apply _ _
  coordinate := by
    intro index row
    rewrite [Arithmetic.powerTable_apply, ← Arithmetic.transpose_power, Rectangular.transpose_apply,
      companion.power_first_entry]
    by_cases same : row = index
    · rewrite [if_pos same, if_pos same.symm]
      rfl
    · rewrite [if_neg same, if_neg (fun reverse => same reverse.symm)]
      rfl

/-- Mapping the original coefficients retains its same leading term and ascending lower table. -/
theorem source_evaluation_map {L : Type*} [CommRing L] (companion : Companion polynomial)
    (function : K → L) (mapZero : function 0 = 0) (point : L) :
    (Map.map function polynomial).eval point = function polynomial.leadingCoeff * point ^ polynomial.natDegree +
      sumFin (fun index : Fin polynomial.natDegree =>
        function (getD companion.coefficients index.val 0) * point ^ index.val) := by
  have lower := Map.evalCoeffs_reverse_sum function mapZero point companion.coefficients
  have aligned : sumFin (fun index : Fin companion.coefficients.length =>
        function (getD companion.coefficients index.val 0) * point ^ index.val) =
      sumFin (fun index : Fin polynomial.natDegree =>
        function (getD companion.coefficients index.val 0) * point ^ index.val) := by
    apply sumFin_congr_size companion.count_eq
    intro first second same
    rewrite [same]
    rfl
  rewrite [← Map.map_normalize_eval function mapZero polynomial point]
  change DensePolynomial.evalCoeffs point (polynomial.normalize.coeffs.map function) = _
  rewrite [companion.source_eq, List.map_cons, DensePolynomial.evalCoeffs_cons_expansion,
    Purelib.Data.List.Map.length_map, Reverse.length_reverse, companion.count_eq]
  exact congrArg (function polynomial.leadingCoeff * point ^ polynomial.natDegree + ·) (lower.trans aligned)

/-- The retained transposed companion generator is an exact root of the original mapped polynomial.

The original feedback equation proves the distinguished column vanishes.
Cyclic reconstruction then proves equality of the entire algebra element,
including over coefficient rings with zero divisors.
-/
theorem root_relation (companion : Companion polynomial) :
    (Map.map (Cyclic.Element.scalar companion.cyclic) polynomial).eval
      (Cyclic.Element.root companion.cyclic) = 0 := by
  let table := companion.cyclic
  let root := Cyclic.Element.root table
  apply Cyclic.Element.eq_of_column
  intro row
  rewrite [companion.source_evaluation_map (Cyclic.Element.scalar table)
      (Cyclic.Element.scalar_zero table) root,
    Cyclic.Element.add_matrix, Arithmetic.add_apply, Cyclic.Element.scalar_mul_apply,
    Cyclic.Element.sumFin_apply]
  have degree : (root ^ polynomial.natDegree).matrix row table.origin = companion.feedback row := by
    rewrite [Cyclic.Element.pow_matrix]
    change Arithmetic.power (Rectangular.transpose companion.matrix) polynomial.natDegree row companion.firstIndex = _
    rewrite [← Arithmetic.transpose_power, Rectangular.transpose_apply, companion.power_degree_first_entry]
    rfl
  have lower : sumFin (fun index : Fin polynomial.natDegree =>
      (Cyclic.Element.scalar table (getD companion.coefficients index.val 0) * root ^ index.val).matrix
        row table.origin) = getD companion.coefficients row.val 0 := by
    calc
      _ = sumFin (fun index : Fin polynomial.natDegree =>
          if index = row then getD companion.coefficients index.val 0 else 0) := by
        apply sumFin_congr
        intro index
        rewrite [Cyclic.Element.scalar_mul_apply, Cyclic.Element.pow_matrix]
        change getD companion.coefficients index.val 0 *
          Arithmetic.power (Rectangular.transpose companion.matrix) index.val row table.origin = _
        rewrite [← table.powers_eq index, table.coordinate index row]
        by_cases same : index = row
        · rewrite [if_pos same, if_pos same.symm, mul_one]
          rfl
        · rewrite [if_neg same, if_neg (fun reverse => same reverse.symm), mul_zero]
          rfl
      _ = _ := sumFin_ite_eq row (fun index => getD companion.coefficients index.val 0)
  rewrite [degree, lower]
  change polynomial.leadingCoeff * companion.feedback row + getD companion.coefficients row.val 0 =
    (Arithmetic.zero : Purelib.LinearAlgebra.Matrix K polynomial.natDegree) row table.origin
  rewrite [Arithmetic.zero_apply, companion.feedback_eq]
  calc
    _ = getD companion.coefficients row.val 0 * (1 - polynomial.leadingCoeff * companion.leadingInverse) := by ring0
    _ = 0 := by rewrite [companion.leading_unit, sub_self, mul_zero]; rfl

end Purelib.Polynomial.Dense.Companion
