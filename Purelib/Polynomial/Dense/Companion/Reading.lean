module

public import Purelib.Polynomial.Dense.Companion
public import Purelib.Polynomial.Dense.Map.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Gaussian readings of an original companion matrix

One coefficient reading builds the observed original polynomial and its
original companion once. Preserving zero, one, negation and multiplication
by the retained source leading inverse is sufficient for every matrix entry;
the reading need not preserve other products or distinguish source scalars.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

namespace Reading

/-- Transport an original bounded degree index through the retained observed-degree equality. -/
@[expose] def index {original observed : Nat} (degree : observed = original) (source : Fin original) :
    Fin observed := ⟨source.val, degree.symm ▸ source.isLt⟩

/-- The observed original companion reads every same source entry at its transported original bounded indices. -/
@[expose] def MatrixAgreement (original : Companion polynomial) (function : K → Canonical)
    (observed : DensePolynomial Canonical) (target : Companion observed)
    (degree : observed.natDegree = polynomial.natDegree) : Prop :=
  ∀ row column : Fin polynomial.natDegree,
    target.matrix (index degree row) (index degree column) = function (original.matrix row column)

end Reading

set_option genInjectivity false in
/-- A once-mapped original coefficient table and its original Gaussian companion retain exact source matrix ownership.

The source companion, coefficient reading and same supplied inverse image
remain indices. Degree transport relates the two original finite matrices;
its entrywise certificate is proof data rather than a second matrix map.
-/
structure Reading (original : Companion polynomial) (function : K → Canonical) (inverseImage : Canonical) where
  /-- The cached mapped original coefficient table. -/
  observed : DensePolynomial Canonical
  /-- The table is the original coefficient map applied to the same source. -/
  observed_eq : observed = Map.map function polynomial
  /-- Its retained nonzero leading image preserves the source degree. -/
  degree_eq : observed.natDegree = polynomial.natDegree
  /-- The original companion computed from this same observed table. -/
  target : Companion observed
  /-- The target keeps exactly the supplied image of the original leading inverse. -/
  inverse_eq : target.leadingInverse = inverseImage
  /-- Every target entry reads the same original source entry. -/
  matrix_eq : Reading.MatrixAgreement original function observed target degree_eq

constructive_injectivity Reading

namespace Reading

/-- The target's ascending lower coefficients are the exact original coefficient reading in the original order. -/
private theorem coefficients_eq (original : Companion polynomial) (function : K → Canonical)
    (mapZero : function 0 = 0) (leadingNonzero : function polynomial.leadingCoeff ≠ 0)
    (target : Companion (Map.map function polynomial)) :
    target.coefficients = original.coefficients.map function := by
  rewrite [target.coefficients_eq,
    ← Map.map_normalize_of_leading_nonzero function mapZero polynomial leadingNonzero]
  change (polynomial.normalize.coeffs.map function).tail.reverse = original.coefficients.map function
  rewrite [original.source_eq]
  change (original.coefficients.reverse.map function).reverse = original.coefficients.map function
  rewrite [Reverse.map_reverse, Reverse.reverse_reverse]
  rfl

/-- The original target constructor's matrix reads the same source entry.

The certificate compares entries without evaluating the reading at runtime cells.
-/
theorem target_matrix (original : Companion polynomial) (function : K → Canonical)
    (inverseImage : Canonical) (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapNeg : ∀ value, function (-value) = -function value)
    (mapScale : ∀ value, function (value * original.leadingInverse) = function value * inverseImage)
    (leadingNonzero : function polynomial.leadingCoeff ≠ 0)
    (target : Companion (Map.map function polynomial)) (inverse : target.leadingInverse = inverseImage)
    (degree : (Map.map function polynomial).natDegree = polynomial.natDegree) :
    MatrixAgreement original function (Map.map function polynomial) target degree := by
  intro row column
  rewrite [original.matrix_eq, target.matrix_eq, matrixOfFeedback, matrixOfFeedback,
    SquareMatrix.matrixOfFn_apply, SquareMatrix.matrixOfFn_apply]
  by_cases next : row.val + 1 < polynomial.natDegree
  · have targetNext : (index degree row).val + 1 < (Map.map function polynomial).natDegree := by
      change row.val + 1 < (Map.map function polynomial).natDegree
      rewrite [degree]
      exact next
    rewrite [dif_pos next, dif_pos targetNext]
    by_cases same : column.val = row.val + 1
    · have sourceSame : column = ⟨row.val + 1, next⟩ := Fin.ext same
      have targetSame : index degree column = ⟨(index degree row).val + 1, targetNext⟩ := Fin.ext same
      rewrite [if_pos sourceSame, if_pos targetSame]
      exact mapOne.symm
    · have sourceDifferent : column ≠ ⟨row.val + 1, next⟩ := fun equal => same (congrArg Fin.val equal)
      have targetDifferent : index degree column ≠ ⟨(index degree row).val + 1, targetNext⟩ :=
        fun equal => same (congrArg Fin.val equal)
      rewrite [if_neg sourceDifferent, if_neg targetDifferent]
      exact mapZero.symm
  · have targetNext : ¬(index degree row).val + 1 < (Map.map function polynomial).natDegree := by
      change ¬row.val + 1 < (Map.map function polynomial).natDegree
      rewrite [degree]
      exact next
    rewrite [dif_neg next, dif_neg targetNext, original.feedback_eq column,
      target.feedback_eq (index degree column), inverse,
      coefficients_eq original function mapZero leadingNonzero target,
      mapScale, mapNeg]
    have coefficient := getD_map function original.coefficients column.val 0
    rewrite [mapZero] at coefficient
    change -getD (original.coefficients.map function) column.val 0 * inverseImage =
      -function (getD original.coefficients column.val 0) * inverseImage
    rewrite [coefficient]
    rfl

/-- Prepare the original Gaussian companion from an already retained observed coefficient table.

The exact cache equation identifies the supplied observed polynomial with
the same original coefficient reading. The original leading-unit proof and
target constructor are reused without evaluating that map again.
-/
@[expose] def ofObserved (original : Companion polynomial) (function : K → Canonical) (inverseImage : Canonical)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map function polynomial)
    (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapNeg : ∀ value, function (-value) = -function value)
    (mapScale : ∀ value, function (value * original.leadingInverse) = function value * inverseImage) :
    Reading original function inverseImage := by
  have leadingUnit : function polynomial.leadingCoeff * inverseImage = 1 :=
    (mapScale polynomial.leadingCoeff).symm.trans ((congrArg function original.leading_unit).trans mapOne)
  have leadingNonzero : function polynomial.leadingCoeff ≠ 0 := by
    intro zero
    have impossible := leadingUnit
    rewrite [zero, zero_mul] at impossible
    exact (by decide : (0 : Canonical) ≠ 1) impossible
  have degree : observed.natDegree = polynomial.natDegree :=
    (congrArg DensePolynomial.natDegree observedEq).trans
      (Map.map_natDegree_of_leading_nonzero function mapZero polynomial leadingNonzero)
  have unit : observed.leadingCoeff * inverseImage = 1 :=
    (congrArg (fun value => value * inverseImage)
      ((congrArg DensePolynomial.leadingCoeff observedEq).trans
        (Map.map_leadingCoeff_of_leading_nonzero function mapZero polynomial leadingNonzero))).trans leadingUnit
  let target := ofUnit observed (degree.symm ▸ original.positive) inverseImage unit
  have inverse : target.leadingInverse = inverseImage := ofUnit_leadingInverse _ _ _ _
  exact
    { observed := observed
      observed_eq := observedEq
      degree_eq := degree
      target := target
      inverse_eq := inverse
      matrix_eq := by
        cases observedEq
        exact target_matrix original function inverseImage mapZero mapOne mapNeg mapScale
          leadingNonzero target inverse degree }

/-- Prepare one original Gaussian companion from a coefficient reading preserving its needed scalar operations.

The same original coefficient map is evaluated once. The shared constructor
then builds the original target companion from that exact retained table
and the same supplied inverse image.
-/
@[expose] def prepare (original : Companion polynomial) (function : K → Canonical) (inverseImage : Canonical)
    (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapNeg : ∀ value, function (-value) = -function value)
    (mapScale : ∀ value, function (value * original.leadingInverse) = function value * inverseImage) :
    Reading original function inverseImage :=
  let observed := Map.map function polynomial
  ofObserved original function inverseImage observed rfl mapZero mapOne mapNeg mapScale

/-- A retained observed cache gives the complete same original reading as its coefficient-map constructor. -/
theorem ofObserved_eq_prepare (original : Companion polynomial) (function : K → Canonical) (inverseImage : Canonical)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map function polynomial)
    (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapNeg : ∀ value, function (-value) = -function value)
    (mapScale : ∀ value, function (value * original.leadingInverse) = function value * inverseImage) :
    ofObserved original function inverseImage observed observedEq mapZero mapOne mapNeg mapScale =
      prepare original function inverseImage mapZero mapOne mapNeg mapScale := by
  cases observedEq
  rfl

variable {original : Companion polynomial} {function : K → Canonical} {inverseImage : Canonical}

/-- The same observed original companion action retains the actual mapped-polynomial residual. -/
theorem action (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) :
    SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers point)
        (index reading.degree_eq row) =
      point * reading.target.powers point (index reading.degree_eq row) -
        (if row.val + 1 = polynomial.natDegree then reading.observed.eval point * inverseImage else 0) := by
  by_cases terminal : row.val + 1 = polynomial.natDegree
  · have observedTerminal : (index reading.degree_eq row).val + 1 = reading.observed.natDegree :=
      terminal.trans reading.degree_eq.symm
    rewrite [reading.target.action, reading.inverse_eq, if_pos observedTerminal, if_pos terminal]
    rfl
  · have observedTerminal : ¬(index reading.degree_eq row).val + 1 = reading.observed.natDegree :=
      fun same => terminal (same.trans reading.degree_eq)
    rewrite [reading.target.action, reading.inverse_eq, if_neg observedTerminal, if_neg terminal]
    rfl

/-- Subtracting the same expected power shift leaves only the actual terminal polynomial error. -/
theorem action_error (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) :
    SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers point)
        (index reading.degree_eq row) -
      point * reading.target.powers point (index reading.degree_eq row) =
        (if row.val + 1 = polynomial.natDegree then -(reading.observed.eval point * inverseImage) else 0) := by
  rewrite [action]
  split <;> ring0

/-- A bound on the same observed polynomial controls every actual companion column error.

Only the retained inverse image scales the bound. Earlier shift rows have
zero error, and the terminal row uses the same cached observed polynomial.
-/
theorem action_error_normSq_le (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) (epsilon : Rat.Fraction.Rational)
    (bound : Norm.Basic.normSq (reading.observed.eval point) ≤ epsilon) :
    Norm.Basic.normSq
      (SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers point)
        (index reading.degree_eq row) - point * reading.target.powers point (index reading.degree_eq row)) ≤
      epsilon * Norm.Basic.normSq inverseImage := by
  rewrite [action_error]
  by_cases terminal : row.val + 1 = polynomial.natDegree
  · rewrite [if_pos terminal, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bound (Norm.Basic.normSq_nonneg _)
  · rewrite [if_neg terminal, Norm.Basic.normSq_zero]
    have nonnegative : 0 ≤ epsilon := (Norm.Basic.normSq_nonneg (reading.observed.eval point)).trans bound
    exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative (Norm.Basic.normSq_nonneg _)

/-- The same source-row coefficient reading equals the retained original target companion action. -/
theorem source_action (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) :
    sumFin (fun column : Fin polynomial.natDegree => function (original.matrix row column) * point ^ column.val) =
      SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers point)
        (index reading.degree_eq row) := by
  apply Eq.symm
  rewrite [SquareMatrix.Multiplication.matrixVector_apply]
  apply sumFin_congr_size reading.degree_eq
  intro first second same
  have bounded : first = index reading.degree_eq second := Fin.ext same
  rewrite [bounded, reading.matrix_eq row second, reading.target.powers_apply]
  rfl

/-- The actual original mapped matrix row retains exactly the same terminal observed-polynomial error. -/
theorem source_action_error (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) :
    sumFin (fun column : Fin polynomial.natDegree => function (original.matrix row column) * point ^ column.val) -
      point * point ^ row.val =
        (if row.val + 1 = polynomial.natDegree then -(reading.observed.eval point * inverseImage) else 0) := by
  have retained := reading.action_error point row
  rewrite [← reading.source_action point row, reading.target.powers_apply] at retained
  exact retained

/-- The original mapped generator-column residual has the same inverse-scaled polynomial norm bound.

The source row is the corresponding column of its original transpose. Degree
transport and entry comparisons are proof-only and reuse the retained target
companion's action estimate.
-/
theorem source_action_error_normSq_le (reading : Reading original function inverseImage) (point : Canonical)
    (row : Fin polynomial.natDegree) (epsilon : Rat.Fraction.Rational)
    (bound : Norm.Basic.normSq (reading.observed.eval point) ≤ epsilon) :
    Norm.Basic.normSq
      (sumFin (fun column : Fin polynomial.natDegree => function (original.matrix row column) * point ^ column.val) -
        point * point ^ row.val) ≤ epsilon * Norm.Basic.normSq inverseImage := by
  have same := (reading.source_action_error point row).trans (reading.action_error point row).symm
  rewrite [same]
  exact reading.action_error_normSq_le point row epsilon bound

end Reading

end Purelib.Polynomial.Dense.Companion

end
