module

import Purelib.Polynomial.Dense.Companion.Reading
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Algebra.FiniteSum.Fin

/-!
# A genuinely nonmultiplicative original companion reading

The source table keeps a leading zero and an imaginary coefficient. Its
real-coordinate reading drops that nonzero imaginary coefficient, while the
same original companion construction retains both degree and inverse.
-/

namespace TestPurelib.Polynomial.Dense.Companion.Reading

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

/-- The original coordinate constructor retains the real coordinate and a zero imaginary coordinate. -/
private def function (value : Canonical) : Canonical := Components.Basic.point value.re 0

/-- The actual coefficient reading sends the nonzero Gaussian imaginary unit to zero. -/
private theorem imaginary_reading : function ⟨0, 1⟩ = function 0 := by decide +kernel

/-- The same coefficient reading fails multiplication on the two original imaginary factors. -/
private theorem nonmultiplicative :
    function ((⟨0, 1⟩ : Canonical) * ⟨0, 1⟩) ≠ function ⟨0, 1⟩ * function ⟨0, 1⟩ := by decide +kernel

/-- The source is the original quadratic table with a displayed leading zero and imaginary linear coefficient. -/
private def source : DensePolynomial Canonical := ⟨[0, 1, ⟨0, 1⟩, 1]⟩

/-- The same original source companion needs only its displayed leading unit inverse. -/
private def original : Companion source := Companion.ofUnit source (by decide +kernel) 1 (by decide +kernel)

/-- Reading the original leading-inverse action requires no other multiplication preservation. -/
private theorem mapScale (value : Canonical) :
    function (value * original.leadingInverse) = function value * 1 := by
  change function (value * 1) = function value * 1
  rewrite [Basic.mul_one, Basic.mul_one]
  rfl

/-- The original once-mapped table and companion are constructed from only their required scalar laws. -/
private def reading : Companion.Reading original function 1 :=
  Companion.Reading.prepare original function 1 (by decide +kernel) (by decide +kernel)
    (fun value => by
      apply Basic.ext
      · rfl
      · change (0 : Purelib.Data.Rat.Fraction.Rational) = -0
        decide +kernel)
    mapScale

/-- The actual cached observed table retains the original raw zero slot and kills only the imaginary coefficient. -/
private theorem observed_table : reading.observed = (⟨[0, 1, 0, 1]⟩ : DensePolynomial Canonical) := rfl

/-- The complete actual original target matrix is the expected quadratic power-shift matrix. -/
private theorem observed_matrix : reading.target.matrix =
    (SquareMatrix.matrixOfFn fun row column : Fin 2 =>
      if row.val = 0 then if column.val = 1 then (1 : Canonical) else 0
      else if column.val = 0 then -1 else 0) := by rfl

/-- The all-input matrix relationship specializes to the original dropped imaginary feedback cell. -/
private theorem same_feedback :
    reading.target.matrix (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩)
      (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩) =
        function (original.matrix ⟨1, by decide +kernel⟩ ⟨1, by decide +kernel⟩) :=
  reading.matrix_eq _ _

/-- The actual terminal action error at one has squared norm four. -/
private theorem terminal_error : Norm.Basic.normSq
    (SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers 1)
      (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩) -
      1 * reading.target.powers 1 (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩)) = 4 := by
  rewrite [Companion.Reading.action_error]
  decide +kernel

/-- The original general residual estimate reads the same exact mapped polynomial and supplied inverse. -/
private theorem terminal_bound : Norm.Basic.normSq
    (SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers 1)
      (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩) -
      1 * reading.target.powers 1 (Companion.Reading.index reading.degree_eq ⟨1, by decide +kernel⟩)) ≤
        4 * Norm.Basic.normSq (1 : Canonical) :=
  reading.action_error_normSq_le 1 ⟨1, by decide +kernel⟩ 4 (by decide +kernel)

/-- The actual preceding shift row has zero error even for the same nonmultiplicative reading. -/
private theorem shift_error : Norm.Basic.normSq
    (SquareMatrix.Multiplication.matrixVector reading.target.matrix (reading.target.powers 1)
      (Companion.Reading.index reading.degree_eq ⟨0, by decide +kernel⟩) -
      1 * reading.target.powers 1 (Companion.Reading.index reading.degree_eq ⟨0, by decide +kernel⟩)) = 0 := by
  rewrite [Companion.Reading.action_error]
  decide +kernel

/-- The same original mapped matrix row satisfies the generator-column residual estimate directly. -/
private theorem source_bound : Norm.Basic.normSq
    (Purelib.Algebra.FiniteSum.Fin.sumFin (fun column : Fin source.natDegree =>
        function (original.matrix ⟨1, by decide +kernel⟩ column) * (1 : Canonical) ^ column.val) -
      (1 : Canonical) * 1 ^ (1 : Nat)) ≤ 4 * Norm.Basic.normSq (1 : Canonical) :=
  reading.source_action_error_normSq_le 1 ⟨1, by decide +kernel⟩ 4 (by decide +kernel)

end TestPurelib.Polynomial.Dense.Companion.Reading
