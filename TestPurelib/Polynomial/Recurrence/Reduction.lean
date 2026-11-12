module

import TestPurelib.Polynomial.Recurrence.Boundary
import Purelib.LinearAlgebra.Matrix.NormalForm.Compute
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Tactic.Ring

/-!
# Automatic reductions of original recurrence boundary rows

Every rectangle below is the actual original startup operator on its retained
mode columns. Its rank, coordinate changes and vectors are computed by the
finite pivot procedure, with no supplied normal form or basis.
-/

namespace TestPurelib.Polynomial.Recurrence.Reduction

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector.Basic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Recurrence
open Purelib.LinearAlgebra.Matrix

/-- The explicit field retains the complete original rational commutative-ring record. -/
private theorem rational_field_parent : (inferInstance : CommRing Rational) =
    (inferInstance : Purelib.Algebra.Field.ExplicitField Rational).toCommRing := rfl

/-- The two retained ordinary inside-mode horizons of the coupled cubic. -/
private def coupledModes : Vec (Vec Rational 5) 2 :=
  .cons (Mode.window (1 / 4) 0 5) (.cons (Mode.window (1 / 2) 0 5) .nil)

/-- The original coupled startup rectangle uses the two cached original boundary columns. -/
private def coupledMatrix : Rectangular Rational 1 2 :=
  Rectangular.transpose (Vec.map (boundary Boundary.coupled 1) coupledModes)

/-- The coupled original matrix is reduced without any supplied rank or vectors. -/
private def coupledForm : NormalForm coupledMatrix := NormalForm.compute coupledMatrix

/-- The actual original coupled row begins with coefficient one. -/
private theorem coupled_entry_first : coupledMatrix 0 0 = 1 := by decide +kernel

/-- The same coupled row has its second coefficient one half. -/
private theorem coupled_entry_second : coupledMatrix 0 1 = 1 / 2 := by decide +kernel

/-- The finite scan computes one independent image coordinate for the coupled row. -/
private theorem coupled_rank : coupledForm.rank = 1 := by decide +kernel

/-- The computed coupled kernel basis first entry is minus one half. -/
private theorem coupled_kernel_first : coupledForm.kernelVector (.cons 1 .nil) 0 = -1 / 2 := by decide +kernel

/-- Its second original entry is one, so the basis uses both original modes. -/
private theorem coupled_kernel_second : coupledForm.kernelVector (.cons 1 .nil) 1 = 1 := by decide +kernel

/-- The actual complementary-target minus kernel coordinate count is minus one. -/
private theorem coupled_defect : coupledForm.defect = -1 := by decide +kernel

/-- The original repeated-root startup matrix retains its generalized-mode column. -/
private def repeatedMatrix : Rectangular Rational 1 2 :=
  Rectangular.transpose (Vec.map (boundary Boundary.repeated 1)
    (.cons (Mode.window (1 / 2) 0 3) (.cons (Mode.window (1 / 2) 1 3) .nil)))

/-- The repeated-root startup row is reduced by the same automatic procedure. -/
private def repeatedForm : NormalForm repeatedMatrix := NormalForm.compute repeatedMatrix

/-- The repeated-root procedure computes one image coordinate. -/
private theorem repeated_rank : repeatedForm.rank = 1 := by decide +kernel

/-- Its computed generalized kernel basis has first coefficient two. -/
private theorem repeated_kernel_first : repeatedForm.kernelVector (.cons 1 .nil) 0 = 2 := by decide +kernel

/-- Its computed generalized kernel basis has second coefficient one. -/
private theorem repeated_kernel_second : repeatedForm.kernelVector (.cons 1 .nil) 1 = 1 := by decide +kernel

/-- The source monomial has one zero-root transient and no startup rows. -/
private def zMatrix : Rectangular Rational 0 1 :=
  Rectangular.transpose (.cons (boundary Boundary.z 0 (Boundary.transient 0 3)) .nil)

/-- The actual minimal negative monomial has one startup row and no modes. -/
private def inverseMatrix : Rectangular Rational 1 0 :=
  Rectangular.transpose (.nil : Vec (Vec Rational 1) 0)

/-- The minimal positive monomial has defect minus one. -/
private theorem z_defect : (NormalForm.compute zMatrix).defect = -1 := by decide +kernel

/-- The minimal negative monomial has defect plus one. -/
private theorem inverse_defect : (NormalForm.compute inverseMatrix).defect = 1 := by decide +kernel

/-- The constant polynomialization's extra transient gives the original row one. -/
private def shiftedOne : Rectangular Rational 1 1 :=
  Rectangular.transpose (.cons (boundary Boundary.z 1 (Boundary.transient 0 3)) .nil)

/-- Its actual extra row removes the added transient, giving zero defect. -/
private theorem shifted_one_defect : (NormalForm.compute shiftedOne).defect = 0 := by decide +kernel

/-- A nonminimal positive monomial retains both actual zero-root transient columns. -/
private def shiftedZ : Rectangular Rational 1 2 :=
  Rectangular.transpose (.cons (boundary Boundary.zSquared 1 (Boundary.transient 0 3))
    (.cons (boundary Boundary.zSquared 1 (Boundary.transient 1 3)) .nil))

/-- The first original zero column forces an actual column transposition in the finite scan. -/
private theorem shifted_z_rank : (NormalForm.compute shiftedZ).rank = 1 := by decide +kernel

/-- The original zeroth transient survives that computed column transposition. -/
private theorem shifted_z_kernel_first :
    (NormalForm.compute shiftedZ).kernelVector (.cons 1 .nil) 0 = 1 := by decide +kernel

/-- The extra first-coordinate transient is removed by the actual original row. -/
private theorem shifted_z_kernel_second :
    (NormalForm.compute shiftedZ).kernelVector (.cons 1 .nil) 1 = 0 := by decide +kernel

/-- A nonminimal negative monomial has both original startup rows on its one transient. -/
private def shiftedInverse : Rectangular Rational 2 1 :=
  Rectangular.transpose (.cons (boundary Boundary.z 2 (Boundary.transient 0 3)) .nil)

/-- The initial zero startup row forces an actual row transposition. -/
private theorem shifted_inverse_rank : (NormalForm.compute shiftedInverse).rank = 1 := by decide +kernel

/-- The untouched original first target coordinate is the computed complementary vector. -/
private theorem shifted_inverse_complement_first :
    (NormalForm.compute shiftedInverse).complementVector (.cons 1 .nil) 0 = 1 := by decide +kernel

/-- The original second target coordinate is already in the computed image. -/
private theorem shifted_inverse_complement_second :
    (NormalForm.compute shiftedInverse).complementVector (.cons 1 .nil) 1 = 0 := by decide +kernel

/-- The quartic source has three distinct inside roots and one outside root. -/
private def quartic : DensePolynomial Rational := ⟨[1, -7 / 2, 59 / 16, -47 / 32, 3 / 16]⟩

/-- Both original startup rows are retained on the three original inside-mode columns. -/
private def twoRowMatrix : Rectangular Rational 2 3 :=
  Rectangular.transpose (Vec.map (boundary quartic 2)
    (.cons (Mode.window (1 / 4) 0 5)
      (.cons (Mode.window (1 / 2) 0 5) (.cons (Mode.window (3 / 4) 0 5) .nil))))

/-- The original two-row operator is reduced through two actual recursive unit pivots. -/
private def twoRowForm : NormalForm twoRowMatrix := NormalForm.compute twoRowMatrix

/-- The first original quartic boundary entry is twenty-three eighths. -/
private theorem two_row_entry_first : twoRowMatrix 0 0 = 23 / 8 := by decide +kernel

/-- The last original quartic boundary entry is minus one quarter. -/
private theorem two_row_entry_last : twoRowMatrix 1 2 = -1 / 4 := by decide +kernel

/-- The recursive producer computes two independent original image coordinates. -/
private theorem two_row_rank : twoRowForm.rank = 2 := by decide +kernel

/-- The six independent exact readings of the original two-row operator. -/
private def twoRowEntries : Rectangular Rational 2 3 :=
  .cons (.cons (23 / 8) (.cons (35 / 16) (.cons (13 / 8) .nil)))
    (.cons (.cons (-3 / 4) (.cons (-3 / 8) (.cons (-1 / 4) .nil))) .nil)

/-- The compact scalar table reads the same complete original boundary matrix. -/
private theorem two_row_entries : twoRowMatrix = twoRowEntries := by
  apply Rectangular.ext
  intro row column
  refine Purelib.Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => ?_) column
    refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => ?_) column
    refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => Fin.elim0 column) column
  · refine Purelib.Data.Fin.cases_induction ?_ (fun row => Fin.elim0 row) row
    refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => ?_) column
    refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => ?_) column
    refine Purelib.Data.Fin.cases_induction (by decide +kernel) (fun column => Fin.elim0 column) column

/-- The first computed source-column entry is read through the exact retained scalar table. -/
private theorem two_row_source_first : twoRowForm.source 0 2 = 1 / 9 := by
  have reading := congrArg (fun matrix : Rectangular Rational 2 3 =>
    (NormalForm.compute matrix).source 0 2) two_row_entries
  exact reading.trans (by decide +kernel)

/-- The middle computed source-column entry is read through the same original table. -/
private theorem two_row_source_second : twoRowForm.source 1 2 = -8 / 9 := by
  have reading := congrArg (fun matrix : Rectangular Rational 2 3 =>
    (NormalForm.compute matrix).source 1 2) two_row_entries
  exact reading.trans (by decide +kernel)

/-- The final computed source-column entry is one at the original last coordinate. -/
private theorem two_row_source_third : twoRowForm.source 2 2 = 1 := by
  have reading := congrArg (fun matrix : Rectangular Rational 2 3 =>
    (NormalForm.compute matrix).source 2 2) two_row_entries
  exact reading.trans (by decide +kernel)

/-- The retained singleton kernel-column index uses the proved computed dimension. -/
private def twoRowBasisIndex : Fin (3 - twoRowForm.rank) :=
  ⟨0, by rw [two_row_rank]; decide +kernel⟩

/-- The computed kernel column reads the original final source column without replaying its producer. -/
private theorem two_row_kernel_entry (row : Fin 3) :
    twoRowForm.kernelBasis row twoRowBasisIndex = twoRowForm.source row 2 := by
  rw [NormalForm.kernelBasis, Rectangular.dropColumns_at]
  apply congrArg (fun column : Fin 3 => twoRowForm.source row column)
  apply Fin.ext
  have indexZero : twoRowBasisIndex.val = 0 := rfl
  exact (congrArg (fun index => twoRowForm.rank + index) indexZero).trans
    ((Nat.add_zero _).trans two_row_rank)

/-- The first original coordinate of its computed kernel basis is one ninth. -/
private theorem two_row_kernel_first : twoRowForm.kernelBasis 0 twoRowBasisIndex = 1 / 9 :=
  (two_row_kernel_entry 0).trans two_row_source_first

/-- Its middle original coordinate is minus eight ninths. -/
private theorem two_row_kernel_second : twoRowForm.kernelBasis 1 twoRowBasisIndex = -8 / 9 :=
  (two_row_kernel_entry 1).trans two_row_source_second

/-- Its last original coordinate is one. -/
private theorem two_row_kernel_third : twoRowForm.kernelBasis 2 twoRowBasisIndex = 1 :=
  (two_row_kernel_entry 2).trans two_row_source_third

end TestPurelib.Polynomial.Recurrence.Reduction
