module
import Purelib.Data.Fin
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.PolynomialMatrix.Leading.Triangular
public import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
public import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Shape
import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Leading

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Bivariate.Gaussian
open Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

/-!
# Separated Gaussian Sylvester matrices

The reflected and lifted coefficient blocks form the same finite Sylvester
matrix. Column degree and diagonal leading certificates retain its original
finite indices and the fraction-free scaled inverse scalar.
-/

public section

namespace Purelib.Polynomial.Elimination.Separated.Sylvester

open Purelib
open Purelib.Data
open Purelib.LinearAlgebra
open Purelib.Polynomial

/-- The finite Sylvester matrix for `p(U)` and `conj(p)(2T-U)`.

The reflected and lifted coefficient blocks occupy the original finite
row and column positions at the same displayed source degree. -/
@[expose] def separatedSylvester (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    PolynomialMatrix.Basic.GaussianMatrix (p.natDegree + p.natDegree) :=
  Bivariate.Resultant.sylvester
    (Lift.SeparatedVariables.lifted p)
      (SeparatedVariables.reflected p) p.natDegree p.natDegree

/-- Assign the original polynomial degree to reflected-block columns and degree zero to lifted-block columns.

The first block retains the original source degree; the second retains
zero. The splitter uses the same bounded column and block boundary. -/
@[expose] def separatedDegrees (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    Fin (p.natDegree + p.natDegree) → Nat :=
  fun column => Data.Fin.addCases
    (fun _ => p.natDegree) (fun _ => 0) column

/-- Assign the reflected leading coefficient and original leading coefficient to their respective Sylvester column
blocks.

The reflected block retains its computed leading coefficient, and the
lifted block retains the original polynomial leader at the same columns. -/
@[expose] def separatedDiagonal (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    Fin (p.natDegree + p.natDegree) → Gaussian.Basic.Canonical :=
  fun column => Data.Fin.addCases
    (fun _ => Reflection.Basic.reflectedLeading p) (fun _ => p.leadingCoeff) column

/-- The top parameter coefficient matrix of the separated Sylvester matrix is
upper triangular.  This is a finite coefficient-list fact: the reflected
block contributes its top term on the first diagonal, and `p(U)` contributes
its leading coefficient on the second diagonal.

Each bounded column retains its original block and degree. The displayed
diagonal leaders certify the same fraction-free scalar construction. -/
theorem separatedSylvester_leading (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    PolynomialMatrix.Leading.Triangular.UpperTriangularLeading
      (separatedSylvester p) (separatedDegrees p)
        (separatedDiagonal p) where
  atMost := by
    intro row column
    rcases Data.Fin.addCases_split column with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p row (Fin.castAdd p.natDegree left) =
            if (left : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (left : Nat) + p.natDegree then
              Bivariate.Resultant.outerCoeff
                (SeparatedVariables.reflected p) ((row : Nat) - left)
            else 0 :=
        Bivariate.Resultant.sylvester_left_apply
          (Lift.SeparatedVariables.lifted p)
            (SeparatedVariables.reflected p) p.natDegree p.natDegree row left
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact Data.Fin.addCases_left _ _ _
      apply Leading.DegreeAtMost.of_equal entryEqual degreeEqual
      by_cases included : (left : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (left : Nat) + p.natDegree
      · exact Leading.DegreeAtMost.of_equal (if_pos included) rfl
          (Reflection.Shape.reflectedCoeff_atMost p nonzero _)
      · exact Leading.DegreeAtMost.of_equal (if_neg included) rfl
          (Leading.DegreeAtMost.zero p.natDegree)
    · have entryEqual :
          separatedSylvester p row (Fin.natAdd p.natDegree right) =
            if (right : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (right : Nat) + p.natDegree then
              Bivariate.Resultant.outerCoeff
                (Lift.SeparatedVariables.lifted p) ((row : Nat) - right)
            else 0 :=
        Bivariate.Resultant.sylvester_right_apply
          (Lift.SeparatedVariables.lifted p)
            (SeparatedVariables.reflected p) p.natDegree p.natDegree row right
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact Data.Fin.addCases_right _ _ _
      apply Leading.DegreeAtMost.of_equal entryEqual degreeEqual
      by_cases included : (right : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (right : Nat) + p.natDegree
      · exact Leading.DegreeAtMost.of_equal (if_pos included) rfl
          (Lift.liftedCoeff_atMost p _)
      · exact Leading.DegreeAtMost.of_equal (if_neg included) rfl
          (Leading.DegreeAtMost.zero 0)
  below := by
    intro row column belowDiagonal
    rcases Data.Fin.addCases_split column with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p row (Fin.castAdd p.natDegree left) =
            if (left : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (left : Nat) + p.natDegree then
              Bivariate.Resultant.outerCoeff
                (SeparatedVariables.reflected p) ((row : Nat) - left)
            else 0 :=
        Bivariate.Resultant.sylvester_left_apply
          (Lift.SeparatedVariables.lifted p)
            (SeparatedVariables.reflected p) p.natDegree p.natDegree row left
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact Data.Fin.addCases_left _ _ _
      apply Leading.DegreeBelow.of_equal entryEqual degreeEqual
      by_cases included : (left : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (left : Nat) + p.natDegree
      · apply Leading.DegreeBelow.of_equal (if_pos included) rfl
        have positive : 0 < (row : Nat) - (left : Nat) := by
          have leftLt : (left : Nat) < (row : Nat) := belowDiagonal
          omega0
        have successorIdentity :
            (row : Nat) - (left : Nat) =
              ((row : Nat) - (left : Nat) - 1) + 1 := by
          have reconstructed := Data.Nat.Subtraction.add_sub_of_le
            (Nat.succ_le_of_lt positive)
          exact reconstructed.symm.trans (Nat.add_comm _ _)
        exact Leading.DegreeBelow.of_equal
          (congrArg
            (Bivariate.Resultant.outerCoeff
              (SeparatedVariables.reflected p))
            successorIdentity)
          rfl (Reflection.Shape.reflectedCoeff_below_of_pos p nonzero _)
      · exact Leading.DegreeBelow.of_equal (if_neg included) rfl
          (Leading.DegreeBelow.zero p.natDegree)
    · have entryEqual :
          separatedSylvester p row (Fin.natAdd p.natDegree right) =
            if (right : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (right : Nat) + p.natDegree then
              Bivariate.Resultant.outerCoeff
                (Lift.SeparatedVariables.lifted p) ((row : Nat) - right)
            else 0 :=
        Bivariate.Resultant.sylvester_right_apply
          (Lift.SeparatedVariables.lifted p)
            (SeparatedVariables.reflected p) p.natDegree p.natDegree row right
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact Data.Fin.addCases_right _ _ _
      apply Leading.DegreeBelow.of_equal entryEqual degreeEqual
      by_cases included : (right : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (right : Nat) + p.natDegree
      · apply Leading.DegreeBelow.of_equal (if_pos included) rfl
        have beyond :
            p.natDegree < (row : Nat) - (right : Nat) := by
          have rightBelow :
              p.natDegree + (right : Nat) < (row : Nat) := belowDiagonal
          omega0
        exact Leading.DegreeBelow.of_equal
          (Lift.liftedCoeff_eq_zero_of_degree_lt p nonzero beyond)
          rfl (Leading.DegreeBelow.zero 0)
      · exact Leading.DegreeBelow.of_equal (if_neg included) rfl
          (Leading.DegreeBelow.zero 0)
  diagonalLeading := by
    intro index
    rcases Data.Fin.addCases_split index with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p
              (Fin.castAdd p.natDegree left)
              (Fin.castAdd p.natDegree left) =
            Bivariate.Resultant.outerCoeff (SeparatedVariables.reflected
              p) 0 := by
        rw [separatedSylvester,
          Bivariate.Resultant.sylvester_left_apply,
          Fin.val_castAdd,
          if_pos ⟨le_rfl, Nat.le_add_right _ _⟩,
          Nat.sub_self]
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact Data.Fin.addCases_left _ _ _
      have diagonalEqual :
          separatedDiagonal p (Fin.castAdd p.natDegree left) =
            Reflection.Basic.reflectedLeading p := by
        unfold separatedDiagonal
        exact Data.Fin.addCases_left _ _ _
      exact Leading.LeadingTerm.of_equal entryEqual degreeEqual diagonalEqual
        (Reflection.Shape.reflectedCoeff_zero_leading p nonzero)
    · have difference :
          p.natDegree + (right : Nat) - (right : Nat) =
            p.natDegree := Data.Nat.Subtraction.add_sub_cancel_right _ _
      have entryEqual :
          separatedSylvester p
              (Fin.natAdd p.natDegree right)
              (Fin.natAdd p.natDegree right) =
            Bivariate.Resultant.outerCoeff (Lift.SeparatedVariables.lifted p) p.natDegree
              := by
        rw [separatedSylvester,
          Bivariate.Resultant.sylvester_right_apply,
          Fin.val_natAdd,
          if_pos ⟨Nat.le_add_left _ _, (Nat.add_comm _ _).le⟩,
          difference]
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact Data.Fin.addCases_right _ _ _
      have diagonalEqual :
          separatedDiagonal p (Fin.natAdd p.natDegree right) =
            p.leadingCoeff := by
        unfold separatedDiagonal
        exact Data.Fin.addCases_right _ _ _
      exact Leading.LeadingTerm.of_equal entryEqual degreeEqual diagonalEqual
        (Lift.liftedCoeff_degree_leading p nonzero)

/-- The fraction-free scaled inverse of the separated Sylvester matrix has a
nonzero scalar polynomial.

The upper-triangular top-coefficient certificate supplies all nonzero
diagonal leaders to the same fixed fraction-free scaled inverse. -/
theorem separatedScalar_nonzero (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
      (p.natDegree + p.natDegree) (separatedSylvester p)).scalar.isZero =
        false :=
  PolynomialMatrix.Leading.Triangular.scaledInverseData_scalar_nonzero
    (separatedSylvester_leading p nonzero)

end Purelib.Polynomial.Elimination.Separated.Sylvester

end
