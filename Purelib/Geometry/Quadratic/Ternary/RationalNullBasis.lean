module

import Purelib.Algebra.Field.Characteristic.Nonzero
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
public import Purelib.Geometry.Rotations.Ternary.Split.Parabolic
public import Purelib.Algebra.Clifford.Split.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Clifford.Split.Matrix

open Purelib.Geometry.Quadratic.Ternary.SplitNullConic

open Purelib.Geometry.Rotations.Ternary.Split.Parabolic

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Pairwise conjugacy of rational Minkowski parabolics

The split Clifford algebra is the displayed two-by-two matrix algebra.  For
one nonzero null-conic parameter pair this file constructs a finite basis in
which its nilpotent matrix is the standard upper-triangular nilpotent.  The
basis uses one decidable chart and has determinant `-1`.  Two such bases and
the two supplied nonzero parabolic parameters then give an explicit
invertible transport matrix.
-/

namespace Purelib.Geometry.Quadratic.Ternary.RationalNullBasis

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section MinkowskiClifford

section ParabolicConjugacy

/-- The standard rank-one nilpotent and its scalar-one unipotent family. -/
def MinkowskiClifford.ParabolicConjugacy.standardNilpotent :
  Coordinates2.Matrix K := ⟨0, 1, 0, 0⟩

/-- The upper-triangular two-by-two unipotent matrix with the supplied parameter. -/
def MinkowskiClifford.ParabolicConjugacy.standardParabolic
  (parameter : K) : Coordinates2.Matrix K :=
  ⟨1, parameter, 0, 1⟩

/-- A diagonal matrix that changes the standard unipotent parameter from the left supplied value to the right supplied
value. -/
def MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
  (left right : K) : Coordinates2.Matrix K :=
  ⟨left, 0, 0, right⟩

/-- The diagonal parameter matrix intertwines the two standard unipotent matrices. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.standardParabolic_parameterDiagonal
  (left right : K) :
    Coordinates2.Matrix.mul
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic left)
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal left right) =
      Coordinates2.Matrix.mul
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal left right)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic right) :=
          by
  apply Coordinates2.Matrix.ext <;>
    unfold Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
      Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
      Coordinates2.Matrix.mul <;> ring1

/-- The parameter diagonal has determinant equal to the product of its parameters. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.parameterDiagonal_determinant
  (left right : K) :
    Coordinates2.Matrix.determinant
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal left right) =
      left * right := by
  unfold Coordinates2.Matrix.determinant
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
  ring1

/-- One finite chart turns the null matrix attached to `(first,second)` into the standard nilpotent. Its first column
spans the null image; the second is chosen to pair to one with the corresponding covector. -/
def MinkowskiClifford.ParabolicConjugacy.nullBasis
  [DecidableEq K] (first second : K) : Coordinates2.Matrix K :=
  if _sumNonzero : first + second ≠ 0 then
    ⟨first - second, (first + second)⁻¹,
      first + second, 0⟩
  else
    ⟨first - second, 0,
      first + second, -(first - second)⁻¹⟩

/-- The selected basis of a nonzero null-conic parameter pair has determinant minus one. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.nullBasis_determinant
  [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Coordinates2.Matrix.determinant
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second) = -1 :=
      by
  by_cases sumZero : first + second = 0
  · have differenceNonzero :=
      Purelib.Algebra.Field.Characteristic.Nonzero.difference_nonzero_of_sum_zero
      twoNonzero first second parametersNonzero sumZero
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (first - second) differenceNonzero
    rw [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis, dif_neg (fun
      nonzero => nonzero sumZero)]
    change (first - second) * (-(first - second)⁻¹) -
      0 * (first + second) = -1
    calc
      (first - second) * (-(first - second)⁻¹) -
          0 * (first + second) =
        -((first - second) * (first - second)⁻¹) := by ring1
      _ = -1 := by rw [cancel]
  · have sumNonzero : first + second ≠ 0 := sumZero
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (first + second) sumNonzero
    have reverseCancel : (first + second)⁻¹ * (first + second) = 1 := by
      calc
        (first + second)⁻¹ * (first + second) =
            (first + second) * (first + second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis, dif_pos sumNonzero]
    change (first - second) * 0 -
      (first + second)⁻¹ * (first + second) = -1
    rw [reverseCancel]
    ring1

/-- The split-matrix display of the supplied null-conic parabolic. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.toMatrix_parabolicAt_nullParameter
    (oneNonzero : (1 : K) ≠ 0) (first second parameter : K) :
    MinkowskiClifford.toMatrix oneNonzero
        (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter first second)
          (MinkowskiClifford.nullParameter_isNull oneNonzero first second)
          parameter).toEvenClifford =
      ⟨1 + parameter * (first + second) * (first - second),
        -(parameter * (first - second) ^ 2),
        parameter * (first + second) ^ 2,
        1 - parameter * (first + second) * (first - second)⟩ := by
  apply Coordinates2.Matrix.ext <;>
    unfold MinkowskiClifford.toMatrix MinkowskiClifford.parabolicAt MinkowskiClifford.parabolicValue
      MinkowskiClifford.parabolicRaw MinkowskiClifford.nullParameter
      Coordinates3.Vector.scale <;> ring1

/-- The chart basis intertwines the displayed parabolic with the standard upper-triangular unipotent having the same
scalar parameter. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.parabolicMatrix_mul_nullBasis
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second parameter : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Coordinates2.Matrix.mul
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter first second)
            (MinkowskiClifford.nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second) =
      Coordinates2.Matrix.mul
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
          := by
  rw
    [MinkowskiClifford.ParabolicConjugacy.toMatrix_parabolicAt_nullParameter]
  by_cases sumZero : first + second = 0
  · have differenceNonzero :=
      Purelib.Algebra.Field.Characteristic.Nonzero.difference_nonzero_of_sum_zero
      twoNonzero first second parametersNonzero sumZero
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (first - second) differenceNonzero
    have reverseCancel : (first - second)⁻¹ * (first - second) = 1 := by
      calc
        (first - second)⁻¹ * (first - second) =
            (first - second) * (first - second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis, dif_neg (fun
      nonzero => nonzero sumZero)]
    apply Coordinates2.Matrix.ext
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      rw [sumZero]
      ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      rw [sumZero]
      calc
        (1 + parameter * 0 * (first - second)) * 0 +
            -(parameter * (first - second) ^ 2) *
              (-(first - second)⁻¹) =
          parameter * (first - second) *
            ((first - second) * (first - second)⁻¹) := by ring1
        _ = parameter * (first - second) := by rw [cancel]; ring1
        _ = (first - second) * parameter + 0 * 1 := by ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      rw [sumZero]
      ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      rw [sumZero]
      ring1
  · have sumNonzero : first + second ≠ 0 := sumZero
    have cancel := Algebra.Field.ExplicitField.mul_inv_cancel
      (first + second) sumNonzero
    have reverseCancel : (first + second)⁻¹ * (first + second) = 1 := by
      calc
        (first + second)⁻¹ * (first + second) =
            (first + second) * (first + second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis, dif_pos sumNonzero]
    apply Coordinates2.Matrix.ext
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      calc
        (1 + parameter * (first + second) * (first - second)) *
              (first + second)⁻¹ +
            -(parameter * (first - second) ^ 2) * 0 =
          (first + second)⁻¹ + parameter * (first - second) *
            ((first + second) * (first + second)⁻¹) := by ring1
        _ = (first + second)⁻¹ +
            parameter * (first - second) := by rw [cancel]; ring1
        _ = (first - second) * parameter +
            (first + second)⁻¹ * 1 := by ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      ring1
    · simp only [Coordinates2.Matrix.mul,
        Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic]
      calc
        parameter * (first + second) ^ 2 * (first + second)⁻¹ +
            (1 - parameter * (first + second) * (first - second)) * 0 =
          parameter * (first + second) *
            ((first + second) * (first + second)⁻¹) := by ring1
        _ = parameter * (first + second) := by rw [cancel]; ring1
        _ = (first + second) * parameter + 0 * 1 := by ring1

set_option genInjectivity false in
/-- Finite cached basis data for one parametrized nonzero null direction. -/
structure MinkowskiClifford.ParabolicConjugacy.NullBasisData
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second : K) (parametersNonzero : first ≠ 0 ∨ second ≠ 0)
    where
  /-- The cached two-by-two chart basis of the original null-conic parameter pair. -/ basis : Coordinates2.Matrix K
  /-- The retained basis is exactly the result of the explicit chart construction. -/ basis_eq : basis =
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second
  /-- The retained basis has determinant minus one. -/ determinant_eq : Coordinates2.Matrix.determinant basis = -1
  /-- The retained basis intertwines each parameterized null-conic parabolic with its standard upper-triangular form. -/
    intertwines : ∀ parameter : K,
    Coordinates2.Matrix.mul
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter first second)
            (MinkowskiClifford.nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford)
        basis = Coordinates2.Matrix.mul basis
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
          parameter)

constructive_injectivity MinkowskiClifford.ParabolicConjugacy.NullBasisData

/-- Compute and retain the chart basis of a nonzero null-conic parameter pair.

The bundle certifies determinant minus one and intertwining with every standard unipotent parameter. -/
def MinkowskiClifford.ParabolicConjugacy.nullBasisData
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second : K) (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.NullBasisData oneNonzero
      twoNonzero first second parametersNonzero where
  basis := Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second
  basis_eq := rfl
  determinant_eq :=
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis_determinant twoNonzero
    first second
    parametersNonzero
  intertwines := fun parameter =>
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parabolicMatrix_mul_nullBasis
      oneNonzero twoNonzero first second
      parameter parametersNonzero

/-- The adjugate basis intertwines in the reverse direction. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.nullBasis_adjugate_mul_parabolicMatrix
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second parameter : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second))
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter first second)
            (MinkowskiClifford.nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford) =
      Coordinates2.Matrix.mul
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
        (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second)) :=
          by
  let basis := Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis first second
  let parabolicMatrix :=
    MinkowskiClifford.toMatrix oneNonzero
      (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter first second)
        (MinkowskiClifford.nullParameter_isNull oneNonzero first second)
        parameter).toEvenClifford
  have determinantEq : Coordinates2.Matrix.determinant basis = -1 :=
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis_determinant twoNonzero
      first second parametersNonzero
  apply
    Purelib.LinearAlgebra.Coordinates2.Matrix.mul_right_cancel_of_determinant_eq_neg_one
    basis _ _ determinantEq
  calc
    Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate basis) parabolicMatrix) basis =
        Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate basis)
          (Coordinates2.Matrix.mul parabolicMatrix basis) := by rw [Coordinates2.Matrix.mul_assoc]
    _ = Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate basis)
        (Coordinates2.Matrix.mul basis
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
          parameter)) := by
      rw
        [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parabolicMatrix_mul_nullBasis
        oneNonzero twoNonzero first second
        parameter parametersNonzero]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate basis) basis)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
          := by rw [Coordinates2.Matrix.mul_assoc]
    _ = Coordinates2.Matrix.mul (Coordinates2.Matrix.scalarScale (-1) Coordinates2.Matrix.identity)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
          := by
      rw [Coordinates2.Matrix.adjugate_mul, determinantEq]
    _ = Coordinates2.Matrix.scalarScale (-1)
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter) :=

        Purelib.LinearAlgebra.Coordinates2.Matrix.scale_identity_mul
        (-1) (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
        parameter)
    _ = Coordinates2.Matrix.mul
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
        (Coordinates2.Matrix.scalarScale (-1) Coordinates2.Matrix.identity) := by
      rw
        [Purelib.LinearAlgebra.Coordinates2.Matrix.mul_scale_identity]
    _ = Coordinates2.Matrix.mul
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic parameter)
        (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate basis) basis) := by
      rw [Coordinates2.Matrix.adjugate_mul, determinantEq]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
          parameter)
          (Coordinates2.Matrix.adjugate basis)) basis := by rw [Coordinates2.Matrix.mul_assoc]

/-- The explicit two-by-two transporter between two parametrized nonzero parabolics. -/
def MinkowskiClifford.ParabolicConjugacy.transportMatrix
  [DecidableEq K]
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K) : Coordinates2.Matrix K :=
  Coordinates2.Matrix.mul
    (Coordinates2.Matrix.mul
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst leftSecond)
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal leftParameter
        rightParameter))
    (Coordinates2.Matrix.adjugate
      (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
      rightSecond))

/-- The null-basis transport matrix has determinant equal to the product of the two parabolic parameters. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.transportMatrix_determinant
  [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0) :
    Coordinates2.Matrix.determinant
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.transportMatrix leftFirst
          leftSecond rightFirst rightSecond
          leftParameter rightParameter) = leftParameter * rightParameter := by
  unfold Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.transportMatrix
  rw [Coordinates2.Matrix.determinant_mul, Coordinates2.Matrix.determinant_mul,
    Coordinates2.Matrix.determinant_adjugate,
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis_determinant twoNonzero
      leftFirst leftSecond
      leftCoordinatesNonzero,
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis_determinant twoNonzero
      rightFirst rightSecond
      rightCoordinatesNonzero,
    Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal_determinant]
  ring1

/-- The cached transport matrix intertwines the two displayed unipotents. -/
theorem
  MinkowskiClifford.ParabolicConjugacy.parabolicMatrix_mul_transportMatrix
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0) :
    Coordinates2.Matrix.mul
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter leftFirst leftSecond)
            (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond)
            leftParameter).toEvenClifford)
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.transportMatrix leftFirst
          leftSecond rightFirst rightSecond
          leftParameter rightParameter) =
      Coordinates2.Matrix.mul
        (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.transportMatrix leftFirst
          leftSecond rightFirst rightSecond
          leftParameter rightParameter)
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter rightFirst rightSecond)
            (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford) := by
  unfold Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.transportMatrix
  calc
    Coordinates2.Matrix.mul
          (MinkowskiClifford.toMatrix oneNonzero
            (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter leftFirst leftSecond)
              (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond)
              leftParameter).toEvenClifford)
          (Coordinates2.Matrix.mul
            (Coordinates2.Matrix.mul
              (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
              leftSecond)
              (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
                leftParameter rightParameter))
            (Coordinates2.Matrix.adjugate
              (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
              rightSecond))) =
        Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul
            (Coordinates2.Matrix.mul
              (MinkowskiClifford.toMatrix oneNonzero
                (MinkowskiClifford.parabolicAt oneNonzero
                  (MinkowskiClifford.nullParameter leftFirst leftSecond)
                  (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond)
                  leftParameter).toEvenClifford)
              (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
                leftSecond))
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
              leftParameter rightParameter))
          (Coordinates2.Matrix.adjugate
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
            rightSecond)) := by
      rw [← Coordinates2.Matrix.mul_assoc, ← Coordinates2.Matrix.mul_assoc]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
            leftSecond)
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
              leftParameter))
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter))
        (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
          rightSecond)) := by
      rw
        [Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parabolicMatrix_mul_nullBasis
        oneNonzero twoNonzero leftFirst
        leftSecond leftParameter leftCoordinatesNonzero]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Coordinates2.Matrix.mul
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
            leftParameter)
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
              leftParameter rightParameter)))
        (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
          rightSecond)) := by
      exact congrArg
        (fun matrix => Coordinates2.Matrix.mul matrix
          (Coordinates2.Matrix.adjugate
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
            rightSecond)))
        (Coordinates2.Matrix.mul_assoc
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
            leftParameter)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter))
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Coordinates2.Matrix.mul
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter)
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
              rightParameter)))
        (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
          rightSecond)) := by
      rw
        [MinkowskiClifford.ParabolicConjugacy.standardParabolic_parameterDiagonal]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
            leftSecond)
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
              leftParameter rightParameter))
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
            rightParameter))
        (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
          rightSecond)) := by
      exact congrArg
        (fun matrix => Coordinates2.Matrix.mul matrix
          (Coordinates2.Matrix.adjugate
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
            rightSecond)))
        (Coordinates2.Matrix.mul_assoc
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
            rightParameter)).symm
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter))
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.standardParabolic
          rightParameter)
          (Coordinates2.Matrix.adjugate
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
            rightSecond))) := by
      rw [Coordinates2.Matrix.mul_assoc]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
          leftSecond)
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
            leftParameter rightParameter))
        (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate
          (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
          rightSecond))
          (MinkowskiClifford.toMatrix oneNonzero
            (MinkowskiClifford.parabolicAt oneNonzero
              (MinkowskiClifford.nullParameter rightFirst rightSecond)
              (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond)
              rightParameter).toEvenClifford)) := by
      rw
        [MinkowskiClifford.ParabolicConjugacy.nullBasis_adjugate_mul_parabolicMatrix
        oneNonzero twoNonzero
        rightFirst rightSecond rightParameter rightCoordinatesNonzero]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis leftFirst
            leftSecond)
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.parameterDiagonal
              leftParameter rightParameter))
          (Coordinates2.Matrix.adjugate
            (Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford.ParabolicConjugacy.nullBasis rightFirst
            rightSecond)))
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter rightFirst rightSecond)
            (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford) := by
      rw [← Coordinates2.Matrix.mul_assoc]
end ParabolicConjugacy

end MinkowskiClifford

end Purelib.Geometry.Quadratic.Ternary.RationalNullBasis

end
