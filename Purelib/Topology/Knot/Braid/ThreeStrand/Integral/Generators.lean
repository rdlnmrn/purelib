module
public import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Two
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat

namespace Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators

open Purelib
open Purelib.Data.Fin
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid

public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

/-- The integral shear with rows (1, -1) and (0, 1). -/
@[expose] def lowerPositiveMatrix : LinearAlgebra.Matrix.Basic.IntegralMatrix := Two.matrix₂ 1 (-1) 0 1
/-- The integral shear with rows (1, 1) and (0, 1). -/
@[expose] def lowerNegativeMatrix : LinearAlgebra.Matrix.Basic.IntegralMatrix := Two.matrix₂ 1 1 0 1
/-- The integral shear with rows (1, 0) and (1, 1). -/
@[expose] def upperPositiveMatrix : LinearAlgebra.Matrix.Basic.IntegralMatrix := Two.matrix₂ 1 0 1 1
/-- The integral shear with rows (1, 0) and (-1, 1). -/
@[expose] def upperNegativeMatrix : LinearAlgebra.Matrix.Basic.IntegralMatrix := Two.matrix₂ 1 0 (-1) 1

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral
/-- Matrix of one signed adjacent generator.

Every `Fin 2` index other than zero is definitionally the upper generator after finite case analysis. -/
@[expose] def generatorMatrix (generator : Braid.Generator 3) : LinearAlgebra.Matrix.Basic.IntegralMatrix :=
  match generator.sign with
  | .positive =>
      if generator.index = 0 then Generators.lowerPositiveMatrix else Generators.upperPositiveMatrix
  | .negative =>
      if generator.index = 0 then Generators.lowerNegativeMatrix else Generators.upperNegativeMatrix

/-- The negative lower shear times the positive lower shear is the identity. -/
@[simp] theorem lower_matrices_inverse_left :
    Multiplication.mul Generators.lowerNegativeMatrix Generators.lowerPositiveMatrix = Multiplication.identity := by
  rw [show Generators.lowerNegativeMatrix = Two.matrix₂ 1 1 0 1 by rfl,
    show Generators.lowerPositiveMatrix = Two.matrix₂ 1 (-1) 0 1 by rfl, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

/-- The positive lower shear times the negative lower shear is the identity. -/
@[simp] theorem lower_matrices_inverse_right :
    Multiplication.mul Generators.lowerPositiveMatrix Generators.lowerNegativeMatrix = Multiplication.identity := by
  rw [show Generators.lowerPositiveMatrix = Two.matrix₂ 1 (-1) 0 1 by rfl,
    show Generators.lowerNegativeMatrix = Two.matrix₂ 1 1 0 1 by rfl, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

/-- The negative upper shear times the positive upper shear is the identity. -/
@[simp] theorem upper_matrices_inverse_left :
    Multiplication.mul Generators.upperNegativeMatrix Generators.upperPositiveMatrix = Multiplication.identity := by
  rw [show Generators.upperNegativeMatrix = Two.matrix₂ 1 0 (-1) 1 by rfl,
    show Generators.upperPositiveMatrix = Two.matrix₂ 1 0 1 1 by rfl, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

/-- The positive upper shear times the negative upper shear is the identity. -/
@[simp] theorem upper_matrices_inverse_right :
    Multiplication.mul Generators.upperPositiveMatrix Generators.upperNegativeMatrix = Multiplication.identity := by
  rw [show Generators.upperPositiveMatrix = Two.matrix₂ 1 0 1 1 by rfl,
    show Generators.upperNegativeMatrix = Two.matrix₂ 1 0 (-1) 1 by rfl, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;>
    rfl

/-- Reversing a signed three-strand generator gives a two-sided inverse matrix.

Both multiplication orders are retained as exact structural matrix equalities. -/
theorem generator_reverse_matrix (generator : Braid.Generator 3) :
    Multiplication.mul (Generators.generatorMatrix generator.reverse) (Generators.generatorMatrix generator) =
        Multiplication.identity ∧
      Multiplication.mul (Generators.generatorMatrix generator) (Generators.generatorMatrix generator.reverse) =
        Multiplication.identity := by
  cases generator with
  | mk index sign =>
      rcases Two.finTwo_cases index with zero | one
      · subst index
        cases sign
        · change Multiplication.mul Generators.lowerNegativeMatrix
              Generators.lowerPositiveMatrix = Multiplication.identity ∧
            Multiplication.mul Generators.lowerPositiveMatrix
              Generators.lowerNegativeMatrix = Multiplication.identity
          exact ⟨Generators.lower_matrices_inverse_left,
            Generators.lower_matrices_inverse_right⟩
        · change Multiplication.mul Generators.lowerPositiveMatrix
              Generators.lowerNegativeMatrix = Multiplication.identity ∧
            Multiplication.mul Generators.lowerNegativeMatrix
              Generators.lowerPositiveMatrix = Multiplication.identity
          exact ⟨Generators.lower_matrices_inverse_right,
            Generators.lower_matrices_inverse_left⟩
      · subst index
        cases sign
        · change Multiplication.mul Generators.upperNegativeMatrix
              Generators.upperPositiveMatrix = Multiplication.identity ∧
            Multiplication.mul Generators.upperPositiveMatrix
              Generators.upperNegativeMatrix = Multiplication.identity
          exact ⟨Generators.upper_matrices_inverse_left,
            Generators.upper_matrices_inverse_right⟩
        · change Multiplication.mul Generators.upperPositiveMatrix
              Generators.upperNegativeMatrix = Multiplication.identity ∧
            Multiplication.mul Generators.upperNegativeMatrix
              Generators.upperPositiveMatrix = Multiplication.identity
          exact ⟨Generators.upper_matrices_inverse_right,
            Generators.upper_matrices_inverse_left⟩

end

end Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
