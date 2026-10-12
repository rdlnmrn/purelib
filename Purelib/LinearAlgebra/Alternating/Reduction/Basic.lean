module

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Algebra.Ring.Int.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Exact replay of integral pairing reductions

An untrusted producer supplies only oriented unit pivots. Each successful
stage retains its shear and reduced matrix; invalidity identifies a bad pivot
or an entry which fails the claimed final normal form. Rejection is only of
this submitted reduction, not of the existence of another integral basis.
-/

namespace Purelib.LinearAlgebra.Alternating

variable {n : Nat}

namespace Reduction.Basic

set_option genInjectivity false in

/-- One retained unit pivot, its certified shear and its computed output matrix.

The record keeps exact equalities tying the pivot coordinates to the requested pair and the cached output to that same
shear transformation. -/
structure Step (matrix : SquareMatrix.IntegralMatrix n)
  (indices : Handle.Basic.PivotIndices n) where
  /-- The oriented unit pivot in the original matrix. -/ pivot : UnitPivot matrix
  /-- The pivot first coordinate is the requested first index. -/ first_eq : pivot.first = indices.1
  /-- The pivot last coordinate is the requested last index. -/ last_eq : pivot.last = indices.2
  /-- The retained two-column shear at the original pivot coordinates. -/ change :
    SquareMatrix.Integral.Shear pivot.first pivot.last
  /-- The retained shear is exactly the shear computed from the pivot. -/ change_eq : change = pivot.shear
  /-- The materialized reduced matrix. -/ output : SquareMatrix.IntegralMatrix n
  /-- The cached output is the transformation by the retained shear. -/ output_eq : output = change.transform matrix

constructive_injectivity Step

end Reduction.Basic
namespace Reduction.Basic.Step

open Purelib.LinearAlgebra.Alternating
/-- Build one reduction step from a certified positive unit entry.

The pivot, shear and output are computed once and retained with their defining equalities. -/
def build (matrix : SquareMatrix.IntegralMatrix n)
  (indices : Handle.Basic.PivotIndices n) (unit : matrix indices.1 indices.2 = 1) :
    Reduction.Basic.Step matrix indices :=
  let pivot : UnitPivot matrix := ⟨indices.1, indices.2, unit⟩
  let change := pivot.shear
  ⟨pivot, rfl, rfl, change, rfl, change.transform matrix, rfl⟩

/-- The retained output equals the pivot reduction. -/
theorem reduced_eq {matrix :
  SquareMatrix.IntegralMatrix n} {indices : Handle.Basic.PivotIndices n} (step : Reduction.Basic.Step matrix
  indices) :
    step.output = step.pivot.reduced := by rw [step.output_eq, step.change_eq]; rfl

/-- A unit-pivot reduction preserves entrywise skew symmetry. -/
theorem skew {matrix : SquareMatrix.IntegralMatrix
  n} {indices : Handle.Basic.PivotIndices n} (step : Reduction.Basic.Step matrix indices)
    (input : ∀ row column, matrix row column = -matrix column row) (row column : Fin n) :
    step.output row column = -step.output column row := by
  rw [step.reduced_eq]
  exact step.pivot.reduced_skew input row column

/-- The retained output has the double finite-sum formula for congruence by its shear basis. -/
theorem congruence {matrix :
  SquareMatrix.IntegralMatrix n} {indices : Handle.Basic.PivotIndices n} (step : Reduction.Basic.Step matrix
  indices)
    (row column : Fin n) : step.output row column =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => step.change.basis row i * matrix i j *
        step.change.basis column j)) := by
  rw [step.output_eq]
  exact step.change.transform_eq matrix row column

end Reduction.Basic.Step

open Purelib.LinearAlgebra.Alternating in
set_option genInjectivity false in
/-- A finite dependent chain of retained unit-pivot steps.

Each tail starts at the exact output matrix of its preceding step and follows the supplied ordered pivot list. -/
inductive Reduction : (matrix :
  SquareMatrix.IntegralMatrix n) → List (Handle.Basic.PivotIndices n) → Type where
  /-- The empty reduction leaves its indexed matrix unchanged. -/ | nil (matrix) :
    Reduction matrix []
  /-- Prepend a retained step to a reduction of its exact output. -/ | cons {matrix indices remaining} (step :
    Reduction.Basic.Step matrix indices) (tail : Reduction step.output
    remaining) :
      Reduction matrix (indices :: remaining)

constructive_injectivity Reduction

namespace Reduction

variable {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

open Purelib.LinearAlgebra.Alternating
/-- Read the final matrix of the retained reduction chain. -/
def output : {matrix :
  SquareMatrix.IntegralMatrix n} → {raw : List (Handle.Basic.PivotIndices n)} → Reduction matrix
  raw → SquareMatrix.IntegralMatrix n
  | _, _, .nil matrix => matrix
  | _, _, .cons _ tail => tail.output

/-- Apply the retained shears in reduction order to integral coordinates.

Each intermediate vector is passed directly to the remaining chain. -/
def forward : {matrix :
  SquareMatrix.IntegralMatrix n} → {raw : List (Handle.Basic.PivotIndices n)} →
    Reduction matrix raw → Data.Vector Int n → Data.Vector Int n
  | _, _, .nil _, values => values
  | _, _, .cons step tail, values => tail.forward (step.change.apply values)

/-- Apply the inverse shears in reverse order to integral coordinates.

The operation uses the retained chain and its original pivot dimensions. -/
def backward : {matrix :
  SquareMatrix.IntegralMatrix n} → {raw : List (Handle.Basic.PivotIndices n)} →
    Reduction matrix raw → Data.Vector Int n → Data.Vector Int n
  | _, _, .nil _, values => values
  | _, _, .cons step tail, values => step.change.unapply (tail.backward values)

/-- The backward coordinate change undoes the forward change. -/
theorem backward_forward (reduction :
  Reduction matrix raw) (values : Data.Vector Int n) :
    reduction.backward (reduction.forward values) = values := by
  induction reduction generalizing values with
  | nil => rfl
  | cons step tail ih =>
      change step.change.unapply (tail.backward (tail.forward (step.change.apply values))) = values
      rw [ih, step.change.unapply_apply]

/-- The forward coordinate change undoes the backward change. -/
theorem forward_backward (reduction :
  Reduction matrix raw) (values : Data.Vector Int n) :
    reduction.forward (reduction.backward values) = values := by
  induction reduction generalizing values with
  | nil => rfl
  | cons step tail ih =>
      change tail.forward (step.change.apply (step.change.unapply (tail.backward values))) = values
      rw [step.change.apply_unapply, ih]

/-- Every retained reduction preserves skew symmetry of its input matrix. -/
theorem output_skew (reduction :
  Reduction matrix raw) (input : ∀ row column, matrix row column = -matrix column row)
    (row column : Fin n) : reduction.output row column = -reduction.output column row := by
  induction reduction with
  | nil => exact input row column
  | cons step tail ih => exact ih (step.skew input)

end Reduction
end Purelib.LinearAlgebra.Alternating

end

public section
namespace Purelib.LinearAlgebra.Alternating.Reduction.Basic.Step

end Purelib.LinearAlgebra.Alternating.Reduction.Basic.Step
end

public section
namespace Purelib.LinearAlgebra.Alternating.Reduction

open Basic (Step)

end Purelib.LinearAlgebra.Alternating.Reduction
end
