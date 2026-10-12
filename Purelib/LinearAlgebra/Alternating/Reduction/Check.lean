module

import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

set_option genInjectivity false in
/-- A retained witness that a submitted pivot chain fails at a concrete stage.

The witness keeps all successful preceding steps and the first requested entry that is not positive one. -/
inductive Reduction.Check.InvalidReduction : (matrix :
  SquareMatrix.IntegralMatrix n) → List (Handle.Basic.PivotIndices n) → Type where
  /-- The requested leading entry is not positive one. -/ | pivot {matrix} (indices : Handle.Basic.PivotIndices n)
    (remaining : List (Handle.Basic.PivotIndices n))
      (notUnit : matrix indices.1 indices.2 ≠ 1) : Reduction.Check.InvalidReduction
        matrix (indices :: remaining)
  /-- A valid retained step precedes a failed tail reduction. -/ | tail {matrix indices remaining} (step :
    Reduction.Basic.Step matrix indices) (invalid : Reduction.Check.InvalidReduction
    step.output remaining) :
      Reduction.Check.InvalidReduction matrix (indices :: remaining)

constructive_injectivity Reduction.Check.InvalidReduction

section
open Purelib.LinearAlgebra.Alternating
/-- Count the successful steps before the first invalid pivot. -/
def Reduction.Check.InvalidReduction.offset {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)} : Reduction.Check.InvalidReduction
  matrix raw → Nat
  | .pivot .. => 0
  | .tail _ invalid => invalid.offset + 1

/-- Read the original requested pair at the failed pivot stage. -/
def Reduction.Check.InvalidReduction.offending {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)} :
    Reduction.Check.InvalidReduction matrix raw → Handle.Basic.PivotIndices n
  | .pivot indices _ _ => indices
  | .tail _ invalid => invalid.offending

end

open Purelib.LinearAlgebra.Alternating in
/-- Check the ordered finite pivot list against successive computed matrices.

Success retains every step and its output; failure retains the successful prefix and exact non-unit entry obstruction.
-/
def Reduction.Check.checkReduction (matrix : SquareMatrix.IntegralMatrix
  n) :
    (raw : List (Handle.Basic.PivotIndices n)) → Except (Reduction.Check.InvalidReduction matrix raw)
      (Reduction matrix raw)
  | [] => .ok (.nil matrix)
  | indices :: remaining =>
      if unit : matrix indices.1 indices.2 = 1 then
        let step := Reduction.Basic.Step.build matrix indices unit
        match Reduction.Check.checkReduction step.output remaining with
        | .ok tail => .ok (.cons step tail)
        | .error invalid => .error (.tail step invalid)
      else .error (.pivot indices remaining unit)
end Purelib.LinearAlgebra.Alternating

end
