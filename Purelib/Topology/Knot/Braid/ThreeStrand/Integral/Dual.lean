module
public import Purelib.LinearAlgebra.Matrix.Integral.Transpose
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Artin
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
import Purelib.Topology.Knot.Braid.Word.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Topology.Knot.Braid.Basic
import Purelib.LinearAlgebra.Matrix.Basic

namespace Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

/-- Matrix acting on the period column obtained by evaluating the displayed differential on the braid-transported
homology basis. -/
@[expose] def periodMatrix (word : Braid.Word 3) : LinearAlgebra.Matrix.Basic.IntegralMatrix :=
  Transpose.transpose (Words.wordMatrix word)

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral
/-- The dual period matrix of the empty three-strand word is the identity. -/
@[simp] theorem periodMatrix_nil :
    Dual.periodMatrix ([] : Braid.Word 3) = Multiplication.identity := by
  unfold Dual.periodMatrix
  rw [Words.wordMatrix_nil, Transpose.transpose_identity]

/-- Path concatenation is contravariant on the period column because periods pair with the transported homology basis.
-/
theorem periodMatrix_append (first second : Braid.Word 3) :
    Dual.periodMatrix (first ++ second) =
      Multiplication.mul (Dual.periodMatrix first) (Dual.periodMatrix second) := by
  unfold Dual.periodMatrix
  rw [Words.wordMatrix_append, Transpose.transpose_mul]

/-- Reversing a braid gives the two-sided inverse dual period action. -/
theorem periodMatrix_inverse_identities (word : Braid.Word 3) :
    Multiplication.mul (Dual.periodMatrix word) (Dual.periodMatrix word.inverse) = Multiplication.identity ∧
      Multiplication.mul (Dual.periodMatrix word.inverse) (Dual.periodMatrix word) = Multiplication.identity := by
  rcases Words.wordMatrix_inverse_identities word with
    ⟨homologyLeft, homologyRight⟩
  constructor
  · unfold Dual.periodMatrix
    rw [← Transpose.transpose_mul]
    exact (congrArg Transpose.transpose homologyLeft).trans Transpose.transpose_identity
  · unfold Dual.periodMatrix
    rw [← Transpose.transpose_mul]
    exact (congrArg Transpose.transpose homologyRight).trans Transpose.transpose_identity

/-- Artin-equivalent braid words induce the same dual period action. -/
theorem equivalent_periodMatrix_eq {left right : Braid.Word 3}
    (relation : Artin.Equivalent left right) :
    Dual.periodMatrix left = Dual.periodMatrix right :=
  congrArg Transpose.transpose (Words.equivalent_matrix_eq relation)

end

end Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
