module
import Purelib.Data.Fin.Two
import Purelib.Data.List.Append
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.Topology.Knot.Braid.Artin
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
import Purelib.Topology.Knot.Braid.Word.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Nat

namespace Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words

open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid
open Purelib.Topology.Knot.Braid.Artin
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

/-- Evaluate a braid word in traversal order. Its head acts first, so later crossings multiply on the left of earlier
crossings. -/
@[expose] def wordMatrix : Braid.Word 3 -> LinearAlgebra.Matrix.Basic.IntegralMatrix
  | [] => Multiplication.identity
  | generator :: remaining =>
      Multiplication.mul (Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words.wordMatrix remaining)
        (Generators.generatorMatrix generator)

section
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral
/-- The empty three-strand word evaluates to the identity matrix. -/
@[simp] theorem wordMatrix_nil : Words.wordMatrix ([] : Braid.Word 3) = Multiplication.identity := rfl

/-- Evaluate the head crossing before the remaining word, multiplying its matrix on the right. -/
@[simp] theorem wordMatrix_cons (generator : Braid.Generator 3)
    (remaining : Braid.Word 3) :
    Words.wordMatrix (generator :: remaining) =
      Multiplication.mul (Words.wordMatrix remaining) (Generators.generatorMatrix generator) := rfl

/-- Concatenating words multiplies the second matrix on the left of the first.

This order expresses traversal in which the first word acts before the second. -/
theorem wordMatrix_append (first second : Braid.Word 3) :
    Words.wordMatrix (first ++ second) = Multiplication.mul (Words.wordMatrix second) (Words.wordMatrix first) := by
  induction first with
  | nil =>
      simp only [List.nil_append, Words.wordMatrix_nil]
      exact (Multiplication.mul_identity_int _).symm
  | cons generator remaining inductionHypothesis =>
      simp only [List.cons_append, Words.wordMatrix_cons, inductionHypothesis]
      exact Multiplication.mul_assoc (Words.wordMatrix second) (Words.wordMatrix remaining)
        (Generators.generatorMatrix generator)

/-- A singleton word evaluates to its generator matrix. -/
theorem wordMatrix_singleton (generator : Braid.Generator 3) :
    Words.wordMatrix [generator] = Generators.generatorMatrix generator := by
  change Multiplication.mul Multiplication.identity (Generators.generatorMatrix generator) = Generators.generatorMatrix
    generator
  exact Multiplication.identity_mul_int _

/-- A generator followed by its reversal evaluates to the identity matrix. -/
theorem wordMatrix_cancel (generator : Braid.Generator 3) :
    Words.wordMatrix [generator, generator.reverse] = Multiplication.identity := by
  change Multiplication.mul (Multiplication.mul Multiplication.identity (Generators.generatorMatrix generator.reverse))
      (Generators.generatorMatrix generator) = Multiplication.identity
  rw [Multiplication.identity_mul_int]
  exact (Generators.generator_reverse_matrix generator).1

/-- An inverse braid word evaluates to a two-sided inverse matrix.

Both orders of multiplication are retained as exact equalities with the identity. -/
theorem wordMatrix_inverse_identities (word : Braid.Word 3) :
    Multiplication.mul (Words.wordMatrix word.inverse) (Words.wordMatrix word) = Multiplication.identity ∧
      Multiplication.mul (Words.wordMatrix word) (Words.wordMatrix word.inverse) = Multiplication.identity := by
  induction word with
  | nil =>
      simp only [Word.inverse_nil, Words.wordMatrix_nil]
      constructor <;> exact Multiplication.identity_mul_int _
  | cons generator remaining inductionHypothesis =>
      have inverseCons : Words.wordMatrix (Word.inverse (generator :: remaining)) =
          Multiplication.mul (Generators.generatorMatrix generator.reverse)
            (Words.wordMatrix (Word.inverse remaining)) := by
        rw [Word.inverse_cons, Words.wordMatrix_append,
          Words.wordMatrix_singleton]
      rw [inverseCons, Words.wordMatrix_cons]
      rcases inductionHypothesis with ⟨inverseLeft, inverseRight⟩
      rcases Generators.generator_reverse_matrix generator with
        ⟨generatorLeft, generatorRight⟩
      constructor
      · rw [Multiplication.mul_assoc,
          ← Multiplication.mul_assoc
            (Words.wordMatrix (Word.inverse remaining)) (Words.wordMatrix remaining),
          inverseLeft, Multiplication.identity_mul_int, generatorLeft]
      · rw [Multiplication.mul_assoc,
          ← Multiplication.mul_assoc
            (Generators.generatorMatrix generator) (Generators.generatorMatrix generator.reverse),
          generatorRight, Multiplication.identity_mul_int, inverseRight]

/-- The two concrete generator matrices satisfy the three-strand Artin relation for either common crossing sign. -/
theorem wordMatrix_artin (index : Fin (3 - 2)) (sign : Braid.CrossingSign) :
    Words.wordMatrix
        [Generator.lower index sign,
          Generator.upper index sign,
          Generator.lower index sign] =
      Words.wordMatrix
        [Generator.upper index sign,
          Generator.lower index sign,
          Generator.upper index sign] := by
  have indexZero : index = 0 := by
    apply Fin.ext
    have bound := index.isLt
    omega0
  subst index
  cases sign
  · change Multiplication.mul
        (Multiplication.mul (Multiplication.mul Multiplication.identity
          Generators.lowerPositiveMatrix) Generators.upperPositiveMatrix)
        Generators.lowerPositiveMatrix =
      Multiplication.mul
        (Multiplication.mul (Multiplication.mul Multiplication.identity
          Generators.upperPositiveMatrix) Generators.lowerPositiveMatrix)
        Generators.upperPositiveMatrix
    rewrite [Multiplication.identity_mul_int, Multiplication.identity_mul_int]
    unfold Generators.lowerPositiveMatrix Generators.upperPositiveMatrix
    rewrite [Two.mul_matrix₂, Two.mul_matrix₂, Two.mul_matrix₂, Two.mul_matrix₂]
    apply LinearAlgebra.Matrix.matrix_ext
    intro row column
    rcases Purelib.Data.Fin.Two.finTwo_cases row with zero | one <;>
      rcases Purelib.Data.Fin.Two.finTwo_cases column with zeroColumn | oneColumn <;>
      subst row <;> subst column <;> rfl
  · change Multiplication.mul
        (Multiplication.mul (Multiplication.mul Multiplication.identity
          Generators.lowerNegativeMatrix) Generators.upperNegativeMatrix)
        Generators.lowerNegativeMatrix =
      Multiplication.mul
        (Multiplication.mul (Multiplication.mul Multiplication.identity
          Generators.upperNegativeMatrix) Generators.lowerNegativeMatrix)
        Generators.upperNegativeMatrix
    rewrite [Multiplication.identity_mul_int, Multiplication.identity_mul_int]
    unfold Generators.lowerNegativeMatrix Generators.upperNegativeMatrix
    rewrite [Two.mul_matrix₂, Two.mul_matrix₂, Two.mul_matrix₂, Two.mul_matrix₂]
    apply LinearAlgebra.Matrix.matrix_ext
    intro row column
    rcases Purelib.Data.Fin.Two.finTwo_cases row with zero | one <;>
      rcases Purelib.Data.Fin.Two.finTwo_cases column with zeroColumn | oneColumn <;>
      subst row <;> subst column <;> rfl

end

/-- Two adjacent-generator indices on three strands cannot be separated by more than one. -/
private theorem no_far_generators
    (first second : Braid.Generator 3)
    (separated : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) : False := by
  have firstBound := first.index.isLt
  have secondBound := second.index.isLt
  omega0

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral
/-- Equal braid-word matrices remain equal inside the same prefix and suffix.

The inserted contexts are arbitrary finite words on three strands. -/
theorem wordMatrix_context {left right : Braid.Word 3}
    (same : Words.wordMatrix left = Words.wordMatrix right)
    (before after : Braid.Word 3) :
    Words.wordMatrix (before ++ left ++ after) =
      Words.wordMatrix (before ++ right ++ after) := by
  rw [Words.wordMatrix_append, Words.wordMatrix_append, Words.wordMatrix_append,
    Words.wordMatrix_append, same]

/-- Every finite cancellation, far-commutation, or Artin rewrite available on three strands preserves the displayed
homology matrix. -/
theorem rewrite_matrix_eq {left right : Braid.Word 3}
    (rewrite : Artin.Rewrite left right) :
    Words.wordMatrix left = Words.wordMatrix right := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [Purelib.Data.List.Append.append_nil] using Words.wordMatrix_context
        ((Words.wordMatrix_cancel generator).trans Words.wordMatrix_nil.symm) before after
  | far before after first second separated =>
      exact (Words.no_far_generators first second separated).elim
  | artin before after index sign =>
      exact Words.wordMatrix_context (Words.wordMatrix_artin index sign) before after

/-- Artin-equivalent three-strand words have equal integral action matrices.

The supplied proof-valued relation is generated by finite rewrites, symmetry and transitivity. -/
theorem equivalent_matrix_eq {left right : Braid.Word 3}
    (relation : Artin.Equivalent left right) :
    Words.wordMatrix left = Words.wordMatrix right := by
  induction relation with
  | refl word => rfl
  | step rewrite => exact Words.rewrite_matrix_eq rewrite
  | symm relation inductionHypothesis => exact inductionHypothesis.symm
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

end

end Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
