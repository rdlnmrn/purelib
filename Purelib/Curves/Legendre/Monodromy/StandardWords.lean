module

public import Purelib.Curves.Legendre.Monodromy
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Data.Fin.Two
import Purelib.Data.List.Append
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-! # Signed integral actions of words in the two labelled standard loops

The original three-strand generator alphabet labels zero and one, with its
original crossing sign. Here each letter means the full labelled loop and
expands to two identical signed crossings. Evaluation uses the original
braid matrix interpreter and traversal order. Arbitrary pure braid words
are a larger language than these expanded standard-loop words.

The determinant and congruences below are necessary image conditions. Their
soundness excludes negative identity in this signed integral lift. A checked
word converse and geometric normalization into this language are separate.
-/

public section

namespace Purelib.Curves.Legendre.Monodromy.StandardWords

open Purelib
open Purelib.Data.List
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

/-- Expand each original signed zero/one letter into its squared labelled-loop braid block.

The list is in traversal order. Negative letters expand to two negative
crossings, retaining the inverse signed lift rather than a projective class.
-/
@[expose] def braid : Braid.Word 3 → Braid.Word 3
  | [] => []
  | letter :: remaining => letter :: letter :: braid remaining

/-- Read the original integral homology action of the actual expanded standard-loop word. -/
@[expose] def matrix (word : Braid.Word 3) : IntegralMatrix := Words.wordMatrix (braid word)

/-- The expanded word preserves the original ordered concatenation of labelled loops. -/
theorem braid_append (first second : Braid.Word 3) :
    braid (first ++ second) = braid first ++ braid second := by
  induction first with
  | nil => rfl
  | cons letter remaining prior =>
    exact congrArg (fun tail => letter :: letter :: tail) prior

/-- Expanding a reversed signed loop word gives the inverse of its same original braid expansion. -/
theorem braid_inverse (word : Braid.Word 3) : braid word.inverse = (braid word).inverse := by
  induction word with
  | nil => rfl
  | cons letter remaining prior =>
    rewrite [Braid.Word.inverse_cons, braid_append]
    change braid (Braid.Word.inverse remaining) ++ [letter.reverse, letter.reverse] =
      Braid.Word.inverse (letter :: letter :: braid remaining)
    rewrite [Braid.Word.inverse_cons, Braid.Word.inverse_cons]
    exact (congrArg (fun tail => tail ++ [letter.reverse, letter.reverse]) prior).trans
      (Append.append_assoc (braid remaining).inverse [letter.reverse] [letter.reverse]).symm

/-- A standard block is squared before its actual tail acts on the left. -/
theorem matrix_cons (letter : Braid.Generator 3) (remaining : Braid.Word 3) :
    matrix (letter :: remaining) = Multiplication.mul (matrix remaining)
      (Multiplication.mul (Generators.generatorMatrix letter) (Generators.generatorMatrix letter)) :=
  Multiplication.mul_assoc _ _ _

/-- Standard-loop concatenation acts in the original homology traversal order. -/
theorem matrix_append (first second : Braid.Word 3) :
    matrix (first ++ second) = Multiplication.mul (matrix second) (matrix first) :=
  (congrArg Words.wordMatrix (braid_append first second)).trans
    (Words.wordMatrix_append (braid first) (braid second))

/-- Reversing the signed standard word gives both inverse identities in the original integral lift. -/
theorem matrix_inverse_identities (word : Braid.Word 3) :
    Multiplication.mul (matrix word.inverse) (matrix word) = Multiplication.identity ∧
      Multiplication.mul (matrix word) (matrix word.inverse) = Multiplication.identity := by
  have readback := congrArg Words.wordMatrix (braid_inverse word)
  have original := Words.wordMatrix_inverse_identities (braid word)
  exact ⟨(congrArg (fun value => Multiplication.mul value (matrix word)) readback).trans original.1,
    (congrArg (fun value => Multiplication.mul (matrix word) value) readback).trans original.2⟩

/-- The positive zero letter has exactly the original squared zero-loop matrix. -/
theorem matrix_zero : matrix [Conventions.lowerPositive] = zeroMatrix := zeroBraid_matrix

/-- The positive one letter has exactly the original squared one-loop matrix. -/
theorem matrix_one : matrix [Conventions.upperPositive] = oneMatrix := oneBraid_matrix

/-- Necessary determinant and signed congruences for the retained integral standard-loop action.

Both off-diagonal entries are even; both diagonal entries are one modulo
four. This keeps the signed lift that is lost on passing to projective
matrices and is stronger than congruence to identity modulo two.
-/
@[expose] def SignedCongruence (value : IntegralMatrix) : Prop :=
  value 0 0 * value 1 1 - value 0 1 * value 1 0 = 1 ∧
    value 0 0 % 4 = 1 ∧ value 0 1 % 2 = 0 ∧ value 1 0 % 2 = 0 ∧ value 1 1 % 4 = 1

/-- The finite signed congruence condition is decidable directly from the four original entries. -/
instance (value : IntegralMatrix) : Decidable (SignedCongruence value) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The displayed matrix reads exactly its four scalar determinant and congruence conditions. -/
private theorem congruence_entries (a b c d : Int) :
    SignedCongruence (Two.matrix₂ a b c d) ↔
      a * d - b * c = 1 ∧ a % 4 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 4 = 1 := Iff.rfl

/-- Each actual positive or negative squared adjacent block preserves the signed congruences. -/
private theorem congruence_block_entries (a b c d : Int)
    (valid : SignedCongruence (Two.matrix₂ a b c d)) (letter : Braid.Generator 3) :
    SignedCongruence (Multiplication.mul (Two.matrix₂ a b c d)
      (Multiplication.mul (Generators.generatorMatrix letter) (Generators.generatorMatrix letter))) := by
  have original := (congruence_entries a b c d).mp valid
  clear valid
  have lowerPositive : Generators.generatorMatrix (⟨0, .positive⟩ : Braid.Generator 3) =
      Two.matrix₂ 1 (-1) 0 1 := rfl
  have lowerNegative : Generators.generatorMatrix (⟨0, .negative⟩ : Braid.Generator 3) =
      Two.matrix₂ 1 1 0 1 := rfl
  have upperPositive : Generators.generatorMatrix (⟨1, .positive⟩ : Braid.Generator 3) =
      Two.matrix₂ 1 0 1 1 := rfl
  have upperNegative : Generators.generatorMatrix (⟨1, .negative⟩ : Braid.Generator 3) =
      Two.matrix₂ 1 0 (-1) 1 := rfl
  cases letter with
  | mk index sign =>
    rcases Data.Fin.Two.finTwo_cases index with lower | upper <;> subst index <;> cases sign
    all_goals
      simp only [lowerPositive, lowerNegative, upperPositive, upperNegative, -eq_self, -iff_self]
      rewrite [Two.mul_matrix₂, Two.mul_matrix₂]
      apply (congruence_entries _ _ _ _).mpr
      constructor
      · exact (show _ = a * d - b * c by ring1).trans original.1
      · rcases original with ⟨determinant, topLeft, topRight, bottomLeft, bottomRight⟩
        clear determinant
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega0

/-- One original squared block preserves the necessary integral lift conditions on the same matrix. -/
theorem congruence_block (value : IntegralMatrix) (valid : SignedCongruence value)
    (letter : Braid.Generator 3) :
    SignedCongruence (Multiplication.mul value
      (Multiplication.mul (Generators.generatorMatrix letter) (Generators.generatorMatrix letter))) := by
  rewrite [← Two.matrix₂_entries value]
  exact congruence_block_entries _ _ _ _
    (Eq.mpr (congrArg SignedCongruence (Two.matrix₂_entries value)) valid) letter

/-- Every finite word in the two signed labelled standard loops satisfies the determinant and lift congruences. -/
theorem signedCongruence (word : Braid.Word 3) : SignedCongruence (matrix word) := by
  induction word with
  | nil => decide +kernel
  | cons letter remaining prior =>
    exact Eq.mpr (congrArg SignedCongruence (matrix_cons letter remaining))
      (congruence_block (matrix remaining) prior letter)

/-- Negative identity violates the diagonal condition of the signed integral standard-loop lift. -/
theorem not_negative_identity : ¬SignedCongruence (Two.matrix₂ (-1) 0 0 (-1)) := by
  intro valid
  have diagonal := ((congruence_entries _ _ _ _).mp valid).2.1
  exact (show ¬((-1 : Int) % 4 = 1) by decide +kernel) diagonal

/-- No finite word in these squared standard blocks acts by negative identity on integral homology. -/
theorem matrix_ne_negative_identity (word : Braid.Word 3) : matrix word ≠ Two.matrix₂ (-1) 0 0 (-1) := by
  intro equal
  exact not_negative_identity (Eq.mp (congrArg SignedCongruence equal) (signedCongruence word))

end Purelib.Curves.Legendre.Monodromy.StandardWords

end
