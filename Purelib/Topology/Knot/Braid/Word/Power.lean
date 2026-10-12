module
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.Append
import Purelib.Algebra.NatCast
public import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Topology.Knot.Braid.Word.Basic
public import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data

open Purelib

section
section
public section

/-!
# Finite torus braids

This file constructs the positive braid
`(σ₁ · … · σₚ₋₁)^q` as an executable finite word on `p`
strands.  It is the combinatorial braid predicted for the algebraic
singularity `z^p = w^q`.  The construction exposes exact crossing count,
writhe, and endpoint permutation iteration without invoking a completed
curve or a topological quotient.
-/

namespace Purelib.Topology.Knot.Braid.Word

open Purelib.Topology.Knot.Braid

/-! ## Finite word powers -/

/-- Concatenate `word` with itself exactly `exponent` times. -/
@[expose] def repeatWord {strands : Nat} (word : Word strands) : Nat → Word strands
  | 0 => []
  | exponent + 1 => Purelib.Topology.Knot.Braid.Word.repeatWord word exponent ++ word

/-- Zero repetitions of a braid word form the empty word. -/
@[simp] theorem repeatWord_zero {strands : Nat} (word : Word strands) :
    Word.repeatWord word 0 = [] := rfl

/-- One additional repetition appends the original word to the previous repetitions. -/
@[simp] theorem repeatWord_succ {strands : Nat} (word : Word strands)
    (exponent : Nat) :
    Word.repeatWord word (exponent + 1) = Word.repeatWord word exponent ++ word := rfl

/-- Repetition by a sum of exponents splits into the corresponding two concatenated powers. -/
theorem repeatWord_add {strands : Nat} (word : Word strands)
    (first second : Nat) :
    Word.repeatWord word (first + second) =
      Word.repeatWord word first ++ Word.repeatWord word second := by
  induction second with
  | zero => simp only [-eq_self, -iff_self, Nat.add_zero, Word.repeatWord_zero, List.Append.append_nil]; rfl
  | succ second inductionHypothesis =>
      rw [Nat.add_succ, Word.repeatWord_succ, Word.repeatWord_succ,
        inductionHypothesis, List.Append.append_assoc]

/-- The length of a repeated braid word is the exponent times its original length. -/
@[simp] theorem repeatWord_length {strands : Nat} (word : Word strands) :
  ∀ exponent : Nat,
      (Word.repeatWord word exponent).length = exponent * word.length
  | 0 => by simp only [-eq_self, -iff_self, Word.repeatWord_zero, List.length_nil, zero_mul]; rfl
  | exponent + 1 => by
      rw [Word.repeatWord_succ, List.Append.length_append, Purelib.Topology.Knot.Braid.Word.repeatWord_length]
      simp only [-eq_self, -iff_self, Nat.Multiplication.right_distrib, Nat.one_mul]
      rfl

/-- The writhe of a repeated braid word is the integer exponent times its original writhe. -/
@[simp] theorem repeatWord_writhe {strands : Nat} (word : Word strands) :
    ∀ exponent : Nat,
      (Word.repeatWord word exponent).writhe = (exponent : Int) * word.writhe
  | 0 => by simp only [-eq_self, -iff_self, Word.repeatWord_zero, Purelib.Topology.Knot.Braid.Word.writhe_nil,
      Int.ofNat_zero, zero_mul]; rfl
  | exponent + 1 => by
      rw [Word.repeatWord_succ, Word.writhe_append,
        Purelib.Topology.Knot.Braid.Word.repeatWord_writhe]
      simp only [-eq_self, -iff_self, Algebra.NatCast.add, Int.natCast_one]
      ring1

/-- Repeating a braid word iterates its explicit strand permutation. -/
theorem repeatWord_permutation {strands : Nat} (word : Word strands) :
    ∀ (exponent : Nat) (index : Fin strands),
      (Word.repeatWord word exponent).permutation.forward index =
        Data.Fin.Bijection.iterateForward
          word.permutation exponent index
  | 0, _ => rfl
  | exponent + 1, index => by
      calc
        (Word.repeatWord word (exponent + 1)).permutation.forward index =
            word.permutation.forward
              ((Word.repeatWord word exponent).permutation.forward index) :=
          Word.permutation_append
            (Word.repeatWord word exponent) word index
        _ = word.permutation.forward
            (Data.Fin.Bijection.iterateForward
              word.permutation exponent index) := by
          rw [Purelib.Topology.Knot.Braid.Word.repeatWord_permutation word exponent index]
        _ = Data.Fin.Bijection.iterateForward
            word.permutation (exponent + 1) index := rfl

end Purelib.Topology.Knot.Braid.Word

end

end

section
public section

/-!
# Coprime torus braids close to knots

This file proves the constructive coprime case of the torus-link component
theorem.  Each positive band decreases the finite strand label by one, with a
displayed wrap count.  Telescoping those finite equalities shows that a return
after `k` bands forces the strand count to divide `k`.  A stored Bézout
certificate then cancels the `q` factor for the braid
`(σ₁…σₚ₋₁)^q`, ruling out every early return when `p` and `q` are
coprime.
-/

namespace Purelib.Topology.Knot.Braid.Word

open Purelib.Topology.Knot.Braid

/-! ## Iterating a word power -/

/-- Iterating a word power multiplies the two finite iteration counts.

At each strand index, circuits of an exponent-fold word equal exponent times circuits iterations of the original
permutation. -/
theorem repeatWord_iterate {strands : Nat} (word : Word strands)
    (exponent circuits : Nat) (index : Fin strands) :
    Data.Fin.Bijection.iterateForward
        (Word.repeatWord word exponent).permutation circuits index =
      Data.Fin.Bijection.iterateForward
        word.permutation (exponent * circuits) index := by
  induction circuits with
  | zero => rfl
  | succ circuits inductionHypothesis =>
      rw [Data.Fin.Bijection.iterateForward_succ,
        Word.repeatWord_permutation, inductionHypothesis]
      calc
        Data.Fin.Bijection.iterateForward word.permutation
              exponent
              (Data.Fin.Bijection.iterateForward
                word.permutation (exponent * circuits) index) =
            Data.Fin.Bijection.iterateForward
              word.permutation (exponent * circuits + exponent) index :=
          (Data.Fin.Bijection.iterateForward_add
            word.permutation (exponent * circuits) exponent index).symm
        _ = Data.Fin.Bijection.iterateForward
            word.permutation (exponent * (circuits + 1)) index := by
          congr 2
end Purelib.Topology.Knot.Braid.Word

end
