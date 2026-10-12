module
import Purelib.Data.Int.Arithmetic
public import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Tactic.Ring
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Finite braid words and combinatorial closures

This file supplies the finite combinatorial target for certified polynomial
root motion.  A braid word is a displayed list of signed adjacent
transpositions.  Its strand action is evaluated into the explicit finite
bijections used by `Purelib.CCL.Progressive.Monodromy`; no quotient group, infinite
configuration space, or choice of representatives is introduced.

The closure predicate deliberately records the exact finite condition needed
to distinguish a knot from a multi-component link: the evaluated strand
permutation is one cycle.  A `CertifiedLoopBraid` then joins a word to the
monodromy of one finite chamber loop by pointwise equality of their displayed
permutations.
-/

namespace Purelib.Topology.Knot.Braid
namespace Word

/-- Finite algebraic crossing count. -/
@[expose] def writhe {strands : Nat} (word : Word strands) : Int :=
  word.foldr (fun generator total => generator.weight + total) 0

/-- The empty braid word has zero writhe. -/
@[simp] theorem writhe_nil (strands : Nat) :
    writhe ([] : Word strands) = 0 := rfl

/-- A word writhe is the head crossing weight plus the writhe of its tail. -/
@[simp] theorem writhe_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    writhe (generator :: remaining) = generator.weight + remaining.writhe :=
  rfl

open Purelib.Data.Int in
/-- Writhe is additive under concatenation of finite braid words.

Both words have the same strand count. Their integer crossing weights are
summed in the displayed word order. -/
theorem writhe_append {strands : Nat} (first second : Word strands) :
    writhe (first ++ second) = writhe first + writhe second := by
  induction first with
  | nil => exact (Arithmetic.zero_add second.writhe).symm
  | cons generator remaining inductionHypothesis =>
      simp only [List.cons_append, writhe_cons, inductionHypothesis]
      omega

/-- Inverting a braid word negates its writhe. -/
theorem writhe_inverse {strands : Nat} (word : Word strands) :
    writhe (inverse word) = -writhe word := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [inverse_cons, writhe_append, inductionHypothesis]
      simp only [writhe_cons, writhe_nil, add_zero, Generator.weight_reverse]
      omega

end Word

end Purelib.Topology.Knot.Braid

end

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

/-- A word containing only positive crossings has writhe equal to its length.

The positivity hypothesis applies to every generator occurrence in the finite word. -/
theorem writhe_eq_length_of_positive {strands : Nat} :
    ∀ word : Word strands,
      (∀ generator ∈ word, generator.sign = .positive) →
      word.writhe = (word.length : Int)
  | [], _ => rfl
  | generator :: remaining, positive => by
      have headPositive : generator.sign = .positive :=
        positive generator List.mem_cons_self
      have tailPositive : ∀ entry ∈ remaining, entry.sign = .positive := by
        intro entry member
        exact positive entry (List.mem_cons_of_mem generator member)
      rw [Word.writhe_cons,
        Purelib.Topology.Knot.Braid.Word.writhe_eq_length_of_positive remaining tailPositive]
      change generator.sign.weight + (remaining.length : Int) =
        ((remaining.length + 1 : Nat) : Int)
      rewrite [headPositive, Int.natCast_add, Int.natCast_one]
      exact Purelib.Data.Int.Arithmetic.add_comm 1 _
end Purelib.Topology.Knot.Braid.Word

end
