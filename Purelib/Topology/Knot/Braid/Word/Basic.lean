module
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
public import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection.Basic

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

/-! ## Executable braid words -/

/-- A finite traversal-ordered list of signed adjacent generators on a fixed strand count. -/
abbrev Word (strands : Nat) := List (Generator strands)

namespace Word

/-- Evaluate a word in traversal order: the head crossing acts first. -/
@[expose] def permutation {strands : Nat} : Word strands → Data.Fin.Bijection strands strands
  | [] => Data.Fin.Bijection.identity strands
  | generator :: remaining =>
      Data.Fin.Bijection.comp
        (permutation remaining) generator.permutation

/-- The empty braid word has the identity endpoint permutation. -/
@[simp] theorem permutation_nil (strands : Nat) :
    permutation ([] : Word strands) =
      Data.Fin.Bijection.identity strands := rfl

/-- The head generator acts before the endpoint action of the remaining word. -/
@[simp] theorem permutation_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    permutation (generator :: remaining) =
      Data.Fin.Bijection.comp
        (permutation remaining) generator.permutation := rfl

/-- Concatenating braid words composes their endpoint actions in traversal order.

The statement compares the forward maps pointwise, with the first word acting before the second. -/
theorem permutation_append {strands : Nat} (first second : Word strands) :
    Data.Fin.Bijection.Same
      (permutation (first ++ second))
      (Data.Fin.Bijection.comp
        (permutation second) (permutation first)) := by
  intro index
  induction first generalizing index with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change (permutation (remaining ++ second)).forward
          (generator.permutation.forward index) =
        (permutation second).forward
          ((permutation remaining).forward
            (generator.permutation.forward index))
      exact inductionHypothesis (generator.permutation.forward index)

/-- Reverse traversal and invert every signed crossing. -/
@[expose] def inverse {strands : Nat} (word : Word strands) : Word strands :=
  (List.reverse word).map Generator.reverse

/-- The inverse of the empty braid word is empty. -/
@[simp] theorem inverse_nil (strands : Nat) :
    inverse ([] : Word strands) = [] := rfl

/-- Invert a nonempty word by appending the reversed head to the inverse tail. -/
@[simp] theorem inverse_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    inverse (generator :: remaining) =
      inverse remaining ++ [generator.reverse] := by
  unfold inverse
  rewrite [Purelib.Data.List.Reverse.reverse_cons, Purelib.Data.List.Map.map_append]
  exact Eq.refl _

/-- The inverse of a concatenation is the concatenation of inverses in reverse order. -/
@[simp] theorem inverse_append {strands : Nat}
    (first second : Word strands) :
    inverse (first ++ second) = inverse second ++ inverse first := by
  unfold inverse
  rw [Purelib.Data.List.Reverse.reverse_append, Purelib.Data.List.Map.map_append]

/-- Inverting a finite braid word twice restores the original word. -/
@[simp] theorem inverse_inverse {strands : Nat} (word : Word strands) :
    inverse (inverse word) = word := by
  unfold inverse
  rw [← Purelib.Data.List.Reverse.map_reverse, Purelib.Data.List.Reverse.reverse_reverse, Purelib.Data.List.Map.map_map]
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change generator.reverse.reverse ::
          List.map (Generator.reverse ∘ Generator.reverse) remaining =
        generator :: remaining
      rw [Generator.reverse_reverse, inductionHypothesis]

/-- The endpoint action of an inverse word agrees with the reversed finite bijection. -/
theorem permutation_inverse {strands : Nat} (word : Word strands) :
    Data.Fin.Bijection.Same
      word.inverse.permutation word.permutation.reverse := by
  intro index
  induction word generalizing index with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [inverse_cons, permutation_append]
      change generator.reverse.permutation.forward
          ((permutation (inverse remaining)).forward index) =
        generator.permutation.backward
          ((permutation remaining).backward index)
      rw [inductionHypothesis]
      exact generator.permutation_reverse _
end Word

end Purelib.Topology.Knot.Braid

end
