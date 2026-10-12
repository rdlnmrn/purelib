module
meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Transposition

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Bijection.Basic

section
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

/-! ## Signed Artin generators -/

@[expose] public section

/-- The two orientations of a signed adjacent braid crossing. -/
inductive CrossingSign
  /-- A positive crossing, contributing one to the writhe. -/ | positive
  /-- A negative crossing, contributing minus one to the writhe. -/ | negative
deriving DecidableEq
derive_exposed_repr CrossingSign

end

namespace CrossingSign

/-- Exchange positive and negative crossing signs. -/
@[expose] def reverse : CrossingSign → CrossingSign
  | .positive => .negative
  | .negative => .positive

/-- Reversing a crossing sign twice restores the original sign. -/
@[simp] theorem reverse_reverse (sign : CrossingSign) :
    sign.reverse.reverse = sign := by
  cases sign <;> rfl

/-- Read a positive crossing as one and a negative crossing as minus one. -/
@[expose] def weight : CrossingSign → Int
  | .positive => 1
  | .negative => -1

/-- Reversing a crossing sign negates its integer weight. -/
@[simp] theorem weight_reverse (sign : CrossingSign) :
    sign.reverse.weight = -sign.weight := by
  cases sign <;> rfl

end CrossingSign

@[expose] public section

set_option genInjectivity false in
/-- A signed crossing between two adjacent positions in a finite strand set.

The index is bounded by one less than the strand count, so both adjacent positions exist. No generator exists on fewer
than two strands. -/
structure Generator (strands : Nat) where
  /-- The lower position of the adjacent pair, bounded by one less than the strand count. -/ index : Fin (strands - 1)
  /-- The orientation of the crossing. -/ sign : CrossingSign
deriving DecidableEq

constructive_injectivity Generator

derive_exposed_repr Generator

end

namespace Generator

/-- The bounded lower strand position of an adjacent generator. -/
@[expose] def left {strands : Nat} (generator : Generator strands) : Fin strands :=
  ⟨generator.index.val, by omega⟩

/-- The bounded upper strand position of an adjacent generator. -/
@[expose] def right {strands : Nat} (generator : Generator strands) : Fin strands :=
  ⟨generator.index.val + 1, by omega⟩

/-- The adjacent strand positions of a generator are distinct. -/
theorem left_ne_right {strands : Nat} (generator : Generator strands) :
    generator.left ≠ generator.right := by
  intro equal
  have values := congrArg Fin.val equal
  change generator.index.val = generator.index.val + 1 at values
  omega

/-- Exchange the two adjacent strand positions of a generator.

The crossing sign does not alter this finite endpoint permutation. -/
@[expose] def permutation {strands : Nat} (generator : Generator strands) :
    Data.Fin.Bijection strands strands :=
  Transposition.transposition generator.left generator.right

/-- Applying a generator endpoint permutation twice fixes every strand. -/
@[simp] theorem permutation_involutive {strands : Nat}
    (generator : Generator strands) (index : Fin strands) :
    generator.permutation.forward
        (generator.permutation.forward index) = index :=
  Transposition.swapIndices_involutive generator.left generator.right index

/-- Reverse the crossing sign while retaining the adjacent strand index. -/
@[expose] def reverse {strands : Nat} (generator : Generator strands) :
    Generator strands :=
  { index := generator.index
    sign := generator.sign.reverse }

/-- Reversing a generator preserves its adjacent strand index. -/
@[simp] theorem reverse_index {strands : Nat}
    (generator : Generator strands) : generator.reverse.index = generator.index :=
  rfl

/-- The sign of a reversed generator is the reversed original sign. -/
@[simp] theorem reverse_sign {strands : Nat}
    (generator : Generator strands) :
    generator.reverse.sign = generator.sign.reverse := rfl

/-- Reversing a generator twice restores the original generator. -/
@[simp] theorem reverse_reverse {strands : Nat}
    (generator : Generator strands) : generator.reverse.reverse = generator := by
  cases generator with
  | mk index sign =>
      change ({ index := index, sign := sign.reverse.reverse } : Generator strands) =
        { index := index, sign := sign }
      rewrite [CrossingSign.reverse_reverse]
      exact Eq.refl _

/-- The endpoint action of a reversed generator agrees pointwise with the inverse action. -/
theorem permutation_reverse {strands : Nat}
    (generator : Generator strands) :
    Data.Fin.Bijection.Same generator.reverse.permutation
      generator.permutation.reverse :=
  fun _ => rfl

/-- The integer crossing weight of a signed generator. -/
@[expose] def weight {strands : Nat} (generator : Generator strands) : Int :=
  generator.sign.weight

/-- Reversing a generator negates its integer crossing weight. -/
@[simp] theorem weight_reverse {strands : Nat}
    (generator : Generator strands) :
    generator.reverse.weight = -generator.weight :=
  CrossingSign.weight_reverse generator.sign

end Generator

end Purelib.Topology.Knot.Braid

end

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

namespace Purelib.Topology.Knot.Braid.Generator

open Purelib.Topology.Knot.Braid

/-! ## Positive bands -/

/-- Construct the positive generator at a supplied bounded adjacent index. -/
@[expose] def positiveGenerator {strands : Nat} (index : Fin (strands - 1))
  :
    Generator strands :=
  { index := index
    sign := .positive }
section
end

end Purelib.Topology.Knot.Braid.Generator

end

end
