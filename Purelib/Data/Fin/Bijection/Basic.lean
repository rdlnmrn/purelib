module

import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Finite multivalued relations with persistent ownership

The fibre displayed here is finite and local.  Refinement maps one old label
to a finite family of new labels, so clusters may split or merge without being
misrepresented as permutations.  A permutation is recovered only from an
explicit collision-free loop certificate.

No declaration claims that a displayed fibre enumerates an unbounded or
completed mathematical fibre.
-/

public section

namespace Purelib.Data.Fin.Bijection.Basic

universe u v w x y

set_option genInjectivity false in
/-- Retain two inverse maps on one displayed finite index type.

The forward and backward maps are executable functions on Fin count. Their two
retained pointwise inverse laws certify a permutation without quotienting functions
or selecting an inverse. -/
structure Permutation (count : Nat) where
  /-- The retained forward permutation map. -/ forward : Fin count → Fin count
  /-- The retained inverse permutation map. -/ backward : Fin count → Fin count
  /-- Applying backward after forward recovers every original index. -/ leftInverse : ∀ label, backward (forward label)
    = label
  /-- Applying forward after backward recovers every original index. -/ rightInverse : ∀ label, forward (backward label)
    = label

constructive_injectivity Permutation

namespace Permutation

end Permutation
end Purelib.Data.Fin.Bijection.Basic

end

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.Data.Fin

/-! ## Finite bijections without a global choice principle -/

set_option genInjectivity false in
/-- Retain an executable bijection between two displayed finite index types.

Both directions and both pointwise inverse laws are explicit data. The source and
target counts remain the original natural indices of the maps. -/
structure Bijection (sourceCount targetCount : Nat) where
  /-- The retained map from source indices to target indices. -/ forward : Fin sourceCount → Fin targetCount
  /-- The retained map from target indices to source indices. -/ backward : Fin targetCount → Fin sourceCount
  /-- The backward map undoes the forward map at every source index. -/ backward_forward : ∀ source, backward (forward
    source) = source
  /-- The forward map undoes the backward map at every target index. -/ forward_backward : ∀ target, forward (backward
    target) = target

constructive_injectivity Bijection

namespace Bijection

end Bijection
namespace Bijection

section
open Purelib.Data.Fin.Bijection.Basic
/-- The identity bijection on a displayed finite index type. -/
def identity (count : Nat) : Bijection count count where
  forward := fun index => index
  backward := fun index => index
  backward_forward := fun _ => rfl
  forward_backward := fun _ => rfl

/-- Transport finite indices across an explicit equality of their bounds.

The supplied equality identifies the source and target counts; both maps reduce to
identity after that equality is eliminated. -/
def cast {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) :
    Bijection sourceCount targetCount := by
  subst targetCount
  exact Bijection.identity sourceCount

/-- The forward map of an equality-transport bijection is Fin.cast. -/
@[simp] theorem cast_forward {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) (index : Fin sourceCount) :
    (Bijection.cast equal).forward index = Fin.cast equal index := by
  subst targetCount
  rfl

/-- The backward map of an equality-transport bijection casts along the reversed
equality. -/
@[simp] theorem cast_backward {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) (index : Fin targetCount) :
    (Bijection.cast equal).backward index = Fin.cast equal.symm index := by
  subst targetCount
  rfl

/-- Compose two retained finite bijections through their common middle count.

The forward map applies left and then right; the backward map applies the inverse
maps in reverse order. The two retained inverse laws compose pointwise. -/
def comp {firstCount middleCount lastCount : Nat}
    (right : Bijection middleCount lastCount)
    (left : Bijection firstCount middleCount) :
    Bijection firstCount lastCount where
  forward := fun index => right.forward (left.forward index)
  backward := fun index => left.backward (right.backward index)
  backward_forward := by
    intro index
    rw [right.backward_forward, left.backward_forward]
  forward_backward := by
    intro index
    rw [left.forward_backward, right.forward_backward]

/-- Reverse a finite bijection by exchanging its two retained maps and inverse laws. -/
def reverse {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Bijection targetCount sourceCount where
  forward := bijection.backward
  backward := bijection.forward
  backward_forward := bijection.forward_backward
  forward_backward := bijection.backward_forward

/-- Pointwise equality of the forward maps of two finite bijections.

Both bijections have the same source and target counts. Equality is asserted
separately at every retained source index, without equating the map functions. -/
def Same {sourceCount targetCount : Nat}
    (left right : Bijection sourceCount targetCount) : Prop :=
  ∀ index, left.forward index = right.forward index

/-- Pointwise agreement of finite bijections is reflexive. -/
theorem same_refl {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Bijection.Same bijection bijection := fun _ => rfl

/-- Pointwise agreement of finite bijections is symmetric. -/
theorem same_symm {sourceCount targetCount : Nat}
    {left right : Bijection sourceCount targetCount}
    (same : Bijection.Same left right) : Bijection.Same right left := by
  intro index
  exact (same index).symm

/-- Pointwise agreement of finite bijections is transitive. -/
theorem same_trans {sourceCount targetCount : Nat}
    {first second third : Bijection sourceCount targetCount}
    (firstSecond : Bijection.Same first second) (secondThird : Bijection.Same second third) :
    Bijection.Same first third := by
  intro index
  exact (firstSecond index).trans (secondThird index)

/-- Composing a finite bijection with target identity preserves its forward map
pointwise. -/
theorem comp_identity_left {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Bijection.Same (Bijection.comp (Bijection.identity targetCount) bijection) bijection :=
  fun _ => rfl

/-- Composing source identity with a finite bijection preserves its forward map
pointwise. -/
theorem comp_identity_right {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Bijection.Same (Bijection.comp bijection (Bijection.identity sourceCount)) bijection :=
  fun _ => rfl

/-- Composition of three finite bijections is associative in pointwise forward-map
agreement. -/
theorem comp_assoc
    {firstCount secondCount thirdCount fourthCount : Nat}
    (third : Bijection thirdCount fourthCount)
    (second : Bijection secondCount thirdCount)
    (first : Bijection firstCount secondCount) :
    Bijection.Same (Bijection.comp third (Bijection.comp second first))
      (Bijection.comp (Bijection.comp third second) first) :=
  fun _ => rfl

/-- Reversing a composite bijection agrees pointwise with composing the reversed maps in
reverse order. -/
theorem reverse_comp
    {firstCount secondCount thirdCount : Nat}
    (right : Bijection secondCount thirdCount)
    (left : Bijection firstCount secondCount) :
    Bijection.Same (Bijection.reverse (Bijection.comp right left))
      (Bijection.comp (Bijection.reverse left) (Bijection.reverse right)) :=
  fun _ => rfl

/-- The forward map of a reversed bijection is its original backward map. -/
theorem reverse_forward {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount)
    (index : Fin targetCount) :
    (Bijection.reverse bijection).forward index = bijection.backward index := rfl

/-- Reversing a finite bijection twice preserves its forward map pointwise. -/
theorem reverse_reverse {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Bijection.Same (Bijection.reverse (Bijection.reverse bijection)) bijection :=
  fun _ => rfl

/-- The forward map of a retained finite bijection is injective.

Apply its stored backward map to an equality of outputs and use the retained
backward-forward inverse law on the two inputs. -/
theorem forward_injective {sourceCount targetCount : Nat}
    (bijection : Bijection sourceCount targetCount) :
    Function.Injective bijection.forward := by
  intro left right equal
  have inverseEqual := congrArg bijection.backward equal
  simpa only [bijection.backward_forward] using inverseEqual
end

end Bijection

end Purelib.Data.Fin

end

section
@[expose] public section

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

namespace Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin.Bijection.Basic in
/-- Pointwise agreement of finite bijections also gives pointwise agreement of their
inverses.

Apply the original agreement at a retained preimage and transport the resulting
equality through the other backward map. -/
theorem reverse_same {count : Nat}
    {left right : Bijection count count}
    (same : Bijection.Same left right) :
    Bijection.Same left.reverse right.reverse := by
  intro target
  change left.backward target = right.backward target
  have forwardEqual := same (left.backward target)
  rw [left.forward_backward] at forwardEqual
  have pulledBack := congrArg right.backward forwardEqual
  rw [right.backward_forward] at pulledBack
  exact pulledBack.symm

end Purelib.Data.Fin.Bijection.Basic

end
