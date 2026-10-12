module
import Purelib.Approximation.Relation.Fibre
public import Purelib.Approximation.Relation.Refinement
public import Purelib.Data.Fin.Bijection.Basic
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Relation

open Purelib.Data.Fin

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

namespace Purelib.Approximation.Relation.Loop

universe u v w x y

set_option genInjectivity false in
/-- A loop refinement that permutes the original finite labels.

Explicit inverse maps certify the permutation, and each continuation family must be exactly the singleton forward image.
-/
structure CollisionFreeLoop
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement fibre fibre Continues) : Type (max u v w) where
  /-- The forward transport of the original fibre labels. -/ forward : Fin fibre.count → Fin fibre.count
  /-- The inverse transport of the original fibre labels. -/ backward : Fin fibre.count → Fin fibre.count
  /-- Backward transport undoes forward transport. -/ leftInverse : ∀ label, backward (forward label) = label
  /-- Forward transport undoes backward transport. -/ rightInverse : ∀ label, forward (backward label) = label
  /-- Each original label continues to exactly its forward image. -/ continues_eq : ∀ label, refinement.continues label
    = [forward label]

constructive_injectivity CollisionFreeLoop

namespace CollisionFreeLoop

/-- The transported label belongs to the original label's continuation family. -/
theorem forward_mem
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    {refinement : Refinement fibre fibre Continues}
    (loop : Approximation.Relation.Loop.CollisionFreeLoop refinement) (label : Fin fibre.count) :
    loop.forward label ∈ refinement.continues label := by
  rw [loop.continues_eq]
  exact List.Mem.head []

/-- Endpoint owner transport of a certified loop is a genuine finite permutation, represented constructively by its two
inverse maps. -/
@[expose] def permutation
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    {refinement : Refinement fibre fibre Continues}
    (loop : Approximation.Relation.Loop.CollisionFreeLoop refinement) :
    Bijection.Basic.Permutation fibre.count where
  forward := loop.forward
  backward := loop.backward
  leftInverse := loop.leftInverse
  rightInverse := loop.rightInverse

end CollisionFreeLoop

end Purelib.Approximation.Relation.Loop

end

public section
namespace Purelib.Approximation.Relation.Loop

end Purelib.Approximation.Relation.Loop
end
