module

meta import Mathlib.Tactic.Linter.Lint
import Init.Core
public import Init.Data.Fin.Basic
import Init.Prelude
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

namespace Purelib.Approximation.Relation

universe u v w x y

set_option genInjectivity false in
/-- A finite displayed relation fibre. `Witness` certifies each local candidate. Every distinct pair is either visibly
separated or belongs to one explicit unresolved cluster. -/
structure Fibre
    (Output : Type u)
    (Separated : Output → Output → Type v)
    (Witness : Output → Type w) : Type (max u v w) where
  /-- The retained finite number of candidate labels. -/ count : Nat
  /-- The output attached to each retained label. -/ candidate : Fin count → Output
  /-- The witness certifying each displayed candidate. -/ certified : ∀ label, Witness (candidate label)
  /-- The retained finite number of unresolved clusters. -/ clusterCount : Nat
  /-- The original candidate labels belonging to each unresolved cluster. -/ cluster : Fin clusterCount → List (Fin
    count)
  /-- Each distinct label pair is explicitly separated or belongs to one retained unresolved cluster. -/ pairResolution
    : ∀ left right, left ≠ right →
    Sum (Separated (candidate left) (candidate right))
      { clusterIndex : Fin clusterCount //
          left ∈ cluster clusterIndex ∧ right ∈ cluster clusterIndex }

constructive_injectivity Fibre

namespace Fibre.mk

end Fibre.mk

namespace Fibre

open Purelib in
/-- A completely separated fibre has no unresolved clusters. -/
@[expose] def ofPairwiseSeparated
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (count : Nat) (candidate : Fin count → Output)
    (certified : ∀ label, Witness (candidate label))
    (pairwise : ∀ left right, left ≠ right →
      Separated (candidate left) (candidate right)) :
    Fibre Output Separated Witness where
  count := count
  candidate := candidate
  certified := certified
  clusterCount := 0
  cluster := Fin.elim0
  pairResolution := fun left right different =>
    Sum.inl (pairwise left right different)

end Fibre

end Purelib.Approximation.Relation

end
