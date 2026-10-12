module

public import Purelib.Approximation.Relation.Fibre
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Relation

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

namespace Purelib.Approximation.Relation.Selection

universe u v w x y

set_option genInjectivity false in
/-- Selection by a persistent label is allowed only when that candidate is separated from every other displayed
candidate. -/
structure Isolation
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (fibre : Fibre Output Separated Witness)
    (label : Fin fibre.count) : Type (max u v w) where
  /-- The selected candidate is separated from every other displayed label. -/ separated : ∀ other, other ≠ label →
    Separated (fibre.candidate label) (fibre.candidate other)

constructive_injectivity Isolation

set_option genInjectivity false in
/-- A displayed fibre label isolated from every other candidate.

The selected output and its witness are read from the original fibre, preserving its finite label identity. -/
structure Selected
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (fibre : Fibre Output Separated Witness) : Type (max u v w) where
  /-- The retained label of the selected candidate. -/ label : Fin fibre.count
  /-- The certificate separating this label from every other candidate. -/ isolation :
    Isolation fibre label

constructive_injectivity Selected

namespace Selected

/-- Read the selected candidate from its original fibre. -/
@[expose] def output
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {fibre : Fibre Output Separated Witness}
    (selected : Approximation.Relation.Selection.Selected fibre) : Output :=
  fibre.candidate selected.label

/-- Read the selected candidate's original certification witness. -/
@[expose] def witness
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {fibre : Fibre Output Separated Witness}
    (selected : Approximation.Relation.Selection.Selected fibre) : Witness selected.output :=
  fibre.certified selected.label

end Selected

set_option genInjectivity false in
/-- Local branch selection may instead be justified by explicit alignment to one already owned reference. -/
structure AlignedSelection
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {Reference : Type x}
    (Aligned : Output → Reference → Type y)
    (fibre : Fibre Output Separated Witness) : Type (max u v w x y) where
  /-- The retained label of the selected candidate. -/ label : Fin fibre.count
  /-- The retained reference used to align the selected candidate. -/ reference : Reference
  /-- The specified relation aligns this exact candidate with the retained reference. -/ aligned : Aligned
    (fibre.candidate label) reference

constructive_injectivity AlignedSelection

end Purelib.Approximation.Relation.Selection

end
