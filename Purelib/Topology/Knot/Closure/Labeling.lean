module

public import Purelib.Topology.Knot.Closure.Basic
import Purelib.Data.Fin.Bijection.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Executable pairwise linking numbers of finite braid closures

The scanner in this file follows the original strand labels through a braid
word.  At each signed adjacent crossing it determines which two closure
components the currently crossing strands belong to.  For a selected pair of
distinct components it adds `+1` or `-1`; all other crossings contribute
zero.  A linking certificate records that the resulting signed crossing sum
is twice the displayed integer linking number.

Everything is a recursion over the finite word and finite index types.  The
component labelling is checked against the closure permutation, so it cannot
split one permutation orbit between different displayed components.
-/

namespace Purelib.Topology.Knot.Closure.Labeling

open Purelib.Topology.Knot.Braid

set_option genInjectivity false in
/-- A displayed component labelling which is constant along every endpoint permutation orbit and represents every
claimed component. -/
structure ComponentLabeling (closure : Closure) (componentCount : Nat)
  where
  /-- Assign each original strand a bounded component label. -/ componentOfStrand : Fin closure.strands → Fin
    componentCount
  /-- The strand permutation preserves each assigned component label. -/ preserved : ∀ strand : Fin closure.strands,
    componentOfStrand (closure.permutation.forward strand) =
      componentOfStrand strand
  /-- Every displayed component label is attained by some strand. -/ represented : ∀ component : Fin componentCount,
    ∃ strand : Fin closure.strands, componentOfStrand strand = component

constructive_injectivity ComponentLabeling

section
end
end Purelib.Topology.Knot.Closure.Labeling

end
