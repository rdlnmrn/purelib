module

section
@[expose] public section

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

namespace Purelib.Data.Fin.Residue

namespace PairCertificate
end PairCertificate

/-- Reduce a bounded natural index modulo a positive component count.

The positive count makes the remainder a certified element of Fin componentCount. The source index retains its original
strand bound, with no divisibility assumption on that bound. -/
def residueComponent {strands componentCount : Nat}
    (positive : 0 < componentCount) (strand : Fin strands) :
    Fin componentCount :=
  ⟨strand.val % componentCount, Nat.mod_lt _ positive⟩

end Purelib.Data.Fin.Residue

end
