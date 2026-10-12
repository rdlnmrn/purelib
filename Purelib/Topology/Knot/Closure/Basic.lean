module
public import Purelib.Topology.Knot.Braid.Word.Basic
meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Topology.Knot.Braid.Basic

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection.Basic

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

namespace Purelib.Topology.Knot.Braid

/-! ## Finite closures and certified root braids -/

set_option genInjectivity false in
/-- A finite combinatorial braid closure with its strand count and word.

The word retains the same dimension as the strand set, and its explicit permutation determines the finite component
data. -/
structure Closure where
  /-- The number of displayed strands. -/ strands : Nat
  /-- The retained braid word on exactly these strands. -/ word : Word strands
constructive_injectivity Closure
derive_exposed_repr Closure

namespace Closure

/-- The endpoint permutation obtained by evaluating the retained closure word. -/
def permutation (closure : Closure) :
    Data.Fin.Bijection closure.strands closure.strands :=
  closure.word.permutation

/-- The finite closure permutation is a single cycle.

This predicate uses the explicit bounded strand action and its finite cycle certificate. -/
def IsKnot (closure : Closure) : Prop :=
  Data.Fin.Bijection.IsSingleCycle closure.permutation

end Closure

end Purelib.Topology.Knot.Braid

end
