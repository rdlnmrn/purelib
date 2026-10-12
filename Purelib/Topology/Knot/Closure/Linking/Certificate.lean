module

public import Purelib.Topology.Knot.Closure.Labeling
public import Purelib.Topology.Knot.Closure.Linking.Scan
import Purelib.Topology.Knot.Closure.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Topology.Knot.Closure

open Purelib.Topology.Knot.Closure.Linking

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

namespace Purelib.Topology.Knot.Closure.Linking.Certificate

open Purelib.Topology.Knot.Braid

set_option genInjectivity false in
/-- Exact signed-crossing definition of an oriented pairwise linking number. The factor two is retained explicitly,
avoiding integer division. -/
structure PairCertificate {closure : Closure} {componentCount :
  Nat}
    (components : Labeling.ComponentLabeling closure componentCount)
    (first second : Fin componentCount) where
  /-- The two selected component labels are distinct. -/ different : first ≠ second
  /-- The retained integer linking number of the selected pair. -/ linking : Int
  /-- The signed crossing sum for the selected components equals twice the retained linking number. -/ twice_linking :
    Scan.signedCrossingSum closure.word components.componentOfStrand first second =
      2 * linking

constructive_injectivity PairCertificate

namespace PairCertificate

open Purelib.Topology.Knot.Closure.Linking in
/-- A pairwise linking certificate witnesses that the selected signed crossing sum is even. -/
theorem crossingSum_even {closure : Closure}
  {componentCount : Nat}
    {components : Labeling.ComponentLabeling closure componentCount}
    {first second : Fin componentCount}
    (certificate : PairCertificate components first second) :
    ∃ half : Int,
      Scan.signedCrossingSum closure.word components.componentOfStrand first second =
        2 * half :=
  ⟨certificate.linking, certificate.twice_linking⟩

end PairCertificate
end Purelib.Topology.Knot.Closure.Linking.Certificate

end
