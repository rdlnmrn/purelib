import CCL.Knot.FiniteBraid

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

namespace CCL.Knot.LinkingNumber

open CCL.Knot.FiniteBraid

/-- Current braid position to original strand label. -/
abbrev PositionLabels (strands : Nat) := Fin strands → Fin strands

def identityLabels (strands : Nat) : PositionLabels strands := fun index => index

/-- Update the strand occupying each position after one adjacent crossing. -/
def advanceLabels {strands : Nat} (labels : PositionLabels strands)
    (generator : Generator strands) : PositionLabels strands :=
  fun position => labels (generator.permutation.forward position)

def isSelectedPair {componentCount : Nat}
    (first second left right : Fin componentCount) : Bool :=
  decide ((left = first ∧ right = second) ∨
    (left = second ∧ right = first))

def crossingContribution {strands componentCount : Nat}
    (componentOfStrand : Fin strands → Fin componentCount)
    (first second : Fin componentCount)
    (labels : PositionLabels strands) (generator : Generator strands) : Int :=
  if isSelectedPair first second
      (componentOfStrand (labels generator.left))
      (componentOfStrand (labels generator.right))
    then generator.weight
    else 0

/-- Signed crossing sum for one selected unordered pair of components. -/
def signedCrossingSumFrom {strands componentCount : Nat}
    (componentOfStrand : Fin strands → Fin componentCount)
    (first second : Fin componentCount) :
    PositionLabels strands → Word strands → Int
  | _labels, [] => 0
  | labels, generator :: remaining =>
      crossingContribution componentOfStrand first second labels generator +
        signedCrossingSumFrom componentOfStrand first second
          (advanceLabels labels generator) remaining

def signedCrossingSum {strands componentCount : Nat}
    (word : Word strands)
    (componentOfStrand : Fin strands → Fin componentCount)
    (first second : Fin componentCount) : Int :=
  signedCrossingSumFrom componentOfStrand first second
    (identityLabels strands) word

/-- A displayed component labelling which is constant along every endpoint
permutation orbit and represents every claimed component. -/
structure ComponentLabeling (closure : Closure) (componentCount : Nat) where
  componentOfStrand : Fin closure.strands → Fin componentCount
  preserved : ∀ strand : Fin closure.strands,
    componentOfStrand (closure.permutation.forward strand) =
      componentOfStrand strand
  represented : ∀ component : Fin componentCount,
    ∃ strand : Fin closure.strands, componentOfStrand strand = component

/-- Exact signed-crossing definition of an oriented pairwise linking number.
The factor two is retained explicitly, avoiding integer division. -/
structure PairCertificate {closure : Closure} {componentCount : Nat}
    (components : ComponentLabeling closure componentCount)
    (first second : Fin componentCount) where
  different : first ≠ second
  linking : Int
  twice_linking :
    signedCrossingSum closure.word components.componentOfStrand first second =
      2 * linking

namespace PairCertificate

theorem crossingSum_even {closure : Closure} {componentCount : Nat}
    {components : ComponentLabeling closure componentCount}
    {first second : Fin componentCount}
    (certificate : PairCertificate components first second) :
    ∃ half : Int,
      signedCrossingSum closure.word components.componentOfStrand first second =
        2 * half :=
  ⟨certificate.linking, certificate.twice_linking⟩

end PairCertificate

/-- Residue-class component labels, used by positive torus closures after a
divisor of both exponents has been displayed. -/
def residueComponent {strands componentCount : Nat}
    (positive : 0 < componentCount) (strand : Fin strands) :
    Fin componentCount :=
  ⟨strand.val % componentCount, Nat.mod_lt _ positive⟩

end CCL.Knot.LinkingNumber
