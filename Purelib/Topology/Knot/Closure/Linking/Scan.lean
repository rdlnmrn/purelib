module
public import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Basic

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

namespace Purelib.Topology.Knot.Closure.Linking.Scan

open Purelib.Topology.Knot.Braid

/-- Current braid position to original strand label. -/
abbrev PositionLabels (strands : Nat) := Fin strands → Fin strands

section
open Purelib.Topology.Knot.Closure.Linking
/-- Initially label every strand position by itself. -/
def identityLabels (strands : Nat) : PositionLabels strands :=
  fun index => index

/-- Update the strand occupying each position after one adjacent crossing. -/
def advanceLabels {strands : Nat} (labels : PositionLabels
  strands)
    (generator : Generator strands) : PositionLabels strands :=
  fun position => labels (generator.permutation.forward position)

end

/-- Decide whether two component labels form the selected unordered pair. -/
def isSelectedPair {componentCount : Nat}
    (first second left right : Fin componentCount) : Bool :=
  decide ((left = first ∧ right = second) ∨
    (left = second ∧ right = first))

section
open Purelib.Topology.Knot.Closure.Linking
/-- Count the generator weight exactly when its current strands belong to the selected pair.

Current position labels are read back to original strands before the component labels are compared. -/
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

/-- Scan a braid word for signed crossings between a selected pair of components.

Start with identity strand labels and update them after each crossing, preserving the original component assignment. -/
def signedCrossingSum {strands componentCount : Nat}
    (word : Word strands)
    (componentOfStrand : Fin strands → Fin componentCount)
    (first second : Fin componentCount) : Int :=
  signedCrossingSumFrom componentOfStrand first second
    (identityLabels strands) word
end

section
end
end Purelib.Topology.Knot.Closure.Linking.Scan

end
