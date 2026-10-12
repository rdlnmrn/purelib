module
public import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Fin.Bijection.Transposition

public import Purelib.Data.Nat.Permutation.Adjacent
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin.Bijection

open Purelib.Data.Nat.Permutation

section
@[expose] public section

/-!
# The finite permutation of a positive torus band

The ascending Artin band moves strand zero to the last position and every
other strand down by one.  This file proves that fact by evaluating each
displayed adjacent transposition.  The auxiliary arithmetic acts only on a
bounded natural prefix and is fully executable.
-/

namespace Purelib.Topology.Knot.Braid.Generator.NaturalAction

open Purelib.Topology.Knot.Braid

/-- Read the finite strand action of a generator as an adjacent natural-number swap.

Taking the value of the bounded output index gives the executable swap at the generator index, for either crossing sign.
-/
theorem generator_permutation_val {strands : Nat}
    (generator : Generator strands) (index : Fin strands) :
    (generator.permutation.forward index).val =
      Adjacent.adjacentNatSwap generator.index.val index.val := by
  change (Transposition.swapIndices generator.left generator.right index).val =
    Adjacent.adjacentNatSwap generator.index.val index.val
  by_cases atLeft : index.val = generator.index.val
  · have equal : index = generator.left := Fin.ext atLeft
    subst index
    rw [Transposition.swapIndices_left]
    change generator.index.val + 1 =
      Adjacent.adjacentNatSwap generator.index.val generator.index.val
    unfold Adjacent.adjacentNatSwap
    rw [if_pos rfl]
  · by_cases atRight : index.val = generator.index.val + 1
    · have equal : index = generator.right := Fin.ext atRight
      subst index
      rw [Transposition.swapIndices_right]
      change generator.index.val =
        Adjacent.adjacentNatSwap generator.index.val (generator.index.val + 1)
      unfold Adjacent.adjacentNatSwap
      rw [if_neg (by omega), if_pos rfl]
    · have notLeft : index ≠ generator.left := by
        intro equal
        exact atLeft (congrArg Fin.val equal)
      have notRight : index ≠ generator.right := by
        intro equal
        exact atRight (congrArg Fin.val equal)
      rw [Transposition.swapIndices_of_ne notLeft notRight]
      change index.val = Adjacent.adjacentNatSwap generator.index.val index.val
      unfold Adjacent.adjacentNatSwap
      rw [if_neg atLeft, if_neg atRight]
end Purelib.Topology.Knot.Braid.Generator.NaturalAction

end
