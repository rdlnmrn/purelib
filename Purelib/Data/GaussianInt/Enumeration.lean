module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

public import Purelib.Data.Int.Interval
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Tactic.Ring

public section

open Purelib.Data.List

namespace Purelib.Data.GaussianInt

open Purelib.Data.Int.Interval

/-- Enumerate the finite square of integral coordinate magnitudes at most the supplied
bound.

Take the Cartesian list of signedComponents in both coordinates. The displayed
enumeration may repeat zero, and contains every Gaussian integer within the quadrance
bound. -/
@[expose] def componentSquare (bound : Nat) : List GaussianInt :=
  (signedComponents bound).flatMap fun real =>
    (signedComponents bound).map fun imaginary => ⟨real, imaginary⟩

/-- The retained signed-component square contains exactly four times the square of bound
plus one entries. -/
@[simp] theorem componentSquare_length (bound : Nat) :
    (componentSquare bound).length = 4 * Nat.pow (bound + 1) 2 := by
  rw [componentSquare, Flatten.length_flatMap_map]
  rw [signedComponents_length]
  change _ = 4 * ((1 * (bound + 1)) * (bound + 1))
  rw [Nat.one_mul]
  ring1

/-- Every Gaussian integer within a natural quadrance bound occurs in the corresponding
component-square enumeration. -/
theorem mem_componentSquare_of_normNat_le {z : GaussianInt} {bound : Nat}
    (bounded : normNat z ≤ bound) : z ∈ componentSquare bound := by
  rw [componentSquare]
  apply Flatten.mem_flatMap.mpr
  refine ⟨z.re, mem_signedComponents
    ((realComponent_natAbs_le_normNat z).trans bounded), ?_⟩
  apply Map.mem_map.mpr
  refine ⟨z.im, mem_signedComponents
    ((imaginaryComponent_natAbs_le_normNat z).trans bounded), ?_⟩
  rfl

/-- Every Gaussian integer of quadrance below the next component square occurs in the retained square.

Either component exceeding the supplied magnitude bound would itself
contribute at least that next square. The strict quadrance bound therefore
supplies both original signed-component membership certificates.
-/
theorem mem_componentSquare_of_normNat_lt_square {z : GaussianInt} {bound : Nat}
    (bounded : normNat z < (bound + 1) ^ 2) : z ∈ componentSquare bound := by
  have magnitudeBound : ∀ magnitude : Nat, magnitude ^ 2 < (bound + 1) ^ 2 → magnitude ≤ bound := by
    intro magnitude squareStrict
    by_cases small : magnitude ≤ bound
    · exact small
    · have successorLe : bound + 1 ≤ magnitude := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge small)
      have squareLower : (bound + 1) ^ 2 ≤ magnitude ^ 2 := by
        change (1 * (bound + 1)) * (bound + 1) ≤ (1 * magnitude) * magnitude
        rewrite [Nat.one_mul, Nat.one_mul]
        exact Nat.mul_le_mul successorLe successorLe
      exact (Nat.not_lt_of_ge squareLower squareStrict).elim
  have realBound : z.re.natAbs ≤ bound := magnitudeBound _
    ((Nat.le_add_right _ _).trans_lt ((Norm.Basic.normNat_eq_component_squares z).symm.trans_lt bounded))
  have imaginaryBound : z.im.natAbs ≤ bound := magnitudeBound _
    ((Nat.le_add_left _ _).trans_lt ((Norm.Basic.normNat_eq_component_squares z).symm.trans_lt bounded))
  unfold componentSquare
  apply Flatten.mem_flatMap.mpr
  refine ⟨z.re, mem_signedComponents realBound, ?_⟩
  apply Map.mem_map.mpr
  exact ⟨z.im, mem_signedComponents imaginaryBound, rfl⟩

/-- Enumerate the Cartesian square of one retained signed-component square.

The component square is computed once and the same list supplies both
coordinates of each Gaussian-integer pair.
-/
@[expose] def componentSquarePairs (bound : Nat) : List (GaussianInt × GaussianInt) :=
  let values := componentSquare bound
  values.flatMap fun left => values.map fun right => (left, right)

/-- The paired component square has the square of its original list length. -/
theorem componentSquarePairs_length (bound : Nat) :
    (componentSquarePairs bound).length =
      (4 * Nat.pow (bound + 1) 2) * (4 * Nat.pow (bound + 1) 2) := by
  unfold componentSquarePairs
  rewrite [Flatten.length_flatMap_map, componentSquare_length]
  rfl

/-- Two members of the original component square occur together in its Cartesian enumeration. -/
theorem mem_componentSquarePairs {left right : GaussianInt} {bound : Nat}
    (leftMember : left ∈ componentSquare bound) (rightMember : right ∈ componentSquare bound) :
    (left, right) ∈ componentSquarePairs bound := by
  unfold componentSquarePairs
  apply Flatten.mem_flatMap.mpr
  refine ⟨left, leftMember, ?_⟩
  apply Map.mem_map.mpr
  exact ⟨right, rightMember, rfl⟩

/-- Two quadrance bounds below the next component square give membership in the same retained pair enumeration. -/
theorem mem_componentSquarePairs_of_normNat_lt_square {left right : GaussianInt} {bound : Nat}
    (leftBounded : normNat left < (bound + 1) ^ 2) (rightBounded : normNat right < (bound + 1) ^ 2) :
    (left, right) ∈ componentSquarePairs bound :=
  mem_componentSquarePairs (mem_componentSquare_of_normNat_lt_square leftBounded)
    (mem_componentSquare_of_normNat_lt_square rightBounded)

end Purelib.Data.GaussianInt
end
