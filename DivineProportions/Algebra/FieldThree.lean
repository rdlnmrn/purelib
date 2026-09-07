import mathlib.RFAP.ExplicitField
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# An executable three-element field

The prime field used in Exercise 10.10 is represented by the three literal
residues.  Its inverse table and field laws are finite kernel computations.
-/

namespace DivineProportions.FieldThree

/-- The three displayed residues with kernel modular arithmetic. -/
abbrev Element := Fin 3

instance instNeZeroThree : NeZero 3 := ⟨by decide⟩
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- The complete inverse table for the three displayed residues. -/
def inverse : Element → Element
  | 0 => 0
  | 1 => 1
  | 2 => 2

instance instInv : Inv Element := ⟨inverse⟩
instance instDiv : Div Element := ⟨fun left right => left * right⁻¹⟩

private theorem add_assoc (a b c : Element) :
    a + b + c = a + (b + c) := by
  decide +revert

private theorem zero_add (a : Element) : 0 + a = a := by
  decide +revert

private theorem neg_add_cancel (a : Element) : -a + a = 0 := by
  decide +revert

private theorem mul_assoc (a b c : Element) :
    a * b * c = a * (b * c) := by
  decide +revert

private theorem mul_comm (a b : Element) : a * b = b * a := by
  decide +revert

private theorem one_mul (a : Element) : 1 * a = a := by
  decide +revert

private theorem left_distrib (a b c : Element) :
    a * (b + c) = a * b + a * c := by
  decide +revert

instance instCommRing : CommRing Element :=
  CommRing.ofMinimalAxioms add_assoc zero_add neg_add_cancel mul_assoc mul_comm
    one_mul left_distrib

instance instExplicitField : RFAP.ExplicitField Element where
  toCommRing := instCommRing
  toInv := instInv
  toDiv := instDiv
  div_eq_mul_inv := by decide
  mul_inv_cancel := by decide
  mul_ne_zero := by decide
  inv_ne_zero := by decide
  inv_neg := by decide

instance instNontrivial : Nontrivial Element where
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- The concrete carrier has characteristic three. -/
theorem three_eq_zero : (3 : Element) = 0 := by decide

/-- A sum of two squares vanishes only when both displayed scalars vanish. -/
theorem sum_squares_eq_zero_iff (first second : Element) :
    first ^ 2 + second ^ 2 = 0 ↔ first = 0 ∧ second = 0 := by
  decide +revert

/-- Every nonzero scalar has square one in the three-element prime field. -/
theorem square_eq_one_of_nonzero (value : Element) (nonzero : value ≠ 0) :
    value ^ 2 = 1 := by
  decide +revert

end DivineProportions.FieldThree
