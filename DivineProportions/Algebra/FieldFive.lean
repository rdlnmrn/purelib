import mathlib.RFAP.ExplicitField
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# An executable five-element field

This small concrete model complements `FieldEleven`.  In `F₅`, the element
`2` squares to `-1`, so it exhibits the null directions used in Chapter 5.
The field operations and inverse table are finite data, and all laws are
checked by kernel `decide`.
-/

namespace DivineProportions.FieldFive

/-- The five displayed residues with kernel modular arithmetic. -/
abbrev Element := Fin 5

instance instNeZeroFive : NeZero 5 := ⟨by decide⟩
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- The complete inverse table for the five displayed residues. -/
def inverse : Element → Element
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4

instance instInv : Inv Element := ⟨inverse⟩
instance instDiv : Div Element := ⟨fun left right => left * right⁻¹⟩

private theorem add_assoc (a b c : Element) : a + b + c = a + (b + c) := by
  decide +revert

private theorem zero_add (a : Element) : 0 + a = a := by
  decide +revert

private theorem neg_add_cancel (a : Element) : -a + a = 0 := by
  decide +revert

private theorem mul_assoc (a b c : Element) : a * b * c = a * (b * c) := by
  decide +revert

private theorem mul_comm (a b : Element) : a * b = b * a := by
  decide +revert

private theorem one_mul (a : Element) : 1 * a = a := by
  decide +revert

private theorem left_distrib (a b c : Element) : a * (b + c) = a * b + a * c := by
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

/-- The concrete carrier has characteristic five. -/
theorem five_eq_zero : (5 : Element) = 0 := by decide

/-- A nonzero residue has the inverse displayed by the finite table. -/
theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

/-- The square of a nonzero residue is one of the two nonzero squares. -/
theorem square_eq_one_or_four_of_nonzero
    (value : Element) (nonzero : value ≠ 0) :
    value ^ 2 = 1 ∨ value ^ 2 = 4 := by
  decide +revert

end DivineProportions.FieldFive
