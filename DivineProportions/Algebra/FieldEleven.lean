import mathlib.RFAP.ExplicitField
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# An executable eleven-element field

The book repeatedly checks universal-geometry formulas in `F₁₁`.  Importing
Mathlib's general finite-field hierarchy would bring in cardinality and
splitting-field machinery far outside this project's finite proof boundary.
This module instead uses Lean's kernel `Fin 11` commutative ring and supplies
the eleven-entry inverse table directly.  Every field-specific law is checked
by kernel `decide`; there is no `native_decide`, choice, or completed object.
-/

namespace DivineProportions.FieldEleven

/-- The eleven displayed residues with kernel modular arithmetic. -/
abbrev Element := Fin 11

instance instNeZeroEleven : NeZero 11 := ⟨by decide⟩
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- The complete inverse table for the eleven displayed residues. -/
def inverse : Element → Element
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 4
  | 4 => 3
  | 5 => 9
  | 6 => 2
  | 7 => 8
  | 8 => 7
  | 9 => 5
  | 10 => 10

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

/-- The concrete carrier has characteristic eleven. -/
theorem eleven_eq_zero : (11 : Element) = 0 := by decide

/-- A nonzero residue has the inverse displayed by the finite table. -/
theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

end DivineProportions.FieldEleven
