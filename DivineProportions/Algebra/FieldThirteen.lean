import mathlib.RFAP.ExplicitField
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# An executable thirteen-element field

This is the finite kernel model used by Chapter 8's order-twelve spread
sequence.  Its inverse table is explicit and every field law is checked by
kernel `decide`.
-/

namespace DivineProportions.FieldThirteen

abbrev Element := Fin 13

instance instNeZeroThirteen : NeZero 13 := ⟨by decide⟩
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

def inverse : Element → Element
  | 0 => 0
  | 1 => 1
  | 2 => 7
  | 3 => 9
  | 4 => 10
  | 5 => 8
  | 6 => 11
  | 7 => 2
  | 8 => 5
  | 9 => 3
  | 10 => 4
  | 11 => 6
  | 12 => 12

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

theorem thirteen_eq_zero : (13 : Element) = 0 := by decide

theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

end DivineProportions.FieldThirteen
