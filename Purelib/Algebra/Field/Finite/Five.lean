module
public import Purelib.Algebra.Field.ExplicitField
-- The exposed ring record retains this constructor and its original defaults.
public import Purelib.Algebra.Ring.Basic
-- The exposed modulus certificate retains zero from this natural parent.
public import Purelib.Algebra.Semiring.Nat
public import Mathlib.Algebra.GroupWithZero.Nat

open Purelib.Algebra.Field

@[expose] public section

/-!
# An executable five-element field

This small concrete model complements `FieldEleven`.  In `F₅`, the element
`2` squares to `-1`, so it exhibits the null directions used in Chapter 5.
The field operations and inverse table are finite data, and all laws are
checked by kernel `decide`.
-/

namespace Purelib.Algebra.Field.Finite.Five

/-- The executable residue carrier with 5 elements.

The abbreviation retains the core finite type Fin 5 and its bounded natural representatives. -/
abbrev Element := Fin 5

/-- The modulus 5 is nonzero.

The displayed successor cannot equal the natural zero constructor, so direct
constructor disjointness supplies the original modulus proposition. -/
instance instNeZeroFive : NeZero 5 := ⟨fun equal => Nat.noConfusion equal⟩
/-- The zero residue in the 5-element carrier. -/
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
/-- The unit residue in the 5-element carrier. -/
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- Compute the total reciprocal by exchanging residues two and three.

The two natural representative comparisons implement the finite reciprocal
table. Zero, one and four retain their input residue; two and three exchange
places, so every nonzero residue maps to its multiplicative inverse. -/
def inverse (value : Element) : Element :=
  if value.val == 2 then 3 else if value.val == 3 then 2 else value

/-- Use the displayed finite reciprocal table as total inversion. -/
instance instInv : Inv Element := ⟨inverse⟩
/-- Divide residues by multiplying by the displayed total reciprocal. -/
instance instDiv : Div Element := ⟨fun left right => left * right⁻¹⟩

/-- Addition of residues modulo 5 is associative. -/
private theorem add_assoc (a b c : Element) : a + b + c = a + (b + c) := by
  decide +revert

/-- Zero is a left additive identity modulo 5. -/
private theorem zero_add (a : Element) : 0 + a = a := by
  decide +revert

/-- A residue and its additive inverse sum to zero modulo 5. -/
private theorem neg_add_cancel (a : Element) : -a + a = 0 := by
  decide +revert

/-- Multiplication of residues modulo 5 is associative. -/
private theorem mul_assoc (a b c : Element) : a * b * c = a * (b * c) := by
  decide +revert

/-- Multiplication of residues modulo 5 is commutative. -/
private theorem mul_comm (a b : Element) : a * b = b * a := by
  decide +revert

/-- One is a left multiplicative identity modulo 5. -/
private theorem one_mul (a : Element) : 1 * a = a := by
  decide +revert

/-- Multiplication distributes over a sum on its right modulo 5. -/
private theorem left_distrib (a b c : Element) : a * (b + c) = a * b + a * c := by
  decide +revert

open Purelib.Algebra in
/-- Equip the 5-element carrier with its checked commutative-ring laws.

The existing modular operations and finite scalar laws are retained. Scalar
multiplication, powers, casts and addition followed by negation for subtraction
keep the original minimal construction's executable defaults. -/
instance instCommRing : CommRing Element :=
  Ring.commRingOfAxioms (by exact add_assoc) (by exact zero_add)
    (by exact neg_add_cancel) (by exact mul_assoc) (by exact mul_comm)
    (by exact one_mul) (by exact left_distrib)
    (fun left right => left + -right) (fun _ _ => rfl)

/-- Equip the 5-element carrier with its executable explicit-field structure.

The retained reciprocal table and division operation satisfy the required cancellation identities by finite checking. -/
instance instExplicitField : ExplicitField Element where
  toCommRing := instCommRing
  toInv := instInv
  toDiv := instDiv
  div_eq_mul_inv := by decide
  mul_inv_cancel := by decide
  mul_ne_zero := by decide
  inv_ne_zero := by decide
  inv_neg := by decide

/-- The zero and unit residues are distinct modulo 5. -/
instance instNontrivial : Nontrivial Element where
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- The natural cast of 5 vanishes in the 5-element field. -/
theorem five_eq_zero : (5 : Element) = 0 := by decide

/-- Every nonzero residue modulo 5 multiplied by its displayed inverse gives one. -/
theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

/-- Every nonzero residue in the five-element field has square one or four. -/
theorem square_eq_one_or_four_of_nonzero
    (value : Element) (nonzero : value ≠ 0) :
    value ^ 2 = 1 ∨ value ^ 2 = 4 := by
  decide +revert

end Purelib.Algebra.Field.Finite.Five

end
