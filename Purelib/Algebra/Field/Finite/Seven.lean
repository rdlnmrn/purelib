module
public import Purelib.Algebra.Field.ExplicitField
-- The exposed ring retains this constructor and its original defaults.
public import Purelib.Algebra.Ring.Basic
-- The exposed modulus certificate retains this natural zero parent.
public import Purelib.Algebra.Semiring.Nat
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# An executable seven-element field

The carrier, inverse table, and all laws are finite kernel data.  No general
finite-field hierarchy or carrier enumeration theorem is imported.
-/

namespace Purelib.Algebra.Field.Finite.Seven

open Purelib.Algebra
open Purelib.Algebra.Field

public section

/-- The executable residue carrier with 7 elements.

The abbreviation retains the core finite type Fin 7 and its bounded natural representatives. -/
abbrev Element := Fin 7

/-- The modulus seven is nonzero.

Its successor constructor cannot equal the natural zero constructor, so
constructor disjointness supplies the retained modulus proposition. -/
instance instNeZeroSeven : NeZero 7 := ⟨fun equal => Nat.noConfusion equal⟩
/-- The zero residue in the 7-element carrier. -/
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
/-- The unit residue in the 7-element carrier. -/
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- Compute the total reciprocal by exchanging the two nontrivial residue pairs.

Natural representative comparisons implement the original reciprocal table:
two exchanges with four, and three with five. Zero, one and six retain their
input residue, so zero maps to zero and every nonzero residue to its inverse. -/
@[expose] def inverse (value : Element) : Element :=
  if value.val == 2 then 4 else
  if value.val == 3 then 5 else
  if value.val == 4 then 2 else
  if value.val == 5 then 3 else value

/-- Use the displayed finite reciprocal table as total inversion. -/
instance instInv : Inv Element := ⟨inverse⟩
/-- Divide residues by multiplying by the displayed total reciprocal. -/
instance instDiv : Div Element := ⟨fun left right => left * right⁻¹⟩

/-- Addition of residues modulo 7 is associative. -/
private theorem add_assoc (a b c : Element) : a + b + c = a + (b + c) := by
  decide +revert

/-- Zero is a left additive identity modulo 7. -/
private theorem zero_add (a : Element) : 0 + a = a := by
  decide +revert

/-- A residue and its additive inverse sum to zero modulo 7. -/
private theorem neg_add_cancel (a : Element) : -a + a = 0 := by
  decide +revert

/-- Multiplication of residues modulo 7 is associative. -/
private theorem mul_assoc (a b c : Element) : a * b * c = a * (b * c) := by
  decide +revert

/-- Multiplication of residues modulo 7 is commutative. -/
private theorem mul_comm (a b : Element) : a * b = b * a := by
  decide +revert

/-- One is a left multiplicative identity modulo 7. -/
private theorem one_mul (a : Element) : 1 * a = a := by
  decide +revert

/-- Multiplication distributes over a sum on its right modulo 7. -/
private theorem left_distrib (a b c : Element) :
    a * (b + c) = a * b + a * c := by
  decide +revert

/-- Equip the 7-element carrier with its checked commutative-ring laws.

The existing modular operations and finite scalar laws are retained. Scalar
multiplication, powers and casts keep the minimal construction's original
recursive defaults; subtraction is addition followed by negation. -/
instance instCommRing : CommRing Element :=
  Ring.commRingOfAxioms (by exact add_assoc) (by exact zero_add)
    (by exact neg_add_cancel) (by exact mul_assoc) (by exact mul_comm)
    (by exact one_mul) (by exact left_distrib)
    (fun left right => left + -right) (fun _ _ => rfl)

/-- Equip the 7-element carrier with its executable explicit-field structure.

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

/-- The zero and unit residues are distinct modulo 7. -/
instance instNontrivial : Nontrivial Element where
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- The natural cast of 7 vanishes in the 7-element field. -/
theorem seven_eq_zero : (7 : Element) = 0 := by decide

/-- Every nonzero residue modulo 7 multiplied by its displayed inverse gives one. -/
theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

end

end Purelib.Algebra.Field.Finite.Seven
