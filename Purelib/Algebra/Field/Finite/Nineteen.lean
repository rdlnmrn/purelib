module
public import Purelib.Algebra.Field.ExplicitField
-- The exposed ring retains this constructor and its original defaults.
public import Purelib.Algebra.Ring.Basic
-- The exposed modulus certificate retains this natural zero parent.
public import Purelib.Algebra.Semiring.Nat
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# An executable nineteen-element field

The Fin 19 carrier retains modular addition, multiplication and
negation. Its explicit total reciprocal table and all field laws are verified
by kernel finite checking over the bounded natural representatives.
-/

namespace Purelib.Algebra.Field.Finite.Nineteen

open Purelib.Algebra
open Purelib.Algebra.Field

public section

/-- The executable residue carrier with 19 elements.

The abbreviation retains the core finite type Fin 19 and its bounded natural representatives. -/
abbrev Element := Fin 19

/-- The modulus nineteen is nonzero.

Its successor constructor cannot equal the natural zero constructor, so
constructor disjointness supplies the retained modulus proposition. -/
instance instNeZeroNineteen : NeZero 19 := ⟨fun equal => Nat.noConfusion equal⟩
/-- The zero residue in the 19-element carrier. -/
instance instZero : Zero Element := ⟨⟨0, by decide⟩⟩
/-- The unit residue in the 19-element carrier. -/
instance instOne : One Element := ⟨⟨1, by decide⟩⟩

/-- Compute the total reciprocal from the displayed explicit residue table.

Natural representative comparisons retain all nineteen selected table
values and the displayed zero fallback. The carrier bound covers every
reachable residue, including zero and both self-inverse nonzero entries. -/
@[expose] def inverse (value : Element) : Element :=
  if value.val == 0 then 0 else
  if value.val == 1 then 1 else
  if value.val == 2 then 10 else
  if value.val == 3 then 13 else
  if value.val == 4 then 5 else
  if value.val == 5 then 4 else
  if value.val == 6 then 16 else
  if value.val == 7 then 11 else
  if value.val == 8 then 12 else
  if value.val == 9 then 17 else
  if value.val == 10 then 2 else
  if value.val == 11 then 7 else
  if value.val == 12 then 8 else
  if value.val == 13 then 3 else
  if value.val == 14 then 15 else
  if value.val == 15 then 14 else
  if value.val == 16 then 6 else
  if value.val == 17 then 9 else
  if value.val == 18 then 18 else
  0

/-- Use the displayed finite reciprocal table as total inversion. -/
instance instInv : Inv Element := ⟨inverse⟩
/-- Divide residues by multiplying by the displayed total reciprocal. -/
instance instDiv : Div Element := ⟨fun left right => left * right⁻¹⟩

/-- Addition of residues modulo 19 is associative.

Both associations use the retained modular addition on the same three residues. Finite checking covers every bounded
representative. -/
private theorem add_assoc (a b c : Element) : a + b + c = a + (b + c) := by
  decide +revert

/-- Zero is a left additive identity modulo 19.

The retained modular zero and addition act on the same supplied residue. Finite checking verifies every bounded
representative. -/
private theorem zero_add (a : Element) : 0 + a = a := by
  decide +revert

/-- A residue and its additive inverse sum to zero modulo 19.

The retained modular negation and addition act on the same supplied residue. Finite checking verifies cancellation for
every bounded representative. -/
private theorem neg_add_cancel (a : Element) : -a + a = 0 := by
  decide +revert

/-- Multiplication of residues modulo 19 is associative.

Both associations use the retained modular multiplication on the same three residues. Finite checking covers every
bounded representative. -/
private theorem mul_assoc (a b c : Element) : a * b * c = a * (b * c) := by
  decide +revert

/-- Multiplication of residues modulo 19 is commutative.

The two products use the same modular multiplication and retained residue pair. Finite checking verifies commutation for
every bounded representative. -/
private theorem mul_comm (a b : Element) : a * b = b * a := by
  decide +revert

/-- One is a left multiplicative identity modulo 19.

The retained modular unit and multiplication act on the same supplied residue. Finite checking verifies every bounded
representative. -/
private theorem one_mul (a : Element) : 1 * a = a := by
  decide +revert

/-- Multiplication distributes over a sum on its right modulo 19.

The retained modular multiplication and addition use the same three supplied residues. Finite checking identifies both
sides for every bounded representative. -/
private theorem left_distrib (a b c : Element) :
    a * (b + c) = a * b + a * c := by
  decide +revert

/-- Equip the 19-element carrier with its checked commutative-ring laws.

The existing modular operations and finite scalar laws are retained. Scalar
multiplication, powers and casts keep the minimal construction's original
recursive defaults; subtraction is addition followed by negation. -/
instance instCommRing : CommRing Element :=
  Ring.commRingOfAxioms (by exact add_assoc) (by exact zero_add)
    (by exact neg_add_cancel) (by exact mul_assoc) (by exact mul_comm)
    (by exact one_mul) (by exact left_distrib)
    (fun left right => left + -right) (fun _ _ => rfl)

/-- Equip the 19-element carrier with its executable explicit-field structure.

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

/-- The zero and unit residues are distinct modulo 19. -/
instance instNontrivial : Nontrivial Element where
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- The natural cast of 19 vanishes in the 19-element field. -/
theorem nineteen_eq_zero : (19 : Element) = 0 := by decide

/-- Every nonzero residue modulo 19 multiplied by its displayed inverse gives one. -/
theorem mul_inverse (value : Element) (nonzero : value ≠ 0) :
    value * value⁻¹ = 1 := by
  decide +revert

end

end Purelib.Algebra.Field.Finite.Nineteen
