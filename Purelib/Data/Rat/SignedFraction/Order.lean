module
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Int.Order
import Purelib.Data.Rat.SignedFraction.Basic
public import Purelib.Data.Rat.SignedFraction.Normalization

import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

/-!
# Weak cross-product order on signed fraction displays

The original positive integer denominators define a decidable comparison
of the same integer cross-products. Equivalent displays preserve that order,
which agrees with the retained canonical normalizations.
-/

namespace Purelib.Data.Rat.SignedFraction.Order

/-- Compare signed displays by integer cross-products, using their positive denominators.

The exact two original numerators are multiplied by the opposite positive
denominators. Their weak integer comparison retains both displayed input owners. -/
@[expose] public def LessEqFraction (left right : SignedFraction) : Prop :=
  left.num * right.den ≤ right.num * left.den

/-- Decide weak cross-product comparison by the displayed integer arithmetic. -/
public instance (left right : SignedFraction) : Decidable (LessEqFraction left right) :=
  inferInstanceAs
    (Decidable (left.num * right.den ≤ right.num * left.den))

/-- Transport weak cross-product comparison along equivalence of both signed displays.

The original positive denominator product permits scalar cancellation.
Multiplying the retained comparison and transporting the two displayed
equivalence equations preserves the same weak integer order. -/
private theorem lessEqFraction_imp {left left' right right' : SignedFraction}
    (leftEquivalent : SignedFraction.Basic.Equivalent left left')
    (rightEquivalent : SignedFraction.Basic.Equivalent right right') :
    LessEqFraction left right → LessEqFraction left' right' := by
  intro lessEqual
  have positiveScale : 0 < left.den * right.den :=
    Int.Order.mul_pos left.den_pos right.den_pos
  apply Int.Order.int_le_of_mul_le_mul_right positiveScale
  have replacementScaleNonnegative : 0 ≤ left'.den * right'.den :=
    Int.Order.le_of_lt (Int.Order.mul_pos left'.den_pos right'.den_pos)
  have scaled := Int.Order.mul_le_mul_of_nonneg_right lessEqual
    replacementScaleNonnegative
  dsimp only [LessEqFraction] at lessEqual scaled ⊢
  dsimp only [SignedFraction.Basic.Equivalent] at leftEquivalent rightEquivalent
  calc
    left'.num * right'.den * (left.den * right.den) =
        (left'.num * left.den) * (right'.den * right.den) := by ring1
    _ = (left.num * left'.den) * (right.den * right'.den) := by
      rw [← leftEquivalent]
      ring1
    _ = (left.num * right.den) * (left'.den * right'.den) := by ring1
    _ ≤ (right.num * left.den) * (left'.den * right'.den) := scaled
    _ = (right.num * right'.den) * (left.den * left'.den) := by ring1
    _ = (right'.num * right.den) * (left'.den * left.den) := by
      rw [rightEquivalent]
      ring1
    _ = right'.num * left'.den * (left.den * right.den) := by ring1

/-- Replacing both signed displays by equivalent ones preserves and reflects weak comparison.

The same direct scalar transport applies in both directions, using each
retained equivalence or its reversal. All four original signed displays and
positive denominators remain unchanged. -/
private theorem lessEqFraction_congr {left left' right right' : SignedFraction}
    (leftEquivalent : SignedFraction.Basic.Equivalent left left')
    (rightEquivalent : SignedFraction.Basic.Equivalent right right') :
    LessEqFraction left right ↔ LessEqFraction left' right' :=
  ⟨lessEqFraction_imp leftEquivalent rightEquivalent,
    lessEqFraction_imp leftEquivalent.symm rightEquivalent.symm⟩

/-- Canonical normalizations are weakly ordered exactly when the signed cross-products are.

Each original normalization retains a cross-product equivalence with its
input signed display. Transporting both certificates compares the same
canonical values and original weak integer products. -/
public theorem ofFraction_le_iff (left right : SignedFraction) :
    SignedFraction.Normalization.ofFraction left ≤ SignedFraction.Normalization.ofFraction right ↔ LessEqFraction left
      right := by
  change
    LessEqFraction (SignedFraction.Normalization.toFraction (SignedFraction.Normalization.ofFraction left))
      (SignedFraction.Normalization.toFraction (SignedFraction.Normalization.ofFraction right)) ↔
        LessEqFraction left right
  exact lessEqFraction_congr
    (SignedFraction.Normalization.normalize_equivalent left)
    (SignedFraction.Normalization.normalize_equivalent right)
end Purelib.Data.Rat.SignedFraction.Order
