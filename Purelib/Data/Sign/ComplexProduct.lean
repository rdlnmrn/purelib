module

public import Purelib.Data.Sign.Sum

/-!
# Compatible coordinate signs of formal complex products

The two formal product coordinates satisfy the retained sum restrictions.
Finite constructor cases certify axis products and nonzero product choices.
-/

namespace Purelib.Data.Sign

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- Relate factor-coordinate signs to compatible complex-product coordinate signs.

The real output is compatible with AC minus BD, and the imaginary output with AD plus
BC, using the finite multiplication, negation, and sum-compatibility tables. -/
@[expose] public def ComplexProductCompatible
    (A B C D E H : Sign) : Prop :=
  Sign.SumCompatible (Sign.mul A C) (Sign.neg (Sign.mul B D)) E ∧
    Sign.SumCompatible (Sign.mul A D) (Sign.mul B C) H

/-- Decide complex-product compatibility through the two formal sum compatibility
conditions. -/
public instance instDecidableComplexProductCompatible (A B C D E H : Sign) :
    Decidable (Sign.ComplexProductCompatible A B C D E H) := by
  unfold Sign.ComplexProductCompatible
  infer_instance

/-- Compute a conservative formal real sign of a complex product.

Combine the real-coordinate product with the negated imaginary-coordinate product
using the conservative formal sum choice; no coordinate magnitudes are assumed. -/
@[expose] public def productRealChoice (A B C D : Sign) : Sign :=
  Sign.sumChoice (Sign.mul A C) (Sign.neg (Sign.mul B D))

/-- Choose the conservative imaginary-coordinate sign of a formal complex product.

Apply the conservative sum choice to the products AD and BC; the output may be zero
when opposite nonzero summands leave the magnitude comparison unspecified. -/
@[expose] public def productImagChoice (A B C D : Sign) : Sign :=
  Sign.sumChoice (Sign.mul A D) (Sign.mul B C)

/-- The two conservative coordinate choices satisfy complex-product compatibility.

Each output is the conservative sum choice for its exact two formal
coordinate products. The sum-choice certificates supply both components of
the retained product compatibility relation. -/
public theorem productChoices_compatible (A B C D : Sign) :
    Sign.ComplexProductCompatible A B C D
      (Sign.productRealChoice A B C D) (Sign.productImagChoice A B C D) := by
  exact ⟨Sign.sumChoice_compatible _ _, Sign.sumChoice_compatible _ _⟩

/-- The explicit coordinate formula is compatible when the left factor's imag sign is
zero.

With that axis coordinate zero, the two complex-product coordinates reduce to the
displayed signed products of the remaining factor signs. -/
public theorem complexProductCompatible_left_imag_zero
    (A C D : Sign) :
    Sign.ComplexProductCompatible A zero C D (Sign.mul A C) (Sign.mul A D) := by
  cases A <;> cases C <;> cases D <;> decide

/-- The explicit coordinate formula is compatible when the left factor's real sign is
zero.

With that axis coordinate zero, the two complex-product coordinates reduce to the
displayed signed products of the remaining factor signs. -/
public theorem complexProductCompatible_left_real_zero
    (B C D : Sign) :
    Sign.ComplexProductCompatible zero B C D (Sign.neg (Sign.mul B D)) (Sign.mul B C) := by
  cases B <;> cases C <;> cases D <;> decide

/-- The explicit coordinate formula is compatible when the right factor's imag sign is
zero.

With that axis coordinate zero, the two complex-product coordinates reduce to the
displayed signed products of the remaining factor signs. -/
public theorem complexProductCompatible_right_imag_zero
    (A B C : Sign) :
    Sign.ComplexProductCompatible A B C zero (Sign.mul A C) (Sign.mul B C) := by
  cases A <;> cases B <;> cases C <;> decide

/-- The explicit coordinate formula is compatible when the right factor's real sign is
zero.

With that axis coordinate zero, the two complex-product coordinates reduce to the
displayed signed products of the remaining factor signs. -/
public theorem complexProductCompatible_right_real_zero
    (A B D : Sign) :
    Sign.ComplexProductCompatible A B zero D (Sign.neg (Sign.mul B D)) (Sign.mul A D) := by
  cases A <;> cases B <;> cases D <;> decide

/-- A scaled formal conjugate is compatible with a nonzero real product.

For a nonzero factor pair and a nonzero desired real sign, the displayed second
factor gives a compatible product with zero imaginary sign. -/
public theorem complexProductCompatible_product_imag_zero
    (A B E : Sign) (factor : A ≠ zero ∨ B ≠ zero)
    (product : E ≠ zero) :
    Sign.ComplexProductCompatible A B (Sign.mul E A) (Sign.neg (Sign.mul E B)) E zero := by
  revert factor product
  cases A <;> cases B <;> cases E <;> decide

/-- A scaled coordinate swap is compatible with a nonzero imaginary product.

For a nonzero factor pair and a nonzero desired imaginary sign, the displayed second
factor gives a compatible product with zero real sign. -/
public theorem complexProductCompatible_product_real_zero
    (A B H : Sign) (factor : A ≠ zero ∨ B ≠ zero)
    (product : H ≠ zero) :
    Sign.ComplexProductCompatible A B (Sign.mul H B) (Sign.mul H A) zero H := by
  revert factor product
  cases A <;> cases B <;> cases H <;> decide

/-- Conservative product coordinates cannot both vanish for two nonzero factor pairs.

Each input pair has at least one nonzero sign. The finite product table ensures at
least one of its two conservative coordinate choices remains nonzero. -/
public theorem productChoices_nonzero (A B C D : Sign)
    (left : A ≠ zero ∨ B ≠ zero)
    (right : C ≠ zero ∨ D ≠ zero) :
    Sign.productRealChoice A B C D ≠ zero ∨
      Sign.productImagChoice A B C D ≠ zero := by
  revert left right
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- Two real-axis factors force a real product with their multiplied real sign.

Both imaginary input signs vanish. The real compatibility condition forces
the retained real product sign, and the imaginary condition forces zero. -/
public theorem compatible_both_denominators_zero
    (A C E H : Sign)
    (compatible : Sign.ComplexProductCompatible A zero C zero E H) :
    E = Sign.mul A C ∧ H = zero := by
  revert compatible
  cases A <;> cases C <;> cases E <;> cases H <;> decide

/-- A zero left imaginary sign forces the product imaginary sign to be AD.

The left imaginary input sign vanishes, so the imaginary coordinate sum
has only its retained AD product sign as a nonzero possible contribution. -/
public theorem compatible_left_denominator_zero
    (A C D E H : Sign)
    (compatible : Sign.ComplexProductCompatible A zero C D E H) :
    H = Sign.mul A D := by
  revert compatible
  cases A <;> cases C <;> cases D <;> cases E <;> cases H <;> decide

/-- A zero right imaginary sign forces the product imaginary sign to be BC.

The right imaginary input sign vanishes, so the imaginary coordinate sum
has only its retained BC product sign as a nonzero possible contribution. -/
public theorem compatible_right_denominator_zero
    (A B C E H : Sign)
    (compatible : Sign.ComplexProductCompatible A B C zero E H) :
    H = Sign.mul B C := by
  revert compatible
  cases A <;> cases B <;> cases C <;> cases E <;> cases H <;> decide

/-- A compatible zero imaginary product has nonzero real sign when both factor imaginary signs are nonzero.

The two factor imaginary signs are nonzero, and their compatible imaginary
product sign is zero. The finite coordinate compatibility conditions then
exclude a zero real product sign. -/
public theorem real_nonzero_of_imag_zero
    (A B C D E : Sign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (compatible : Sign.ComplexProductCompatible A B C D E zero) : E ≠ zero := by
  revert compatible BNonzero DNonzero
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> decide

/-- A compatible product with a real-axis left factor has coordinates AC and AD.

The left imaginary input sign vanishes. Both coordinate compatibility
conditions therefore force the real and imaginary output signs of AC and AD. -/
public theorem compatible_left_imag_zero
    (A C D E H : Sign)
    (compatible : Sign.ComplexProductCompatible A zero C D E H) :
    E = Sign.mul A C ∧ H = Sign.mul A D := by
  revert compatible
  cases A <;> cases C <;> cases D <;> cases E <;> cases H <;> decide

/-- A compatible product with a real-axis right factor has coordinates AC and BC.

The right imaginary input sign vanishes. Both coordinate compatibility
conditions therefore force the real and imaginary output signs of AC and BC. -/
public theorem compatible_right_imag_zero
    (A B C E H : Sign)
    (compatible : Sign.ComplexProductCompatible A B C zero E H) :
    E = Sign.mul A C ∧ H = Sign.mul B C := by
  revert compatible
  cases A <;> cases B <;> cases C <;> cases E <;> cases H <;> decide

end Purelib.Data.Sign
