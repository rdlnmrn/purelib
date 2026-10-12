module

public import Purelib.Data.Sign.CauchyIndex.Endpoint
public import Purelib.Data.Sign.ComplexProduct
public import Purelib.Data.Sign.Stability
import Purelib.Data.Sign.Sum
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Int

/-!
# Finite one-sided Cauchy product identities

The retained endpoint signs, stability witnesses and compatible products
determine an exact integer identity with its two denominator corrections.
-/

namespace Purelib.Data.Sign

/-- The finite hypotheses for a one-sided complex-product event.

Both initial factor pairs are nonzero, the three later denominator signs are nonzero,
all six coordinates are stable, and the factor/product signs are compatible at both
displayed endpoints. -/
@[expose] public def LocalProductAdmissible
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign) : Prop :=
  (A₀ ≠ zero ∨ B₀ ≠ zero) ∧
  (C₀ ≠ zero ∨ D₀ ≠ zero) ∧
  B₁ ≠ zero ∧ D₁ ≠ zero ∧ H₁ ≠ zero ∧
  Sign.Stable A₀ A₁ ∧ Sign.Stable B₀ B₁ ∧
  Sign.Stable C₀ C₁ ∧ Sign.Stable D₀ D₁ ∧
  Sign.Stable E₀ E₁ ∧ Sign.Stable H₀ H₁ ∧
  Sign.ComplexProductCompatible A₀ B₀ C₀ D₀ E₀ H₀ ∧
  Sign.ComplexProductCompatible A₁ B₁ C₁ D₁ E₁ H₁

/-- Decide local product admissibility from the displayed sign and stability conditions. -/
public instance instDecidableLocalProductAdmissible (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign) :
    Decidable (Sign.LocalProductAdmissible
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold Sign.LocalProductAdmissible
  infer_instance

/-- Compute the doubled product correction from three denominator signs.

The correction is the jump from the positive sign to the product of the product
denominator sign and the two factor denominator signs. -/
@[expose] public def productCorrection2 (H B D : Sign) : Nat :=
  Sign.jump positive (Sign.mul H (Sign.mul B D))

/-- The one-sided Cauchy product identity with its two endpoint corrections.

The product contribution equals the sum of the two factor contributions, minus the
correction at the initial endpoint and plus the correction at the later endpoint. -/
@[expose] public def LocalProductIdentity
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign) : Prop :=
  Sign.leftEndpointIndex2 E₀ H₀ E₁ H₁ =
    Sign.leftEndpointIndex2 A₀ B₀ A₁ B₁ +
      Sign.leftEndpointIndex2 C₀ D₀ C₁ D₁ -
      (productCorrection2 H₀ B₀ D₀ : Int) +
      productCorrection2 H₁ B₁ D₁

/-- Decide the local product identity by exact equality of its integer sign readings. -/
public instance instDecidableLocalProductIdentity (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign) :
    Decidable (Sign.LocalProductIdentity
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold Sign.LocalProductIdentity
  infer_instance

/-- Evaluate the local product correction when the left initial denominator is zero.

With the three displayed remaining signs nonzero, the later correction cancels the
initial correction and the left factor's integer sign-product contribution. -/
private theorem correction_identity_left_zero
    (A D B : Sign)
    (ANonzero : A ≠ zero) (DNonzero : D ≠ zero)
    (BNonzero : B ≠ zero) :
    (0 : Int) = Sign.value (Sign.mul A B) -
      (productCorrection2 (Sign.mul A D) zero D : Int) +
      productCorrection2 (Sign.mul A D) B D := by
  revert ANonzero DNonzero BNonzero
  cases A <;> cases D <;> cases B <;> decide

/-- Evaluate the local product correction when the right initial denominator is zero.

With the three displayed remaining signs nonzero, the later correction cancels the
initial correction and the right factor's integer sign-product contribution. -/
private theorem correction_identity_right_zero
    (B C D : Sign)
    (BNonzero : B ≠ zero) (CNonzero : C ≠ zero)
    (DNonzero : D ≠ zero) :
    (0 : Int) = Sign.value (Sign.mul C D) -
      (productCorrection2 (Sign.mul B C) B zero : Int) +
      productCorrection2 (Sign.mul B C) B D := by
  revert BNonzero CNonzero DNonzero
  cases B <;> cases C <;> cases D <;> decide

/-- Evaluate the correction when both initial denominator signs are zero.

Nonzero factor, denominator, and product signs plus complex-product compatibility
identify the product contribution with the two factor contributions and their
correction difference. -/
private theorem correction_identity_both_zero
    (A C B D H : Sign)
    (ANonzero : A ≠ zero) (CNonzero : C ≠ zero)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (HNonzero : H ≠ zero)
    (compatible : Sign.ComplexProductCompatible A B C D (Sign.mul A C) H) :
    Sign.value (Sign.mul (Sign.mul A C) H) =
      Sign.value (Sign.mul A B) + Sign.value (Sign.mul C D) -
        (productCorrection2 zero zero zero : Int) +
        productCorrection2 H B D := by
  revert ANonzero CNonzero BNonzero DNonzero HNonzero compatible
  cases A <;> cases C <;> cases B <;> cases D <;> cases H <;> decide

/-- Evaluate the correction when the compatible product imaginary sign vanishes.

Nonzero factor denominator signs and the later product denominator sign identify the
product contribution with the difference of the two corrections. -/
private theorem correction_identity_imag_zero
    (A B C D E H : Sign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (HNonzero : H ≠ zero)
    (compatible : Sign.ComplexProductCompatible A B C D E zero) :
    Sign.value (Sign.mul E H) =
      -(productCorrection2 zero B D : Int) +
        productCorrection2 H B D := by
  revert BNonzero DNonzero HNonzero compatible
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> cases H <;> decide

/-- The exhaustive one-sided product table.

The outer proof splits the only three denominator cases which matter; each closed
helper above checks at most six explicit three-valued inputs. -/
public theorem localProductTable :
    ∀ A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign,
      Sign.LocalProductAdmissible
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ →
        Sign.LocalProductIdentity
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ := by
  intro A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ admissible
  rcases admissible with ⟨AB₀, CD₀, B₁Nonzero, D₁Nonzero, H₁Nonzero,
    AStable, BStable, CStable, DStable, EStable, HStable,
    product₀, product₁⟩
  by_cases B₀Zero : B₀ = zero
  · subst B₀
    have A₀Nonzero : A₀ ≠ zero :=
        AB₀.elim (fun nonzero => nonzero) (fun impossible => (impossible rfl).elim)
    have AA₁ := Sign.eq_of_stable_of_ne_zero AStable A₀Nonzero
    subst A₁
    by_cases D₀Zero : D₀ = zero
    · subst D₀
      have C₀Nonzero : C₀ ≠ zero :=
        CD₀.elim (fun nonzero => nonzero) (fun impossible => (impossible rfl).elim)
      have CC₁ := Sign.eq_of_stable_of_ne_zero CStable C₀Nonzero
      subst C₁
      obtain ⟨E₀Equal, rfl⟩ :=
        Sign.compatible_both_denominators_zero A₀ C₀ E₀ H₀ product₀
      rw [E₀Equal] at EStable ⊢
      have ACNonzero : Sign.mul A₀ C₀ ≠ zero :=
        Sign.mul_ne_zero A₀Nonzero C₀Nonzero
      have EE₁ := Sign.eq_of_stable_of_ne_zero EStable ACNonzero
      subst E₁
      unfold Sign.LocalProductIdentity Sign.leftEndpointIndex2
      exact Sign.correction_identity_both_zero
        A₀ C₀ B₁ D₁ H₁ A₀Nonzero C₀Nonzero B₁Nonzero D₁Nonzero
          H₁Nonzero product₁
    · have DD₁ := Sign.eq_of_stable_of_ne_zero DStable D₀Zero
      subst D₁
      have H₀Equal := Sign.compatible_left_denominator_zero
        A₀ C₀ D₀ E₀ H₀ product₀
      have ADNonzero : Sign.mul A₀ D₀ ≠ zero :=
        Sign.mul_ne_zero A₀Nonzero D₀Zero
      rw [H₀Equal] at HStable ⊢
      have HH₁ := Sign.eq_of_stable_of_ne_zero HStable ADNonzero
      subst H₁
      unfold Sign.LocalProductIdentity Sign.leftEndpointIndex2
      rewrite [if_neg D₀Zero, if_neg ADNonzero]
      have sumIdentity : Sign.value (Sign.mul A₀ B₁) + (0 : Int) =
          Sign.value (Sign.mul A₀ B₁) := by ring1
      rewrite [if_pos (Eq.refl zero), sumIdentity]
      exact Sign.correction_identity_left_zero
        A₀ D₀ B₁ A₀Nonzero D₀Zero B₁Nonzero
  · have BB₁ := Sign.eq_of_stable_of_ne_zero BStable B₀Zero
    subst B₁
    by_cases D₀Zero : D₀ = zero
    · subst D₀
      have C₀Nonzero : C₀ ≠ zero :=
        CD₀.elim (fun nonzero => nonzero) (fun impossible => (impossible rfl).elim)
      have CC₁ := Sign.eq_of_stable_of_ne_zero CStable C₀Nonzero
      subst C₁
      have H₀Equal := Sign.compatible_right_denominator_zero
        A₀ B₀ C₀ E₀ H₀ product₀
      have BCNonzero : Sign.mul B₀ C₀ ≠ zero :=
        Sign.mul_ne_zero B₀Zero C₀Nonzero
      rw [H₀Equal] at HStable ⊢
      have HH₁ := Sign.eq_of_stable_of_ne_zero HStable BCNonzero
      subst H₁
      unfold Sign.LocalProductIdentity Sign.leftEndpointIndex2
      rewrite [if_neg B₀Zero, if_neg BCNonzero]
      have sumIdentity : (0 : Int) + Sign.value (Sign.mul C₀ D₁) =
          Sign.value (Sign.mul C₀ D₁) := by ring1
      rewrite [if_pos (Eq.refl zero), sumIdentity]
      exact Sign.correction_identity_right_zero
        B₀ C₀ D₁ B₀Zero C₀Nonzero D₁Nonzero
    · have DD₁ := Sign.eq_of_stable_of_ne_zero DStable D₀Zero
      subst D₁
      by_cases H₀Zero : H₀ = zero
      · subst H₀
        have E₀Nonzero := Sign.real_nonzero_of_imag_zero
          A₀ B₀ C₀ D₀ E₀ B₀Zero D₀Zero product₀
        have EE₁ := Sign.eq_of_stable_of_ne_zero EStable E₀Nonzero
        subst E₁
        unfold Sign.LocalProductIdentity Sign.leftEndpointIndex2
        rewrite [if_neg B₀Zero, if_neg D₀Zero]
        have correctionIdentity : (0 : Int) + 0 -
            (productCorrection2 zero B₀ D₀ : Int) =
              -(productCorrection2 zero B₀ D₀ : Int) := by ring1
        rewrite [correctionIdentity]
        exact Sign.correction_identity_imag_zero
          A₀ B₀ C₀ D₀ E₀ H₁ B₀Zero D₀Zero H₁Nonzero product₀
      · have HH₁ := Sign.eq_of_stable_of_ne_zero HStable H₀Zero
        subst H₁
        unfold Sign.LocalProductIdentity Sign.leftEndpointIndex2
        rewrite [if_neg B₀Zero, if_neg D₀Zero, if_neg H₀Zero]
        ring1

/-- The two integer factor sign-products cancel for a compatible real-axis product.

Both factor imaginary signs must be nonzero; compatibility with zero product
imaginary sign forces the sum of the factor product readings to be zero. -/
private theorem value_factor_products_cancel_of_product_imag_zero
    (A B C D E : Sign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (compatible : Sign.ComplexProductCompatible A B C D E zero) :
    Sign.value (Sign.mul A B) + Sign.value (Sign.mul C D) = 0 := by
  revert BNonzero DNonzero compatible
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> decide

/-- The product correction equals one when its left denominator sign is zero. -/
private theorem productCorrection2_left_zero
    (H D : Sign) : productCorrection2 H zero D = 1 := by
  cases H <;> cases D <;> rfl

/-- The product correction equals one when its right denominator sign is zero. -/
private theorem productCorrection2_right_zero
    (H B : Sign) : productCorrection2 H B zero = 1 := by
  cases H <;> cases B <;> rfl

/-- The product correction equals one when its product denominator sign is zero. -/
private theorem productCorrection2_product_zero
    (B D : Sign) : productCorrection2 zero B D = 1 := by
  cases B <;> cases D <;> rfl

/-- The one-sided finite product table remains valid when a displayed denominator
coordinate is identically zero.

Both factor pairs are nonzero at the displayed endpoints, and all retained
coordinates are stable and product-compatible. Three zero-denominator branches
use the exact axis identities; the all-nonzero branch uses the original table. -/
public theorem localProductTable_of_target_pairs_nonzero :
    ∀ A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : Sign,
      (A₀ ≠ zero ∨ B₀ ≠ zero) →
      (C₀ ≠ zero ∨ D₀ ≠ zero) →
      (A₁ ≠ zero ∨ B₁ ≠ zero) →
      (C₁ ≠ zero ∨ D₁ ≠ zero) →
      Sign.Stable A₀ A₁ → Sign.Stable B₀ B₁ →
      Sign.Stable C₀ C₁ → Sign.Stable D₀ D₁ →
      Sign.Stable E₀ E₁ → Sign.Stable H₀ H₁ →
      Sign.ComplexProductCompatible A₀ B₀ C₀ D₀ E₀ H₀ →
      Sign.ComplexProductCompatible A₁ B₁ C₁ D₁ E₁ H₁ →
      Sign.LocalProductIdentity
        A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ := by
  intro A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁
    left₀ right₀ left₁ right₁ AStable BStable CStable DStable
    EStable HStable product₀ product₁
  by_cases B₁Zero : B₁ = zero
  · have B₀Zero : B₀ = zero := by
      rcases BStable with B₀Zero | equal
      · exact B₀Zero
      · exact equal.trans B₁Zero
    have A₀Nonzero : A₀ ≠ zero := by
      rcases left₀ with nonzero | contradiction
      · exact nonzero
      · exact (contradiction B₀Zero).elim
    have A₁Nonzero : A₁ ≠ zero := by
      rcases left₁ with nonzero | contradiction
      · exact nonzero
      · exact (contradiction B₁Zero).elim
    have AEqual : A₀ = A₁ := AStable.resolve_left A₀Nonzero
    obtain ⟨E₀Equal, H₀Equal⟩ := Sign.compatible_left_imag_zero A₀ C₀ D₀ E₀ H₀ (by
          have retained := product₀
          rewrite [B₀Zero] at retained
          exact retained)
    obtain ⟨E₁Equal, H₁Equal⟩ := Sign.compatible_left_imag_zero A₁ C₁ D₁ E₁ H₁ (by
          have retained := product₁
          rewrite [B₁Zero] at retained
          exact retained)
    subst A₁
    rw [B₀Zero, B₁Zero, E₀Equal, H₀Equal, E₁Equal, H₁Equal]
    unfold Sign.LocalProductIdentity
    rw [Sign.leftEndpointIndex2_scale_left A₀ C₀ D₀ C₁ D₁ A₀Nonzero]
    rw [Sign.leftEndpointIndex2_zero_to_zero]
    rw [Sign.productCorrection2_left_zero, Sign.productCorrection2_left_zero]
    ring1
  · by_cases D₁Zero : D₁ = zero
    · have D₀Zero : D₀ = zero := by
        rcases DStable with D₀Zero | equal
        · exact D₀Zero
        · exact equal.trans D₁Zero
      have C₀Nonzero : C₀ ≠ zero := by
        rcases right₀ with nonzero | contradiction
        · exact nonzero
        · exact (contradiction D₀Zero).elim
      have C₁Nonzero : C₁ ≠ zero := by
        rcases right₁ with nonzero | contradiction
        · exact nonzero
        · exact (contradiction D₁Zero).elim
      have CEqual : C₀ = C₁ := CStable.resolve_left C₀Nonzero
      obtain ⟨E₀Equal, H₀Equal⟩ := Sign.compatible_right_imag_zero A₀ B₀ C₀ E₀ H₀ (by
          have retained := product₀
          rewrite [D₀Zero] at retained
          exact retained)
      obtain ⟨E₁Equal, H₁Equal⟩ := Sign.compatible_right_imag_zero A₁ B₁ C₁ E₁ H₁ (by
          have retained := product₁
          rewrite [D₁Zero] at retained
          exact retained)
      subst C₁
      rw [D₀Zero, D₁Zero, E₀Equal, H₀Equal, E₁Equal, H₁Equal]
      unfold Sign.LocalProductIdentity
      rw [Sign.leftEndpointIndex2_scale_right C₀ A₀ B₀ A₁ B₁ C₀Nonzero]
      rw [Sign.leftEndpointIndex2_zero_to_zero]
      rw [Sign.productCorrection2_right_zero, Sign.productCorrection2_right_zero]
      ring1
    · by_cases H₁Zero : H₁ = zero
      · have H₀Zero : H₀ = zero := by
          rcases HStable with H₀Zero | equal
          · exact H₀Zero
          · exact equal.trans H₁Zero
        by_cases B₀Zero : B₀ = zero
        · have A₀Nonzero : A₀ ≠ zero := by
            rcases left₀ with nonzero | contradiction
            · exact nonzero
            · exact (contradiction B₀Zero).elim
          have AD₀Zero : Sign.mul A₀ D₀ = zero := by
            have imaginary :=
              (Sign.compatible_left_imag_zero A₀ C₀ D₀ E₀ H₀ (by
                have retained := product₀
                rewrite [B₀Zero] at retained
                exact retained)).2
            exact imaginary.symm.trans H₀Zero
          have D₀Zero : D₀ = zero := by
            by_cases D₀Zero : D₀ = zero
            · exact D₀Zero
            · exact (Sign.mul_ne_zero A₀Nonzero D₀Zero AD₀Zero).elim
          have cancellation :=
            Sign.value_factor_products_cancel_of_product_imag_zero
              A₁ B₁ C₁ D₁ E₁ B₁Zero D₁Zero (by
                have retained := product₁
                rewrite [H₁Zero] at retained
                exact retained)
          unfold Sign.LocalProductIdentity
          rw [B₀Zero, D₀Zero, H₀Zero, H₁Zero]
          rw [Sign.leftEndpointIndex2_zero_to_zero,
            Sign.productCorrection2_product_zero,
            Sign.productCorrection2_product_zero]
          change (0 : Int) = Sign.value (Sign.mul A₁ B₁) +
            Sign.value (Sign.mul C₁ D₁) - (1 : Int) + 1
          calc
            (0 : Int) = Sign.value (Sign.mul A₁ B₁) +
                Sign.value (Sign.mul C₁ D₁) := cancellation.symm
            _ = Sign.value (Sign.mul A₁ B₁) +
                Sign.value (Sign.mul C₁ D₁) - (1 : Int) + 1 := by ring1
        · have D₀Nonzero : D₀ ≠ zero := by
            intro D₀Zero
            have C₀Nonzero : C₀ ≠ zero := by
              rcases right₀ with nonzero | contradiction
              · exact nonzero
              · exact (contradiction D₀Zero).elim
            have BC₀Nonzero : Sign.mul B₀ C₀ ≠ zero :=
              Sign.mul_ne_zero B₀Zero C₀Nonzero
            have imaginary :=
              (Sign.compatible_right_imag_zero A₀ B₀ C₀ E₀ H₀ (by
                have retained := product₀
                rewrite [D₀Zero] at retained
                exact retained)).2
            exact BC₀Nonzero (imaginary.symm.trans H₀Zero)
          unfold Sign.LocalProductIdentity
          rw [H₀Zero, H₁Zero, Sign.leftEndpointIndex2_zero_to_zero,
            Sign.productCorrection2_product_zero,
            Sign.productCorrection2_product_zero]
          unfold Sign.leftEndpointIndex2
          rewrite [if_neg B₀Zero, if_neg D₀Nonzero]
          ring1
      · exact Sign.localProductTable
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁
          ⟨left₀, right₀, B₁Zero, D₁Zero, H₁Zero,
            AStable, BStable, CStable, DStable, EStable, HStable,
            product₀, product₁⟩

end Purelib.Data.Sign
