import mathlib.Tactic.QuotientFreeRing
import RFAP.Sturm

/-!
# Finite signs for the constructive Cauchy-product identity

This module isolates the finite local sign calculation behind multiplication
of two displayed complex paths.  The three signs are split explicitly: there
is no `Fintype` instance, enumeration of a carrier, or choice-based search.
-/

namespace RFAP.CauchyProductSigns

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

open RFAP.Sturm

inductive FiniteSign where
  | negative
  | zero
  | positive
deriving DecidableEq, Repr

namespace FiniteSign

def value : FiniteSign → Int
  | negative => -1
  | zero => 0
  | positive => 1

def ofCoordinate (x : Coordinate) : FiniteSign :=
  if x < 0 then negative else if x = 0 then zero else positive

def mul : FiniteSign → FiniteSign → FiniteSign
  | zero, _ => zero
  | _, zero => zero
  | positive, y => y
  | x, positive => x
  | negative, negative => positive

def neg : FiniteSign → FiniteSign
  | negative => positive
  | zero => zero
  | positive => negative

def jump (x y : FiniteSign) : Nat := (x.value - y.value).natAbs

theorem value_injective : Function.Injective value := by
  intro x y equal
  cases x <;> cases y
  · rfl
  · exact ((by decide : (-1 : Int) ≠ 0) equal).elim
  · exact ((by decide : (-1 : Int) ≠ 1) equal).elim
  · exact ((by decide : (0 : Int) ≠ -1) equal).elim
  · rfl
  · exact ((by decide : (0 : Int) ≠ 1) equal).elim
  · exact ((by decide : (1 : Int) ≠ -1) equal).elim
  · exact ((by decide : (1 : Int) ≠ 0) equal).elim
  · rfl

@[simp] theorem value_ofCoordinate (x : Coordinate) :
    value (ofCoordinate x) = sign x := by
  by_cases negative : x < 0
  · rw [ofCoordinate, if_pos negative, value, sign_of_neg negative]
  · by_cases zero : x = 0
    · subst x
      rfl
    · have positive : 0 < x := lt_of_le_of_ne (not_lt.mp negative) (Ne.symm zero)
      rw [ofCoordinate, if_neg negative, if_neg zero, value,
        sign_of_pos positive]

@[simp] theorem ofCoordinate_zero : ofCoordinate 0 = zero := rfl

@[simp] theorem ofCoordinate_eq_zero_iff {x : Coordinate} :
    ofCoordinate x = zero ↔ x = 0 := by
  constructor
  · intro equal
    have values := congrArg value equal
    rw [value_ofCoordinate, value] at values
    exact sign_eq_zero_iff.mp values
  · rintro rfl
    rfl

@[simp] theorem ofCoordinate_ne_zero_iff {x : Coordinate} :
    ofCoordinate x ≠ zero ↔ x ≠ 0 :=
  not_congr ofCoordinate_eq_zero_iff

theorem ofCoordinate_of_neg {x : Coordinate} (negative : x < 0) :
    ofCoordinate x = .negative := by
  rw [ofCoordinate, if_pos negative]

theorem ofCoordinate_of_pos {x : Coordinate} (positive : 0 < x) :
    ofCoordinate x = .positive := by
  rw [ofCoordinate, if_neg (not_lt.mpr positive.le),
    if_neg positive.ne']

@[simp] theorem value_mul (x y : FiniteSign) :
    value (mul x y) = value x * value y := by
  cases x <;> cases y <;> decide

@[simp] theorem value_neg (x : FiniteSign) : value (neg x) = -value x := by
  cases x <;> decide

@[simp] theorem ofCoordinate_mul (x y : Coordinate) :
    ofCoordinate (x * y) = mul (ofCoordinate x) (ofCoordinate y) := by
  apply value_injective
  rw [value_ofCoordinate, value_mul, value_ofCoordinate, value_ofCoordinate,
    sign_mul]

@[simp] theorem ofCoordinate_neg (x : Coordinate) :
    ofCoordinate (-x) = neg (ofCoordinate x) := by
  apply value_injective
  rw [value_ofCoordinate, value_neg, value_ofCoordinate, sign_neg]

@[simp] theorem jump_ofCoordinate (x y : Coordinate) :
    jump (ofCoordinate x) (ofCoordinate y) = signJump x y := by
  rw [jump, signJump, value_ofCoordinate, value_ofCoordinate]

theorem jump_eq_positive_mul
    (x y : FiniteSign) (nonzero : x ≠ zero ∨ y ≠ zero) :
    jump x y = jump positive (mul x y) := by
  cases x <;> cases y <;>
    simp_all [jump, value, mul]

def SumCompatible (x y z : FiniteSign) : Prop :=
  if x = zero then z = y
  else if y = zero then z = x
  else if x = y then z = x
  else True

instance (x y z : FiniteSign) : Decidable (SumCompatible x y z) := by
  unfold SumCompatible
  infer_instance

theorem sumCompatible_ofCoordinate (x y : Coordinate) :
    SumCompatible (ofCoordinate x) (ofCoordinate y)
      (ofCoordinate (x + y)) := by
  rcases lt_trichotomy x 0 with negativeX | rfl | positiveX <;>
    rcases lt_trichotomy y 0 with negativeY | rfl | positiveY
  · have sumNegative : x + y < 0 := add_neg negativeX negativeY
    rw [ofCoordinate_of_neg negativeX, ofCoordinate_of_neg negativeY,
      ofCoordinate_of_neg sumNegative]
    trivial
  · rw [add_zero, ofCoordinate_of_neg negativeX]
    trivial
  · rw [ofCoordinate_of_neg negativeX, ofCoordinate_of_pos positiveY]
    trivial
  · rw [zero_add, ofCoordinate_of_neg negativeY]
    trivial
  · trivial
  · rw [zero_add, ofCoordinate_of_pos positiveY]
    trivial
  · rw [ofCoordinate_of_pos positiveX, ofCoordinate_of_neg negativeY]
    trivial
  · rw [add_zero, ofCoordinate_of_pos positiveX]
    trivial
  · have sumPositive : 0 < x + y := add_pos positiveX positiveY
    rw [ofCoordinate_of_pos positiveX, ofCoordinate_of_pos positiveY,
      ofCoordinate_of_pos sumPositive]
    trivial

/-- Conservative formal sign of a sum: retain every forced sign and use
`zero` only for the genuinely magnitude-dependent opposite-sign case. -/
def sumChoice (x y : FiniteSign) : FiniteSign :=
  if x = zero then y
  else if y = zero then x
  else if x = y then x
  else zero

theorem sumChoice_compatible (x y : FiniteSign) :
    SumCompatible x y (sumChoice x y) := by
  cases x <;> cases y <;>
    simp [SumCompatible, sumChoice]

def Stable (atEndpoint nearby : FiniteSign) : Prop :=
  atEndpoint = zero ∨ atEndpoint = nearby

instance (atEndpoint nearby : FiniteSign) : Decidable (Stable atEndpoint nearby) := by
  unfold Stable
  infer_instance

theorem Stable.mul {a a' b b' : FiniteSign}
    (left : Stable a a') (right : Stable b b') :
    Stable (mul a b) (mul a' b') := by
  rcases left with aZero | aEqual
  · subst a
    left
    cases b <;> rfl
  · subst a'
    rcases right with bZero | bEqual
    · subst b
      left
      cases a <;> rfl
    · subst b'
      exact Or.inr rfl

theorem Stable.neg {a a' : FiniteSign} (stable : Stable a a') :
    Stable (neg a) (neg a') := by
  rcases stable with aZero | aEqual
  · subst a
    exact Or.inl rfl
  · subst a'
    exact Or.inr rfl

theorem neg_ne_zero {a : FiniteSign} (nonzero : a ≠ zero) :
    neg a ≠ zero := by
  cases a <;> simp_all [neg]

def ComplexProductCompatible
    (A B C D E H : FiniteSign) : Prop :=
  SumCompatible (mul A C) (neg (mul B D)) E ∧
    SumCompatible (mul A D) (mul B C) H

instance (A B C D E H : FiniteSign) :
    Decidable (ComplexProductCompatible A B C D E H) := by
  unfold ComplexProductCompatible
  infer_instance

/-- Conservative formal coordinates of a complex product. -/
def productRealChoice (A B C D : FiniteSign) : FiniteSign :=
  sumChoice (mul A C) (neg (mul B D))

def productImagChoice (A B C D : FiniteSign) : FiniteSign :=
  sumChoice (mul A D) (mul B C)

theorem productChoices_compatible (A B C D : FiniteSign) :
    ComplexProductCompatible A B C D
      (productRealChoice A B C D) (productImagChoice A B C D) := by
  exact ⟨sumChoice_compatible _ _, sumChoice_compatible _ _⟩

theorem complexProductCompatible_left_imag_zero
    (A C D : FiniteSign) :
    ComplexProductCompatible A zero C D (mul A C) (mul A D) := by
  cases A <;> cases C <;> cases D <;>
    simp [ComplexProductCompatible, SumCompatible, mul, neg]

theorem complexProductCompatible_left_real_zero
    (B C D : FiniteSign) :
    ComplexProductCompatible zero B C D (neg (mul B D)) (mul B C) := by
  cases B <;> cases C <;> cases D <;>
    simp [ComplexProductCompatible, SumCompatible, mul, neg]

theorem complexProductCompatible_right_imag_zero
    (A B C : FiniteSign) :
    ComplexProductCompatible A B C zero (mul A C) (mul B C) := by
  cases A <;> cases B <;> cases C <;>
    simp [ComplexProductCompatible, SumCompatible, mul, neg]

theorem complexProductCompatible_right_real_zero
    (A B D : FiniteSign) :
    ComplexProductCompatible A B zero D (neg (mul B D)) (mul A D) := by
  cases A <;> cases B <;> cases D <;>
    simp [ComplexProductCompatible, SumCompatible, mul, neg]

theorem complexProductCompatible_product_imag_zero
    (A B E : FiniteSign) (factor : A ≠ zero ∨ B ≠ zero)
    (product : E ≠ zero) :
    ComplexProductCompatible A B (mul E A) (neg (mul E B)) E zero := by
  cases A <;> cases B <;> cases E <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

theorem complexProductCompatible_product_real_zero
    (A B H : FiniteSign) (factor : A ≠ zero ∨ B ≠ zero)
    (product : H ≠ zero) :
    ComplexProductCompatible A B (mul H B) (mul H A) zero H := by
  cases A <;> cases B <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

theorem productChoices_nonzero (A B C D : FiniteSign)
    (left : A ≠ zero ∨ B ≠ zero)
    (right : C ≠ zero ∨ D ≠ zero) :
    productRealChoice A B C D ≠ zero ∨
      productImagChoice A B C D ≠ zero := by
  cases A <;> cases B <;> cases C <;> cases D <;>
    simp_all [productRealChoice, productImagChoice, sumChoice, mul, neg]

def LocalProductAdmissible
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) : Prop :=
  (A₀ ≠ zero ∨ B₀ ≠ zero) ∧
  (C₀ ≠ zero ∨ D₀ ≠ zero) ∧
  B₁ ≠ zero ∧ D₁ ≠ zero ∧ H₁ ≠ zero ∧
  Stable A₀ A₁ ∧ Stable B₀ B₁ ∧
  Stable C₀ C₁ ∧ Stable D₀ D₁ ∧
  Stable E₀ E₁ ∧ Stable H₀ H₁ ∧
  ComplexProductCompatible A₀ B₀ C₀ D₀ E₀ H₀ ∧
  ComplexProductCompatible A₁ B₁ C₁ D₁ E₁ H₁

instance (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) :
    Decidable (LocalProductAdmissible
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold LocalProductAdmissible
  infer_instance

def leftEndpointIndex2
    (_P₀ Q₀ P₁ Q₁ : FiniteSign) : Int :=
  if Q₀ = zero then value (mul P₁ Q₁) else 0

def productCorrection2 (H B D : FiniteSign) : Nat :=
  jump positive (mul H (mul B D))

def LocalProductIdentity
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) : Prop :=
  leftEndpointIndex2 E₀ H₀ E₁ H₁ =
    leftEndpointIndex2 A₀ B₀ A₁ B₁ +
      leftEndpointIndex2 C₀ D₀ C₁ D₁ -
      (productCorrection2 H₀ B₀ D₀ : Int) +
      productCorrection2 H₁ B₁ D₁

instance (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) :
    Decidable (LocalProductIdentity
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold LocalProductIdentity
  infer_instance

theorem mul_ne_zero {x y : FiniteSign}
    (xNonzero : x ≠ zero) (yNonzero : y ≠ zero) : mul x y ≠ zero := by
  cases x <;> cases y <;> simp_all [mul]

private theorem eq_of_stable_of_ne_zero {x y : FiniteSign}
    (stable : Stable x y) (nonzero : x ≠ zero) : x = y :=
  stable.resolve_left nonzero

private theorem compatible_both_denominators_zero
    (A C E H : FiniteSign)
    (compatible : ComplexProductCompatible A zero C zero E H) :
    E = mul A C ∧ H = zero := by
  cases A <;> cases C <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem compatible_left_denominator_zero
    (A C D E H : FiniteSign)
    (compatible : ComplexProductCompatible A zero C D E H) :
    H = mul A D := by
  cases A <;> cases C <;> cases D <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem compatible_right_denominator_zero
    (A B C E H : FiniteSign)
    (compatible : ComplexProductCompatible A B C zero E H) :
    H = mul B C := by
  cases A <;> cases B <;> cases C <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem real_nonzero_of_imag_zero
    (A B C D E : FiniteSign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (compatible : ComplexProductCompatible A B C D E zero) : E ≠ zero := by
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem correction_identity_left_zero
    (A D B : FiniteSign)
    (ANonzero : A ≠ zero) (DNonzero : D ≠ zero)
    (BNonzero : B ≠ zero) :
    (0 : Int) = value (mul A B) -
      (productCorrection2 (mul A D) zero D : Int) +
      productCorrection2 (mul A D) B D := by
  cases A <;> cases D <;> cases B <;>
    simp_all [productCorrection2, jump, value, mul]

private theorem correction_identity_right_zero
    (B C D : FiniteSign)
    (BNonzero : B ≠ zero) (CNonzero : C ≠ zero)
    (DNonzero : D ≠ zero) :
    (0 : Int) = value (mul C D) -
      (productCorrection2 (mul B C) B zero : Int) +
      productCorrection2 (mul B C) B D := by
  cases B <;> cases C <;> cases D <;>
    simp_all [productCorrection2, jump, value, mul]

private theorem correction_identity_both_zero
    (A C B D H : FiniteSign)
    (ANonzero : A ≠ zero) (CNonzero : C ≠ zero)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (HNonzero : H ≠ zero)
    (compatible : ComplexProductCompatible A B C D (mul A C) H) :
    value (mul (mul A C) H) =
      value (mul A B) + value (mul C D) -
        (productCorrection2 zero zero zero : Int) +
        productCorrection2 H B D := by
  cases A <;> cases C <;> cases B <;> cases D <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, productCorrection2,
      jump, value, mul, neg]

private theorem correction_identity_imag_zero
    (A B C D E H : FiniteSign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (HNonzero : H ≠ zero)
    (compatible : ComplexProductCompatible A B C D E zero) :
    value (mul E H) =
      -(productCorrection2 zero B D : Int) +
        productCorrection2 H B D := by
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, productCorrection2,
      jump, value, mul, neg]

/-- The exhaustive one-sided product table.  The outer proof splits the only
three denominator cases which matter; each closed helper above checks at most
six explicit three-valued inputs. -/
theorem localProductTable :
    ∀ A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign,
      LocalProductAdmissible
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ →
        LocalProductIdentity
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ := by
  intro A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ admissible
  rcases admissible with ⟨AB₀, CD₀, B₁Nonzero, D₁Nonzero, H₁Nonzero,
    AStable, BStable, CStable, DStable, EStable, HStable,
    product₀, product₁⟩
  by_cases B₀Zero : B₀ = zero
  · subst B₀
    have A₀Nonzero : A₀ ≠ zero := by simpa using AB₀
    have AA₁ := eq_of_stable_of_ne_zero AStable A₀Nonzero
    subst A₁
    by_cases D₀Zero : D₀ = zero
    · subst D₀
      have C₀Nonzero : C₀ ≠ zero := by simpa using CD₀
      have CC₁ := eq_of_stable_of_ne_zero CStable C₀Nonzero
      subst C₁
      obtain ⟨E₀Equal, rfl⟩ :=
        compatible_both_denominators_zero A₀ C₀ E₀ H₀ product₀
      rw [E₀Equal] at EStable ⊢
      have ACNonzero : mul A₀ C₀ ≠ zero :=
        mul_ne_zero A₀Nonzero C₀Nonzero
      have EE₁ := eq_of_stable_of_ne_zero EStable ACNonzero
      subst E₁
      unfold LocalProductIdentity leftEndpointIndex2
      simpa using correction_identity_both_zero
        A₀ C₀ B₁ D₁ H₁ A₀Nonzero C₀Nonzero B₁Nonzero D₁Nonzero
          H₁Nonzero product₁
    · have DD₁ := eq_of_stable_of_ne_zero DStable D₀Zero
      subst D₁
      have H₀Equal := compatible_left_denominator_zero
        A₀ C₀ D₀ E₀ H₀ product₀
      have ADNonzero : mul A₀ D₀ ≠ zero :=
        mul_ne_zero A₀Nonzero D₀Zero
      rw [H₀Equal] at HStable ⊢
      have HH₁ := eq_of_stable_of_ne_zero HStable ADNonzero
      subst H₁
      unfold LocalProductIdentity leftEndpointIndex2
      simp only [if_neg D₀Zero, if_neg ADNonzero, add_zero]
      exact correction_identity_left_zero
        A₀ D₀ B₁ A₀Nonzero D₀Zero B₁Nonzero
  · have BB₁ := eq_of_stable_of_ne_zero BStable B₀Zero
    subst B₁
    by_cases D₀Zero : D₀ = zero
    · subst D₀
      have C₀Nonzero : C₀ ≠ zero := by simpa using CD₀
      have CC₁ := eq_of_stable_of_ne_zero CStable C₀Nonzero
      subst C₁
      have H₀Equal := compatible_right_denominator_zero
        A₀ B₀ C₀ E₀ H₀ product₀
      have BCNonzero : mul B₀ C₀ ≠ zero :=
        mul_ne_zero B₀Zero C₀Nonzero
      rw [H₀Equal] at HStable ⊢
      have HH₁ := eq_of_stable_of_ne_zero HStable BCNonzero
      subst H₁
      unfold LocalProductIdentity leftEndpointIndex2
      simp only [if_neg B₀Zero, if_neg BCNonzero, zero_add]
      exact correction_identity_right_zero
        B₀ C₀ D₁ B₀Zero C₀Nonzero D₁Nonzero
    · have DD₁ := eq_of_stable_of_ne_zero DStable D₀Zero
      subst D₁
      by_cases H₀Zero : H₀ = zero
      · subst H₀
        have E₀Nonzero := real_nonzero_of_imag_zero
          A₀ B₀ C₀ D₀ E₀ B₀Zero D₀Zero product₀
        have EE₁ := eq_of_stable_of_ne_zero EStable E₀Nonzero
        subst E₁
        unfold LocalProductIdentity leftEndpointIndex2
        simp only [if_neg B₀Zero, if_neg D₀Zero, zero_add, zero_sub]
        exact correction_identity_imag_zero
          A₀ B₀ C₀ D₀ E₀ H₁ B₀Zero D₀Zero H₁Nonzero product₀
      · have HH₁ := eq_of_stable_of_ne_zero HStable H₀Zero
        subst H₁
        simp [LocalProductIdentity, leftEndpointIndex2,
          B₀Zero, D₀Zero, H₀Zero]

/-! The interior partition normally keeps all three displayed denominator
coordinates away from zero.  An identically-zero coordinate cannot satisfy
that convention, even though its finite event record remains perfectly
valid.  The following small lemmas extend the same table to that case.  They
reason only about the three displayed signs; no polynomial root or ambient
infinite carrier is introduced. -/

private theorem compatible_left_imag_zero
    (A C D E H : FiniteSign)
    (compatible : ComplexProductCompatible A zero C D E H) :
    E = mul A C ∧ H = mul A D := by
  cases A <;> cases C <;> cases D <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem compatible_right_imag_zero
    (A B C E H : FiniteSign)
    (compatible : ComplexProductCompatible A B C zero E H) :
    E = mul A C ∧ H = mul B C := by
  cases A <;> cases B <;> cases C <;> cases E <;> cases H <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg]

private theorem leftEndpointIndex2_scale_left
    (A C₀ D₀ C₁ D₁ : FiniteSign) (ANonzero : A ≠ zero) :
    leftEndpointIndex2 (mul A C₀) (mul A D₀)
        (mul A C₁) (mul A D₁) =
      leftEndpointIndex2 C₀ D₀ C₁ D₁ := by
  by_cases D₀Zero : D₀ = zero
  · subst D₀
    simp only [mul, leftEndpointIndex2, ↓reduceIte]
    cases A <;> cases C₁ <;> cases D₁ <;> simp_all [value]
  · have scaledNonzero : mul A D₀ ≠ zero :=
      mul_ne_zero ANonzero D₀Zero
    simp only [leftEndpointIndex2, scaledNonzero, D₀Zero, ↓reduceIte]

private theorem leftEndpointIndex2_scale_right
    (C A₀ B₀ A₁ B₁ : FiniteSign) (CNonzero : C ≠ zero) :
    leftEndpointIndex2 (mul A₀ C) (mul B₀ C)
        (mul A₁ C) (mul B₁ C) =
      leftEndpointIndex2 A₀ B₀ A₁ B₁ := by
  by_cases B₀Zero : B₀ = zero
  · subst B₀
    simp only [mul, leftEndpointIndex2, ↓reduceIte]
    cases C <;> cases A₁ <;> cases B₁ <;> simp_all [value]
  · have scaledNonzero : mul B₀ C ≠ zero :=
      mul_ne_zero B₀Zero CNonzero
    simp only [leftEndpointIndex2, scaledNonzero, B₀Zero, ↓reduceIte]

private theorem value_factor_products_cancel_of_product_imag_zero
    (A B C D E : FiniteSign)
    (BNonzero : B ≠ zero) (DNonzero : D ≠ zero)
    (compatible : ComplexProductCompatible A B C D E zero) :
    value (mul A B) + value (mul C D) = 0 := by
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;>
    simp_all [ComplexProductCompatible, SumCompatible, mul, neg, value]

private theorem productCorrection2_left_zero
    (H D : FiniteSign) : productCorrection2 H zero D = 1 := by
  cases H <;> cases D <;> rfl

private theorem productCorrection2_right_zero
    (H B : FiniteSign) : productCorrection2 H B zero = 1 := by
  cases H <;> cases B <;> rfl

private theorem productCorrection2_product_zero
    (B D : FiniteSign) : productCorrection2 zero B D = 1 := by
  cases B <;> cases D <;> rfl

private theorem leftEndpointIndex2_zero_to_zero
    (P₀ P₁ : FiniteSign) :
    leftEndpointIndex2 P₀ zero P₁ zero = 0 := by
  cases P₁ <;> rfl

/-- The one-sided finite product table remains valid when a displayed
denominator coordinate is identically zero.  Compared with
`localProductTable`, the target asks only that each factor pair be nonzero.
The four branches below are the three possible zero denominators and the
original all-nonzero row. -/
theorem localProductTable_of_target_pairs_nonzero :
    ∀ A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign,
      (A₀ ≠ zero ∨ B₀ ≠ zero) →
      (C₀ ≠ zero ∨ D₀ ≠ zero) →
      (A₁ ≠ zero ∨ B₁ ≠ zero) →
      (C₁ ≠ zero ∨ D₁ ≠ zero) →
      Stable A₀ A₁ → Stable B₀ B₁ →
      Stable C₀ C₁ → Stable D₀ D₁ →
      Stable E₀ E₁ → Stable H₀ H₁ →
      ComplexProductCompatible A₀ B₀ C₀ D₀ E₀ H₀ →
      ComplexProductCompatible A₁ B₁ C₁ D₁ E₁ H₁ →
      LocalProductIdentity
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
    obtain ⟨E₀Equal, H₀Equal⟩ := by
      simpa only [B₀Zero] using
        compatible_left_imag_zero A₀ C₀ D₀ E₀ H₀ (by
          simpa only [B₀Zero] using product₀)
    obtain ⟨E₁Equal, H₁Equal⟩ := by
      simpa only [B₁Zero] using
        compatible_left_imag_zero A₁ C₁ D₁ E₁ H₁ (by
          simpa only [B₁Zero] using product₁)
    subst A₁
    rw [B₀Zero, B₁Zero, E₀Equal, H₀Equal, E₁Equal, H₁Equal]
    unfold LocalProductIdentity
    rw [leftEndpointIndex2_scale_left A₀ C₀ D₀ C₁ D₁ A₀Nonzero]
    rw [leftEndpointIndex2_zero_to_zero]
    rw [productCorrection2_left_zero, productCorrection2_left_zero]
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
      obtain ⟨E₀Equal, H₀Equal⟩ := by
        simpa only [D₀Zero] using
          compatible_right_imag_zero A₀ B₀ C₀ E₀ H₀ (by
            simpa only [D₀Zero] using product₀)
      obtain ⟨E₁Equal, H₁Equal⟩ := by
        simpa only [D₁Zero] using
          compatible_right_imag_zero A₁ B₁ C₁ E₁ H₁ (by
            simpa only [D₁Zero] using product₁)
      subst C₁
      rw [D₀Zero, D₁Zero, E₀Equal, H₀Equal, E₁Equal, H₁Equal]
      unfold LocalProductIdentity
      rw [leftEndpointIndex2_scale_right C₀ A₀ B₀ A₁ B₁ C₀Nonzero]
      rw [leftEndpointIndex2_zero_to_zero]
      rw [productCorrection2_right_zero, productCorrection2_right_zero]
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
          have AD₀Zero : mul A₀ D₀ = zero := by
            have imaginary :=
              (compatible_left_imag_zero A₀ C₀ D₀ E₀ H₀ (by
                simpa only [B₀Zero] using product₀)).2
            exact imaginary.symm.trans H₀Zero
          have D₀Zero : D₀ = zero := by
            by_cases D₀Zero : D₀ = zero
            · exact D₀Zero
            · exact (mul_ne_zero A₀Nonzero D₀Zero AD₀Zero).elim
          have cancellation :=
            value_factor_products_cancel_of_product_imag_zero
              A₁ B₁ C₁ D₁ E₁ B₁Zero D₁Zero (by
                simpa only [H₁Zero] using product₁)
          unfold LocalProductIdentity
          rw [B₀Zero, D₀Zero, H₀Zero, H₁Zero]
          rw [leftEndpointIndex2_zero_to_zero,
            productCorrection2_product_zero,
            productCorrection2_product_zero]
          simp only [leftEndpointIndex2, ↓reduceIte, Nat.cast_one]
          simpa only [pow_one, mul_one, add_zero, sub_add_cancel] using
            cancellation.symm
        · have D₀Nonzero : D₀ ≠ zero := by
            intro D₀Zero
            have C₀Nonzero : C₀ ≠ zero := by
              rcases right₀ with nonzero | contradiction
              · exact nonzero
              · exact (contradiction D₀Zero).elim
            have BC₀Nonzero : mul B₀ C₀ ≠ zero :=
              mul_ne_zero B₀Zero C₀Nonzero
            have imaginary :=
              (compatible_right_imag_zero A₀ B₀ C₀ E₀ H₀ (by
                simpa only [D₀Zero] using product₀)).2
            exact BC₀Nonzero (imaginary.symm.trans H₀Zero)
          unfold LocalProductIdentity
          rw [H₀Zero, H₁Zero, leftEndpointIndex2_zero_to_zero,
            productCorrection2_product_zero,
            productCorrection2_product_zero]
          simp [leftEndpointIndex2, B₀Zero, D₀Nonzero]
      · exact localProductTable
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁
          ⟨left₀, right₀, B₁Zero, D₁Zero, H₁Zero,
            AStable, BStable, CStable, DStable, EStable, HStable,
            product₀, product₁⟩

/-- Net doubled contribution of one isolated two-sided event. -/
def eventIndex2
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) : Int :=
  leftEndpointIndex2 Pₑ Qₑ Pᵣ Qᵣ -
    leftEndpointIndex2 Pₑ Qₑ Pₗ Qₗ

/-- Re-centering a formal event at its displayed left endpoint leaves exactly
the one-sided contribution toward the right endpoint. -/
theorem eventIndex2_self_left
    (P Q Pᵣ Qᵣ : FiniteSign) :
    eventIndex2 P Q P Q Pᵣ Qᵣ =
      leftEndpointIndex2 P Q Pᵣ Qᵣ := by
  cases P <;> cases Q <;> cases Pᵣ <;> cases Qᵣ <;>
    simp [eventIndex2, leftEndpointIndex2, value, mul]

/-- The corresponding right-endpoint statement after reversing orientation. -/
theorem neg_eventIndex2_self_right
    (P Q Pₗ Qₗ : FiniteSign) :
    -eventIndex2 P Q Pₗ Qₗ P Q =
      leftEndpointIndex2 P Q Pₗ Qₗ := by
  cases P <;> cases Q <;> cases Pₗ <;> cases Qₗ <;>
    simp [eventIndex2, leftEndpointIndex2, value, mul]

/-- A nonzero formal sign pair stable against both displayed endpoints. -/
def EventCenterAdmissible
    (P Q Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) : Prop :=
  (P ≠ zero ∨ Q ≠ zero) ∧
    Stable P Pₗ ∧ Stable Q Qₗ ∧
    Stable P Pᵣ ∧ Stable Q Qᵣ

instance (P Q Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) :
    Decidable (EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ) := by
  unfold EventCenterAdmissible
  infer_instance

/-- The event index is independent of which nonzero stable finite sign pair
is used as its formal center.  This is an exhaustive statement about three
explicit signs, not a choice of a point or root. -/
theorem eventIndex2_eq_of_stable
    (P Q P' Q' Pₗ Qₗ Pᵣ Qᵣ : FiniteSign)
    (first : EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ)
    (second : EventCenterAdmissible P' Q' Pₗ Qₗ Pᵣ Qᵣ) :
    eventIndex2 P Q Pₗ Qₗ Pᵣ Qᵣ =
      eventIndex2 P' Q' Pₗ Qₗ Pᵣ Qᵣ := by
  cases P <;> cases Q <;> cases P' <;> cases Q' <;>
    cases Pₗ <;> cases Qₗ <;> cases Pᵣ <;> cases Qᵣ <;>
    simp_all [EventCenterAdmissible, Stable, eventIndex2,
      leftEndpointIndex2, value, mul]

/-- A formal zero denominator and stable nonzero numerator represent exactly
the change of the first signed-chain jump. -/
theorem eventIndex2_of_stableNumerator
    (P Qₗ Qᵣ : FiniteSign) (PNonzero : P ≠ zero) :
    eventIndex2 P zero P Qₗ P Qᵣ =
      (jump Qₗ P : Int) - jump Qᵣ P := by
  cases P <;> cases Qₗ <;> cases Qᵣ <;>
    simp_all [eventIndex2, leftEndpointIndex2, jump, value, mul]

def LocalEventProductIdentity
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) : Prop :=
  eventIndex2 Eₑ Hₑ Eₗ Hₗ Eᵣ Hᵣ =
    eventIndex2 Aₑ Bₑ Aₗ Bₗ Aᵣ Bᵣ +
      eventIndex2 Cₑ Dₑ Cₗ Dₗ Cᵣ Dᵣ -
      (productCorrection2 Hₗ Bₗ Dₗ : Int) +
      productCorrection2 Hᵣ Bᵣ Dᵣ

/-- Applying the one-sided table to both orientations around the same formal
event cancels the unrepresented center correction. -/
theorem localProductEventTable
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign)
    (left : LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (right : LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    LocalEventProductIdentity
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have leftIdentity := localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ left
  have rightIdentity := localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ right
  unfold LocalProductIdentity at leftIdentity rightIdentity
  unfold LocalEventProductIdentity eventIndex2
  rw [leftIdentity, rightIdentity]
  ring1

/-- Two applications of the generalized one-sided table give the complete
event identity even when one or more endpoint denominator signs are zero. -/
theorem localProductEventTable_of_endpoint_pairs_nonzero
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign)
    (centerLeft : Aₑ ≠ zero ∨ Bₑ ≠ zero)
    (centerRight : Cₑ ≠ zero ∨ Dₑ ≠ zero)
    (lowerLeft : Aₗ ≠ zero ∨ Bₗ ≠ zero)
    (lowerRight : Cₗ ≠ zero ∨ Dₗ ≠ zero)
    (upperLeft : Aᵣ ≠ zero ∨ Bᵣ ≠ zero)
    (upperRight : Cᵣ ≠ zero ∨ Dᵣ ≠ zero)
    (AStableLower : Stable Aₑ Aₗ) (BStableLower : Stable Bₑ Bₗ)
    (CStableLower : Stable Cₑ Cₗ) (DStableLower : Stable Dₑ Dₗ)
    (EStableLower : Stable Eₑ Eₗ) (HStableLower : Stable Hₑ Hₗ)
    (AStableUpper : Stable Aₑ Aᵣ) (BStableUpper : Stable Bₑ Bᵣ)
    (CStableUpper : Stable Cₑ Cᵣ) (DStableUpper : Stable Dₑ Dᵣ)
    (EStableUpper : Stable Eₑ Eᵣ) (HStableUpper : Stable Hₑ Hᵣ)
    (productCenter : ComplexProductCompatible Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ)
    (productLower : ComplexProductCompatible Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (productUpper : ComplexProductCompatible Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    LocalEventProductIdentity
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have lower := localProductTable_of_target_pairs_nonzero
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
    centerLeft centerRight lowerLeft lowerRight
    AStableLower BStableLower CStableLower DStableLower
    EStableLower HStableLower productCenter productLower
  have upper := localProductTable_of_target_pairs_nonzero
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
    centerLeft centerRight upperLeft upperRight
    AStableUpper BStableUpper CStableUpper DStableUpper
    EStableUpper HStableUpper productCenter productUpper
  unfold LocalProductIdentity at lower upper
  unfold LocalEventProductIdentity eventIndex2
  rw [lower, upper]
  ring1

end FiniteSign

/-- Exact one-sided contribution when the displayed denominator vanishes at
the left endpoint of a resolved cell. -/
def leftEndpointIndex2
    (_P₀ Q₀ P₁ Q₁ : Coordinate) : Int :=
  if Q₀ = 0 then sign (P₁ * Q₁) else 0

theorem finiteSign_leftEndpointIndex2_ofCoordinate
    (P₀ Q₀ P₁ Q₁ : Coordinate) :
    FiniteSign.leftEndpointIndex2
        (FiniteSign.ofCoordinate P₀) (FiniteSign.ofCoordinate Q₀)
        (FiniteSign.ofCoordinate P₁) (FiniteSign.ofCoordinate Q₁) =
      leftEndpointIndex2 P₀ Q₀ P₁ Q₁ := by
  by_cases QZero : Q₀ = 0
  · subst Q₀
    rw [leftEndpointIndex2, if_pos rfl,
      FiniteSign.leftEndpointIndex2,
      FiniteSign.ofCoordinate_zero, if_pos rfl,
      ← FiniteSign.ofCoordinate_mul, FiniteSign.value_ofCoordinate]
  · have signNonzero :
        FiniteSign.ofCoordinate Q₀ ≠ FiniteSign.zero := by
      intro equal
      exact QZero (FiniteSign.ofCoordinate_eq_zero_iff.mp equal)
    rw [leftEndpointIndex2, if_neg QZero,
      FiniteSign.leftEndpointIndex2, if_neg signNonzero]

theorem finiteSign_productCorrection2_ofCoordinate
    (H B D : Coordinate) :
    FiniteSign.productCorrection2
        (FiniteSign.ofCoordinate H) (FiniteSign.ofCoordinate B)
        (FiniteSign.ofCoordinate D) =
      signJump 1 (H * (B * D)) := by
  unfold FiniteSign.productCorrection2
  rw [show FiniteSign.positive = FiniteSign.ofCoordinate 1 by
      exact (FiniteSign.ofCoordinate_of_pos (by decide)).symm,
    ← FiniteSign.ofCoordinate_mul B D,
    ← FiniteSign.ofCoordinate_mul H (B * D),
    FiniteSign.jump_ofCoordinate]

theorem finiteSign_stable_of_eq_zero_or_mul_pos {x₀ x₁ : Coordinate}
    (stable : x₀ = 0 ∨ 0 < x₀ * x₁) :
    FiniteSign.Stable
      (FiniteSign.ofCoordinate x₀) (FiniteSign.ofCoordinate x₁) := by
  rcases stable with rfl | positive
  · exact Or.inl rfl
  · apply Or.inr
    apply FiniteSign.value_injective
    rw [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos positive

theorem finiteSign_complexProductCompatible
    (A B C D : Coordinate) :
    FiniteSign.ComplexProductCompatible
      (FiniteSign.ofCoordinate A) (FiniteSign.ofCoordinate B)
      (FiniteSign.ofCoordinate C) (FiniteSign.ofCoordinate D)
      (FiniteSign.ofCoordinate (A * C - B * D))
      (FiniteSign.ofCoordinate (A * D + B * C)) := by
  constructor
  · change FiniteSign.SumCompatible
      (FiniteSign.mul (FiniteSign.ofCoordinate A)
        (FiniteSign.ofCoordinate C))
      (FiniteSign.neg (FiniteSign.mul (FiniteSign.ofCoordinate B)
        (FiniteSign.ofCoordinate D)))
      (FiniteSign.ofCoordinate (A * C + -(B * D)))
    rw [← FiniteSign.ofCoordinate_mul A C,
      ← FiniteSign.ofCoordinate_mul B D,
      ← FiniteSign.ofCoordinate_neg]
    exact FiniteSign.sumCompatible_ofCoordinate (A * C) (-(B * D))
  · rw [← FiniteSign.ofCoordinate_mul A D,
      ← FiniteSign.ofCoordinate_mul B C]
    exact FiniteSign.sumCompatible_ofCoordinate (A * D) (B * C)

/-- Constructive-coordinate specialization of the local product table. -/
theorem coordinateLocalProductTable
    (A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : Coordinate)
    (factorLeft₀ : A₀ ≠ 0 ∨ B₀ ≠ 0)
    (factorRight₀ : C₀ ≠ 0 ∨ D₀ ≠ 0)
    (B₁Nonzero : B₁ ≠ 0) (D₁Nonzero : D₁ ≠ 0)
    (H₁Nonzero : A₁ * D₁ + B₁ * C₁ ≠ 0)
    (AStable : A₀ = 0 ∨ 0 < A₀ * A₁)
    (BStable : B₀ = 0 ∨ 0 < B₀ * B₁)
    (CStable : C₀ = 0 ∨ 0 < C₀ * C₁)
    (DStable : D₀ = 0 ∨ 0 < D₀ * D₁)
    (EStable : A₀ * C₀ - B₀ * D₀ = 0 ∨
      0 < (A₀ * C₀ - B₀ * D₀) * (A₁ * C₁ - B₁ * D₁))
    (HStable : A₀ * D₀ + B₀ * C₀ = 0 ∨
      0 < (A₀ * D₀ + B₀ * C₀) * (A₁ * D₁ + B₁ * C₁)) :
    leftEndpointIndex2
        (A₀ * C₀ - B₀ * D₀) (A₀ * D₀ + B₀ * C₀)
        (A₁ * C₁ - B₁ * D₁) (A₁ * D₁ + B₁ * C₁) =
      leftEndpointIndex2 A₀ B₀ A₁ B₁ +
        leftEndpointIndex2 C₀ D₀ C₁ D₁ -
        (signJump 1 ((A₀ * D₀ + B₀ * C₀) * (B₀ * D₀)) : Int) +
        signJump 1 ((A₁ * D₁ + B₁ * C₁) * (B₁ * D₁)) := by
  let A₀s := FiniteSign.ofCoordinate A₀
  let B₀s := FiniteSign.ofCoordinate B₀
  let C₀s := FiniteSign.ofCoordinate C₀
  let D₀s := FiniteSign.ofCoordinate D₀
  let E₀s := FiniteSign.ofCoordinate (A₀ * C₀ - B₀ * D₀)
  let H₀s := FiniteSign.ofCoordinate (A₀ * D₀ + B₀ * C₀)
  let A₁s := FiniteSign.ofCoordinate A₁
  let B₁s := FiniteSign.ofCoordinate B₁
  let C₁s := FiniteSign.ofCoordinate C₁
  let D₁s := FiniteSign.ofCoordinate D₁
  let E₁s := FiniteSign.ofCoordinate (A₁ * C₁ - B₁ * D₁)
  let H₁s := FiniteSign.ofCoordinate (A₁ * D₁ + B₁ * C₁)
  have admissible : FiniteSign.LocalProductAdmissible
      A₀s B₀s C₀s D₀s E₀s H₀s A₁s B₁s C₁s D₁s E₁s H₁s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [A₀s, B₀s, FiniteSign.ofCoordinate_ne_zero_iff]
        using factorLeft₀
    · simpa only [C₀s, D₀s, FiniteSign.ofCoordinate_ne_zero_iff]
        using factorRight₀
    · simpa only [B₁s, FiniteSign.ofCoordinate_ne_zero_iff]
        using B₁Nonzero
    · simpa only [D₁s, FiniteSign.ofCoordinate_ne_zero_iff]
        using D₁Nonzero
    · simpa only [H₁s, FiniteSign.ofCoordinate_ne_zero_iff]
        using H₁Nonzero
    · exact finiteSign_stable_of_eq_zero_or_mul_pos AStable
    · exact finiteSign_stable_of_eq_zero_or_mul_pos BStable
    · exact finiteSign_stable_of_eq_zero_or_mul_pos CStable
    · exact finiteSign_stable_of_eq_zero_or_mul_pos DStable
    · exact finiteSign_stable_of_eq_zero_or_mul_pos EStable
    · exact finiteSign_stable_of_eq_zero_or_mul_pos HStable
    · exact finiteSign_complexProductCompatible A₀ B₀ C₀ D₀
    · exact finiteSign_complexProductCompatible A₁ B₁ C₁ D₁
  have table := FiniteSign.localProductTable
    A₀s B₀s C₀s D₀s E₀s H₀s A₁s B₁s C₁s D₁s E₁s H₁s admissible
  dsimp only [A₀s, B₀s, C₀s, D₀s, E₀s, H₀s,
    A₁s, B₁s, C₁s, D₁s, E₁s, H₁s] at table
  simpa only [FiniteSign.LocalProductIdentity,
    finiteSign_leftEndpointIndex2_ofCoordinate,
    finiteSign_productCorrection2_ofCoordinate] using table

end RFAP.CauchyProductSigns
