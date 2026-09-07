import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ExplicitField
import mathlib.Tactic.QuotientFreeRing

/-!
# Divine Proportions, §2.6: pairs of quadratic equations

This file begins the numbered theorem sequence in *Divine Proportions*.  The
source's theorem has a genuine degenerate-case omission: when the two centres
are equal, its displayed polynomial condition merely says that the two
equations are identical; it does not prove that the common equation has a
solution in the field.  The exact arbitrary-field result is therefore split
into the distinct-centre theorem proved by the source's calculation and a
separate same-centre characterization.

Everything is parameterized by the project's explicit, choice-free field-law
interface.  The only characteristic assumption used below is the displayed
witness that `2` is nonzero.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem sub_ne_zero_of_ne {a b : K} (different : a ≠ b) : a - b ≠ 0 := by
  intro differenceZero
  apply different
  calc
    a = (a - b) + b := by ring1
    _ = 0 + b := by rw [differenceZero]
    _ = b := zero_add b

/-- Two normal-form quadratic equations have a displayed common solution. -/
def QuadraticsCompatible (p₁ q₁ p₂ q₂ : K) : Prop :=
  ∃ x, (x - p₁) ^ 2 = q₁ ∧ (x - p₂) ^ 2 = q₂

/-- The polynomial compatibility expression from Theorem 1. -/
def quadraticCompatibilityIdentity (p₁ q₁ p₂ q₂ : K) : Prop :=
  ((p₁ - p₂) ^ 2 - (q₁ + q₂)) ^ 2 = 4 * q₁ * q₂

/-- Any common solution implies the polynomial identity, including in the
degenerate same-centre case. -/
theorem quadraticCompatibilityIdentity_of_compatible
    {p₁ q₁ p₂ q₂ : K}
    (compatible : QuadraticsCompatible p₁ q₁ p₂ q₂) :
    quadraticCompatibilityIdentity p₁ q₁ p₂ q₂ := by
  rcases compatible with ⟨x, firstEquation, secondEquation⟩
  unfold quadraticCompatibilityIdentity
  rw [← firstEquation, ← secondEquation]
  ring1

/-- Candidate common root in the nondegenerate case, equation (2.2) of the
book. -/
def quadraticCommonRoot (p₁ q₁ p₂ q₂ : K) : K :=
  (p₁ + p₂) / 2 - (q₁ - q₂) / (2 * (p₁ - p₂))

private theorem quadraticCommonRoot_alternate
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂) :
    quadraticCommonRoot p₁ q₁ p₂ q₂ =
      (p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂) / (2 * (p₁ - p₂)) := by
  have differenceNonzero : p₁ - p₂ ≠ 0 := sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : (2 : K) * (p₁ - p₂) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have denominatorCancel :
      (2 * (p₁ - p₂)) * (2 * (p₁ - p₂))⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  have inverseRewrite :
      (2 : K)⁻¹ = (p₁ - p₂) * (2 * (p₁ - p₂))⁻¹ := by
    calc
      (2 : K)⁻¹ = 1 * 2⁻¹ := by rw [one_mul]
      _ = ((2 * (p₁ - p₂)) * (2 * (p₁ - p₂))⁻¹) * 2⁻¹ := by
        rw [denominatorCancel]
      _ = ((p₁ - p₂) * (2 * (p₁ - p₂))⁻¹) * (2 * 2⁻¹) := by
        ring1
      _ = (p₁ - p₂) * (2 * (p₁ - p₂))⁻¹ := by rw [twoCancel, mul_one]
  simp only [quadraticCommonRoot, RFAP.ExplicitField.div_eq_mul_inv]
  rw [inverseRewrite]
  ring1

private theorem quadraticCommonRoot_first
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂)
    (identity : quadraticCompatibilityIdentity p₁ q₁ p₂ q₂) :
    (quadraticCommonRoot p₁ q₁ p₂ q₂ - p₁) ^ 2 = q₁ := by
  let denominator : K := 2 * (p₁ - p₂)
  let numerator : K := p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂
  have differenceNonzero : p₁ - p₂ ≠ 0 := sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have polynomialIdentity :
      (numerator - p₁ * denominator) ^ 2 = q₁ * denominator ^ 2 := by
    unfold numerator denominator
    unfold quadraticCompatibilityIdentity at identity
    calc
      (p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂ - p₁ * (2 * (p₁ - p₂))) ^ 2 =
          q₁ * (2 * (p₁ - p₂)) ^ 2 +
            ((((p₁ - p₂) ^ 2 - (q₁ + q₂)) ^ 2) - 4 * q₁ * q₂) := by
        ring1
      _ = q₁ * (2 * (p₁ - p₂)) ^ 2 := by rw [identity]; ring1
  rw [quadraticCommonRoot_alternate twoNonzero centresDistinct]
  change (numerator / denominator - p₁) ^ 2 = q₁
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  have rewriteDifference :
      numerator * denominator⁻¹ - p₁ =
        (numerator - p₁ * denominator) * denominator⁻¹ := by
    calc
      numerator * denominator⁻¹ - p₁ =
          numerator * denominator⁻¹ - p₁ * 1 := by ring1
      _ = numerator * denominator⁻¹ -
          p₁ * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = (numerator - p₁ * denominator) * denominator⁻¹ := by ring1
  rw [rewriteDifference]
  calc
    ((numerator - p₁ * denominator) * denominator⁻¹) ^ 2 =
        (numerator - p₁ * denominator) ^ 2 * denominator⁻¹ ^ 2 := by ring1
    _ = q₁ * denominator ^ 2 * denominator⁻¹ ^ 2 := by rw [polynomialIdentity]
    _ =
        q₁ * (denominator * denominator⁻¹) ^ 2 := by ring1
    _ = q₁ := by rw [denominatorCancel]; ring1

private theorem quadraticCommonRoot_second
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂)
    (identity : quadraticCompatibilityIdentity p₁ q₁ p₂ q₂) :
    (quadraticCommonRoot p₁ q₁ p₂ q₂ - p₂) ^ 2 = q₂ := by
  have reversedCentres : p₂ ≠ p₁ := Ne.symm centresDistinct
  have reversedIdentity : quadraticCompatibilityIdentity p₂ q₂ p₁ q₁ := by
    unfold quadraticCompatibilityIdentity at identity ⊢
    calc
      ((p₂ - p₁) ^ 2 - (q₂ + q₁)) ^ 2 =
          ((p₁ - p₂) ^ 2 - (q₁ + q₂)) ^ 2 := by ring1
      _ = 4 * q₁ * q₂ := identity
      _ = 4 * q₂ * q₁ := by ring1
  have reversedRoot :=
    quadraticCommonRoot_first twoNonzero reversedCentres reversedIdentity
  have rootSymmetry :
      quadraticCommonRoot p₂ q₂ p₁ q₁ =
        quadraticCommonRoot p₁ q₁ p₂ q₂ := by
    simp only [quadraticCommonRoot, RFAP.ExplicitField.div_eq_mul_inv]
    have denominatorNegation :
        (2 : K) * (p₂ - p₁) = -(2 * (p₁ - p₂)) := by ring1
    rw [denominatorNegation, RFAP.ExplicitField.inv_neg]
    ring1
  rwa [rootSymmetry] at reversedRoot

/-- Theorem 1 (Quadratic compatibility), in the nondegenerate case where the
source's proof and formula are valid over an arbitrary field. -/
theorem quadraticCompatibility_of_distinct_centres
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂) :
    QuadraticsCompatible p₁ q₁ p₂ q₂ ↔
      quadraticCompatibilityIdentity p₁ q₁ p₂ q₂ := by
  constructor
  · exact quadraticCompatibilityIdentity_of_compatible
  · intro identity
    exact ⟨quadraticCommonRoot p₁ q₁ p₂ q₂,
      quadraticCommonRoot_first twoNonzero centresDistinct identity,
      quadraticCommonRoot_second twoNonzero centresDistinct identity⟩

/-- The common solution in the distinct-centre case is unique. -/
theorem quadraticCommonRoot_unique
    {p₁ q₁ p₂ q₂ x : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂)
    (firstEquation : (x - p₁) ^ 2 = q₁)
    (secondEquation : (x - p₂) ^ 2 = q₂) :
    x = quadraticCommonRoot p₁ q₁ p₂ q₂ := by
  let denominator : K := 2 * (p₁ - p₂)
  have differenceNonzero : p₁ - p₂ ≠ 0 := sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have cleared :
      denominator * x = p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂ := by
    unfold denominator
    calc
      2 * (p₁ - p₂) * x =
          p₁ ^ 2 - p₂ ^ 2 - (x - p₁) ^ 2 + (x - p₂) ^ 2 := by ring1
      _ = p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂ := by rw [firstEquation, secondEquation]
  rw [quadraticCommonRoot_alternate twoNonzero centresDistinct]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [← cleared]
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
    _ = denominator * x * denominator⁻¹ := by ring1

/-- Exact characterization omitted by the book when the two centres coincide.
The common equation must itself have a displayed solution. -/
theorem quadraticCompatibility_same_centre (p q₁ q₂ : K) :
    QuadraticsCompatible p q₁ p q₂ ↔
      q₁ = q₂ ∧ ∃ x, (x - p) ^ 2 = q₁ := by
  constructor
  · rintro ⟨x, firstEquation, secondEquation⟩
    exact ⟨firstEquation.symm.trans secondEquation, ⟨x, firstEquation⟩⟩
  · rintro ⟨rfl, x, equation⟩
    exact ⟨x, equation, equation⟩

/-- Example 2.19: `7` is the displayed common solution of the two equations.
The calculation is valid in every commutative ring. -/
theorem example_2_19 (K : Type*) [CommRing K] :
    ((7 : K) - 4) ^ 2 = 9 ∧ ((7 : K) - 6) ^ 2 = 1 := by
  constructor <;> ring1

end DivineProportions
