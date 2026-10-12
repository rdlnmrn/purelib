module
public import Purelib.Algebra.Field.ExplicitField
-- Exposed common-root formulas retain their explicit successor certificates.
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
public section

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

namespace Purelib.Polynomial.Quadratic.CommonRoot.Centered

variable {K : Type*} [ExplicitField K]

/-- Two normal-form quadratic equations have a displayed common solution. -/
@[expose] def QuadraticsCompatible (p₁ q₁ p₂ q₂ : K) : Prop :=
  ∃ x, (x - p₁) ^ 2 = q₁ ∧ (x - p₂) ^ 2 = q₂

/-- The root-free polynomial compatibility condition for two centered quadratic equations. -/
@[expose] def quadraticCompatibilityIdentity (p₁ q₁ p₂ q₂ : K) :
  Prop :=
  ((p₁ - p₂) ^ 2 - (q₁ + q₂)) ^ 2 = 4 * q₁ * q₂

open Purelib.Polynomial in
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

/-- The explicit common-root candidate for two centered quadratic equations with distinct centers.

The formula uses division by two and by twice the center difference; its correctness lemmas retain their nonzero
witnesses. -/
@[expose] def quadraticCommonRoot (p₁ q₁ p₂ q₂ : K) : K :=
  (p₁ + p₂) / 2 - (q₁ - q₂) / (2 * (p₁ - p₂))

open Purelib.Polynomial
/-- The centered common-root candidate equals its denominator-cleared quotient when two and the center difference are
nonzero. -/
private theorem quadraticCommonRoot_alternate
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂) :
    quadraticCommonRoot p₁ q₁ p₂ q₂ =
      (p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂) / (2 * (p₁ - p₂)) := by
  have differenceNonzero : p₁ - p₂ ≠ 0 := ExplicitField.sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : (2 : K) * (p₁ - p₂) ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  have denominatorCancel :
      (2 * (p₁ - p₂)) * (2 * (p₁ - p₂))⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  have inverseRewrite :
      (2 : K)⁻¹ = (p₁ - p₂) * (2 * (p₁ - p₂))⁻¹ := by
    calc
      (2 : K)⁻¹ = 1 * 2⁻¹ := by rw [one_mul]
      _ = ((2 * (p₁ - p₂)) * (2 * (p₁ - p₂))⁻¹) * 2⁻¹ := by
        rw [denominatorCancel]
      _ = ((p₁ - p₂) * (2 * (p₁ - p₂))⁻¹) * (2 * 2⁻¹) := by
        ring1
      _ = (p₁ - p₂) * (2 * (p₁ - p₂))⁻¹ := by rw [twoCancel, mul_one]
  simp only [quadraticCommonRoot, ExplicitField.div_eq_mul_inv]
  rw [inverseRewrite]
  ring1

/-- Under the compatibility identity and nonzero denominators, the explicit candidate solves the first centered
equation. -/
private theorem quadraticCommonRoot_first
    {p₁ q₁ p₂ q₂ : K}
    (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : p₁ ≠ p₂)
    (identity : quadraticCompatibilityIdentity p₁ q₁ p₂ q₂) :
    (quadraticCommonRoot p₁ q₁ p₂ q₂ - p₁) ^ 2 = q₁ := by
  let denominator : K := 2 * (p₁ - p₂)
  let numerator : K := p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂
  have differenceNonzero : p₁ - p₂ ≠ 0 := ExplicitField.sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
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
  rw [ExplicitField.div_eq_mul_inv]
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

/-- Under the compatibility identity and nonzero denominators, the explicit candidate solves the second centered
equation. -/
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
    simp only [quadraticCommonRoot, ExplicitField.div_eq_mul_inv]
    have denominatorNegation :
        (2 : K) * (p₂ - p₁) = -(2 * (p₁ - p₂)) := by ring1
    rw [denominatorNegation, ExplicitField.inv_neg]
    ring1
  rwa [rootSymmetry] at reversedRoot

/-- For distinct centers and nonzero two, the polynomial compatibility condition is equivalent to a displayed common
root. -/
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
  have differenceNonzero : p₁ - p₂ ≠ 0 := ExplicitField.sub_ne_zero_of_ne centresDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have cleared :
      denominator * x = p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂ := by
    unfold denominator
    calc
      2 * (p₁ - p₂) * x =
          p₁ ^ 2 - p₂ ^ 2 - (x - p₁) ^ 2 + (x - p₂) ^ 2 := by ring1
      _ = p₁ ^ 2 - p₂ ^ 2 - q₁ + q₂ := by rw [firstEquation, secondEquation]
  rw [quadraticCommonRoot_alternate twoNonzero centresDistinct]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [← cleared]
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
    _ = denominator * x * denominator⁻¹ := by ring1

/-- Centered equations with the same center are compatible exactly when their targets agree and the common equation has
a displayed solution. -/
theorem quadraticCompatibility_same_centre (p q₁ q₂ : K) :
    QuadraticsCompatible p q₁ p q₂ ↔
      q₁ = q₂ ∧ ∃ x, (x - p) ^ 2 = q₁ := by
  constructor
  · rintro ⟨x, firstEquation, secondEquation⟩
    exact ⟨firstEquation.symm.trans secondEquation, ⟨x, firstEquation⟩⟩
  · rintro ⟨rfl, x, equation⟩
    exact ⟨x, equation, equation⟩
end Purelib.Polynomial.Quadratic.CommonRoot.Centered

end
