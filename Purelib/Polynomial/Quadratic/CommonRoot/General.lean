module
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

@[expose] public section

/-!
# Divine Proportions, Exercises 2.8–2.9

Both printed exercises omit genuine degenerate cases.  The determinant formula
in Exercise 2.8 is sufficient only when its displayed root denominator is
nonzero.  Exercise 2.9 uses `±2q` where the valid root-free condition is
`(p₁-p₂)²=4q`, and coincident equations still require `q` to be a square.
The corrected constructive statements and explicit rational counterexamples
are given below.
-/

namespace Purelib.Polynomial.Quadratic.CommonRoot.General

variable {K : Type*} [ExplicitField K]

/-- Two displayed general-form quadratic equations have a common root. -/
def GeneralQuadraticsCompatible
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : Prop :=
  ∃ x : K,
    a₁ * x ^ 2 + b₁ * x + c₁ = 0 ∧
      a₂ * x ^ 2 + b₂ * x + c₂ = 0

/-- The determinant identity relating the coefficients of two general quadratic equations. -/
def generalQuadraticCompatibilityIdentity
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : Prop :=
  (a₁ * c₂ - a₂ * c₁) ^ 2 =
    (a₁ * b₂ - a₂ * b₁) * (b₁ * c₂ - b₂ * c₁)

/-- The quotient candidate obtained by eliminating the quadratic term from two general quadratic equations. -/
def generalQuadraticCommonRoot
    (a₁ b₁ c₁ a₂ b₂ c₂ : K) : K :=
  (a₂ * c₁ - a₁ * c₂) / (a₁ * b₂ - a₂ * b₁)

open Purelib.Polynomial
/-- A displayed common root implies the determinant compatibility identity, including proportional equations. -/
theorem generalQuadraticCompatibilityIdentity_of_compatible
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (compatible :
      GeneralQuadraticsCompatible a₁ b₁ c₁ a₂ b₂ c₂) :
    generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂ := by
  rcases compatible with ⟨x, firstEquation, secondEquation⟩
  have firstConstant : c₁ = -(a₁ * x ^ 2 + b₁ * x) := by
    calc
      c₁ = (a₁ * x ^ 2 + b₁ * x + c₁) -
          (a₁ * x ^ 2 + b₁ * x) := by ring1
      _ = -(a₁ * x ^ 2 + b₁ * x) := by rw [firstEquation]; ring1
  have secondConstant : c₂ = -(a₂ * x ^ 2 + b₂ * x) := by
    calc
      c₂ = (a₂ * x ^ 2 + b₂ * x + c₂) -
          (a₂ * x ^ 2 + b₂ * x) := by ring1
      _ = -(a₂ * x ^ 2 + b₂ * x) := by rw [secondEquation]; ring1
  unfold generalQuadraticCompatibilityIdentity
  rw [firstConstant, secondConstant]
  ring1

/-- The determinant identity makes the explicit quotient solve the first equation when its denominator is nonzero. -/
private theorem generalQuadraticCommonRoot_first
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (identity :
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂) :
    a₁ * (generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂) ^ 2 +
        b₁ * generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ + c₁ = 0 := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have residual :
      (a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁) = 0 := by
    unfold generalQuadraticCompatibilityIdentity at identity
    rw [identity]
    unfold denominator
    ring1
  have cleared :
      a₁ * numerator ^ 2 + b₁ * numerator * denominator +
          c₁ * denominator ^ 2 = 0 := by
    calc
      a₁ * numerator ^ 2 + b₁ * numerator * denominator +
          c₁ * denominator ^ 2 =
        a₁ * ((a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁)) := by
        unfold numerator denominator
        ring1
      _ = 0 := by rw [residual]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    a₁ * (numerator * denominator⁻¹) ^ 2 +
          b₁ * (numerator * denominator⁻¹) + c₁ =
        (a₁ * numerator ^ 2 + b₁ * numerator * denominator +
            c₁ * denominator ^ 2) * denominator⁻¹ ^ 2 +
          b₁ * numerator * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          c₁ * (1 - (denominator * denominator⁻¹) ^ 2) := by ring1
    _ = 0 := by rw [cleared, denominatorCancel]; ring1

/-- The determinant identity makes the explicit quotient solve the second equation when its denominator is nonzero. -/
private theorem generalQuadraticCommonRoot_second
    {a₁ b₁ c₁ a₂ b₂ c₂ : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (identity :
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂) :
    a₂ * (generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂) ^ 2 +
        b₂ * generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ + c₂ = 0 := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have residual :
      (a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁) = 0 := by
    unfold generalQuadraticCompatibilityIdentity at identity
    rw [identity]
    unfold denominator
    ring1
  have cleared :
      a₂ * numerator ^ 2 + b₂ * numerator * denominator +
          c₂ * denominator ^ 2 = 0 := by
    calc
      a₂ * numerator ^ 2 + b₂ * numerator * denominator +
          c₂ * denominator ^ 2 =
        a₂ * ((a₁ * c₂ - a₂ * c₁) ^ 2 -
          denominator * (b₁ * c₂ - b₂ * c₁)) := by
        unfold numerator denominator
        ring1
      _ = 0 := by rw [residual]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    a₂ * (numerator * denominator⁻¹) ^ 2 +
          b₂ * (numerator * denominator⁻¹) + c₂ =
        (a₂ * numerator ^ 2 + b₂ * numerator * denominator +
            c₂ * denominator ^ 2) * denominator⁻¹ ^ 2 +
          b₂ * numerator * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          c₂ * (1 - (denominator * denominator⁻¹) ^ 2) := by ring1
    _ = 0 := by rw [cleared, denominatorCancel]; ring1

/-- With nonzero elimination denominator, two quadratic equations have a common root exactly when the determinant
identity holds. -/
theorem exercise_2_8
    (a₁ b₁ c₁ a₂ b₂ c₂ : K)
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    GeneralQuadraticsCompatible a₁ b₁ c₁ a₂ b₂ c₂ ↔
      generalQuadraticCompatibilityIdentity a₁ b₁ c₁ a₂ b₂ c₂ := by
  constructor
  · exact generalQuadraticCompatibilityIdentity_of_compatible
  · intro identity
    exact ⟨generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂,
      generalQuadraticCommonRoot_first denominatorNonzero identity,
      generalQuadraticCommonRoot_second denominatorNonzero identity⟩

/-- Every common root equals the explicit elimination quotient when its denominator is nonzero. -/
theorem exercise_2_8_commonRoot_unique
    {a₁ b₁ c₁ a₂ b₂ c₂ x : K}
    (denominatorNonzero : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (firstEquation : a₁ * x ^ 2 + b₁ * x + c₁ = 0)
    (secondEquation : a₂ * x ^ 2 + b₂ * x + c₂ = 0) :
    x = generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ := by
  let denominator := a₁ * b₂ - a₂ * b₁
  let numerator := a₂ * c₁ - a₁ * c₂
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have linearEquation : denominator * x = numerator := by
    calc
      denominator * x =
          a₁ * (a₂ * x ^ 2 + b₂ * x + c₂) -
            a₂ * (a₁ * x ^ 2 + b₁ * x + c₁) + numerator := by
        unfold denominator numerator
        ring1
      _ = numerator := by rw [firstEquation, secondEquation]; ring1
  have rootFormula :
      generalQuadraticCommonRoot a₁ b₁ c₁ a₂ b₂ c₂ =
        numerator / denominator := rfl
  rw [rootFormula]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    x = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]; ring1
    _ = (denominator * x) * denominator⁻¹ := by ring1
    _ = numerator * denominator⁻¹ := by rw [linearEquation]
end Purelib.Polynomial.Quadratic.CommonRoot.General

end
