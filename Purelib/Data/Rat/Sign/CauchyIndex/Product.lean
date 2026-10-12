module

public import Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.ComplexProduct
import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.CauchyIndex.Product
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Rational readback of the one-sided Cauchy product table

The retained nonzero factor pairs and stable coordinates satisfy the formal
product table. Scalar sign readbacks give its exact rational-coordinate form.
-/

namespace Purelib.Data.Rat.Sign.CauchyIndex.Product

open Purelib.Data.Rat
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- Prove the local doubled-index product identity from finite endpoint nonvanishing and sign stability data.

The endpoint pairs retain nonvanishing evidence, the terminal denominators are nonzero, and each start/end component
satisfies the stated zero-or-positive-product stability condition. Their finite sign table yields the product index as
the sum of factor indices corrected by the two endpoint jumps. -/
public theorem coordinateLocalProductTable
    (A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : Fraction.Rational)
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
    Sign.CauchyIndex.Endpoint.leftEndpointIndex2
        (A₀ * C₀ - B₀ * D₀) (A₀ * D₀ + B₀ * C₀)
        (A₁ * C₁ - B₁ * D₁) (A₁ * D₁ + B₁ * C₁) =
      Sign.CauchyIndex.Endpoint.leftEndpointIndex2 A₀ B₀ A₁ B₁ +
        Sign.CauchyIndex.Endpoint.leftEndpointIndex2 C₀ D₀ C₁ D₁ -
        (Sign.Jump.signJump 1 ((A₀ * D₀ + B₀ * C₀) * (B₀ * D₀)) : Int) +
        Sign.Jump.signJump 1 ((A₁ * D₁ + B₁ * C₁) * (B₁ * D₁)) := by
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
    · exact factorLeft₀.elim
        (fun nonzero => Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
        (fun nonzero => Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
    · exact factorRight₀.elim
        (fun nonzero => Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
        (fun nonzero => Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
    · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr B₁Nonzero
    · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr D₁Nonzero
    · exact FiniteSign.ofCoordinate_ne_zero_iff.mpr H₁Nonzero
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos AStable
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos BStable
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos CStable
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos DStable
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos EStable
    · exact Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos HStable
    · exact Sign.ComplexProduct.sign_complexProductCompatible A₀ B₀ C₀ D₀
    · exact Sign.ComplexProduct.sign_complexProductCompatible A₁ B₁ C₁ D₁
  have table := FiniteSign.localProductTable
    A₀s B₀s C₀s D₀s E₀s H₀s A₁s B₁s C₁s D₁s E₁s H₁s admissible
  dsimp only [A₀s, B₀s, C₀s, D₀s, E₀s, H₀s,
    A₁s, B₁s, C₁s, D₁s, E₁s, H₁s] at table
  unfold FiniteSign.LocalProductIdentity at table
  rewrite [Sign.CauchyIndex.Endpoint.sign_leftEndpointIndex2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_leftEndpointIndex2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_leftEndpointIndex2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate,
    Sign.CauchyIndex.Endpoint.sign_productCorrection2_ofCoordinate] at table
  exact table

end Purelib.Data.Rat.Sign.CauchyIndex.Product
