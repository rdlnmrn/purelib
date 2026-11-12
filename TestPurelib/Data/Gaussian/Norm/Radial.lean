module

import Purelib.Data.Gaussian.Norm.Radial
import Purelib.Data.Rat.Fraction.Cast

/-!
# Actual nonzero radial perturbations

The requests are fixed before either endpoint. Both examples change the
real and imaginary coordinates, pay the actual positive squared displacement
using different inverse norms, and apply the general radial transfer laws.
-/

namespace TestPurelib.Data.Gaussian.Norm.Radial

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat

/-- Fixed unit endpoint bounds and inverse quadrance two preserve an inside half-width collar. -/
private def inside := Norm.Radial.Request.prepare 1 1 2 (1/2)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The inside request retains the independently calculated coefficient, denominator, cap and endpoints. -/
private theorem inside_data :
    inside.coefficient = 8 ∧ inside.denominator = 72 ∧ inside.cap = 1/288 ∧
      inside.halfWidth = 1/4 ∧ inside.ceiling = 3/4 ∧ inside.floor = 5/4 := by decide +kernel

/-- The actual inside perturbation is nonzero and consumes exactly its displayed positive residual payment. -/
private theorem inside_displacement :
    Norm.Basic.normSq ((⟨1/2, 0⟩ : Canonical) - ⟨51/100, 1/100⟩) = 1/5000 ∧
      (0 : Rational) < 1/10000 ∧ (1/10000 : Rational) * 2 = 1/5000 := by decide +kernel

/-- The same fixed request transfers the actual inside collar to the changed nonreal read root. -/
private theorem inside_transfer :
    Norm.Basic.normSq (⟨51/100, 1/100⟩ : Canonical) ≤ inside.ceiling :=
  inside.inside ⟨1/2, 0⟩ ⟨51/100, 1/100⟩ (residual := 1/10000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Independent scalar computation checks the actual read quadrance and the retained ceiling. -/
private theorem inside_readback :
    Norm.Basic.normSq (⟨51/100, 1/100⟩ : Canonical) = 1301/5000 ∧
      Norm.Basic.normSq (⟨51/100, 1/100⟩ : Canonical) ≤ 3/4 := by decide +kernel

/-- Fixed quadrance bounds four and inverse quadrance one half preserve an outside unit-width collar. -/
private def outside := Norm.Radial.Request.prepare 4 4 (1/2) 1
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The outside request has independently calculated coefficient eight and residual cap one over seventy-two. -/
private theorem outside_data :
    outside.coefficient = 8 ∧ outside.denominator = 72 ∧ outside.cap = 1/72 ∧
      outside.halfWidth = 1/2 ∧ outside.ceiling = 1/2 ∧ outside.floor = 3/2 := by decide +kernel

/-- The actual outside perturbation is nonzero and consumes exactly its displayed positive residual payment. -/
private theorem outside_displacement :
    Norm.Basic.normSq ((⟨2, 0⟩ : Canonical) - ⟨199/100, 1/100⟩) = 1/5000 ∧
      (0 : Rational) < 1/2500 ∧ (1/2500 : Rational) * (1/2) = 1/5000 := by decide +kernel

/-- The same fixed request transfers the actual outside collar to the changed nonreal read root. -/
private theorem outside_transfer :
    outside.floor ≤ Norm.Basic.normSq (⟨199/100, 1/100⟩ : Canonical) :=
  outside.outside ⟨2, 0⟩ ⟨199/100, 1/100⟩ (residual := 1/2500)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The exact outside read quadrance and retained floor agree with the paid transfer. -/
private theorem outside_readback :
    Norm.Basic.normSq (⟨199/100, 1/100⟩ : Canonical) = 19801/5000 ∧
      3/2 ≤ Norm.Basic.normSq (⟨199/100, 1/100⟩ : Canonical) := by
  constructor
  · change _ = ((19801 : Nat) : Rational) / ((5000 : Nat) : Rational)
    rewrite [Fraction.Cast.natCast_eq_fromInt 19801, Fraction.Cast.natCast_eq_fromInt 5000]
    decide +kernel
  · have bound := outside_transfer
    rewrite [outside_data.2.2.2.2.2] at bound
    exact bound

/-- A zero inverse norm still gives a positive fixed cap and requires no exceptional constructor branch. -/
private theorem zero_inverse_cap :
    (Norm.Radial.Request.prepare 0 0 0 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).cap = 1/2 := by decide +kernel

end TestPurelib.Data.Gaussian.Norm.Radial
