module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Inverse.Subtraction

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
public import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.Calculus.Secant.Gaussian.Arithmetic

/-! ## Exact compositional secant identities -/

open Purelib.Data
/-- The product-rule kernel factors a product difference through the displayed argument difference.

Each input difference already factors through x minus y with its supplied kernel. Their product difference has kernel
deltaF times gX plus fY times deltaG, without requiring x and y to be distinct. -/
theorem product_kernel_factor
    (x y fX fY gX gY deltaF deltaG : Canonical)
    (fFactor : fX - fY = (x - y) * deltaF)
    (gFactor : gX - gY = (x - y) * deltaG) :
    fX * gX - fY * gY =
      (x - y) * (deltaF * gX + fY * deltaG) := by
  calc
    fX * gX - fY * gY =
        (fX - fY) * gX + fY * (gX - gY) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
        ring1
    _ = ((x - y) * deltaF) * gX +
        fY * ((x - y) * deltaG) := by rw [fFactor, gFactor]
    _ = (x - y) * (deltaF * gX + fY * deltaG) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
        ring1

/-- The product of inner and outer kernels factors the composite difference.

The inner difference factors through x minus y, and the outer difference factors through that inner difference.
Multiplying the two supplied kernels gives the displayed composite identity. -/
theorem composition_kernel_factor
    (x y innerX innerY outerX outerY deltaInner deltaOuter : Canonical)
    (innerFactor : innerX - innerY = (x - y) * deltaInner)
    (outerFactor : outerX - outerY =
      (innerX - innerY) * deltaOuter) :
    outerX - outerY = (x - y) * (deltaInner * deltaOuter) := by
  calc
    outerX - outerY = (innerX - innerY) * deltaOuter := outerFactor
    _ = ((x - y) * deltaInner) * deltaOuter := by rw [innerFactor]
    _ = (x - y) * (deltaInner * deltaOuter) :=
      Gaussian.Basic.mul_assoc _ _ _

/-- The reciprocal-rule kernel factors the inverse difference at two nonzero values.

The original difference factors through x minus y. Negating its kernel times the product of the two inverses gives the
reciprocal kernel, with no nonzero assumption on x minus y. -/
theorem reciprocal_kernel_factor
    (x y fX fY deltaF : Canonical)
    (fXNonzero : fX ≠ 0) (fYNonzero : fY ≠ 0)
    (factor : fX - fY = (x - y) * deltaF) :
    fX⁻¹ - fY⁻¹ =
      (x - y) * (-(deltaF * (fX⁻¹ * fY⁻¹))) := by
  calc
    fX⁻¹ - fY⁻¹ =
        -(fX - fY) * (fX⁻¹ * fY⁻¹) :=
      Gaussian.Inverse.Subtraction.inverse_sub_inverse fXNonzero fYNonzero
    _ = (-((x - y) * deltaF)) * (fX⁻¹ * fY⁻¹) := by
      rw [factor]
    _ = (x - y) * (-(deltaF * (fX⁻¹ * fY⁻¹))) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
        ring1

end Purelib.Calculus.Secant.Gaussian.Arithmetic

end
