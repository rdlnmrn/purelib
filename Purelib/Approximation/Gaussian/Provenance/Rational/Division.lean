module

public import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

/-!
# Exact rational provenance for actual prepared division

The original denominator and its supplied preparation determine the numerical
reciprocal. A product-to-unit certificate compares that actual program to the
exact inverse coefficient; multiplication then transports numerator evidence.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division
open Purelib.Algebra.Field (ExplicitField)

/-- Propagate exact inverse data through the same supplied numerical denominator preparation. -/
@[noinline, nospecialize] def reciprocal {channel : CoherentNamed} (sidecar : RationalSidecar channel)
    (prepared : Prepared channel) (nonzero : sidecar.value ≠ 0) :
    RationalSidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)) := by
  let value := 1 / sidecar.value
  let inverse := CoherentNamed.Coherence.exact value
  let product := sidecar.mul (RationalSidecar.exact value)
  have value_eq : product.value = 1 := by
    change sidecar.value * (1 / sidecar.value) = 1
    rewrite [_root_.mul_comm]
    exact ExplicitField.div_mul_cancel 1 nonzero
  have identity := product.equivalent
  rewrite [value_eq] at identity
  exact ⟨value, prepared.reciprocal_equivalent_of_product inverse identity⟩

/-- The reciprocal's exact reading uses the same original denominator coefficient. -/
theorem reciprocal_value {channel : CoherentNamed} (sidecar : RationalSidecar channel)
    (prepared : Prepared channel) (nonzero : sidecar.value ≠ 0) :
    (sidecar.reciprocal prepared nonzero).value = 1 / sidecar.value :=
  (Eq.refl _).trans (Eq.refl _)

/-- Propagate exact numerator and denominator data through multiplication by the actual prepared reciprocal. -/
@[noinline, nospecialize] def divide {numerator denominator : CoherentNamed}
    (top : RationalSidecar numerator) (bottom : RationalSidecar denominator)
    (prepared : Prepared denominator) (nonzero : bottom.value ≠ 0) :
    RationalSidecar (CoherentNamed.mul numerator (prepared.quotient (CoherentNamed.Coherence.exact 1))) :=
  top.mul (bottom.reciprocal prepared nonzero)

/-- The actual prepared product reading is the quotient of the same two original exact coefficients. -/
theorem divide_value {numerator denominator : CoherentNamed}
    (top : RationalSidecar numerator) (bottom : RationalSidecar denominator)
    (prepared : Prepared denominator) (nonzero : bottom.value ≠ 0) :
    (top.divide bottom prepared nonzero).value = top.value / bottom.value := by
  unfold divide
  change top.value * (bottom.reciprocal prepared nonzero).value = top.value / bottom.value
  rewrite [reciprocal_value]
  change top.value * (1 * bottom.value⁻¹) = top.value * bottom.value⁻¹
  rewrite [_root_.one_mul]
  rfl

end Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

end
