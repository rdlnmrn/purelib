import mathlib.RFAP.CanonicalPolynomial

/-!
# Displayed Newton residuals over canonical finite arithmetic

This is the representative RFAP calculation for the quotient-free pilot.  It
computes a polynomial value and its finite automatic derivative at a supplied
Gaussian-rational sample, forms the displayed Newton correction, and proves
its squared displacement by canonical Gaussian arithmetic alone.
-/

namespace RFAP.CanonicalResidual

abbrev Coordinate := RFAP.CanonicalFraction.Rational
abbrev Gaussian := RFAP.CanonicalGaussian.Gaussian
abbrev Polynomial := RFAP.CanonicalPolynomial.Polynomial

open RFAP.CanonicalGaussian.Gaussian

/-- Squared residual at one explicitly supplied Gaussian-rational sample. -/
def residualSq (polynomial : Polynomial) (sample : Gaussian) : Coordinate :=
  normSq (RFAP.CanonicalPolynomial.eval polynomial sample)

/-- Value of the finite automatic derivative at the supplied sample. -/
def derivativeValue (polynomial : Polynomial) (sample : Gaussian) : Gaussian :=
  RFAP.CanonicalPolynomial.eval
    (RFAP.CanonicalPolynomial.derivative polynomial) sample

/-- Executable Newton update based only at the supplied finite sample. -/
def newtonCenter (polynomial : Polynomial) (sample : Gaussian) : Gaussian :=
  sample - RFAP.CanonicalPolynomial.eval polynomial sample /
    derivativeValue polynomial sample

/-- Residual quadrance is multiplicative for the finite dense product. -/
theorem residualSq_mul (left right : Polynomial) (sample : Gaussian) :
    residualSq (RFAP.CanonicalPolynomial.mul left right) sample =
      residualSq left sample * residualSq right sample := by
  unfold residualSq
  rw [RFAP.CanonicalPolynomial.eval_mul, normSq_mul]

theorem newtonCenter_sub_sample
    (polynomial : Polynomial) (sample : Gaussian) :
    newtonCenter polynomial sample - sample =
      -(RFAP.CanonicalPolynomial.eval polynomial sample /
        derivativeValue polynomial sample) := by
  unfold newtonCenter
  exact sub_sub_right sample
    (RFAP.CanonicalPolynomial.eval polynomial sample /
      derivativeValue polynomial sample)

/-- The exact displayed Newton-displacement identity used by residual
localization.  It is an equality of finite canonical records. -/
theorem newtonDisplacementSq
    (polynomial : Polynomial) (sample : Gaussian)
    (derivativeNonzero : derivativeValue polynomial sample ≠ 0) :
    normSq (newtonCenter polynomial sample - sample) =
      residualSq polynomial sample *
        (normSq (derivativeValue polynomial sample))⁻¹ := by
  rw [newtonCenter_sub_sample, normSq_neg,
    normSq_div _ _ derivativeNonzero]
  rfl

end RFAP.CanonicalResidual
