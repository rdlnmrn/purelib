module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection

/-! # Computed localization and original-channel decisions from quantitative residual certificates -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Prepare the original residual polynomial and actual sample program once using its retained quantitative bound. -/
@[expose] def prepareLocalization {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) : Localization.Preparation polynomial residual.source :=
  Localization.Preparation.ofResidual polynomial residual.degreePositive residual.source residual.scale
    residual.scale_nonnegative residual.bound

/-- Consume one already retained original residual preparation to decide zero or preparation of its original channel. -/
def decidePrepared {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (preparation : Localization.Preparation polynomial residual.source) :
    Division.Prepared.Decision channel := preparation.select.decideOriginal channel residual.equivalent

/-- Original residual decisions use the same prepared stable selection and original-channel comparison. -/
theorem decidePrepared_eq {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (preparation : Localization.Preparation polynomial residual.source) :
    residual.decidePrepared preparation = preparation.select.decideOriginal channel residual.equivalent := by
  unfold decidePrepared
  rfl

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
