module

import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Data.Gaussian.Field
meta import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
meta import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
meta import Purelib.Data.Gaussian.Field

/-! # Reusable quantitative residuals on exact, original root and arithmetic channels -/

namespace TestPurelib.Polynomial.ResidualChannel

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian (Residual)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation

example {polynomial : CoefficientPolynomial} {channel : CoherentNamed} (residual : Residual polynomial channel) :
    Equivalence.NamedEquivalent
      (Polynomial.Approximation.Gaussian.Evaluation.Horner.polynomialEval polynomial channel).name
      (CoherentNamed.Coherence.exact 0).name := residual.equation

example (point : Canonical) (index : Nat) : (Residual.exact point).source.sample index = point :=
  Residual.exact_sample point index

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track) :
    Residual polynomial root.value := root.residualCertificate

/-- Execute exact original-channel decisions through one retained coefficient residual preparation. -/
private def checkExactResiduals : IO Unit := do
  let nonzero := Residual.exact 2
  let preparation := nonzero.prepareLocalization
  let decision := nonzero.decidePrepared preparation
  unless decision.isPrepared ∧ preparation.source.sample 5 = 2 do
    throw (IO.userError "exact residual preparation lost the same original numerical channel or stored sample")
  let zero := Residual.exact 0
  let zeroPreparation := zero.prepareLocalization
  unless !(zero.decidePrepared zeroPreparation).isPrepared ∧ zeroPreparation.source.sample 7 = 0 do
    throw (IO.userError "exact zero residual did not certify exclusion on its original numerical channel")

#eval checkExactResiduals

end TestPurelib.Polynomial.ResidualChannel
