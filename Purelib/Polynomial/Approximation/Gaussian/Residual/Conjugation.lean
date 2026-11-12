module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.Conjugation
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Data.Gaussian.Norm.Basic

/-! # Conjugation of retained quantitative polynomial residuals -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial.Dense.Gaussian

/-- Conjugate the original polynomial and every same-index residual sample on the original conjugated channel.

The same source cache supplies each sample, and the residual scale is retained
exactly. Conjugation does not run a new isolation or choose a replacement root.
-/
@[expose] def conj {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) :
    Residual (Conjugation.conjugate polynomial) (CoherentNamed.conj channel) :=
  let source := residual.source.conj
  {
    degreePositive := by rw [Conjugation.natDegree]; exact residual.degreePositive
    source := source
    equivalent := CoherentNamed.conj_geometricWith residual.source source residual.equivalent (fun _ => rfl)
    scale := residual.scale
    scale_nonnegative := residual.scale_nonnegative
    bound := by
      intro index
      change Data.Gaussian.Norm.Basic.normSq
        ((Conjugation.conjugate polynomial).eval (Data.Gaussian.Basic.conj (residual.source.sample index))) ≤ _
      rw [Conjugation.eval, Data.Gaussian.Norm.Basic.normSq_conj]
      exact residual.bound index }

/-- Conjugated residuals retain the original scale without recomputing a numerical certificate. -/
theorem conj_scale {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) : residual.conj.scale = residual.scale := rfl

/-- Conjugated residuals read the conjugate of the same retained original finite sample. -/
theorem conj_sample {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (index : Nat) :
    residual.conj.source.sample index = Data.Gaussian.Basic.conj (residual.source.sample index) := rfl

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
