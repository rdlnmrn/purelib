module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Negation
-- The exposed residual constructor retains the original negation comparison certificate.
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

/-! # Negation of retained quantitative polynomial residuals -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial.Dense.Gaussian.Substitution
open Purelib.Approximation.Gaussian.Geometric.Coherent

/-- Negate the original same-index samples and substitute the negative argument in their polynomial.

The actual original child cache supplies every retained numerical sample.
Source error scale, center bound and polynomial residual scale remain the
same, and the original stateful negation channel is compared to that program.
-/
@[expose] def neg {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) :
    Residual (Negation.negateVariable polynomial) (CoherentNamed.neg channel) :=
  let source := residual.source.neg
  {
    degreePositive := by rewrite [Negation.natDegree]; exact residual.degreePositive
    source := source
    equivalent := Comparison.neg_agreesWith channel residual.source source residual.equivalent (fun _ => rfl)
    scale := residual.scale
    scale_nonnegative := residual.scale_nonnegative
    bound := by
      intro index
      change Data.Gaussian.Norm.Basic.normSq
        ((Negation.negateVariable polynomial).eval (-residual.source.sample index)) ≤ _
      rewrite [Negation.eval_neg]
      exact residual.bound index }

/-- Negated residuals retain the same original polynomial error scale. -/
theorem neg_scale {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) : residual.neg.scale = residual.scale := rfl

/-- Negated residuals read the negative of the same actual original indexed sample. -/
theorem neg_sample {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (index : Nat) :
    residual.neg.source.sample index = -residual.source.sample index := rfl

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
