module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Quantitative derivative separation on rational boxes

The original polynomial and rational box index positive residual and derivative
quadrance thresholds. Restricting a certificate retains these exact values and
transports its lower bound through the supplied box refinement witness.
-/

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic

@[expose] public section

set_option genInjectivity false in
/-- Positive residual and derivative-quadrance thresholds certify separation on a rational box.

The original polynomial and ambient box index both retained positive thresholds.
At every point of that same box, a squared residual below the threshold forces
the displayed lower bound on the original polynomial derivative quadrance. -/
structure Certificate (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient :
  Geometry.Rational.Box) where
  /-- The retained squared-residual threshold. -/ threshold : Fraction.Rational
  /-- The residual threshold is positive. -/ threshold_pos : 0 < threshold
  /-- The retained lower bound on derivative quadrance. -/ margin : Fraction.Rational
  /-- The derivative margin is positive. -/ margin_pos : 0 < margin
  /-- Every point of the retained box below the residual threshold has derivative quadrance at least the margin. -/
    lower : ∀ {z : Gaussian.Basic.Canonical}, ambient.Contains z →
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ threshold →
      margin ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval z)

constructive_injectivity Certificate

end

namespace Certificate

/-- Restrict a derivative-separation certificate through a retained rational-box refinement.

The original polynomial, residual threshold and derivative margin remain unchanged.
The supplied refinement sends each point of the smaller box into the original
ambient box, where the same lower-bound certificate applies. -/
@[expose] public def restrict
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient small :
      Geometry.Rational.Box}
    (certificate : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient) (refines : small.Refines ambient) :
    Dense.Gaussian.Derivative.Separation.Basic.Certificate p small where
  threshold := certificate.threshold
  threshold_pos := certificate.threshold_pos
  margin := certificate.margin
  margin_pos := certificate.margin_pos
  lower := fun inside residual => certificate.lower
    (refines.contains inside) residual

/-- Restriction to a subbox preserves the original residual threshold. -/
@[simp] public theorem restrict_threshold
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient small :
      Geometry.Rational.Box}
    (certificate : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient) (refines : small.Refines ambient) :
    (certificate.restrict refines).threshold = certificate.threshold := rfl

/-- Restriction to a subbox preserves the original derivative margin. -/
@[simp] public theorem restrict_margin
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient small :
      Geometry.Rational.Box}
    (certificate : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient) (refines : small.Refines ambient) :
    (certificate.restrict refines).margin = certificate.margin := rfl

end Certificate

end Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
