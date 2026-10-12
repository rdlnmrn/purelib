module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Global residual localization

This module extends the local residual Newton construction to the
coefficient-computed large isolation square.  An explicit leading-term
estimate excludes small residuals outside that square.  Inside it, the
minimal `ProtectedAmbient` interface constructs a winding-one track without
assuming that the parent square itself has winding one; finite maximality
then assigns the track to one of the already isolated output tracks.

Every input and output point is a displayed Gaussian rational.  The global
classifier never constructs or quantifies over a completed root.
-/

namespace Purelib.RootIsolation.Residual.Global

set_option genInjectivity false in
/-- Total result of inspecting an arbitrary displayed Gaussian-rational
sample.  The failure constructor records the explicit rational inequality
that prevented localization. -/
inductive Observation
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) : Type where
  /-- The supplied exact Gaussian sample is a root of the original polynomial. -/ | exact (evaluation : p.eval sample =
    0)
  /-- The supplied sample has a retained localized winding-one box and owner in the original computed isolation. -/ |
    assigned (result : Residual.Global.Assignment.AssignedResult input sample epsilon)
  /-- The sample's measured residual meets or exceeds the explicit localization threshold. -/ | residualNotSmall
      (failure : Residual.Global.Assignment.residualThreshold input sample epsilon ≤
        Data.Gaussian.Norm.Basic.normSq (p.eval sample))

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Observation

namespace Observation

/-- Classify any displayed Gaussian-rational sample by finite evaluation,
protected Newton localization plus output ownership, or a witnessed failure
of the explicit positive small-residual hypothesis. -/
@[expose] def classify
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) : Observation input sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else if inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains sample then
    if residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
        Residual.Global.Assignment.residualThreshold input sample epsilon then
      .assigned (Residual.Global.Assignment.assignInside input sample inside epsilonPositive (by
        rw [Residual.Global.Assignment.residualThreshold, if_pos inside] at residualSmall
        exact residualSmall))
    else
      .residualNotSmall (le_of_not_gt residualSmall)
  else
    .residualNotSmall (by
      rw [Residual.Global.Assignment.residualThreshold, if_neg inside]
      exact Residual.Global.Bounds.outsideResidualThreshold_le input.degreeAtLeastTwo sample inside)

end Observation

end Purelib.RootIsolation.Residual.Global

end
