module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
public import Purelib.RootIsolation.FTA.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

section

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

set_option genInjectivity false in
/-- Exact or shrinking-box observation supplied by one squarefree basis
factor.  The exact constructor is used only when exact evaluation proves a
displayed Gaussian-rational zero. -/
inductive FactorObservation
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries) :
      Type where
  /-- An exact root of the original degree-one focused factor, with the opposite polynomial nonzero at that same point.
  -/
  | exact
      (root : Dense.Gaussian.Roots.Certificate.ExactRoot
        context.focus.part.polynomial)
      (degree : context.focus.part.polynomial.natDegree = 1)
      (oppositeAtRoot : opposite.eval root.point ≠ 0)
  /-- The original complete shrinking-box isolation of the focused factor of degree at least two. -/ | higher
      (boxes : FTA.Squarefree.BoxResult
        context.focus.part.polynomial)
      (degree : 2 ≤ context.focus.part.polynomial.natDegree)

constructive_injectivity FactorObservation

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end

end
