module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.FTA.Positive.Build
public import Purelib.RootIsolation.Multiplicity.Observation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

/-- Observe the retained positive multiplicity factor with the original positive-degree box construction.

Return its exact linear root with the opposite polynomial's nonvanishing proof, or its complete higher-degree box
family. -/
@[expose] def observe
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries) :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context := by
  let positive := FTA.Positive.Build.provePositive
    { squarefree := context.focus.part.squarefree
      degreePositive := context.focus.degreePositive }
  cases positive with
  | linear root degree =>
      have alternative := (input.focusOppositeCoprime context).eval_ne_zero
        root.point
      have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
        rcases alternative with focusNonzero | oppositeNonzero
        · exact (focusNonzero root.root).elim
        · exact oppositeNonzero
      exact .exact root degree oppositeAtRoot
  | higher boxes degree => exact .higher boxes degree
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
