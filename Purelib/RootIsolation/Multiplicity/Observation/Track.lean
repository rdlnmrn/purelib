module
import Purelib.Data.Gaussian.Basic
public import Purelib.RootIsolation.Multiplicity.Site.Winding
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Multiplicity.Site.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput

section PositiveSideInput

/-- Build the fully protected signed-multiplicity track input for any track
of a higher-degree basis factor. -/
def higherTrackInput
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries)
    (boxes : FTA.Squarefree.BoxResult
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    Multiplicity.Site.Basic.TrackSiteInput
      source.normalize opposite :=
  let track := boxes.isolation.trackAt index
  { decomposition := input.preprocessing.decomposition
    pairwise := input.entries_pairwise
    context := context
    oppositeNonzero := input.oppositeNonzero
    focusOppositeCoprime := input.focusOppositeCoprime context
    track := track
    current := track.initial }

/-- The source represented by a retained higher-factor track evaluates exactly as the original source polynomial. -/
theorem
  higherRepresentedSource_eval
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries)
    (boxes : FTA.Squarefree.BoxResult
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree)
    (point : Gaussian.Basic.Canonical) :
    ((input.higherTrackInput context boxes index).representedSource).eval point =
      source.eval point := by
  let site := input.higherTrackInput context boxes index
  have factorization := Dense.Gaussian.Factorization.Identity.eval_factorization
    site.representedFactorization point
  change source.normalize.eval point = _ at factorization
  rw [Dense.Basic.DensePolynomial.eval_normalize] at factorization
  change (Dense.Gaussian.Power.polynomialPower
      context.focus.part.polynomial context.focus.multiplicity *
    context.otherPolynomial input.preprocessing.decomposition).eval point =
      source.eval point
  rw [Dense.Basic.DensePolynomial.eval_mul]
  exact factorization.symm
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput

end
