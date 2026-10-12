module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.Multiplicity.Family.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Ownership
import Purelib.RootIsolation.Multiplicity.Observation.Separation

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Multiplicity.Observation.Build
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

open Purelib.Polynomial

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

/-- Construct the original finite family of positive-factor observations.

Retain the exact contexts and weighted degree, together with internal separation, atomic maximality and pairwise
separation of those same observations. -/
@[expose] def buildFamily
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.PositiveFamily input where
  observationAt := fun index => input.observe (input.contexts.get index)
  contextCount := input.contexts_length
  weightedDegree := input.multiplicityDegree
  internallySeparated := fun index =>
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.observationInternallySeparated
      (input.observe (input.contexts.get index))
  atomicMaximality := fun index =>
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.observationAtomicMaximality
      (input.observe (input.contexts.get index))
  pairwiseSeparated := fun left right different =>
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.separateObservations
      (input.observe (input.contexts.get left))
      (input.observe (input.contexts.get right))
      (input.contextCoprime left right different)

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
