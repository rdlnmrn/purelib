module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.RootIsolation.Multiplicity.Observation.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Ownership
public import Purelib.RootIsolation.Multiplicity.Observation.Separation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

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

set_option genInjectivity false in
/-- The observations of every retained positive multiplicity context in the original coprime side. -/
structure PositiveFamily
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) where
  /-- Read the observation at the exact retained context index. -/ observationAt : ∀ index : Fin input.contexts.length,
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input (input.contexts.get index)
  /-- Count the original retained positive multiplicity contexts. -/ contextCount : input.contexts.length =
    input.entries.length
  /-- The retained weighted multiplicity count equals the original source polynomial degree. -/ weightedDegree :
    Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree input.entries =
      source.natDegree
  /-- Each retained context observation carries its original internal site separation. -/ internallySeparated : ∀ index
    : Fin input.contexts.length,
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationInternallySeparated (observationAt
      index)
  /-- Each retained context observation carries its exact-root or higher-track maximality operation. -/ atomicMaximality
    : ∀ index : Fin input.contexts.length,
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationAtomicMaximality (observationAt index)
  /-- Different original context indices retain their certified cross-observation site separation. -/ pairwiseSeparated
    : ∀ (left right : Fin input.contexts.length),
    left ≠ right →
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationsSeparated (observationAt left)
        (observationAt right)

constructive_injectivity
  PositiveFamily

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
