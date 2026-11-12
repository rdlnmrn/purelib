module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.RootIsolation.Multiplicity.Observation.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Ownership
public import Purelib.RootIsolation.Multiplicity.Observation.Separation
public import Purelib.Data.List.DependentProduct

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

open Purelib.Polynomial
open Purelib.Data

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

/-- Actual original factor observations stored in their bounded context-list product. -/
abbrev Observations {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (contexts : List (Context.Basic.PositiveContext input.entries)) :=
  List.DependentProduct contexts (fun index => FactorObservation input (contexts.get index))

set_option genInjectivity false in
/-- The observations of every retained positive multiplicity context in the original coprime side. -/
structure PositiveFamily
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) where
  /-- The actual stored observation at every original bounded context occurrence. -/
  observations : List.DependentProduct input.contexts (fun index =>
    FactorObservation input (input.contexts.get index))
  /-- Count the original retained positive multiplicity contexts. -/ contextCount : input.contexts.length =
    input.entries.length
  /-- The retained weighted multiplicity count equals the original source polynomial degree. -/ weightedDegree :
    Product.positiveDegree input.entries =
      source.natDegree
  /-- Each retained context observation carries its original internal site separation. -/ internallySeparated : ∀ index
    : Fin input.contexts.length,
    ObservationInternallySeparated (List.DependentProduct.get input.contexts observations index)
  /-- Each retained context observation carries its exact-root or higher-track maximality operation. -/ atomicMaximality
    : ∀ index : Fin input.contexts.length,
    ObservationAtomicMaximality (List.DependentProduct.get input.contexts observations index)
  /-- Different original context indices retain their certified cross-observation site separation. -/ pairwiseSeparated
    : ∀ (left right : Fin input.contexts.length),
    left ≠ right →
      ObservationsSeparated (List.DependentProduct.get input.contexts observations left)
        (List.DependentProduct.get input.contexts observations right)

constructive_injectivity
  PositiveFamily

namespace PositiveFamily

/-- Read the same stored observation at its original bounded context occurrence.

The lookup follows the retained product spine. It never invokes the original
isolation producer, and all family ownership and separation operations refer
to these same stored observations.
-/
@[expose] def observationAt
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : PositiveSideInput source opposite} (family : PositiveFamily input) (index : Fin input.contexts.length) :
    FactorObservation input (input.contexts.get index) :=
  List.DependentProduct.get input.contexts family.observations index

end PositiveFamily

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
