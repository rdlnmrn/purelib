module
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.Multiplicity.Family.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Ownership
import Purelib.RootIsolation.Multiplicity.Observation.Separation

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Multiplicity.Observation.Build
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

open Purelib.Polynomial
open Purelib.Data

open Purelib.Data.Rat.Fraction (Rational)

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

namespace Observations

/-- Compute and store each original focused-context observation once in its original list order. -/
@[expose] def ofContexts {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (contexts : List (Context.Basic.PositiveContext input.entries))
    (request : Option Rational := none) : Observations input contexts :=
  List.DependentProduct.ofFn contexts (fun index => input.observe (contexts.get index) request)

/-- Materialized lookup returns the complete original observation at the same bounded context occurrence. -/
theorem get_ofContexts {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (contexts : List (Context.Basic.PositiveContext input.entries))
    (index : Fin contexts.length) (request : Option Rational := none) :
    List.DependentProduct.get contexts (ofContexts input contexts request) index =
      input.observe (contexts.get index) request :=
  List.DependentProduct.get_ofFn contexts (fun index => input.observe (contexts.get index) request) index

end Observations

/-- Retain original factor observations with their same ownership and separation operations.

All operations read the supplied original product spine. No factor
observation or numerical isolation is requested by this constructor.
-/
@[expose] def fromObservations
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (observations : Observations input input.contexts) : PositiveFamily input :=
  { observations
    contextCount := input.contexts_length
    weightedDegree := input.multiplicityDegree
    internallySeparated := fun index =>
      observationInternallySeparated (List.DependentProduct.get input.contexts observations index)
    atomicMaximality := fun index =>
      observationAtomicMaximality (List.DependentProduct.get input.contexts observations index)
    pairwiseSeparated := fun left right different =>
      separateObservations
        (List.DependentProduct.get input.contexts observations left)
        (List.DependentProduct.get input.contexts observations right)
        (input.contextCoprime left right different) }

/-- Construct and cache the original finite family of positive-factor observations.

Retain each original context's observation once. The existing access function
reads that same cache, and all separation, maximality and degree certificates
consume those actual retained observations rather than repeating isolation.
-/
@[expose] def buildFamily
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (request : Option Rational := none) : PositiveFamily input :=
  fromObservations input (Observations.ofContexts input input.contexts request)

/-- A retained original ordered observation cache gives the complete original family. -/
theorem fromObservations_eq_buildFamily
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (observations : Observations input input.contexts)
    {request : Option Rational}
    (same : observations = Observations.ofContexts input input.contexts request) :
    fromObservations input observations = input.buildFamily request :=
  congrArg (fromObservations input) same

/-- Each retained family lookup preserves the original observation at its exact original context index. -/
theorem buildFamily_observationAt
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (index : Fin input.contexts.length) (request : Option Rational := none) :
    (input.buildFamily request).observationAt index = input.observe (input.contexts.get index) request :=
  Observations.get_ofContexts input input.contexts index request

/-- The absent event request preserves the complete original ordered observation cache and family. -/
theorem buildFamily_none
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) :
    input.buildFamily none = fromObservations input (Observations.ofContexts input input.contexts) := rfl

/-- Every actual cached family observation retains the original constructor of each higher root track. -/
theorem buildFamily_newtonOrigins
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (request : Option Rational)
    (index : Fin input.contexts.length) :
    ((input.buildFamily request).observationAt index).NewtonOrigins := by
  rewrite [input.buildFamily_observationAt index request]
  exact input.observe_newtonOrigins (input.contexts.get index) request

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
