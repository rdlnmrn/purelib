module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Representation.Basic
public import Purelib.Approximation.Gaussian.Translation.Request
public import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Translation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace Purelib.Approximation.Gaussian.Translation

namespace Realizer

set_option genInjectivity false in
/-- One certified response of a progressive finite realizer. Both directions of the reading relation are explicit;
enclosure-only clients may choose a relation whose reverse direction contains the required witness data. -/
structure TranslationResult
    (source target : Representation)
    (observation : source.Observation) (request : Request) where
  /-- The refined original-source observation retained by this response. -/ source' : source.Observation
  /-- The retained target observation produced by this request. -/ output : target.Observation
  /-- The retained source observation refines the exact original source observation. -/ source_refines : source.Refines
    source' observation
  /-- The explicit relation between original source and produced target readings. -/ relates :
    Canonical → Canonical → Prop
  /-- Every retained source reading has an explicitly related admitted target reading. -/ source_to_target : ∀
    {sourceValue : Canonical},
    source.Possible source' sourceValue →
      ∃ targetValue : Canonical,
        target.Possible output targetValue ∧ relates sourceValue targetValue
  /-- Every admitted target reading has an explicitly related retained source reading. -/ target_to_source : ∀
    {targetValue : Canonical},
    target.Possible output targetValue →
      ∃ sourceValue : Canonical,
        source.Possible source' sourceValue ∧ relates sourceValue targetValue
  /-- The retained rational loss in the target's native precision gauge. -/ precisionLoss : Fraction.Rational
  /-- The retained precision loss is nonnegative. -/ precisionLoss_nonneg : 0 ≤ precisionLoss
  /-- The output precision is strictly below the requested target plus its retained loss. -/ precision :
    target.precisionSq output <
    request.targetSq + precisionLoss
  /-- The finite action schedule of this exact translation response. -/ schedule : Schedule
  /-- The retained natural upper bound for the response's work. -/ costBound : Nat
  /-- The response schedule's work is at most its retained cost bound. -/ cost_le : schedule.work ≤ costBound

constructive_injectivity TranslationResult

end Realizer

namespace Realizer.TranslationResult.mk

end Realizer.TranslationResult.mk

set_option genInjectivity false in
/-- A request-driven translation. Coherence is derived below from the two explicit reading directions rather than
incorrectly demanding that approximate target observations share the same rational representative. -/
structure Realizer
    (source target : Representation) where
  /-- Produce a certified translation response for the exact observation and positive precision request. -/ translate :
    (observation : source.Observation) → (request : Request) →
    Realizer.TranslationResult source target observation request

constructive_injectivity Realizer

namespace Realizer.mk

end Realizer.mk

namespace Realizer

/-- Relational coherence of two independent finite requests. A common source reading is transported to one explicitly
related reading in each output. If both result relations are equality, the two target observations are literally
compatible in `Representation.Compatible`. -/
theorem coherent {source target :
  Representation}
    (realizer : Realizer source target)
    (observation : source.Observation) (leftRequest rightRequest : Request)
    (sourceCompatible : source.Compatible
      (realizer.translate observation leftRequest).source'
      (realizer.translate observation rightRequest).source') :
    ∃ sourceValue : Canonical,
      source.Possible
          (realizer.translate observation leftRequest).source' sourceValue ∧
        source.Possible
          (realizer.translate observation rightRequest).source' sourceValue ∧
        (∃ leftValue : Canonical,
          target.Possible
              (realizer.translate observation leftRequest).output leftValue ∧
            (realizer.translate observation leftRequest).relates
              sourceValue leftValue) ∧
        (∃ rightValue : Canonical,
          target.Possible
              (realizer.translate observation rightRequest).output rightValue ∧
            (realizer.translate observation rightRequest).relates
              sourceValue rightValue) := by
  rcases sourceCompatible with
    ⟨sourceValue, leftSourcePossible, rightSourcePossible⟩
  rcases (realizer.translate observation leftRequest).source_to_target
      leftSourcePossible with ⟨leftValue, leftPossible, leftRelated⟩
  rcases (realizer.translate observation rightRequest).source_to_target
      rightSourcePossible with ⟨rightValue, rightPossible, rightRelated⟩
  exact ⟨sourceValue, leftSourcePossible, rightSourcePossible,
    ⟨leftValue, leftPossible, leftRelated⟩,
    ⟨rightValue, rightPossible, rightRelated⟩⟩

end Realizer

end Purelib.Approximation.Gaussian.Translation

end
