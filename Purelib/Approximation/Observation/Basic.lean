module

public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite-request refinement protocols

The structures here retain only finite observations.  They express arbitrary
accuracy, finite satisfiability, monotone refinement, and pairwise shrinking
without constructing a stream, an intersection, or a completed value.
-/

namespace Purelib.Approximation

set_option genInjectivity false in
/-- One finitely satisfiable observation with a displayed pairwise spread. -/
structure Observation (α : Type) (distance : α → α → Fraction.Rational) where
  /-- The finite observation's predicate of admitted candidates. -/ Possible : α → Prop
  /-- The retained explicit candidate witnessing consistency. -/ witness : α
  /-- The retained witness satisfies the observation predicate. -/ witness_possible : Possible witness
  /-- The displayed rational pairwise spread bound. -/ spread : Fraction.Rational
  /-- The pairwise spread bound is nonnegative. -/ spread_nonnegative : 0 ≤ spread
  /-- Any two admitted candidates have distance at most the retained spread. -/ pairwise : ∀ {left right : α}, Possible
    left → Possible right →
    distance left right ≤ spread

constructive_injectivity Observation

namespace Observation

/-- Transport a finite observation through a displayed sensitivity bound. -/
def map
    {α β : Type} {sourceDistance : α → α → Fraction.Rational}
    {targetDistance : β → β → Fraction.Rational}
    (observation : Approximation.Observation α sourceDistance)
    (function : α → β) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      targetDistance (function left) (function right) ≤
        factor * sourceDistance left right) :
    Approximation.Observation β targetDistance where
  Possible value := ∃ source, observation.Possible source ∧
    value = function source
  witness := function observation.witness
  witness_possible :=
    ⟨observation.witness, observation.witness_possible, rfl⟩
  spread := factor * observation.spread
  spread_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    nonnegative observation.spread_nonnegative
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftSource, leftSourcePossible, rfl⟩
    rcases rightPossible with ⟨rightSource, rightSourcePossible, rfl⟩
    exact (sensitive leftSource rightSource).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (observation.pairwise leftSourcePossible rightSourcePossible)
        nonnegative)

/-- The later finite predicate contains no candidates rejected by the older predicate. -/
structure Refines {α : Type} {distance : α → α → Fraction.Rational}
    (inner outer : Approximation.Observation α distance) : Prop where
  /-- Every candidate admitted by the inner observation is admitted by the outer one. -/ possible : ∀ {value : α},
    inner.Possible value → outer.Possible value

namespace Refines

/-- Each observation refines itself. -/
theorem refl {α : Type} {distance : α → α → Fraction.Rational}
    (observation : Approximation.Observation α distance) : Approximation.Observation.Refines observation observation :=
  ⟨fun possible => possible⟩

/-- Compose two successive observation refinements. -/
theorem trans {α : Type} {distance : α → α → Fraction.Rational}
    {inner middle outer : Approximation.Observation α distance}
    (innerMiddle : Approximation.Observation.Refines inner middle)
    (middleOuter : Approximation.Observation.Refines middle outer) : Approximation.Observation.Refines inner outer :=
  ⟨fun possible => middleOuter.possible (innerMiddle.possible possible)⟩

/-- The inner observation's retained witness remains possible in the outer observation. -/
theorem witness_possible {α : Type} {distance : α → α →
  Fraction.Rational}
    {inner outer : Approximation.Observation α distance} (refines : Approximation.Observation.Refines inner outer) :
    outer.Possible inner.witness :=
  refines.possible inner.witness_possible

/-- A map with the displayed sensitivity bound preserves observation refinement. -/
theorem map
    {α β : Type} {sourceDistance : α → α → Fraction.Rational}
    {targetDistance : β → β → Fraction.Rational}
    {inner outer : Approximation.Observation α sourceDistance}
    (refines : Approximation.Observation.Refines inner outer)
    (function : α → β) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      targetDistance (function left) (function right) ≤
        factor * sourceDistance left right) :
    Approximation.Observation.Refines (inner.map function factor nonnegative sensitive)
      (outer.map function factor nonnegative sensitive) := by
  constructor
  rintro value ⟨source, possible, equal⟩
  exact ⟨source, refines.possible possible, equal⟩

end Refines

set_option genInjectivity false in
/-- A chronological finite refinement history, indexed by its latest observation. There is no constructor for an
infinite history. -/
inductive History {α : Type} {distance : α → α → Fraction.Rational}
    (initial : Approximation.Observation α distance) : Approximation.Observation α distance → Type where
  /-- Start a finite history at its initial observation. -/ | start : History initial
    initial
  /-- Extend a finite history by one certified refinement. -/ | step {older newer : Approximation.Observation α
    distance} :
      History initial older → Approximation.Observation.Refines newer older →
        History initial newer

constructive_injectivity History

namespace History

/-- The end of a finite history refines its beginning. -/
theorem refines_initial
    {α : Type} {distance : α → α → Fraction.Rational}
    {initial latest : Approximation.Observation α distance}
    (history : Approximation.Observation.History initial latest) : Approximation.Observation.Refines latest initial :=
      by
  induction history with
  | start => exact Approximation.Observation.Refines.refl initial
  | @step older newer history refines inductionHypothesis =>
      exact refines.trans inductionHypothesis

/-- The latest witness of any finite history satisfies the initial finite predicate. This is the
inhabited-finite-intersection argument. -/
theorem latest_witness_possible_initial
    {α : Type} {distance : α → α → Fraction.Rational}
    {initial latest : Approximation.Observation α distance}
    (history : Approximation.Observation.History initial latest) :
    initial.Possible latest.witness := by
  exact history.refines_initial.possible latest.witness_possible

/-- Every candidate admitted at the end of a finite history was admitted at the beginning. -/
theorem latest_possible_initial
    {α : Type} {distance : α → α → Fraction.Rational}
    {initial latest : Approximation.Observation α distance}
    (history : Approximation.Observation.History initial latest) {value : α}
    (possible : latest.Possible value) : initial.Possible value := by
  exact history.refines_initial.possible possible

end History

end Observation
namespace ProgressiveObservation
end ProgressiveObservation
namespace BoundProcess
end BoundProcess

end Purelib.Approximation

end
