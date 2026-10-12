module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Representation.Basic
public import Purelib.Approximation.Gaussian.Translation.Schedule

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Approximation.Gaussian.Translation (Schedule)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Representation.Basic

open Purelib.Approximation.Gaussian.Translation

open Purelib.Approximation.Gaussian.Translation.Schedule

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

namespace Purelib.Approximation.Gaussian.Translation.Observation

set_option genInjectivity false in
/-- A direct conversion of one fixed observation. It cannot claim precision which was not already supplied by the
source. -/
structure ObservationMap
    (source target : Approximation.Gaussian.Representation) where
  /-- Convert the original source observation directly to a target observation. -/ map : source.Observation →
    target.Observation
  /-- Every original source reading remains admitted by the converted observation. -/ covers : ∀ {observation value},
    source.Possible observation value →
      target.Possible (map observation) value
  /-- Refining the source gives compatible converted target observations. -/ coherent : ∀ {inner outer}, source.Refines
    inner outer →
    target.Compatible (map inner) (map outer)
  /-- The displayed rational precision loss assigned to each original source observation. -/ precisionLoss :
    source.Observation → Fraction.Rational
  /-- Every displayed precision loss is nonnegative. -/ precisionLoss_nonneg : ∀ observation, 0 ≤ precisionLoss
    observation
  /-- Converted precision is bounded by source precision plus the displayed loss. -/ precision_le : ∀ observation,
    target.precisionSq (map observation) ≤
      source.precisionSq observation + precisionLoss observation
  /-- The finite action schedule associated with each direct observation conversion. -/ schedule : source.Observation →
    Schedule
  /-- The retained natural work bound for each original observation. -/ costBound : source.Observation → Nat
  /-- The conversion schedule's work is bounded by the retained cost. -/ cost_le : ∀ observation, (schedule
    observation).work ≤ costBound observation

constructive_injectivity ObservationMap

namespace ObservationMap

/-- The direct observation map that retains the original observation with zero loss and zero work. -/
def identity (representation :
  Approximation.Gaussian.Representation) :
    Approximation.Gaussian.Translation.Observation.ObservationMap representation representation where
  map observation := observation
  covers possible := possible
  coherent refines := Approximation.Gaussian.Representation.compatible_of_refines refines
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by rewrite [add_zero]; exact le_rfl
  schedule _ := Schedule.zero
  costBound _ := 0
  cost_le _ := Nat.le_refl 0

/-- Compose direct observation maps and retain their accumulated precision losses and work.

The second map consumes the exact observation produced by the first; coverage and finite compatibility compose through
their retained reading witnesses. -/
def comp {first middle last :
  Approximation.Gaussian.Representation}
    (right : Approximation.Gaussian.Translation.Observation.ObservationMap middle last)
    (left : Approximation.Gaussian.Translation.Observation.ObservationMap first middle) :
    Approximation.Gaussian.Translation.Observation.ObservationMap first last where
  map observation := right.map (left.map observation)
  covers possible := right.covers (left.covers possible)
  coherent refines := by
    rcases left.coherent refines with
      ⟨value, innerPossible, outerPossible⟩
    exact ⟨value, right.covers innerPossible, right.covers outerPossible⟩
  precisionLoss observation :=
    left.precisionLoss observation +
      right.precisionLoss (left.map observation)
  precisionLoss_nonneg observation :=
    add_nonneg (left.precisionLoss_nonneg observation)
      (right.precisionLoss_nonneg (left.map observation))
  precision_le observation := by
    calc
      last.precisionSq (right.map (left.map observation)) ≤
          middle.precisionSq (left.map observation) +
            right.precisionLoss (left.map observation) :=
        right.precision_le (left.map observation)
      _ ≤ (first.precisionSq observation +
            left.precisionLoss observation) +
            right.precisionLoss (left.map observation) :=
        add_le_add (left.precision_le observation) le_rfl
      _ = first.precisionSq observation +
          (left.precisionLoss observation +
            right.precisionLoss (left.map observation)) := by
        rw [add_assoc]
  schedule observation :=
    (left.schedule observation).add
      (right.schedule (left.map observation))
  costBound observation :=
    left.costBound observation + right.costBound (left.map observation)
  cost_le observation := by
    rw [Schedule.work_add]
    exact Nat.add_le_add (left.cost_le observation)
      (right.cost_le (left.map observation))

end ObservationMap

end Purelib.Approximation.Gaussian.Translation.Observation

end
