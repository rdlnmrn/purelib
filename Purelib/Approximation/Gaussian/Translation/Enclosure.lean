module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Translation.Observation
public import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Representation.Ball
public import Purelib.Approximation.Gaussian.Representation.Box
public import Purelib.Approximation.Gaussian.Representation.Process
public import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Translation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Translation.Enclosure
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

open Purelib.Data.Rat in
/-- Forget the rectangular geometry of a box while retaining a sound closed ball. The native squared gauge is unchanged
exactly. -/
def boxToBall : Observation.ObservationMap
  Gaussian.Representation.Box.boxRepresentation Ball.ballRepresentation where
  map box := Approximation.Gaussian.Enclosure.Ball.ofBox box
  covers possible := Approximation.Gaussian.Enclosure.Ball.contains_ofBox possible
  coherent := by
    intro inner outer refines
    refine ⟨inner.anchor, ?_, ?_⟩
    · exact Approximation.Gaussian.Enclosure.Ball.contains_ofBox
        inner.contains_anchor
    · exact Approximation.Gaussian.Enclosure.Ball.contains_ofBox
        (refines.contains inner.contains_anchor)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by
    simp only [Ball.ballRepresentation, Gaussian.Representation.Box.boxRepresentation,
      Approximation.Gaussian.Enclosure.Ball.ofBox, add_zero, -eq_self, -iff_self]
    exact Fraction.Order.Basic.le_refl _
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1

/-- One arbitrary-precision process request realized as a rational ball. The reverse reading relation records the
explicit four-radius estimate between an arbitrary point of the output ball and the process's displayed witness. -/
def processToBall (process : Process)
  :
    Approximation.Gaussian.Translation.Realizer (Process.processRepresentation process) Ball.ballRepresentation where
  translate state request := by
    let refined := process.refine state request.targetSq request.positive
    let output := process.ball refined
    exact
      { source' := refined
        output := output
        source_refines := by
          intro value possible
          exact process.refine_persists state request.targetSq
            request.positive possible
        relates := fun sourceValue targetValue =>
          Data.Gaussian.Norm.Basic.normSq (targetValue - sourceValue) ≤ 4 * output.radiusSq
        source_to_target := by
          intro sourceValue possible
          refine ⟨sourceValue, process.possible_inside possible, ?_⟩
          rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
          exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            output.radiusSq_nonneg
        target_to_source := by
          intro targetValue targetPossible
          let sourceValue := (process.witness refined).val
          refine ⟨sourceValue, (process.witness refined).property, ?_⟩
          exact Approximation.Gaussian.Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq targetPossible
            (process.possible_inside (process.witness refined).property)
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change (process.ball refined).radiusSq < request.targetSq + 0
          calc
            (process.ball refined).radiusSq < request.targetSq :=
              process.accurate state request.targetSq request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 0
            arithmeticSteps := 0 }
        costBound := 1
        cost_le := Nat.le_refl 1 }

/-- A finite fast-Cauchy random-access query is a specialization of the process-to-ball realizer. Its source schedule
consists of exactly one call to the displayed `refineIndex` modulus. -/
def approximationToBall (approximation :
  ApproximationData) :
    Approximation.Gaussian.Translation.Realizer (Sequence.approximationRepresentation approximation)
      Ball.ballRepresentation where
  translate index request := by
    let refined := approximation.refineIndex index request.targetSq
      request.positive
    let output : Approximation.Gaussian.Enclosure.Ball :=
      { center := approximation.sample refined
        radiusSq := approximation.radiusSq refined
        radiusSq_nonneg := approximation.radiusSq_nonneg refined }
    exact
      { source' := refined
        output := output
        source_refines := approximation.refineIndex_ge index
          request.targetSq request.positive
        relates := fun sourceValue targetValue =>
          Data.Gaussian.Norm.Basic.normSq (targetValue - sourceValue) ≤ 4 * output.radiusSq
        source_to_target := by
          intro sourceValue possible
          refine ⟨sourceValue, approximation.possible_inside possible, ?_⟩
          rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
          exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            output.radiusSq_nonneg
        target_to_source := by
          intro targetValue targetPossible
          refine ⟨approximation.sample refined,
            approximation.sample_possible refined, ?_⟩
          exact Approximation.Gaussian.Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq targetPossible
            (approximation.possible_inside
              (approximation.sample_possible refined))
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change approximation.radiusSq refined < request.targetSq + 0
          calc
            approximation.radiusSq refined < request.targetSq :=
              approximation.refineIndex_accurate index request.targetSq
                request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 0
            arithmeticSteps := 0 }
        costBound := 1
        cost_le := Nat.le_refl 1 }

end Purelib.Approximation.Gaussian.Translation.Enclosure

end
