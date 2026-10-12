module
import Purelib.Data.List.Append
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Gauge

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Gauge

open Purelib.Data.Rat.Fraction

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingPrefixMinimaxWordAlias -> Word

open Purelib.Data.List

open Purelib.Data.Rat

section
public section

/-!
# Finite prefix minimax over the pure CCL bitstream

This module formalizes the information-theoretic theorem of Section 7.  It is
only about finite `List Bool` tags.  Chordal geometry, boxed names, arithmetic
sidecars, completed streams, and collections of all compatible values do not
occur here.
-/

namespace Purelib.Data.List.BinaryPrefix.Minimax

/-- Take the larger gauge distance from one finite candidate to two displayed witness
words. -/
@[expose] def twoWitnessRadius (gauge : Gauge) (candidate left right :
  Word) :
    Rational :=
  max (Gauge.distance gauge candidate left) (Gauge.distance gauge candidate right)

/-- Two witnesses in opposite bit branches characterize optimal finite-prefix candidates.

A candidate extending their common stem has maximum distance exactly the stem gauge.
Every candidate outside that prefix has strictly larger maximum distance, for any
retained witness tails. -/
theorem twoWitness_minimax (gauge : Gauge)
    (stem candidate leftTail rightTail : Word) :
    let leftWitness := stem ++ false :: leftTail
    let rightWitness := stem ++ true :: rightTail
    (stem.IsPrefix candidate →
      twoWitnessRadius gauge candidate leftWitness rightWitness =
        gauge.value stem) ∧
    (¬stem.IsPrefix candidate →
      gauge.value stem <
        twoWitnessRadius gauge candidate leftWitness rightWitness) := by
  dsimp only
  constructor
  · intro candidatePrefix
    rcases candidatePrefix with ⟨candidateTail, rfl⟩
    have leftUpper :
        Gauge.distance gauge (stem ++ candidateTail)
            (stem ++ false :: leftTail) ≤ gauge.value stem :=
      Gauge.distance_le_of_common_prefix gauge
        (List.prefix_append _ _) (List.prefix_append _ _)
    have rightUpper :
        Gauge.distance gauge (stem ++ candidateTail)
            (stem ++ true :: rightTail) ≤ gauge.value stem :=
      Gauge.distance_le_of_common_prefix gauge
        (List.prefix_append _ _) (List.prefix_append _ _)
    apply le_antisymm
    · exact Fraction.Order.Basic.max_le leftUpper rightUpper
    · cases candidateTail with
      | nil =>
          rw [Append.append_nil]
          calc
            gauge.value stem =
                Gauge.distance gauge stem (stem ++ false :: leftTail) :=
              (Gauge.distance_prefix_child gauge stem leftTail false).symm
            _ ≤ max
                (Gauge.distance gauge stem (stem ++ false :: leftTail))
                (Gauge.distance gauge stem (stem ++ true :: rightTail)) :=
              Fraction.Order.Basic.le_max_left _ _
      | cons bit remaining =>
          cases bit with
          | false =>
              calc
                gauge.value stem = Gauge.distance gauge
                    (stem ++ false :: remaining)
                    (stem ++ true :: rightTail) :=
                  (Gauge.distance_opposite_child gauge stem remaining rightTail
                    false).symm
                _ ≤ max
                    (Gauge.distance gauge (stem ++ false :: remaining)
                      (stem ++ false :: leftTail))
                    (Gauge.distance gauge (stem ++ false :: remaining)
                      (stem ++ true :: rightTail)) := Fraction.Order.Basic.le_max_right _ _
          | true =>
              calc
                gauge.value stem = Gauge.distance gauge
                    (stem ++ true :: remaining)
                    (stem ++ false :: leftTail) :=
                  (Gauge.distance_opposite_child gauge stem remaining leftTail
                    true).symm
                _ ≤ max
                    (Gauge.distance gauge (stem ++ true :: remaining)
                      (stem ++ false :: leftTail))
                    (Gauge.distance gauge (stem ++ true :: remaining)
                      (stem ++ true :: rightTail)) := Fraction.Order.Basic.le_max_left _ _
  · intro notPrefix
    let common := Basic.lcp candidate stem
    have commonPrefix : common.IsPrefix stem := Basic.lcp_prefix_right _ _
    have commonDifferent : common ≠ stem := by
      intro equal
      apply notPrefix
      rw [← equal]
      exact Basic.lcp_prefix_left candidate stem
    have gaugeStrict : gauge.value stem < gauge.value common :=
      gauge.lt_of_strict_prefix commonPrefix commonDifferent
    have candidateDifferent :
        candidate ≠ stem ++ false :: leftTail := by
      intro equal
      apply notPrefix
      rw [equal]
      exact List.prefix_append _ _
    have leftDistance :
        Gauge.distance gauge candidate (stem ++ false :: leftTail) =
          gauge.value common := by
      rw [Gauge.distance, if_neg candidateDifferent,
        Basic.lcp_append_right_of_not_prefix candidate stem
          (false :: leftTail) notPrefix]
    exact gaugeStrict.trans_le (leftDistance.ge.trans (Fraction.Order.Basic.le_max_left _ _))
end Purelib.Data.List.BinaryPrefix.Minimax

end
