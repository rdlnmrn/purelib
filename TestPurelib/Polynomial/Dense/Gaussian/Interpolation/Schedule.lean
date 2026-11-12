module

import Purelib.Polynomial.Dense.Gaussian.Interpolation.Schedule
import Purelib.Data.Rat.Fraction.Cast

/-!
# Unequal residual targets on a retained original synthetic chain

The schedule is prepared from three positive targets and separation one,
before the original polynomial or its samples are consumed. Every actual
retained remainder is nonzero, so the certificates pay genuine residual
bounds rather than identifying the rational nodes as exact roots.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Interpolation.Schedule

open Purelib
open Data.Gaussian
open Data.Gaussian.Basic (Canonical)
open Data.Rat.Fraction
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Interpolation

/-- Three different positive source-residual targets in their original order. -/
private def targets : List Rational := [1 / Cast.fromInt 128, 1 / Cast.fromInt 64, 1 / Cast.fromInt 32]

/-- Each original target supplies its exact constructive positivity certificate. -/
private theorem targets_positive : ∀ target ∈ targets, 0 < target := by
  intro target member
  cases member with
  | head => decide +kernel
  | tail _ member =>
      cases member with
      | head => decide +kernel
      | tail _ member =>
          cases member with
          | head => decide +kernel
          | tail _ impossible => nomatch impossible

/-- The original backward schedule uses only the positive separation and target data. -/
private def schedule : Schedule.Prepared 1 targets := Schedule.prepare 1 (by decide) targets targets_positive

/-- The actual initial payment is computed before any source samples are supplied. -/
private theorem initial_payment : schedule.val.initial = 1 / Cast.fromInt 512 := by decide +kernel

/-- The same stored first tail retains its actual different sufficient incoming payment. -/
private theorem next_payment : schedule.val.next.initial = 1 / Cast.fromInt 128 := by decide +kernel

/-- The same stored final cell uses the final original target as its incoming payment. -/
private theorem final_payment : schedule.val.next.next.initial = 1 / Cast.fromInt 32 := by decide +kernel

/-- The first original target and its same cached incoming payment are both strictly positive. -/
private theorem initial_positive : 0 < schedule.val.initial := schedule.property.positive

/-- A small nonzero original cubic with three distinct rational sampling nodes. -/
private def polynomial : CoefficientPolynomial :=
  ⟨[⟨1 / Cast.fromInt 1024, 0⟩, ⟨2 / Cast.fromInt 1024, 0⟩, ⟨3 / Cast.fromInt 1024, 0⟩, ⟨4 / Cast.fromInt 1024, 0⟩]⟩

/-- The original ordered rational nodes have common squared-distance floor one. -/
private def nodes : List Canonical := [0, 1, 2]

/-- Every distinct original ordered node pair pays the same positive squared-distance floor. -/
private theorem separated : nodes.Pairwise (fun left right =>
    (1 : Rational) ≤ Norm.Basic.normSq (left - right)) := by
  apply List.Pairwise.cons
  · intro other member
    cases member with
    | head => decide +kernel
    | tail _ member =>
        cases member with
        | head => decide +kernel
        | tail _ impossible => nomatch impossible
  · apply List.Pairwise.cons
    · intro other member
      cases member with
      | head => decide +kernel
      | tail _ impossible => nomatch impossible
    · exact List.Pairwise.cons (fun _ impossible => nomatch impossible) List.Pairwise.nil

/-- Actual original source sample quadrances pay the once-computed initial schedule tolerance. -/
private theorem source_samples : ∀ node ∈ nodes,
    Norm.Basic.normSq (polynomial.eval node) ≤ schedule.val.initial := by
  intro node member
  cases member with
  | head => decide +kernel
  | tail _ member =>
      cases member with
      | head => decide +kernel
      | tail _ member =>
          cases member with
          | head => decide +kernel
          | tail _ impossible => nomatch impossible

/-- The actual original materialized chain retains every sequential quotient exactly once. -/
private def expansion : Expansion polynomial nodes := Expansion.prepare polynomial nodes

/-- The first actual retained remainder is nonzero and has its original exact scalar value. -/
private theorem first_remainder :
    expansion.first.remainder = (⟨1 / Cast.fromInt 256, 0⟩ : Canonical) := by decide +kernel

/-- The second actual retained remainder comes from the same first quotient and is nonzero. -/
private theorem second_remainder :
    expansion.next.first.remainder = (⟨3 / Cast.fromInt 512, 0⟩ : Canonical) := by decide +kernel

/-- The third actual retained remainder comes from the same second quotient and is nonzero. -/
private theorem third_remainder :
    expansion.next.next.first.remainder = (⟨5 / Cast.fromInt 1024, 0⟩ : Canonical) := by decide +kernel

/-- All three actual retained residuals are explicitly nonzero despite satisfying their different targets. -/
private theorem remainders_nonzero : expansion.first.remainder ≠ 0 ∧
    expansion.next.first.remainder ≠ 0 ∧ expansion.next.next.first.remainder ≠ 0 := by
  rewrite [first_remainder, second_remainder, third_remainder]
  decide +kernel

/-- The original schedule certifies every actual retained nonzero residual against its corresponding target. -/
private theorem paid : expansion.Pays targets :=
  expansion.pays (by decide) schedule.val schedule.property rfl separated source_samples

/-- The first constructive payment reads the actual cached first remainder. -/
private theorem first_paid :
    Norm.Basic.normSq expansion.first.remainder ≤ (1 : Rational) / Cast.fromInt 128 :=
  paid.head

/-- The second constructive payment reads the same first quotient's retained expansion. -/
private theorem second_paid :
    Norm.Basic.normSq expansion.next.first.remainder ≤ (1 : Rational) / Cast.fromInt 64 :=
  paid.next.head

/-- Original source evaluation readback pays the first target without another division. -/
private theorem first_value_paid :
    Norm.Basic.normSq (polynomial.eval 0) ≤ (1 : Rational) / Cast.fromInt 128 :=
  paid.head_eval

/-- The original stored first quotient's head-node value pays the second target without redivision. -/
private theorem second_value_paid :
    Norm.Basic.normSq (expansion.first.quotient.eval 1) ≤ (1 : Rational) / Cast.fromInt 64 :=
  paid.next.head_eval

/-- The final constructive payment reads the same second quotient's retained expansion. -/
private theorem third_paid :
    Norm.Basic.normSq expansion.next.next.first.remainder ≤ (1 : Rational) / Cast.fromInt 32 :=
  paid.next.next.head

/-- The complete certificate accounts for all and only the three original target occurrences. -/
private theorem complete_count : targets.length = nodes.length := paid.length

end TestPurelib.Polynomial.Dense.Gaussian.Interpolation.Schedule
