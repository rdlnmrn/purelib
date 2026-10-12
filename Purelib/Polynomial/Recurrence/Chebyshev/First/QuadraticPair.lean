module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the alternating binomial formula

Exercise 8.6 is proved by expanding the two finite powers in Theorem 59 and
pairing their even and odd terms.  Every sum below has an explicit natural
bound and is implemented by primitive recursion.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.QuadraticPair

variable {K : Type*} [ExplicitField K]

/-- Powers of an element satisfying the Chebyshev quadratic relation obey the same second-order recurrence. -/
private theorem
  quadraticPair_power_recurrence
    {R : Type*} [CommRing R] (root center : R)
    (quadratic : root ^ 2 = 2 * center * root - 1)
    (index : Nat) :
    root ^ (index + 2) =
      2 * center * root ^ (index + 1) - root ^ index := by
  calc
    root ^ (index + 2) = root ^ index * root ^ 2 := by rw [pow_add]
    _ = root ^ index * (2 * center * root - 1) := by rw [quadratic]
    _ = 2 * center * (root ^ index * root) - root ^ index := by ring1
    _ = 2 * center * root ^ (index + 1) - root ^ index := by rw [pow_succ]

/-- The sum of conjugate quadratic-pair powers equals the scalar embedding of twice the first Chebyshev value. -/
private theorem
  quadraticPair_chebyshev_trace
    (index : Nat) (center radialSquare : K)
    (radialEquation : radialSquare = 1 - center ^ 2) :
    let scalar :=
      Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
    let generator :=
      Algebra.Quadratic.Pair.generator (K := K)
        (radialSquare := radialSquare)
    (scalar center + generator) ^ index +
        (scalar center - generator) ^ index =
      scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst index center) := by
  dsimp only
  let scalar :=
    Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
  let generator :=
    Algebra.Quadratic.Pair.generator (K := K)
      (radialSquare := radialSquare)
  let positive := scalar center + generator
  let negative := scalar center - generator
  have positiveQuadratic :
      positive ^ 2 = 2 * scalar center * positive - 1 := by
    unfold positive scalar generator
    rw [Algebra.Quadratic.Pair.two_eq_scalar]
    apply Algebra.Quadratic.Pair.ext <;>
      simp only [pow_two, Algebra.Quadratic.Pair.mul_re,
        Algebra.Quadratic.Pair.mul_im, Algebra.Quadratic.Pair.add_re,
        Algebra.Quadratic.Pair.add_im, Algebra.Quadratic.Pair.sub_re,
        Algebra.Quadratic.Pair.sub_im, Algebra.Quadratic.Pair.scalar_re,
        Algebra.Quadratic.Pair.scalar_im, Algebra.Quadratic.Pair.generator_re,
        Algebra.Quadratic.Pair.generator_im, Algebra.Quadratic.Pair.one_re,
        Algebra.Quadratic.Pair.one_im]
    all_goals rw [radialEquation]
    all_goals ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * scalar center * negative - 1 := by
    unfold negative scalar generator
    rw [Algebra.Quadratic.Pair.two_eq_scalar]
    apply Algebra.Quadratic.Pair.ext <;>
      simp only [pow_two, Algebra.Quadratic.Pair.mul_re,
        Algebra.Quadratic.Pair.mul_im, Algebra.Quadratic.Pair.sub_re,
        Algebra.Quadratic.Pair.sub_im, Algebra.Quadratic.Pair.scalar_re,
        Algebra.Quadratic.Pair.scalar_im, Algebra.Quadratic.Pair.generator_re,
        Algebra.Quadratic.Pair.generator_im, Algebra.Quadratic.Pair.one_re,
        Algebra.Quadratic.Pair.one_im]
    all_goals rw [radialEquation]
    all_goals ring1
  let traceAt := fun current : Nat =>
    positive ^ current + negative ^ current =
      scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst current center)
  have allPairs : ∀ current : Nat,
      traceAt current ∧ traceAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold traceAt positive negative scalar generator Recurrence.Chebyshev.First.Basic.chebyshevFirst
          apply Algebra.Quadratic.Pair.ext <;>
            simp only [pow_zero, Algebra.Quadratic.Pair.add_re,
              Algebra.Quadratic.Pair.add_im, Algebra.Quadratic.Pair.one_re,
              Algebra.Quadratic.Pair.one_im, Algebra.Quadratic.Pair.scalar_re,
              Algebra.Quadratic.Pair.scalar_im]
          all_goals ring1
        · unfold traceAt positive negative scalar generator Recurrence.Chebyshev.First.Basic.chebyshevFirst
          apply Algebra.Quadratic.Pair.ext <;>
            simp only [Nat.zero_add, pow_one, Algebra.Quadratic.Pair.add_re,
              Algebra.Quadratic.Pair.add_im, Algebra.Quadratic.Pair.sub_re,
              Algebra.Quadratic.Pair.sub_im, Algebra.Quadratic.Pair.scalar_re,
              Algebra.Quadratic.Pair.scalar_im,
              Algebra.Quadratic.Pair.generator_re,
              Algebra.Quadratic.Pair.generator_im]
          all_goals ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold traceAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [Recurrence.Chebyshev.First.QuadraticPair.quadraticPair_power_recurrence
            positive (scalar center)
              positiveQuadratic,
            Recurrence.Chebyshev.First.QuadraticPair.quadraticPair_power_recurrence
              negative (scalar center)
              negativeQuadratic]
          calc
            (2 * scalar center * positive ^ (current + 1) -
                  positive ^ current) +
                (2 * scalar center * negative ^ (current + 1) -
                  negative ^ current) =
              2 * scalar center *
                  (positive ^ (current + 1) + negative ^ (current + 1)) -
                (positive ^ current + negative ^ current) := by
                  generalize positive ^ (current + 1) = positiveNextPower
                  generalize negative ^ (current + 1) = negativeNextPower
                  generalize positive ^ current = positivePriorPower
                  generalize negative ^ current = negativePriorPower
                  ring1
            _ = 2 * scalar center *
                  scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (current + 1) center) -
                scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst current center) := by
                  rw [inductionHypothesis.1, inductionHypothesis.2]
            _ = scalar
                (2 * center * (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (current + 1) center) -
                  2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst current center) := by
                  rw [Algebra.Quadratic.Pair.two_eq_scalar]
                  rw [← Algebra.Quadratic.Pair.scalar_mul,
                    ← Algebra.Quadratic.Pair.scalar_mul,
                    ← Algebra.Quadratic.Pair.scalar_sub]
            _ = scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (current + 2) center) := by
                  rw [Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ]
                  congr 1
                  ring1
  exact (allPairs index).1

/-- The finite quadratic-pair trace formula for the first Chebyshev
polynomial.  It exposes the constructive two-coordinate calculation used by
the spread-binomial formulas, so later finite-field arguments can supply
explicit powers of the two norm-one conjugates without choosing roots. -/
theorem chebyshevFirst_quadraticPair_trace
    (index : Nat) (center radialSquare : K)
    (radialEquation : radialSquare = 1 - center ^ 2) :
    let scalar :=
      Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
    let generator :=
      Algebra.Quadratic.Pair.generator (K := K)
        (radialSquare := radialSquare)
    (scalar center + generator) ^ index +
        (scalar center - generator) ^ index =
      scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst index center) :=
  Recurrence.Chebyshev.First.QuadraticPair.quadraticPair_chebyshev_trace index center
    radialSquare radialEquation
end Purelib.Polynomial.Recurrence.Chebyshev.First.QuadraticPair

end
