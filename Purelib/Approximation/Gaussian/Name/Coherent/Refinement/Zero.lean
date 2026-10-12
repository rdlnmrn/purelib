module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Persistent exact-zero obstructions to division

This is extra finite input evidence, not an automatic interpretation of an
unsuccessful numerical test. The invariant is scoped to the retained source
and candidates with provenance back to it. A later numerical ball need not
have radius zero for the obstruction to remain valid.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical

/-- Strong exact-zero candidate evidence at one retained source. This is distinct from operational equivalence to zero
with approximate candidates. -/
def ZeroCandidates (denominator :
  Coherent.CoherentNamed) (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) : Prop :=
  ∀ {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible state.source value → value = 0

namespace ZeroCandidates

/-- Exact-zero candidate evidence persists along any supplied backwards candidate transport between retained states. -/
theorem after {denominator :
  Coherent.CoherentNamed} {first last : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator first)
    (persists : ∀ {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) :
        Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator last :=
  fun possible => zero (persists possible)

/-- Canonical refinement preserves exact-zero candidate evidence at the retained denominator state. -/
theorem advance {denominator :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator state) :
      Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator state.advance :=
  zero.after (fun possible => denominator.name.process.refine_persists state.source
    (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex) possible)

/-- Every finitely reachable refinement state retains the original exact-zero candidate evidence. -/
theorem reachable {denominator :
  Coherent.CoherentNamed} {first last : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator first) (path :
      State.Reachable first last) :
    Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator last := zero.after
      path.possible_persists

/-- Exact-zero candidate evidence contradicts apartness of the process based at that same retained source. -/
theorem incompatible {denominator :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator state)
    (evidence : Possible.PossibleApart (Gaussian.Process.Based.based denominator.name.process state.source)) :
    False := by
  let witness := denominator.name.process.witness state.source
  have lower := evidence.lower
    (BasedState.initial denominator.name.process state.source)
    witness.property
  rw [zero witness.property, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower) evidence.positive

/-- Exact-zero candidates prevent the retained source ball from passing the center-separation test. -/
theorem not_separated {denominator :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator state) :
    ¬ 2 * (denominator.name.process.ball state.source).radiusSq <
      Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center :=
  fun separated => zero.incompatible (Preparation.evidenceOfSeparation state separated)

/-- Arbitrary requested-target refinement also preserves the obstruction; no canonical-step assertion is needed. -/
theorem requested {denominator :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator state) {target :
      Fraction.Rational} {positive : 0 < target}
    (inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator state target positive) :
    Approximation.Gaussian.Name.Coherent.Refinement.Zero.ZeroCandidates denominator inspection.retained := zero.after
      inspection.possible_at_start

end ZeroCandidates

end Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

end
