module
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Negating the actual operational square-root channel

Negation preserves the square certificate and its displayed denominator
clearance. Equal-index finite samples also prove that an apart channel cannot
be operationally equivalent to its own negative.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootNegation

open Purelib.Riemann.RootContinuation.CertifiedSquareRoot

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Approximation.Gaussian
/-- Negating the original Gaussian process preserves its sampled state sequence. -/
private theorem negStateAt (process : Approximation.Gaussian.Process)
    (start : process.State) (index : Nat) :
    Process.Sampling.stateAt process.neg start index =
      Process.Sampling.stateAt process start index := by
  induction index with
  | zero => rfl
  | succ index induction =>
    rw [Process.Sampling.stateAt_succ,
      Process.Sampling.stateAt_succ, induction]
    rfl

/-- Sampling the negated original channel yields the negation of its exact original sample. -/
theorem neg_sample (input : CoherentNamed) (index : Nat) :
    (Name.Sampling.approximation input.neg.name).sample index =
      -(Name.Sampling.approximation input.name).sample index := by
  change Process.Sampling.witnessAt input.name.process.neg input.name.state index =
    -Process.Sampling.witnessAt input.name.process input.name.state index
  unfold Process.Sampling.witnessAt
  rw [negStateAt]
  rfl

end

open Purelib.Data.Gaussian in
/-- Negation preserves the original channel equivalence and its requested comparison indices. -/
@[expose] def neg_equivalent (first second : CoherentNamed)
    (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent first.neg.name second.neg.name where
  compare := by
    intro firstStart secondStart target positive
    let comparison := equivalent.compare firstStart secondStart target positive
    refine ⟨comparison.leftIndex, comparison.rightIndex,
      comparison.left_ge, comparison.right_ge, ?_⟩
    intro left right leftOrder rightOrder
    rw [neg_sample, neg_sample,
      show ∀ a b : Gaussian, -a - -b = -(a - b) by intros; ring1, Norm.Basic.normSq_neg]
    exact comparison.close leftOrder rightOrder

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- Negate a channel's apartness certificate with the same positive lower bound.

The reflected enclosure retains the original process, state and lower-bound
certificate; no replacement channel or comparison index is selected. -/
@[expose] def negApart (input : CoherentNamed)
    (apart : Name.Basic.Named.Apart input.name) :
    Name.Basic.Named.Apart input.neg.name where
  certificate :=
    { lowerSq := apart.certificate.lowerSq
      positive := apart.certificate.positive
      lower := by
        intro state value inside
        change (input.name.process.ball state).neg.Contains value at inside
        have reflected := Approximation.Gaussian.Enclosure.Ball.contains_neg inside
        have original : (input.name.process.ball state).Contains (-value) := by
          simpa only [Approximation.Gaussian.Enclosure.Ball.Contains,
            Approximation.Gaussian.Enclosure.Ball.neg, neg_neg] using reflected
        exact (apart.certificate.lower state original).trans_eq (Norm.Basic.normSq_neg value) }

open Purelib.Approximation.Gaussian in
/-- Negate a certified square-root channel while preserving its exact parameter and square identity.

The original sampled product remains unchanged under paired negation; apartness is transported with its same lower
bound, so no replacement root is selected. -/
@[expose] def Certificate.neg {parameter : Gaussian} (source : Certificate parameter) :
    Certificate parameter := by
  let value := source.value.neg
  have samples : ∀ index,
      (Sequence.Arithmetic.Product.sampledProductApproximation value.name value.name).sample index =
      (Sequence.Arithmetic.Product.sampledProductApproximation source.value.name source.value.name).sample index := by
    intro index
    change (Name.Sampling.approximation source.value.neg.name).sample index *
        (Name.Sampling.approximation source.value.neg.name).sample index = _
    rw [neg_sample]
    change (-_ : Gaussian) * (-_) = _ * _
    ring1
  let sampled := Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Sequence.Equivalence.approximationEquivalentOfSamplesEq _ _ samples)
  exact
    { value := value
      apart := negApart source.value source.apart
      square := Equivalence.NamedEquivalent.trans
        (Name.Coherent.Arithmetic.Product.Bridge.coherentMul_toNamed value value)
        (Equivalence.NamedEquivalent.trans sampled (Equivalence.NamedEquivalent.trans
          (Equivalence.NamedEquivalent.symm (Name.Coherent.Arithmetic.Product.Bridge.coherentMul_toNamed source.value
            source.value))
          source.square)) }

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An apart channel cannot be equivalent to its own negation.

A common retained sample index satisfies both comparison thresholds. Its positive
lower bound contradicts the requested distance to the negated same sample. -/
theorem apart_not_neg (input : CoherentNamed)
    (apart : Name.Basic.Named.Apart input.name)
    (equivalent : NamedEquivalent input.name input.neg.name) : False := by
  let comparison := equivalent.compare 0 0 apart.certificate.lowerSq apart.certificate.positive
  let index := max comparison.leftIndex comparison.rightIndex
  have close := comparison.close
    (Purelib.Data.Nat.Order.le_max_left comparison.leftIndex comparison.rightIndex)
    (Purelib.Data.Nat.Order.le_max_right comparison.leftIndex comparison.rightIndex)
  rw [Norm.Basic.normSq_eq_canonical] at close
  change normSq ((Name.Sampling.approximation input.name).sample index -
    (Name.Sampling.approximation input.neg.name).sample index) < apart.certificate.lowerSq at close
  rw [neg_sample] at close
  have doubled (value : Gaussian) : normSq (value - -value) = 4 * normSq value := by
    simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im]
    ring1
  rw [doubled] at close
  have lower := Name.Apart.Sampling.sampled_lower input apart index
  rw [Norm.Basic.normSq_eq_canonical] at lower
  have scaled : apart.certificate.lowerSq ≤
      4 * normSq ((Name.Sampling.approximation input.name).sample index) :=
    lower.trans (by
      have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 : Coordinate) ≤ 4 by decide)
        (Basic.Canonical.normSq_nonneg ((Name.Sampling.approximation input.name).sample index))
      simpa only [Fraction.Field.one_mul] using bound)
  exact (not_lt_of_ge scaled) close

end Purelib.Riemann.RootContinuation.SquareRootNegation
