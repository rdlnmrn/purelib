module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Name
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Addition
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Subtraction

section
public section

/-!
# The integrated exponential family agrees with the existing `exp(1)-1` name

The right side below is the ordinary stateful subtraction of the existing
finite exponential name and exact one.  Its actual sampler retains the
exponential source index as the first component of its state.  We compare
through that index and its requested radius, rather than assuming equality
of independently selected samples or introducing a completed exponential.
-/

namespace Purelib.Integration.Exponential.Equivalence.Reference

open Purelib.Approximation

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Approximation.Gaussian in
/-- The Gaussian name formed by subtracting the exact unit from the Horner exponential name at one. -/
@[expose] def exponentialMinusOne : Name.Basic.Named :=
  (Gaussian.Exponential.Horner.Name.named 1 (by decide)).sub (Name.Basic.Named.exact 1)

open Purelib in
open Purelib.Approximation.Gaussian in
/-- Read the exact product-process state after the requested number of reference sampling refinements. -/
@[expose] def referenceState (index : Nat) : Nat × Unit :=
  Process.Sampling.stateAt exponentialMinusOne.process exponentialMinusOne.state index

open Purelib in
/-- Read the retained Horner source index from the original reference process state. -/
@[expose] def referenceSourceIndex (index : Nat) : Nat := (referenceState index).1

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
/-- The reference process's Horner source index does not decrease in one sampling step. -/
theorem referenceSourceIndex_step (index : Nat) :
    referenceSourceIndex index ≤ referenceSourceIndex (index + 1) := by
  change referenceSourceIndex index ≤
    Geometric.Search.firstQuarterBelow 10 (referenceSourceIndex index)
      (Request.Basic.Name.additiveInputTarget (Process.Sampling.refinementTarget (index + 1)))
  exact Geometric.Search.firstQuarterBelow_ge _ _ _

open Purelib in
open Purelib.Data.Nat in
/-- Ordered reference sampling stages have ordered retained Horner source indices.

The supplied stage order gives the exact natural difference between stages.
Finite successor induction relates their retained Horner source indices. -/
theorem referenceSourceIndex_monotone {earlier later : Nat} (order : earlier ≤ later) :
    referenceSourceIndex earlier ≤ referenceSourceIndex later := by
  have extended : ∀ extra : Nat,
      referenceSourceIndex earlier ≤
        referenceSourceIndex (earlier + extra) := by
    intro extra
    induction extra with
    | zero => exact Nat.le_refl _
    | succ extra inductionHypothesis =>
        exact inductionHypothesis.trans
          (referenceSourceIndex_step (earlier + extra))
  have retained := extended (later - earlier)
  rw [Subtraction.add_sub_of_le order] at retained
  exact retained

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- The sampled reference name is the original Horner value at its retained source index, minus one. -/
theorem reference_sample (index : Nat) :
    (Name.Sampling.approximation exponentialMinusOne).sample index =
      Gaussian.Exponential.Horner.Sample.sample 1 (referenceSourceIndex index) - 1 := by
  change Gaussian.Exponential.Horner.Sample.sample 1 (referenceSourceIndex index) + -(1 : Basic.Canonical) = _
  exact (Basic.sub_eq_add_neg _ _).symm

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
/-- The retained Horner source radius is strictly below the original reference stage's refinement target. -/
theorem reference_source_radius (index : Nat) :
    Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) < Process.Sampling.refinementTarget index := by
  have accurate := Process.Sampling.stateAt_accurate
    exponentialMinusOne.process exponentialMinusOne.state index
  change 2 * (Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) + 0) <
    Process.Sampling.refinementTarget index at accurate
  apply lt_of_le_of_lt _ accurate
  calc
    Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) =
        0 + Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) := by ring1
    _ ≤ Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) + Geometric.Basic.quarterRadius 10
      (referenceSourceIndex index) :=
      add_le_add (Geometric.Basic.quarterRadius_nonneg (by decide) _) le_rfl
    _ = 2 * (Geometric.Basic.quarterRadius 10 (referenceSourceIndex index) + 0) := by ring1
end Purelib.Integration.Exponential.Equivalence.Reference

end
