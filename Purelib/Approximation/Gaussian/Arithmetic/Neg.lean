module
public import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Arithmetic.Neg

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name

section
public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

/-- Negating the exact Gaussian channel is operationally equivalent to the exact channel of its negated value. -/
@[expose] def exactNeg (value : Data.Gaussian.Basic.Canonical) : Gaussian.Equivalence.NamedEquivalent
    (CoherentNamed.neg (Coherence.exact value)).name
    (Coherence.exact (-value)).name :=
  Equivalent.of_constant_samples _ _ (-value) (fun _ => rfl) (fun _ => rfl)

end

public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

section
/-- Negation preserves the original process's canonical sampling states. -/
private theorem negStateAt
    (process : Process)
    (start : process.State) (index : Nat) :
    Gaussian.Process.Sampling.stateAt
        (Process.neg process) start index =
      Gaussian.Process.Sampling.stateAt process start index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rw [Gaussian.Process.Sampling.stateAt_succ,
        Gaussian.Process.Sampling.stateAt_succ, induction]
      change process.refine _ _ _ = process.refine _ _ _
      rfl
/-- The canonical sample of the negated coherent name is the negative of the original sample at the same index. -/
private theorem negSampling_sample (input :
  CoherentNamed) (index : Nat) :
    (Sampling.approximation
      (Named.neg input.name)).sample index =
      -(Sampling.approximation input.name).sample
        index := by
  change
    Gaussian.Process.Sampling.witnessAt
        (Process.neg input.name.process)
        input.name.state index =
      -Gaussian.Process.Sampling.witnessAt
        input.name.process input.name.state index
  unfold Gaussian.Process.Sampling.witnessAt
  rw [Purelib.Approximation.Gaussian.Arithmetic.Neg.negStateAt]
  rfl
end

/-- A coherent CCL name plus its actual stateful negation is operationally the terminating exact zero name. -/
@[expose] def coherentAdd_neg_right (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add input.name
        (Named.neg input.name))
      (Named.exact 0) := by
  let negative := CoherentNamed.neg input
  let zeroApproximation :=
    Sampling.approximation
      (Named.exact 0)
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation input.name negative.name).toNamed
      zeroApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation input.name negative.name)
        zeroApproximation
        (by
          intro index
          rw [Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample,
            show
              (Sampling.approximation
                negative.name).sample index =
                -(Sampling.approximation
                    input.name).sample index by
              simpa only [negative,
                CoherentNamed.neg] using
                Purelib.Approximation.Gaussian.Arithmetic.Neg.negSampling_sample input index]
          change
            (Sampling.approximation input.name).sample
                  index +
                -(Sampling.approximation
                    input.name).sample index = 0
          apply Data.Gaussian.Basic.ext <;>
            simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
              Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im,
              Purelib.Data.Gaussian.Basic.zero_re, Purelib.Data.Gaussian.Basic.zero_im] <;>
            ring1))
  exact NamedEquivalent.trans
    (by
      simpa only [negative,
        CoherentNamed.neg] using
        Bridge.coherentAdd_toNamed input negative)
    (NamedEquivalent.trans pointwise
      (NamedEquivalent.symm
        (Equivalence.named_toSamplingNamed
          (Named.exact 0))))

/-- Negation on the left gives the same operational zero law. -/
@[expose] def coherentAdd_neg_left (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.neg input.name) input.name)
      (Named.exact 0) :=
  NamedEquivalent.trans
    (Add.coherentAdd_comm
      (CoherentNamed.neg input) input)
    (Approximation.Gaussian.Arithmetic.Neg.coherentAdd_neg_right input)

end

end

end Purelib.Approximation.Gaussian.Arithmetic.Neg
