module

public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Coherence.Conjugation
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Nat.Parity
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling

/-! # Conjugation of original coherent numerical channels -/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

/-- Conjugate the original channel while retaining its original process state and refinement program. -/
@[expose] def conj (channel : CoherentNamed) : CoherentNamed :=
  { name := { process := channel.name.process.conj, state := channel.name.state }
    coherent := channel.coherent.conj }

private theorem conjugate_state (process : Process) (start : process.State) :
    ∀ index, Process.Sampling.stateAt process.conj start index =
      Process.Sampling.stateAt process start index
  | 0 => rfl
  | index + 1 => congrArg (fun state => process.refine state
      (Process.Sampling.refinementTarget (index + 1))
      (Process.Sampling.refinementTarget_pos (index + 1))) (conjugate_state process start index)

/-- Every original finite sampling index reads the conjugate of the same original channel sample. -/
theorem conj_sample (channel : CoherentNamed) (index : Nat) :
    (Name.Sampling.approximation (conj channel).name).sample index =
      Basic.conj ((Name.Sampling.approximation channel.name).sample index) := by
  change Basic.conj (channel.name.process.witness
    (Process.Sampling.stateAt channel.name.process.conj channel.name.state index)).val = _
  rw [conjugate_state]
  rfl

/-- An original operational comparison transports through conjugation using the same paid indices and squared bound. -/
def conj_respects {first second : CoherentNamed} (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent (conj first).name (conj second).name where
  compare firstStart secondStart target positive := by
    let comparison := equivalent.compare firstStart secondStart target positive
    refine ⟨comparison.leftIndex, comparison.rightIndex, comparison.left_ge, comparison.right_ge, ?_⟩
    intro firstLater secondLater firstOrder secondOrder
    rw [conj_sample, conj_sample, Basic.conj_eq_canonical, Basic.conj_eq_canonical,
      ← Basic.Canonical.conj_sub, ← Basic.conj_eq_canonical, Norm.Basic.normSq_conj]
    exact comparison.close firstOrder secondOrder

/-- Conjugating an original channel realizes an actual retained target with conjugated same-index readings. -/
def conj_geometricWith {channel : CoherentNamed} (source target : GeometricApproximation)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (sample_eq : ∀ index, target.sample index = Basic.conj (source.sample index)) :
    NamedEquivalent (conj channel).name target.toApproximation.toNamed := by
  let compared := Equivalence.Equivalent.trans equivalent
    (Equivalence.Equivalent.toNamed_sampling source.toApproximation)
  have direct : Equivalence.Equivalent (Name.Sampling.approximation (conj channel).name)
      target.toApproximation := by
    refine ⟨?_⟩
    intro firstStart secondStart target positive
    let comparison := compared.compare firstStart secondStart target positive
    refine ⟨comparison.leftIndex, comparison.rightIndex, comparison.left_ge, comparison.right_ge, ?_⟩
    intro firstLater secondLater firstOrder secondOrder
    rw [conj_sample, GeometricApproximation.toApproximation_sample, sample_eq secondLater,
      Basic.conj_eq_canonical, Basic.conj_eq_canonical,
      ← Basic.Canonical.conj_sub, ← Basic.conj_eq_canonical, Norm.Basic.normSq_conj]
    exact comparison.close firstOrder secondOrder
  exact Equivalence.Equivalent.trans direct
    (Equivalence.Equivalent.symm (Equivalence.Equivalent.toNamed_sampling target.toApproximation))

/-- Conjugating an original realization agrees with conjugating its same retained geometric sample program. -/
def conj_geometric {channel : CoherentNamed} (source : GeometricApproximation)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    NamedEquivalent (conj channel).name source.conj.toApproximation.toNamed :=
  conj_geometricWith source source.conj equivalent (fun _ => rfl)

/-- Conjugating the original exact coherent channel agrees with the exact conjugated Gaussian coefficient. -/
def conj_exact (point : Basic.Canonical) :
    NamedEquivalent (conj (Coherence.exact point)).name (Coherence.exact (Basic.Canonical.conj point)).name := by
  let first := conj (Coherence.exact point)
  let second := Coherence.exact (Basic.Canonical.conj point)
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Name.Sampling.approximation first.name) (Name.Sampling.approximation second.name) (by
      intro index
      change (Name.Sampling.approximation (conj (Coherence.exact point)).name).sample index = _
      rewrite [conj_sample]
      change Basic.conj point = Basic.Canonical.conj point
      exact Basic.conj_eq_canonical point)
  exact (Sequence.Name.Equivalence.named_toSamplingNamed first.name).trans
    (samples.toNamed.trans (Sequence.Name.Equivalence.named_toSamplingNamed second.name).symm)

/-- Retain each actual iterated conjugate of the original numerical process. -/
@[expose] def conjIterate (channel : CoherentNamed) : Nat → CoherentNamed
  | 0 => channel
  | count + 1 => conj (conjIterate channel count)

/-- Zero conjugations retain the whole original coherent channel. -/
theorem conjIterate_zero (channel : CoherentNamed) : conjIterate channel 0 = channel := rfl

/-- A successor retains the actual conjugate of the same preceding channel. -/
theorem conjIterate_succ (channel : CoherentNamed) (count : Nat) :
    conjIterate channel (count + 1) = conj (conjIterate channel count) := rfl

/-- Twice conjugating an actual channel agrees operationally with that same original channel.

The original and twice-conjugated processes remain distinct owners. The
comparison follows their equal samples at the same original bounded indices.
-/
def conj_conj (channel : CoherentNamed) :
    NamedEquivalent (conj (conj channel)).name channel.name := by
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Name.Sampling.approximation (conj (conj channel)).name)
    (Name.Sampling.approximation channel.name) (by
      intro index
      rewrite [conj_sample, conj_sample, Basic.conj_conj]
      rfl)
  exact (Sequence.Name.Equivalence.named_toSamplingNamed (conj (conj channel)).name).trans
    (samples.toNamed.trans (Sequence.Name.Equivalence.named_toSamplingNamed channel.name).symm)

/-- Compare each actual iterated conjugate with its same original zero-or-one conjugation history. -/
private def conjIterate_reduce (channel : CoherentNamed) : (count : Nat) →
    NamedEquivalent (conjIterate channel count).name (conjIterate channel (count % 2)).name
  | 0 => NamedEquivalent.refl _
  | 1 => NamedEquivalent.refl _
  | count + 2 => by
      change NamedEquivalent (conj (conj (conjIterate channel count))).name
        (conjIterate channel ((count + 2) % 2)).name
      rewrite [Parity.add_two_mod]
      exact (conj_conj (conjIterate channel count)).trans (conjIterate_reduce channel count)

/-- Compare two actual iterated conjugations through their original operational double-conjugation laws.

The complete actual input channels remain the endpoints. Equality of the
finite remainders chooses a comparison path, not a nominal process or Sidecar
identity, and each cancelled pair retains the original conj_conj relation.
-/
def conjIterate_respects (channel : CoherentNamed) (first second : Nat) (same : first % 2 = second % 2) :
    NamedEquivalent (conjIterate channel first).name (conjIterate channel second).name := by
  have after := (conjIterate_reduce channel second).symm
  rewrite [← same] at after
  exact (conjIterate_reduce channel first).trans after

end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

end
