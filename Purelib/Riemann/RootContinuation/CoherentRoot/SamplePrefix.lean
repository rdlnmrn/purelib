module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix.Addition
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence.Sampling

/-! # Original root-state observations as checked numerical sample tables -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

open Purelib.Approximation.Gaussian

variable {polynomial : GaussianPolynomial} {ambient : Box}
  {track : WindingOneTrack polynomial ambient}

/-- Consume one retained root state as the original numerical approximation's same-index scalar observation. -/
@[expose] def approximationEntry (root : CertifiedName track) (entry : StateCache.Entry track) :
    Sequence.SamplePrefix.Entry root.approximation where
  index := entry.index
  value := entry.value.get.box.anchor
  value_eq := by
    have same : entry.value.get = root.stateAt entry.index :=
      entry.value_eq.trans (root.stateAt_eq entry.index).symm
    exact (congrArg (fun state : WindingOneState polynomial ambient => state.box.anchor) same).trans
      (root.sample_stateAt entry.index).symm

/-- Read one original named observation from its retained primitive-state entry.

The supplied index identity binds the actual entry to the unchanged canonical
sampling trajectory. The returned entry retains that named index and the same
cached anchor; no original state or named sample producer is evaluated again.
-/
def namedEntry (root : CertifiedName track) (entry : StateCache.Entry track) (index : Nat)
    (primitive : entry.index = Equivalence.Sampling.emittedSampleIndex root.approximation index) :
    {reading : Sequence.SamplePrefix.Entry (Name.Sampling.approximation root.value.name) //
      reading.index = index} := by
  let saved := root.approximationEntry entry
  have scalar : saved.value = root.approximation.sample entry.index := saved.value_eq
  have actual : (Name.Sampling.approximation root.value.name).sample index =
      root.approximation.sample (Equivalence.Sampling.emittedSampleIndex root.approximation index) := by
    rewrite [root.value_approximation]
    exact Equivalence.Sampling.emittedSample_eq root.approximation index
  exact ⟨⟨index, saved.value,
    scalar.trans ((congrArg root.approximation.sample primitive).trans actual.symm)⟩, rfl⟩

/-- Execute the actual original approximation through saved original state anchors at unchanged finite indices. -/
@[expose] def approximationSamples (root : CertifiedName track) (entries : List (StateCache.Entry track)) :
    Sequence.SamplePrefix root.approximation :=
  Sequence.SamplePrefix.ofEntries root.approximation (entries.map root.approximationEntry)

/-- Read saved original root states through another retained numerical program with the same scalar observations. -/
@[expose] def samplesFor (root : CertifiedName track) (target : Sequence.ApproximationData)
    (same : ∀ index, root.approximation.sample index = target.sample index)
    (entries : List (StateCache.Entry track)) : Sequence.SamplePrefix target :=
  (root.approximationSamples entries).onSamples target same

/-- Saved root observations read the exact original certified name's scalar samples at all named indices. -/
theorem approximationSamples_named (root : CertifiedName track)
    (entries : List (StateCache.Entry track)) (index : Nat) :
    (Name.Sampling.approximation (root.approximationSamples entries).view.toNamed).sample index =
      (Name.Sampling.approximation root.value.name).sample index := by
  rewrite [(root.approximationSamples entries).named_sample, root.value_approximation]
  rfl

/-- Read requested original named observations through the retained exact root-state entries.

The finite view keeps the same certified root, named source and requested
indices. Its named scalars consume those actual cached primitive anchors
instead of invoking a fresh original root-state producer on a covered read.
-/
@[expose] def namedSamples (root : CertifiedName track) (entries : List (StateCache.Entry track))
    (indices : List Nat) : Sequence.SamplePrefix (Name.Sampling.approximation root.value.name) :=
  ((root.approximationSamples entries).namedSamples indices).onSamples
    (Name.Sampling.approximation root.value.name) (fun _ => by
      rewrite [root.value_approximation]
      rfl)

/-- Two saved original root prefixes retain every scalar observation of their original paired sum process. -/
theorem approximationSamples_add {otherPolynomial : GaussianPolynomial} {otherAmbient : Box}
    {otherTrack : WindingOneTrack otherPolynomial otherAmbient}
    (root : CertifiedName track) (other : CertifiedName otherTrack)
    (entries : List (StateCache.Entry track)) (otherEntries : List (StateCache.Entry otherTrack)) (index : Nat) :
    (Name.Sampling.approximation ((root.approximationSamples entries).view.toNamed.add
      (other.approximationSamples otherEntries).view.toNamed)).sample index =
      (Name.Sampling.approximation (Name.Coherent.CoherentNamed.add root.value other.value).name).sample index := by
  rewrite [(root.approximationSamples entries).add_sample (other.approximationSamples otherEntries) index,
    root.value_approximation, other.value_approximation]
  rfl

end Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

end
