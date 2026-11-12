module

public import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Checked finite sample prefixes of original approximation programs -/

public section

namespace Purelib.Approximation.Gaussian.Sequence

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

namespace SamplePrefix

set_option genInjectivity false in
/-- One actual saved sample at its unchanged original approximation index. -/
structure Entry (original : ApproximationData) where
  /-- The original finite sample index. -/
  index : Nat
  /-- The actual retained Gaussian observation. -/
  value : Canonical
  /-- The retained observation is the exact original reading at the same index. -/
  value_eq : value = original.sample index

constructive_injectivity Entry

/-- Read the retained observation on a cache hit and the original sample function on a miss. -/
@[expose] def read (original : ApproximationData) (index : Nat) : List (Entry original) → Canonical
  | [] => original.sample index
  | entry :: remaining => if entry.index = index then entry.value else read original index remaining

/-- Every retained or fallback reading agrees with the exact original scalar sample at that index. -/
theorem read_eq (original : ApproximationData) (index : Nat) (entries : List (Entry original)) :
    read original index entries = original.sample index := by
  induction entries with
  | nil => rfl
  | cons entry remaining previous =>
      dsimp only [read]
      split
      · rename_i same
        exact entry.value_eq.trans (congrArg original.sample same)
      · exact previous

/-- A matching first retained entry is consumed directly without running the original sample function. -/
theorem read_head {original : ApproximationData} (entry : Entry original) (remaining : List (Entry original)) :
    read original entry.index (entry :: remaining) = entry.value := by
  dsimp only [read]
  rewrite [if_pos rfl]
  rfl

end SamplePrefix

set_option genInjectivity false in
/-- An original approximation with its actual finite checked sample table and unchanged-index execution view.

The stored original record remains identical to the supplied parent. Entries
retain actual observations and scalar readbacks. The execution view changes
only sample lookup; radius, refiner, requests and bounds remain original.
-/
structure SamplePrefix (original : ApproximationData) where
  /-- The actual original approximation record retained for cache misses. -/
  source : ApproximationData
  /-- The retained source is the supplied complete original approximation. -/
  source_eq : source = original
  /-- The actual finite original-index observations. -/
  entries : List (SamplePrefix.Entry original)

constructive_injectivity SamplePrefix

namespace SamplePrefix

variable {original : ApproximationData}

/-- Retain the original approximation and its supplied checked finite sample entries. -/
@[expose] def ofEntries (original : ApproximationData) (entries : List (Entry original)) : SamplePrefix original :=
  ⟨original, rfl, entries⟩

/-- Transfer a saved entry to another original program with the same all-index scalar readback. -/
@[expose] def Entry.onSamples {first second : ApproximationData} (entry : Entry first)
    (same : ∀ index, first.sample index = second.sample index) : Entry second :=
  ⟨entry.index, entry.value, entry.value_eq.trans (same entry.index)⟩

/-- Consume the actual saved observations through a pointwise-identical original numerical program.

Only scalar readings are transported. The supplied complete target program is
retained for misses, and every saved value keeps its original finite index.
-/
@[expose] def onSamples (cache : SamplePrefix original) (target : ApproximationData)
    (same : ∀ index, original.sample index = target.sample index) : SamplePrefix target :=
  ofEntries target (cache.entries.map fun entry => entry.onSamples same)

/-- Read the same original numerical program through the actual retained finite observation table. -/
@[expose] def sample (cache : SamplePrefix original) (index : Nat) : Canonical :=
  read cache.source index (cache.source_eq.symm ▸ cache.entries)

/-- Every finite observation from the retained table or original fallback is the original scalar reading. -/
theorem sample_eq (cache : SamplePrefix original) (index : Nat) : cache.sample index = original.sample index := by
  unfold sample
  have reading := read_eq cache.source index (cache.source_eq.symm ▸ cache.entries)
  exact reading.trans (congrArg (fun source : ApproximationData => source.sample index) cache.source_eq)

/-- Consume the finite saved observations while retaining every original numerical request and bound.

Pointwise scalar readbacks transfer movement and magnitude bounds. No equality
of changed sample functions or complete changed records is asserted.
-/
@[expose] def view (cache : SamplePrefix original) : ApproximationData where
  sample := cache.sample
  radiusSq := original.radiusSq
  radiusSq_nonneg := original.radiusSq_nonneg
  later_close := by
    intro earlier later order
    rewrite [cache.sample_eq later, cache.sample_eq earlier]
    exact original.later_close order
  refineIndex := original.refineIndex
  refineIndex_ge := original.refineIndex_ge
  refineIndex_accurate := original.refineIndex_accurate
  centerBound := original.centerBound
  centerBound_nonneg := original.centerBound_nonneg
  sample_bounded := by
    intro index
    rewrite [cache.sample_eq]
    exact original.sample_bounded index

/-- The execution view reads the actual saved cache with original fallback at the same finite index. -/
theorem view_sample (cache : SamplePrefix original) (index : Nat) : cache.view.sample index = cache.sample index := rfl

/-- The execution view retains the exact original squared radius at every finite index. -/
theorem view_radiusSq (cache : SamplePrefix original) (index : Nat) :
    cache.view.radiusSq index = original.radiusSq index := rfl

/-- Every execution-view refinement is the same original request from the same starting index. -/
theorem view_refineIndex (cache : SamplePrefix original) (start : Nat) (target : Rational) (positive : 0 < target) :
    cache.view.refineIndex start target positive = original.refineIndex start target positive := rfl

/-- The cache-backed named execution view has the same actual finite state trajectory as the original name. -/
theorem named_state (cache : SamplePrefix original) : ∀ index,
    Process.Sampling.stateAt cache.view.toProcess (show Nat from 0) index =
      Process.Sampling.stateAt original.toProcess (show Nat from 0) index
  | 0 => rfl
  | index + 1 => congrArg
      (fun state => original.refineIndex state (Process.Sampling.refinementTarget (index + 1))
        (Process.Sampling.refinementTarget_pos (index + 1))) (cache.named_state index)

/-- Every named-view observation reads the same original name's finite scalar observation at its unchanged state. -/
theorem named_sample (cache : SamplePrefix original) (index : Nat) :
    (Name.Sampling.approximation cache.view.toNamed).sample index =
      (Name.Sampling.approximation original.toNamed).sample index := by
  change cache.sample (Process.Sampling.stateAt cache.view.toProcess (show Nat from 0) index) =
    original.sample (Process.Sampling.stateAt original.toProcess (show Nat from 0) index)
  rewrite [cache.named_state, cache.sample_eq]
  rfl

/-- Retain requested original named observations using the same cached primitive sample table.

The named process keeps its original refinement trajectory and indices. Each
stored scalar is read through the supplied primitive cache; unlisted named
requests retain the original named sampling fallback.
-/
@[expose] def namedSamples (cache : SamplePrefix original) (indices : List Nat) :
    SamplePrefix (Name.Sampling.approximation original.toNamed) :=
  ofEntries (Name.Sampling.approximation original.toNamed)
    (indices.map fun index =>
      ⟨index, (Name.Sampling.approximation cache.view.toNamed).sample index, cache.named_sample index⟩)

/-- Retain an existing named comparison's exact indices and bounds while consuming the saved right-hand samples. -/
@[expose] def comparisonRight (cache : SamplePrefix original) {left : Name.Basic.Named}
    (equivalent : Equivalence.NamedEquivalent left original.toNamed) :
    Equivalence.NamedEquivalent left cache.view.toNamed :=
  equivalent.withSamples (Name.Sampling.approximation left) (Name.Sampling.approximation cache.view.toNamed)
    (fun _ => rfl) cache.named_sample

end SamplePrefix

end Purelib.Approximation.Gaussian.Sequence

end
