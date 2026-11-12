module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization.Power
public import Purelib.Polynomial.Multivariate.Gaussian.Renaming
public import Purelib.Polynomial.Multivariate.Gaussian.Conjugation
public import Purelib.Data.Fin.Check
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Data.List.Search
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Original binding and polynomial views of checked constructions

An exact view retains the actual leaf table, its original optional sidecars and
an original Normalized at the unchanged numerical channel. Arithmetic consumes
its retained denotation caches. Binary rebasing keeps both original tables and
admissions, aligning coefficients through authenticated actual interpreted
channel identities at the same original leaves and conjugation histories.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)
open Purelib.Data.List
open Purelib.Data.Fin (Check)

variable {arity : Nat}

/-- The actual original occurrence table, interpreted channels, sidecars and indexed normalization.

The finite conjugation count authenticates each actual channel against its
original unchanged leaf. Actual channels and sidecars are retained separately;
no equality of independently supplied admissions follows from that equation.
-/
abbrev Polynomial (environment : Fin arity → Annotated) (channel : CoherentNamed) :=
  (bindings : List (Basic.Binding environment)) × (depths : Fin bindings.length → Nat) ×
    (channels : Fin bindings.length → CoherentNamed) ×
      PLift (∀ index, channels index =
        CoherentNamed.conjIterate (Basic.Binding.channels bindings index) (depths index)) ×
        (_slots : Base.Slots bindings channels) × Normalized channels channel

namespace Polynomial

variable {environment : Fin arity → Annotated} {channel : CoherentNamed}

/-- Read the complete original occurrence table without rebuilding annotations. -/
@[expose] def bindings (input : Polynomial environment channel) : List (Basic.Binding environment) := input.1

/-- Read the actual finite conjugation history of each original occurrence. -/
@[expose] def depths (input : Polynomial environment channel) : Fin input.bindings.length → Nat := input.2.1

/-- Read each actual retained interpreted channel at its unchanged original occurrence. -/
@[expose] def channels (input : Polynomial environment channel) :
    Fin input.bindings.length → CoherentNamed := input.2.2.1

/-- Each actual interpreted channel is the original leaf's actual iterated conjugate. -/
theorem channels_eq (input : Polynomial environment channel) (index : Fin input.bindings.length) :
    input.channels index =
      CoherentNamed.conjIterate (Basic.Binding.channels input.bindings index) (input.depths index) :=
  input.2.2.2.1.down index

/-- Read the same original sidecar table, including absent and repeated actual interpreted owners. -/
@[expose] def slots (input : Polynomial environment channel) :
    Base.Slots input.bindings input.channels := input.2.2.2.2.1

/-- Read the original coefficient, product and suffix caches at their actual retained interpreted channels. -/
@[expose] def normalized (input : Polynomial environment channel) : Normalized input.channels channel := input.2.2.2.2.2

/-- Read one actual original optional generator at its same bounded occurrence. -/
@[expose] def generator (input : Polynomial environment channel) (index : Fin input.bindings.length) :
    Option (Algebraic.Sidecar (input.channels index)) := DependentProduct.get input.bindings input.slots index

/-- Retain an actual original normalization and its same original default-index sidecars. -/
@[expose] def ofOriginal (bindings : List (Basic.Binding environment)) (slots : Base.Slots bindings)
    (normalized : Normalized (Basic.Binding.channels bindings) channel) : Polynomial environment channel :=
  ⟨bindings, (fun _ => 0), Basic.Binding.channels bindings, ⟨fun _ => rfl⟩, slots, normalized⟩

/-- Retain the original base polynomial or normalize its same stored compilation once on actual demand.

Available original reductions are read literally. An omitted normalization
consumes the original retained compilation, annotations and root caches;
compilation, root isolation, reduction and Euclidean work are not repeated.
-/
@[expose] def ofBase {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (certificate : Base.Certificate cached) : Option (Polynomial environment cached.channel) :=
  match selected : cached.normalized with
  | none =>
      let retained := cached.compiled.normalize
      some (ofOriginal cached.compiled.bindings certificate.generatorSlots retained.polynomial)
  | some retained =>
      let reduced := cached.reduction retained selected
      some (ofOriginal cached.compiled.bindings certificate.generatorSlots reduced.polynomial)

/-- Negate the cached form while preserving the whole original input occurrence and admission tables. -/
@[expose] def neg (input : Polynomial environment channel) : Polynomial environment (CoherentNamed.neg channel) :=
  let cached := input.normalized.prepareNeg
  ⟨input.bindings, input.depths, input.channels, ⟨input.channels_eq⟩, input.slots,
    input.normalized.neg (some cached)⟩

/-- Power the cached form while preserving the whole original input occurrence and admission tables. -/
@[expose] def pow (input : Polynomial environment channel) (exponent : Nat) :
    Polynomial environment (Power.namedPower channel exponent) :=
  let cached := input.normalized.preparePow exponent
  ⟨input.bindings, input.depths, input.channels, ⟨input.channels_eq⟩, input.slots,
    input.normalized.pow exponent (some cached)⟩

/-- Conjugate the actual numerical input and each retained actual generator once.

The original leaf spine is unchanged. Original Sidecar.conj constructs the
actual conjugated admission, and the numerical target bank is shared with the
same original Normalized.conj cache construction. Repetition retains actual
iterated channels rather than replacing two conjugations by an original owner.
-/
@[expose] def conj (input : Polynomial environment channel) : Polynomial environment (CoherentNamed.conj channel) := by
  let cached := input.normalized.prepareConj
  let slots := Base.Slots.conj input.bindings (first := input.channels) (second := cached.channels)
    cached.channels_eq input.slots
  have origin : ∀ index, cached.channels index = CoherentNamed.conjIterate
      (Basic.Binding.channels input.bindings index) (input.depths index + 1) := by
    intro index
    exact (cached.channels_eq index).trans (congrArg CoherentNamed.conj (input.channels_eq index))
  exact ⟨input.bindings, (fun index => input.depths index + 1), cached.channels, ⟨origin⟩, slots,
    input.normalized.conj cached⟩

/-- Rebase actual cached coefficients through supplied operational channel relations and optional literal identities.

An actual literal identity bank permits reuse of the same stored variable
power channels. Purely operational agreement retains both source owners and
builds genuine target powers, using its own actual comparison payment.
-/
@[expose] def rebase (input : Polynomial environment channel) {size : Nat}
    (destination : Fin size → CoherentNamed) (mapping : Fin input.bindings.length → Fin size)
    (equivalent : ∀ index, NamedEquivalent (input.channels index).name (destination (mapping index)).name)
    (same : Option (PLift (∀ index, input.channels index = destination (mapping index)))) :
    Normalized destination channel :=
  let cached := input.normalized.prepareRename destination mapping same
  input.normalized.rename destination mapping equivalent (some cached)

/-- Appending actual interpreted channels retains both original leaf authentications pointwise. -/
theorem append_origin :
    (first second : List (Basic.Binding environment)) →
    (leftDepths : Fin first.length → Nat) → (rightDepths : Fin second.length → Nat) →
    (leftChannels : Fin first.length → CoherentNamed) → (rightChannels : Fin second.length → CoherentNamed) →
    (∀ index, leftChannels index = CoherentNamed.conjIterate (Basic.Binding.channels first index) (leftDepths index)) →
    (∀ index, rightChannels index =
      CoherentNamed.conjIterate (Basic.Binding.channels second index) (rightDepths index)) →
    ∀ index, DependentProduct.appendFn first second leftChannels rightChannels index =
      CoherentNamed.conjIterate (Basic.Binding.channels (first ++ second) index)
        (DependentProduct.appendFn first second leftDepths rightDepths index)
  | [], _, _, _, _, _, _, right, index => right index
  | _ :: remaining, second, leftDepths, rightDepths, leftChannels, rightChannels, left, right, index => by
      refine Fin.cases (left 0) ?_ index
      intro tail
      exact append_origin remaining second (fun index => leftDepths index.succ) rightDepths
        (fun index => leftChannels index.succ) rightChannels (fun index => left index.succ) right tail

/-- Select the first operationally matching original interpreted occurrence through the original bounded list search.

The table and actual input owners are unchanged. Matching original leaves
and conjugation remainders choose a coefficient position; complete histories
and original Sidecars remain stored separately at their actual channels.
-/
@[expose] def alignedIndex (bindings : List (Basic.Binding environment)) (depths : Fin bindings.length → Nat)
    (index : Fin bindings.length) : Fin bindings.length :=
  match (List.ofFn (fun index : Fin bindings.length => index)).find? (fun candidate =>
      decide ((Basic.Binding.read bindings index).leaf = (Basic.Binding.read bindings candidate).leaf ∧
        depths index % 2 = depths candidate % 2)) with
  | some retained => retained
  | none => index

/-- The selected finite coefficient representative has the same original leaf and conjugation remainder. -/
theorem alignedIndex_origin (bindings : List (Basic.Binding environment)) (depths : Fin bindings.length → Nat)
    (index : Fin bindings.length) :
    (Basic.Binding.read bindings index).leaf = (Basic.Binding.read bindings (alignedIndex bindings depths index)).leaf ∧
      depths index % 2 = depths (alignedIndex bindings depths index) % 2 := by
  unfold alignedIndex
  split
  · rename_i retained found
    have accepted := Search.find?_eq_some_accepts_certificate found
    exact of_decide_eq_true accepted
  · exact ⟨rfl, rfl⟩

/-- An aligned occurrence has its same entire original leaf annotation, without identifying supplied admissions. -/
theorem alignedIndex_original (bindings : List (Basic.Binding environment)) (depths : Fin bindings.length → Nat)
    (index : Fin bindings.length) :
    Basic.Binding.channels bindings index = Basic.Binding.channels bindings (alignedIndex bindings depths index) := by
  have same := (alignedIndex_origin bindings depths index).1
  have annotation : (Basic.Binding.read bindings index).annotation =
      (Basic.Binding.read bindings (alignedIndex bindings depths index)).annotation :=
    (Basic.Binding.read bindings index).annotation_eq.trans
      ((congrArg (Basic.Leaf.annotation environment) same).trans
        (Basic.Binding.read bindings (alignedIndex bindings depths index)).annotation_eq.symm)
  exact congrArg Annotated.channel annotation

/-- Equal complete histories yield literal whole-channel identity at the selected original occurrence. -/
theorem alignedIndex_channels (bindings : List (Basic.Binding environment)) (depths : Fin bindings.length → Nat)
    (channels : Fin bindings.length → CoherentNamed)
    (origin : ∀ index, channels index =
      CoherentNamed.conjIterate (Basic.Binding.channels bindings index) (depths index))
    (index : Fin bindings.length) (history : depths index = depths (alignedIndex bindings depths index)) :
    channels index = channels (alignedIndex bindings depths index) :=
  (origin index).trans
    ((congrArg₂ CoherentNamed.conjIterate (alignedIndex_original bindings depths index) history).trans
    (origin (alignedIndex bindings depths index)).symm)

/-- Different complete histories compare through actual iterated double-conjugation relations,
retaining both endpoints. -/
def alignedIndex_equivalent (bindings : List (Basic.Binding environment)) (depths : Fin bindings.length → Nat)
    (channels : Fin bindings.length → CoherentNamed)
    (origin : ∀ index, channels index =
      CoherentNamed.conjIterate (Basic.Binding.channels bindings index) (depths index))
    (index : Fin bindings.length) :
    NamedEquivalent (channels index).name (channels (alignedIndex bindings depths index)).name := by
  let selected := alignedIndex bindings depths index
  have compared := CoherentNamed.conjIterate_respects (Basic.Binding.channels bindings index)
    (depths index) (depths selected) (alignedIndex_origin bindings depths index).2
  have after := origin selected
  rewrite [← alignedIndex_original bindings depths index] at after
  rewrite [← origin index, ← after] at compared
  exact compared

/-- The same ordered child normalizations over the literal append of both actual interpreted tables. -/
abbrev Paired {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) :=
  Normalized (DependentProduct.appendFn left.bindings right.bindings left.channels right.channels) first ×
    Normalized (DependentProduct.appendFn left.bindings right.bindings left.channels right.channels) second

/-- Align equal original interpreted leaves while retaining both original tables, sidecars and numerical input caches.

All actual conjugated input channels remain stored at their original positions.
Operational double-conjugation can align coefficients while retaining both
actual inputs and their new target-power payment. Unavailable generator
agreement falls back accurately, and no equality of independently supplied
admissions or annihilators is inferred from equal original leaf channels.
-/
@[expose] def pair {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) : Paired left right := by
  let bindings := left.bindings ++ right.bindings
  let depths := DependentProduct.appendFn left.bindings right.bindings left.depths right.depths
  let channels := DependentProduct.appendFn left.bindings right.bindings left.channels right.channels
  have origin := append_origin left.bindings right.bindings left.depths right.depths left.channels right.channels
    left.channels_eq right.channels_eq
  let leftMapping := fun index => alignedIndex bindings depths
    (DependentProduct.leftIndex left.bindings right.bindings index)
  let rightMapping := fun index => alignedIndex bindings depths
    (DependentProduct.rightIndex left.bindings right.bindings index)
  have leftEquivalent : ∀ index, NamedEquivalent (left.channels index).name (channels (leftMapping index)).name := by
    intro index
    have compared := alignedIndex_equivalent bindings depths channels origin
      (DependentProduct.leftIndex left.bindings right.bindings index)
    dsimp only [channels] at compared
    rewrite [DependentProduct.appendFn_left] at compared
    exact compared
  have rightEquivalent : ∀ index, NamedEquivalent (right.channels index).name (channels (rightMapping index)).name := by
    intro index
    have compared := alignedIndex_equivalent bindings depths channels origin
      (DependentProduct.rightIndex left.bindings right.bindings index)
    dsimp only [channels] at compared
    rewrite [DependentProduct.appendFn_right] at compared
    exact compared
  let leftSame : Option (PLift (∀ index, left.channels index = channels (leftMapping index))) :=
    match Check.check (fun index => left.depths index = depths (leftMapping index)) with
    | .valid history => some ⟨fun index =>
        (DependentProduct.appendFn_left left.bindings right.bindings left.channels right.channels index).symm.trans
          (alignedIndex_channels bindings depths channels origin
            (DependentProduct.leftIndex left.bindings right.bindings index)
            ((DependentProduct.appendFn_left left.bindings right.bindings left.depths right.depths index).trans
              (history index)))⟩
    | .invalid _ _ => none
  let rightSame : Option (PLift (∀ index, right.channels index = channels (rightMapping index))) :=
    match Check.check (fun index => right.depths index = depths (rightMapping index)) with
    | .valid history => some ⟨fun index =>
        (DependentProduct.appendFn_right left.bindings right.bindings left.channels right.channels index).symm.trans
          (alignedIndex_channels bindings depths channels origin
            (DependentProduct.rightIndex left.bindings right.bindings index)
            ((DependentProduct.appendFn_right left.bindings right.bindings left.depths right.depths index).trans
              (history index)))⟩
    | .invalid _ _ => none
  exact ⟨left.rebase channels leftMapping leftEquivalent leftSame,
    right.rebase channels rightMapping rightEquivalent rightSame⟩

/-- Retain both actual tables and admission products with an already computed common-coordinate polynomial output. -/
@[expose] def ofPair {first second output : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second)
    (normalized :
      Normalized (DependentProduct.appendFn left.bindings right.bindings left.channels right.channels) output) :
    Polynomial environment output :=
  ⟨left.bindings ++ right.bindings,
    DependentProduct.appendFn left.bindings right.bindings left.depths right.depths,
    DependentProduct.appendFn left.bindings right.bindings left.channels right.channels,
    ⟨append_origin left.bindings right.bindings left.depths right.depths left.channels right.channels
      left.channels_eq right.channels_eq⟩,
    DependentProduct.append (fun channel => Option (Algebraic.Sidecar channel)) left.bindings right.bindings
      left.channels right.channels left.slots right.slots, normalized⟩

/-- Add exact original channels using their cached coordinates and both original admission products. -/
@[expose] def add {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) : Polynomial environment (CoherentNamed.add first second) :=
  let aligned := left.pair right
  let cached := aligned.1.prepareAdd aligned.2
  ofPair left right (aligned.1.add aligned.2 (some cached))

/-- Subtract exact original channels using their cached coordinates and both original admission products. -/
@[expose] def sub {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) :
    Polynomial environment (CoherentNamed.add first (CoherentNamed.neg second)) :=
  let aligned := left.pair right
  let cached := aligned.1.prepareSub aligned.2
  ofPair left right (aligned.1.sub aligned.2 (some cached))

/-- Multiply exact original channels using their cached coordinates and both original admission products. -/
@[expose] def mul {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) : Polynomial environment (CoherentNamed.mul first second) :=
  let aligned := left.pair right
  let cached := aligned.1.prepareMul aligned.2
  ofPair left right (aligned.1.mul aligned.2 (some cached))

/-- Exact negation preserves the whole original admission product. -/
theorem neg_slots (input : Polynomial environment channel) : input.neg.slots = input.slots := rfl

/-- Exact powering preserves the whole original admission product. -/
theorem pow_slots (input : Polynomial environment channel) (exponent : Nat) :
    (input.pow exponent).slots = input.slots := rfl

/-- Exact addition retains both whole actual admission products in their original order. -/
theorem add_slots {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) :
    (left.add right).slots = DependentProduct.append (fun channel => Option (Algebraic.Sidecar channel))
      left.bindings right.bindings left.channels right.channels left.slots right.slots := rfl

/-- Exact subtraction retains both whole actual admission products in their original order. -/
theorem sub_slots {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) :
    (left.sub right).slots = DependentProduct.append (fun channel => Option (Algebraic.Sidecar channel))
      left.bindings right.bindings left.channels right.channels left.slots right.slots := rfl

/-- Exact multiplication retains both whole actual admission products in their original order. -/
theorem mul_slots {first second : CoherentNamed} (left : Polynomial environment first)
    (right : Polynomial environment second) :
    (left.mul right).slots = DependentProduct.append (fun channel => Option (Algebraic.Sidecar channel))
      left.bindings right.bindings left.channels right.channels left.slots right.slots := rfl

/-- Combine available exact views only when both actual original children supply them. -/
@[expose] def combine {first second output : CoherentNamed}
    (operation : Polynomial environment first → Polynomial environment second → Polynomial environment output)
    (left : Option (Polynomial environment first)) (right : Option (Polynomial environment second)) :
    Option (Polynomial environment output) :=
  match left, right with
  | some first, some second => some (operation first second)
  | none, _ | _, none => none

end Polynomial

/-- Retain the actual original selected-generator certificate at the unchanged denominator channel. -/
abbrev GeneratorInverse (channel : CoherentNamed) :=
  (size : Nat) × (bindings : Fin size → CoherentNamed) ×
    (input : Normalized bindings channel) × Normalized.Inverse input

/-- Read the same actual numerical reciprocal output cached by the original selected-generator certificate. -/
@[expose] def GeneratorInverse.output {channel : CoherentNamed} (cache : GeneratorInverse channel) : CoherentNamed :=
  cache.2.2.2.output

/-- Read the same actual original denominator preparation from the retained unit-product certificate. -/
@[expose] def GeneratorInverse.prepared {channel : CoherentNamed} (cache : GeneratorInverse channel) :
    Prepared channel :=
  cache.2.2.2.prepared

/-- The demanded reciprocal preparation receipt is bound to this same actual original inverse certificate. -/
abbrev GeneratorInverse.Reciprocal {channel : CoherentNamed} (cache : GeneratorInverse channel) :=
  {receipt : cache.2.2.2.ReciprocalPreparation // receipt = cache.2.2.2.prepareReciprocal}

namespace GeneratorInverse

variable {environment : Fin arity → Annotated} {channel : CoherentNamed}

/-- An exact binding-table view of the same original generic selected-generator cache.

The whole-cache equation preserves the original arbitrary binding function,
normalization and inverse certificate. The supplied original admission table is
retained separately; no Sidecar identity follows from channel agreement alone.
-/
abbrev Source (environment : Fin arity → Annotated) (cache : GeneratorInverse channel) :=
  (input : Polynomial environment channel) ×
    {certificate : Normalized.Inverse input.normalized //
      (⟨input.bindings.length, input.channels, input.normalized, certificate⟩ : GeneratorInverse channel) = cache ∧
        input.generator certificate.index = some certificate.generator}

/-- Read the same complete original table, actual channels, sidecars and source normalization. -/
@[expose] def Source.input {cache : GeneratorInverse channel} (source : Source environment cache) :
    Polynomial environment channel := source.1

/-- Read the actual original inverse certificate without reconstructing its Euclidean or preparation data. -/
@[expose] def Source.certificate {cache : GeneratorInverse channel} (source : Source environment cache) :
    Normalized.Inverse source.input.normalized := source.2.val

/-- The complete generic inverse cache is this same actual original bounded source/certificate tuple. -/
theorem Source.cache_eq {cache : GeneratorInverse channel} (source : Source environment cache) :
    (⟨source.input.bindings.length, source.input.channels, source.input.normalized, source.certificate⟩ :
      GeneratorInverse channel) = cache := source.2.property.1

/-- The selected original generator is the identical stored Sidecar at its actual bounded source occurrence. -/
theorem Source.generator_eq {cache : GeneratorInverse channel} (source : Source environment cache) :
    source.input.generator source.certificate.index = some source.certificate.generator := source.2.property.2

/-- Construct the reciprocal polynomial from the same whole original selected-generator source view. -/
@[expose] def Source.normalizeOutput {cache : GeneratorInverse channel} (source : Source environment cache) :
    Polynomial environment cache.output := by
  rcases source with ⟨input, certificate⟩
  let output := certificate.val.normalizeOutput
  have same := congrArg GeneratorInverse.output certificate.property.1
  exact same ▸ (⟨input.bindings, input.depths, input.channels, ⟨input.channels_eq⟩, input.slots, output⟩ :
    Polynomial environment certificate.val.output)

/-- A selected-generator cache with its actual original binding and admission view. -/
abbrev Selected (environment : Fin arity → Annotated) (channel : CoherentNamed) :=
  (cache : GeneratorInverse channel) × Source environment cache

/-- Read the original generic selected-generator cache without replacing its owner. -/
@[expose] def Selected.cache (result : Selected environment channel) : GeneratorInverse channel := result.1

/-- Read the exact original binding-table view of this same retained cache. -/
@[expose] def Selected.source (result : Selected environment channel) : Source environment result.cache := result.2

end GeneratorInverse

namespace Polynomial

variable {environment : Fin arity → Annotated} {channel : CoherentNamed}

/-- The original ordered inverse scan at this same literal polynomial and admission table. -/
abbrev InverseCheck (input : Polynomial environment channel) := input.normalized.InverseCheck input.generator

/-- Run and retain the original selected-generator scan once at the actual polynomial cache. -/
@[expose] def inverseCheck (input : Polynomial environment channel)
    (supplied : Option (Prepared channel) := none) : input.InverseCheck :=
  input.normalized.inverseCheck input.generator supplied

/-- Retain a successful original inverse and the same actual source table without rebuilding either owner. -/
@[expose] def ofInverse (input : Polynomial environment channel) (certificate : Normalized.Inverse input.normalized)
    (selected : input.generator certificate.index = some certificate.generator) :
    GeneratorInverse.Selected environment channel :=
  ⟨⟨input.bindings.length, input.channels, input.normalized, certificate⟩, ⟨input, ⟨certificate, rfl, selected⟩⟩⟩

end Polynomial

/-- An available original polynomial view and its optional once computed demanded inverse check. -/
abbrev PolynomialCache (environment : Fin arity → Annotated) (channel : CoherentNamed) :=
  (polynomial : Option (Polynomial environment channel)) ×
    (match polynomial with | none => PUnit | some input => Option input.InverseCheck)

namespace PolynomialCache

variable {environment : Fin arity → Annotated} {channel : CoherentNamed}

/-- Read the literal optional polynomial view retained by this construction cache. -/
@[expose] def polynomial (cached : PolynomialCache environment channel) : Option (Polynomial environment channel) :=
  cached.1

/-- Store an actual polynomial view without performing a speculative inverse guard. -/
@[expose] def ofPolynomial (polynomial : Option (Polynomial environment channel)) :
    PolynomialCache environment channel :=
  match polynomial with
  | none => ⟨none, PUnit.unit⟩
  | some input => ⟨some input, none⟩

/-- Read whether an actual inverse request/result is already retained, without preparing another denominator. -/
@[expose] def hasInverseCheck (cached : PolynomialCache environment channel) : Bool :=
  match cached with
  | ⟨none, _⟩ => false
  | ⟨some _, old⟩ => old.isSome

/-- Pay one demanded inverse check or reuse its complete existing ordered cache.

The original normalization, occurrence order, unsupported cases and Euclidean
results are retained. An inconclusive exact route returns none for the existing
full materialization fallback; it proves no pole or impossibility.
-/
@[expose] def checkInverse (cached : PolynomialCache environment channel)
    (supplied : Option (Prepared channel) := none) :
    PolynomialCache environment channel × Option (GeneratorInverse.Selected environment channel) :=
  match cached with
  | ⟨none, _⟩ => ⟨⟨none, PUnit.unit⟩, none⟩
  | ⟨some input, old⟩ =>
      let checked := match old with | some retained => retained | none => input.inverseCheck supplied
      let result := match selected : checked.val.2 with
        | none => none
        | some certificate => some (input.ofInverse certificate
            (input.normalized.inverseCheck_generator input.generator checked certificate selected))
      ⟨⟨some input, some checked⟩, result⟩

/-- Demanded inverse checking preserves the complete original polynomial view and its literal caches. -/
theorem checkInverse_polynomial (cached : PolynomialCache environment channel)
    (supplied : Option (Prepared channel) := none) :
    (cached.checkInverse supplied).1.polynomial = cached.polynomial := by
  rcases cached with ⟨polynomial, old⟩
  cases polynomial <;> rfl

/-- Repeating a demanded check retains the entire existing polynomial and original ordered attempt cache. -/
theorem checkInverse_idempotent (cached : PolynomialCache environment channel)
    (supplied : Option (Prepared channel) := none) :
    (cached.checkInverse supplied).1.checkInverse.1 = (cached.checkInverse supplied).1 := by
  rcases cached with ⟨polynomial, old⟩
  cases polynomial with
  | none => rfl
  | some input => cases old <;> rfl

/-- Repeating a demanded check returns its same complete selected-generator certificate and source view. -/
theorem checkInverse_result (cached : PolynomialCache environment channel)
    (supplied : Option (Prepared channel) := none) :
    (cached.checkInverse supplied).1.checkInverse.2 = (cached.checkInverse supplied).2 := by
  rcases cached with ⟨polynomial, old⟩
  cases polynomial with
  | none => rfl
  | some input => cases old <;> rfl

/-- An already stored scan is reused on its actual request, before any proposed new preparation is inspected. -/
theorem checkInverse_cached (input : Polynomial environment channel) (checked : input.InverseCheck)
    (supplied : Option (Prepared channel)) :
    checkInverse (⟨some input, some checked⟩ : PolynomialCache environment channel) supplied =
      (⟨some input, some checked⟩,
       match selected : checked.val.2 with
       | none => none
       | some certificate => some (input.ofInverse certificate
           (input.normalized.inverseCheck_generator input.generator checked certificate selected))) := rfl

/-- A first inverse demand retains its exact supplied preparation request together with its complete actual scan. -/
theorem checkInverse_first (input : Polynomial environment channel) (supplied : Option (Prepared channel)) :
    (checkInverse (⟨some input, none⟩ : PolynomialCache environment channel) supplied).1 =
      ⟨some input, some (input.inverseCheck supplied)⟩ := rfl

/-- Storing a polynomial view reads back that same complete optional owner. -/
theorem ofPolynomial_polynomial (polynomial : Option (Polynomial environment channel)) :
    (ofPolynomial polynomial).polynomial = polynomial := by
  cases polynomial <;> rfl

/-- An original coefficient construction remains unrequested or equals the same complete stored output view. -/
@[expose] def Matches (cached : PolynomialCache environment channel)
    (construction : Unit → Option (Polynomial environment channel)) : Prop :=
  cached.polynomial = none ∨ cached.polynomial = construction ()

/-- Demand an original coefficient construction once and retain any already stored complete polynomial/check cache.

The producer is called only for an absent cache. Both original base and
reciprocal-output preparations use this same branch procedure, keeping their
actual construction and source-owner equations as its correctness index.
-/
@[expose] def prepare (cached : PolynomialCache environment channel)
    (construction : Unit → Option (Polynomial environment channel)) (origin : cached.Matches construction) :
    {polynomial : PolynomialCache environment channel // polynomial.polynomial = construction ()} :=
  match selected : cached.polynomial with
  | none => ⟨ofPolynomial (construction ()), ofPolynomial_polynomial _⟩
  | some _ =>
      have same : cached.polynomial = construction () := by
        cases origin with
        | inl absent =>
            have impossible : (none : Option (Polynomial environment channel)) = some _ := absent.symm.trans selected
            cases impossible
        | inr actual => exact actual
      ⟨cached, same⟩

end PolynomialCache

/-- The original base guard and its stored polynomial preparation retain the same certificate parent. -/
abbrev BaseCache {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    (cached : Base.Cached environment expression) (certificate : Base.Certificate cached) :=
  Option ((request : Option (Prepared cached.channel)) ×
    {result : Option (Base.Certificate.InverseCheck certificate) // result = certificate.inverseCheck request}) ×
      PolynomialCache environment cached.channel

namespace BaseCache

variable {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    {cached : Base.Cached environment expression} {certificate : Base.Certificate cached}

/-- An absent base view remains unrequested, while every stored view is the original preparation's actual output. -/
@[expose] def Matches (retained : BaseCache cached certificate) : Prop :=
  retained.2.Matches (fun _ => Polynomial.ofBase cached certificate)

/-- Prepare an original-evidence base only on demand, or return its same existing polynomial/check cache. -/
@[expose] def preparePolynomial (retained : BaseCache cached certificate) (origin : retained.Matches) :
    {polynomial : PolynomialCache environment cached.channel //
      polynomial.polynomial = Polynomial.ofBase cached certificate} :=
  retained.2.prepare (fun _ => Polynomial.ofBase cached certificate) origin

end BaseCache

namespace GeneratorInverse

variable {environment : Fin arity → Annotated} {channel : CoherentNamed}

/-- Retained reciprocal request, exact source view and output polynomial at the same original inverse cache. -/
abbrev Caches (environment : Fin arity → Annotated) (cache : GeneratorInverse channel) :=
  Option (Reciprocal cache) × (_source : Option (Source environment cache)) ×
    PolynomialCache environment cache.output

namespace Caches

/-- Read the literal optional demanded receipt without preparing another output. -/
@[expose] def reciprocal {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    Option (Reciprocal cache) := cached.1

/-- Read the same actual original source normalization, binding table and admission cache view. -/
@[expose] def source {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    Option (Source environment cache) := cached.2.1

/-- Read the literal stored output polynomial and its demanded inverse check. -/
@[expose] def polynomial {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    PolynomialCache environment cache.output := cached.2.2

/-- Read an already demanded reciprocal's retained observation, without preparing an absent receipt. -/
@[expose] def cachedSource {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    Option (Prepared.Sum.Source cache.output) :=
  cached.reciprocal.map (fun receipt => receipt.val.cachedSource)

/-- The view of a stored reciprocal consumes its same original preparation receipt. -/
theorem cachedSource_cached {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (receipt : Reciprocal cache) (selected : cached.reciprocal = some receipt) :
    cached.cachedSource = some receipt.val.cachedSource := by
  unfold cachedSource
  rewrite [selected]
  rfl

/-- Replace only the demanded receipt while retaining the same exact source and output polynomial caches. -/
@[expose] def withReciprocal {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (reciprocal : Option (Reciprocal cache)) : Caches environment cache :=
  ⟨reciprocal, cached.source, cached.polynomial⟩

/-- Retain a demanded output inverse check while preserving the actual reciprocal receipt and source owners. -/
@[expose] def withPolynomial {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (polynomial : PolynomialCache environment cache.output) : Caches environment cache :=
  ⟨cached.reciprocal, cached.source, polynomial⟩

/-- Demand one original reciprocal-output receipt or reuse the exact already stored request and result.

Only an absent receipt invokes the original inverse's preparation procedure.
The complete source and polynomial caches remain literal. This branch is shared
by denominator refinement and the original checked decision operation.
-/
@[expose] def demandReciprocal {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    Caches environment cache × Prepared cache.output :=
  let receipt := match cached.reciprocal with
    | some retained => retained
    | none => ⟨cache.2.2.2.prepareReciprocal, rfl⟩
  ⟨cached.withReciprocal (some receipt), receipt.val.prepared⟩

/-- Demanding a reciprocal retains the exact original source view. -/
theorem demandReciprocal_source {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    cached.demandReciprocal.1.source = cached.source := rfl

/-- Demanding a reciprocal retains the exact original polynomial and ordered inverse-check cache. -/
theorem demandReciprocal_polynomial {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    cached.demandReciprocal.1.polynomial = cached.polynomial := rfl

/-- A stored reciprocal request returns its same complete actual cache and prepared presentation. -/
theorem demandReciprocal_cached {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (receipt : Reciprocal cache) (selected : cached.reciprocal = some receipt) :
    cached.demandReciprocal = (cached, receipt.val.prepared) := by
  rcases cached with ⟨old, source, polynomial⟩
  change old = some receipt at selected
  cases selected
  rfl

/-- A repeated reciprocal demand reuses its whole first cache and actual prepared result. -/
theorem demandReciprocal_idempotent {cache : GeneratorInverse channel} (cached : Caches environment cache) :
    cached.demandReciprocal.1.demandReciprocal = cached.demandReciprocal := by
  rcases cached with ⟨old, source, polynomial⟩
  cases old <;> rfl

/-- Output coordinates remain unrequested, or are the same original retained Horner construction's complete output. -/
@[expose] def Matches {cache : GeneratorInverse channel} (cached : Caches environment cache) : Prop :=
  cached.polynomial.Matches (fun _ => cached.source.map Source.normalizeOutput)

/-- The shared reciprocal demand preserves the same original polynomial construction equation. -/
theorem demandReciprocal_matches {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (origin : cached.Matches) : cached.demandReciprocal.1.Matches := origin

/-- Prepare original reciprocal output coordinates only on demand, or retain the same stored polynomial/check cache. -/
@[expose] def preparePolynomial {cache : GeneratorInverse channel} (cached : Caches environment cache)
    (origin : cached.Matches) : {polynomial : PolynomialCache environment cache.output //
      polynomial.polynomial = cached.source.map Source.normalizeOutput} :=
  cached.polynomial.prepare (fun _ => cached.source.map Source.normalizeOutput) origin

end Caches
end GeneratorInverse
end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
end
