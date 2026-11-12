module

public import Purelib.Polynomial.Approximation.Gaussian.Localization.Coverage
public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Separation
public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Decision
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Approximation.Gaussian.Sequence.Selection
import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stable selection of original multiplicity root candidates

The same retained decomposition computes factor coprimality once. Its original
root caches supply a materialized tail-separation bank. Complete residual
coverage and source coherence select one fixed original occurrence and prove
an all-input comparison to that occurrence's actual retained channel.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Localization.Preparation

open Purelib
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Riemann.RootContinuation

variable {polynomial : CoefficientPolynomial} {original : GeometricApproximation}

set_option genInjectivity false in
/-- A fixed original root occurrence with its same retained factor certificates, pair bank and source anchor.

The separation bank keeps the actual original candidate programs and tail
stages. The anchor consumes that same bank and the original source's computed
coverage, without requiring a supplied result branch or successful search.
-/
structure Selection (preparation : Preparation polynomial original) where
  /-- The actual ordered Bézout certificates on the same original factor list. -/
  factorPairs : Multiplicity.Basis.Positive.CoprimePairs preparation.factors.entries
  /-- The materialized original root-pair tail bounds and same-entry common summaries. -/
  rootPairs : Sequence.Selection.Pairs preparation.roots.candidates
  /-- The actual source anchor and original candidate at this same cached separation budget. -/
  anchor : Sequence.Selection.Anchor preparation.source.toApproximation rootPairs.separated

constructive_injectivity Selection

/-- Compute the original ordered coprimality certificates from the same retained factor decomposition. -/
def factorPairs (preparation : Preparation polynomial original) :
    Multiplicity.Basis.Positive.CoprimePairs preparation.factors.entries :=
  let pairwise : preparation.factors.entries.Pairwise fun left right =>
      Multiplicity.CoprimeRelation left.part right.part := by
    rewrite [preparation.factors.entries_eq]
    exact preparation.decomposition.positiveMultiplicityEntries_pairwise
  Multiplicity.Basis.Positive.CoprimePairs.ofPairwise preparation.factors.entries pairwise

/-- Compute one stable original root occurrence from the same retained polynomial residual program and root caches. -/
def select (preparation : Preparation polynomial original) : Selection preparation :=
  let factorPairs := preparation.factorPairs
  let rootPairs := preparation.roots.pairs factorPairs
  let anchor := Sequence.Selection.Anchor.ofCoverage preparation.source.toApproximation
    rootPairs.separated preparation.coverage
  ⟨factorPairs, rootPairs, anchor⟩

/-- Naming the factor-pair construction preserves the complete original selection and all its caches. -/
private theorem select_eq_original (preparation : Preparation polynomial original) :
    preparation.select = (by
      let pairwise : preparation.factors.entries.Pairwise fun left right =>
          Multiplicity.CoprimeRelation left.part right.part := by
        rewrite [preparation.factors.entries_eq]
        exact preparation.decomposition.positiveMultiplicityEntries_pairwise
      let factorPairs := Multiplicity.Basis.Positive.CoprimePairs.ofPairwise preparation.factors.entries pairwise
      let rootPairs := preparation.roots.pairs factorPairs
      let anchor := Sequence.Selection.Anchor.ofCoverage preparation.source.toApproximation
        rootPairs.separated preparation.coverage
      exact ⟨factorPairs, rootPairs, anchor⟩) := (rfl)

namespace Selection

open CoherentRoot (CertifiedName WindingOneState)

/-- Construct the original stable selection from its retained pair caches and authenticated nearby result.

Both pair caches keep their complete defining readbacks. The request retains
the original zero start and one-sixteenth gap allocation; its nearby witness
supplies the exact original anchor without executing localization again. -/
def ofNearby (preparation : Preparation polynomial original)
    (factorPairs : { value : Multiplicity.Basis.Positive.CoprimePairs preparation.factors.entries //
      value = preparation.factorPairs })
    (rootPairs : { value : Sequence.Selection.Pairs preparation.roots.candidates //
      value = preparation.roots.pairs factorPairs.val })
    (request : Sequence.Selection.Coverage.Request preparation.coverage 0 (rootPairs.val.separated.gap / 16))
    (nearby : { value : Sequence.Selection.Nearby preparation.roots.candidates
      (preparation.source.sample request.index) (rootPairs.val.separated.gap / 16) //
      value = request.locate }) :
    { value : Selection preparation // value = preparation.select } :=
  let anchor := Sequence.Selection.Anchor.ofNearby preparation.source.toApproximation
    rootPairs.val.separated preparation.coverage request nearby
  ⟨⟨factorPairs.val, rootPairs.val, anchor⟩, by
    rcases factorPairs with ⟨factorPairs, factorPairsEq⟩
    cases factorPairsEq
    rcases rootPairs with ⟨rootPairs, rootPairsEq⟩
    cases rootPairsEq
    change Selection.mk _ _
        (Sequence.Selection.Anchor.ofNearby preparation.source.toApproximation
          (preparation.roots.pairs preparation.factorPairs).separated preparation.coverage request nearby) = _
    exact congrArg (Selection.mk preparation.factorPairs (preparation.roots.pairs preparation.factorPairs))
      (Sequence.Selection.Anchor.ofNearby_eq preparation.source.toApproximation
        (preparation.roots.pairs preparation.factorPairs).separated preparation.coverage request nearby)⟩

/-- Read the selected occurrence with its same original factor and bounded root indices. -/
@[expose] def occurrence {preparation : Preparation polynomial original} (selection : Selection preparation) :
    CoherentRoot.Multiplicity.Index preparation.factors.factors :=
  CoherentRoot.Multiplicity.Index.ofFin preparation.factors.factors selection.anchor.nearby.owner

/-- Read the source multiplicity at the same selected original factor occurrence.

This is the multiplicity in the displayed result polynomial's decomposition.
It does not identify multiplicities belonging to independent input parents.
-/
@[expose] def multiplicity {preparation : Preparation polynomial original} (selection : Selection preparation) : Nat :=
  (preparation.factors.entries.get selection.occurrence.factorIndex).multiplicity

/-- The selected source occurrence retains its original strictly positive multiplicity. -/
theorem multiplicity_positive {preparation : Preparation polynomial original} (selection : Selection preparation) :
    0 < selection.multiplicity :=
  (preparation.factors.entries.get selection.occurrence.factorIndex).multiplicityPositive

/-- Read the actual retained approximation of the fixed original selected root occurrence. -/
@[expose] def approximation {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Sequence.ApproximationData := preparation.roots.approximation selection.occurrence

/-- Read the actual retained coherent channel of the same fixed original selected root occurrence. -/
@[expose] def channel {preparation : Preparation polynomial original} (selection : Selection preparation) :
    CoherentNamed := preparation.roots.channel selection.occurrence

/-- Read the exact selected original squarefree factor independently of the complete displayed annihilator. -/
@[expose] def factorPolynomial {preparation : Preparation polynomial original} (selection : Selection preparation) :
    CoefficientPolynomial := (preparation.factors.entries.get selection.occurrence.factorIndex).part.polynomial

/-- Read the selected factor's actual retained residual program without recreating its root cache.

The polynomial is the selected original squarefree factor. The preparation
and occurrence still retain the full displayed annihilator and multiplicity.
The actual selected root program is retained unchanged through channel transport.
-/
def residualCertificate {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Polynomial.Approximation.Gaussian.Residual selection.factorPolynomial selection.channel :=
  let retained := (preparation.roots.get selection.occurrence.factorIndex).residualCertificate
    selection.occurrence.rootIndex
  have equivalent : Equivalence.NamedEquivalent selection.channel.name
      ((preparation.roots.get selection.occurrence.factorIndex).channel selection.occurrence.rootIndex).name := by
    unfold channel
    rewrite [preparation.roots.channel_projections selection.occurrence]
    exact Equivalence.NamedEquivalent.refl _
  retained.transport equivalent

/-- The selected factor residual consumes the same actual selected original root program. -/
theorem residualCertificate_source {preparation : Preparation polynomial original}
    (selection : Selection preparation) : selection.residualCertificate.source =
      ((preparation.roots.get selection.occurrence.factorIndex).residualCertificate
        selection.occurrence.rootIndex).source := by
  unfold residualCertificate
  exact Polynomial.Approximation.Gaussian.Residual.transport_source _ _

/-- Read an original selected linear entry's exact scalar evidence through the same occurrence projections. -/
@[expose] def scalar? {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Option (Provenance.Rational.Basic.RationalSidecar selection.channel) := by
  unfold channel
  rewrite [preparation.roots.channel_projections selection.occurrence]
  exact (preparation.roots.get selection.occurrence.factorIndex).scalar? selection.occurrence.rootIndex

/-- Project the actual selected nonlinear track and root cache through the same original occurrence. -/
@[expose] def view? {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Option (CoherentRoot.CertifiedName.View selection.channel) := by
  unfold channel
  rewrite [preparation.roots.channel_projections selection.occurrence]
  exact (preparation.roots.get selection.occurrence.factorIndex).view? selection.occurrence.rootIndex

/-- Read the selected original view from the same retained factor-family state bank.

The actual selected occurrence supplies both bounded indices. Its exact view
projection identifies the original root and ambient, so this accessor reuses
the same owner reader used by separation and localization payments.
-/
def stateFromView {m : Type → Type} {preparation : Preparation polynomial original}
    (selection : Selection preparation) (states : CoherentRoot.Multiplicity.Family.StateReaders m preparation.roots)
    (view : CertifiedName.View selection.channel) (found : selection.view? = some view) (index : Nat) :
    m {current : WindingOneState view.polynomial view.ambient //
      current = view.root.stateAt index} := by
  let roots := preparation.roots.get selection.occurrence.factorIndex
  let owner := selection.occurrence.rootIndex
  have original : (view : CertifiedName.View (roots.channel owner)) → roots.view? owner = some view →
      m {current : WindingOneState view.polynomial view.ambient // current = view.root.stateAt index} :=
    fun view found => CoherentRoot.Multiplicity.Realization.stateFromView roots
      (states selection.occurrence.factorIndex) owner view found index
  have moved : (channel : CoherentNamed) → (same : roots.channel owner = channel) →
      (view : CertifiedName.View channel) →
      Eq.mp (congrArg (fun channel => Option (CertifiedName.View channel)) same) (roots.view? owner) = some view →
      m {current : WindingOneState view.polynomial view.ambient // current = view.root.stateAt index} := by
    intro channel same
    cases same
    exact original
  exact moved selection.channel (preparation.roots.channel_projections selection.occurrence).symm view found

/-- Every original pair of independent starting stages admits comparison to the fixed same cached root approximation. -/
def equivalent {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Equivalence.Equivalent original.toApproximation selection.approximation := by
  have comparison := selection.anchor.equivalent preparation.coverage
  change Equivalence.Equivalent preparation.source.toApproximation selection.approximation at comparison
  have identity := congrArg
    (fun source : GeometricApproximation => Equivalence.Equivalent source.toApproximation selection.approximation)
    preparation.source_eq
  exact identity.mp comparison

/-- The selected original coherent channel agrees with its same stored approximation without rebuilding either. -/
def channel_agrees {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Equivalence.NamedEquivalent selection.channel.name selection.approximation.toNamed := by
  let occurrence := selection.occurrence
  have channelEqual := preparation.roots.channel_projections occurrence
  change selection.channel =
    (preparation.roots.get occurrence.factorIndex).channel occurrence.rootIndex at channelEqual
  have approximationEqual := preparation.roots.approximation_projections occurrence
  change selection.approximation =
    (preparation.roots.get occurrence.factorIndex).approximation occurrence.rootIndex at approximationEqual
  rewrite [channelEqual, approximationEqual]
  exact (preparation.roots.get occurrence.factorIndex).channel_agrees occurrence.rootIndex

/-- The unchanged original source program agrees with the fixed selected original coherent root channel. -/
def namedEquivalent {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Equivalence.NamedEquivalent original.toApproximation.toNamed selection.channel.name :=
  selection.equivalent.toNamed.trans selection.channel_agrees.symm

/-- Decide exact zero or denominator preparation for the same original selected root occurrence's channel. -/
def decide {preparation : Preparation polynomial original} (selection : Selection preparation) :
    Division.Prepared.Decision selection.channel :=
  preparation.roots.decide selection.occurrence

/-- Transport the computed selected-root decision to an explicitly compared unchanged original numerical channel. -/
def decideOriginal {preparation : Preparation polynomial original} (selection : Selection preparation)
    (channel : CoherentNamed)
    (equivalent : Equivalence.NamedEquivalent channel.name original.toApproximation.toNamed) :
    Division.Prepared.Decision channel :=
  let originalSelected := equivalent.trans selection.namedEquivalent
  match selection.decide with
  | .prepared prepared => .prepared (prepared.transport originalSelected.symm)
  | .excluded zero => .excluded (originalSelected.trans zero)

end Selection

end Purelib.Polynomial.Approximation.Gaussian.Localization.Preparation

end
