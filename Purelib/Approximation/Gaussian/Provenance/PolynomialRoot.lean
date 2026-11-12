module

import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.RootIsolation.Multiplicity.Site.Realization
public import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection

public import Purelib.RootIsolation.State.WindingOne.Admission
public import Purelib.RootIsolation.Track.Newton.Build
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Riemann.RootContinuation.CoherentRoot.Linear
public import Purelib.Riemann.RootContinuation.CoherentRoot.PointComparison
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Dense.Gaussian.Roots.Candidates
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# General polynomial-root provenance on original numerical channels

An original isolated track, intrinsic multiplicity realization or coefficient-computed admission owns
the exact polynomial, branch and cache. A sidecar retains that same owner and
an operational comparison to the original supplied numerical channel. Exact
equations and zero/preparation decisions consume those retained owners.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.PolynomialRoot

open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic (NonzeroResult)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index.NonzeroResult (RootIndex)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial (Admission)
open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Approximation.Gaussian.Localization (Preparation)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName)
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Polynomial.Dense.Gaussian.Roots.Certificate (ExactRoot)
open Purelib.Polynomial.Dense.Gaussian.Roots
open Purelib.Polynomial.Elimination.Axis
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

set_option genInjectivity false in
/-- An original isolated root, coefficient-computed admission or computed result selection with its actual cache.

The isolated constructor retains its original track and squarefree input.
The admitted constructor retains the complete original source result, dependent
root index and admission, including its original source multiplicity. An intrinsic
realization retains its original source decomposition, focused occurrence,
cofactor and same numerical root cache. A result selection retains its original
displayed annihilator, decomposition and selected factor/root occurrence.
-/
inductive Owner : Type 1 where
  /-- Retain a checked original positive-degree squarefree track and the same actual cached root certificate. -/
  | isolated {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
      {track : CoherentRoot.WindingOneTrack polynomial ambient}
      (root : CoherentRoot.CertifiedName track) (input : FTA.Positive.Input.PositiveInput polynomial)
  /-- Retain the same original coefficient-computed polynomial root result, dependent index and actual admission. -/
  | admitted {polynomial : CoefficientPolynomial}
      {result : NonzeroResult polynomial}
      {index : RootIndex result}
      (admission : Admission result index)
  /-- Retain the original multiplicity site, source decomposition and same realized root cache. -/
  | realized {source opposite : CoefficientPolynomial}
      {input : Multiplicity.Site.Basic.TrackSiteInput source opposite}
      (realization : Multiplicity.Site.Realization input)

  /-- Retain the computed selection of the same original result residual and its full displayed source equation. -/
  | selected {polynomial : CoefficientPolynomial} {source : Geometric.GeometricApproximation}
      (preparation : Preparation polynomial source)
      (selection : Preparation.Selection preparation)
      (equation : Equivalence.NamedEquivalent (Horner.polynomialEval polynomial selection.channel).name
        (CoherentNamed.Coherence.exact 0).name)

constructive_injectivity Owner

namespace Owner

/-- The same retained numerical root channel of the original mathematical owner. -/
@[expose] def channel : Owner → CoherentNamed
  | .isolated root _ => root.value
  | .admitted admission => admission.channel
  | .realized realization => realization.root.value
  | .selected _ selection _ => selection.channel

/-- The original source coefficient polynomial, including repeated-source multiplicity when admitted. -/
@[expose] def polynomial : Owner → CoefficientPolynomial
  | .isolated (polynomial := polynomial) _ _ => polynomial
  | .admitted (polynomial := polynomial) _ => polynomial
  | .realized (source := source) _ => source
  | .selected (polynomial := polynomial) _ _ _ => polynomial

/-- The original source occurrence count retained by this root owner. -/
@[expose] def multiplicity : Owner → Nat
  | .isolated _ _ => 1
  | .admitted admission => admission.multiplicity
  | .realized (input := input) _ => input.context.focus.multiplicity
  | .selected _ selection _ => selection.multiplicity

/-- Actual coherent Horner evaluation of the original source polynomial at its retained root channel is zero. -/
def equation (owner : Owner) :
    Equivalence.NamedEquivalent (Horner.polynomialEval owner.polynomial owner.channel).name
      (CoherentNamed.Coherence.exact 0).name := by
  cases owner with
  | isolated root _ => exact root.polynomial_zero
  | admitted admission => exact admission.equation
  | realized realization => exact realization.equation
  | selected _ _ equation => exact equation

/-- Compute exact zero or a prepared presentation of the same original retained root channel. -/
def decide : (owner : Owner) → Division.Prepared.Decision owner.channel
  | .isolated root input => CoherentRoot.PointComparison.decide root input 0
  | .admitted admission => admission.decide
  | .realized realization => CoherentRoot.PointComparison.decide realization.root realization.factorInput 0
  | .selected _ selection _ => selection.decide

/-- Project the complete actual root certificate and original squarefree input already retained by this owner.

Admitted higher evidence projects its actual original realization through its
original result and index. Exact admissions retain scalar evidence separately. An absent view records
only that no actual track occurs in that retained exact evidence.
-/
@[expose] def view? : (owner : Owner) → Option (CertifiedName.View owner.channel)
  | .isolated root input => some (CertifiedName.View.ofRoot root input)
  | .admitted admission => admission.view?
  | .realized realization =>
      some (CertifiedName.View.ofRoot realization.root realization.factorInput)
  | .selected _ selection _ => selection.view?

/-- Read exact scalar evidence from retained exact admissions or original degree-one track readback.

Higher isolated tracks without an exact terminal remain unclassified by this
scalar reader. That absence asserts no irrationality or numerical obstruction.
-/
@[expose] def scalar? : (owner : Owner) → Option (RationalSidecar owner.channel)
  | .isolated root _ =>
      if degree : _ = 1 then
        let data := Dense.Gaussian.Roots.Linear.rootData degree
        some ⟨data.point, root.linear_equivalent data⟩
      else none
  | .admitted admission => admission.scalar?
  | .realized realization =>
      if degree : _ = 1 then
        let data := Dense.Gaussian.Roots.Linear.rootData degree
        some ⟨data.point, realization.root.linear_equivalent data⟩
      else none
  | .selected _ selection _ => selection.scalar?

/-- Read quantitative numerical polynomial residual data from the same original retained mathematical root owner.

An isolated owner uses its original polynomial and cached root samples. An
admitted owner uses its retained factor or exact reading; the unreduced source,
focused multiplicity and attachment remain in that same original owner.
-/
def numericalResidual : (owner : Owner) →
    Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial owner.channel
  | .isolated root _ => ⟨_, root.residualCertificate⟩
  | .admitted admission => admission.numericalResidual
  | .realized realization => ⟨_, realization.root.residualCertificate⟩
  | .selected _ selection _ => ⟨selection.factorPolynomial, selection.residualCertificate⟩

end Owner

set_option genInjectivity false in
/-- Original polynomial-root ownership and a checked link to one original numerical channel.

The mathematical owner retains its exact source, branch, multiplicity and
actual root cache. The separate numerical channel is linked by its supplied
operational comparison; no owner is replaced by that channel's runtime name.
-/
structure Sidecar (channel : CoherentNamed) where
  /-- The retained original isolated or coefficient-computed root owner. -/
  owner : Owner
  /-- The original numerical channel agrees with the same retained owner's root channel. -/
  equivalent : Equivalence.NamedEquivalent channel.name owner.channel.name
  /-- The actual cached numerical polynomial and residual program of this same original owner. -/
  numerical : Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial owner.channel
  /-- The stored numerical data is computed from this same original mathematical owner. -/
  numerical_eq : numerical = owner.numericalResidual
  /-- Genuine entire-channel identity retained by an original constructor or supplied equality transport. -/
  channelEq? : Option (PLift (channel = owner.channel)) := none

constructive_injectivity Sidecar

namespace Sidecar

/-- Attach the original isolated root and positive squarefree input to that same original cached channel. -/
@[expose] def ofIsolated {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) : Sidecar root.value :=
  let owner : Owner := .isolated root input
  let numerical := owner.numericalResidual
  ⟨owner, Equivalence.NamedEquivalent.refl _, numerical, rfl, some ⟨rfl⟩⟩

/-- Attach one original coefficient-computed admission without rebuilding its source, branch or cache. -/
@[expose] def ofAdmission {polynomial : CoefficientPolynomial}
    {result : NonzeroResult polynomial}
    {index : RootIndex result}
    (admission : Admission result index) : Sidecar admission.channel :=
  let owner : Owner := .admitted admission
  let numerical := owner.numericalResidual
  ⟨owner, Equivalence.NamedEquivalent.refl _, numerical, rfl, some ⟨rfl⟩⟩

/-- Attach an original multiplicity-site realization without replacing its source, occurrence or numerical cache.

The same realized root supplies its quantitative focused-factor residual.
The original site retains its complete source decomposition, multiplicity,
cofactor and source equation, independently of the numerical factor view.
-/
@[expose] def ofRealization {source opposite : CoefficientPolynomial}
    {input : Multiplicity.Site.Basic.TrackSiteInput source opposite}
    (realization : Multiplicity.Site.Realization input) : Sidecar realization.root.value :=
  let owner : Owner := .realized realization
  let numerical := owner.numericalResidual
  ⟨owner, Equivalence.NamedEquivalent.refl _, numerical, rfl, some ⟨rfl⟩⟩

/-- Isolated-root attachment retains its genuine whole-channel identity. -/
theorem ofIsolated_channelEq {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) :
    (ofIsolated root input).channelEq? = some ⟨rfl⟩ := rfl

/-- Admission attachment retains its genuine whole-channel identity independently of its evidence branch. -/
theorem ofAdmission_channelEq {polynomial : CoefficientPolynomial}
    {result : Multiplicity.CCL.Polynomial.Basic.NonzeroResult polynomial}
    {index : Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result}
    (admission : Multiplicity.CCL.Polynomial.Admission result index) :
    (ofAdmission admission).channelEq? = some ⟨rfl⟩ := rfl

/-- Realization attachment retains the same entire original root channel. -/
theorem ofRealization_channelEq {source opposite : CoefficientPolynomial}
    {input : Multiplicity.Site.Basic.TrackSiteInput source opposite}
    (realization : Multiplicity.Site.Realization input) :
    (ofRealization realization).channelEq? = some ⟨rfl⟩ := rfl

/-- Intrinsic realization admission preserves the complete original source polynomial. -/
theorem ofRealization_polynomial {source opposite : CoefficientPolynomial}
    {input : Multiplicity.Site.Basic.TrackSiteInput source opposite}
    (realization : Multiplicity.Site.Realization input) :
    (ofRealization realization).owner.polynomial = source := rfl

/-- Intrinsic realization admission preserves its same original focused occurrence count. -/
theorem ofRealization_multiplicity {source opposite : CoefficientPolynomial}
    {input : Multiplicity.Site.Basic.TrackSiteInput source opposite}
    (realization : Multiplicity.Site.Realization input) :
    (ofRealization realization).owner.multiplicity = input.context.focus.multiplicity := rfl

/-- Transport the same original root owner to an explicitly compared numerical channel without another producer call. -/
@[expose] def transport {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name)
    (same : Option (PLift (second = first)) := none) : Sidecar second :=
  let channelEq : Option (PLift (second = sidecar.owner.channel)) := match same, sidecar.channelEq? with
    | some supplied, some retained => some ⟨supplied.down.trans retained.down⟩
    | _, _ => none
  ⟨sidecar.owner, equivalent.trans sidecar.equivalent, sidecar.numerical, sidecar.numerical_eq, channelEq⟩

/-- Operational-only transport preserves every original stored field and records no whole-channel identity. -/
theorem transport_none {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name) :
    sidecar.transport equivalent none =
      ⟨sidecar.owner, equivalent.trans sidecar.equivalent, sidecar.numerical, sidecar.numerical_eq, none⟩ := rfl

/-- Equality transport consumes only the supplied channel identity and the original retained identity. -/
theorem transport_channelEq {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name) (same : PLift (second = first)) :
    (sidecar.transport equivalent (some same)).channelEq? =
      match sidecar.channelEq? with
      | some retained => some ⟨same.down.trans retained.down⟩
      | none => none := by
  change (match some same, sidecar.channelEq? with
    | some supplied, some retained =>
        some (⟨supplied.down.trans retained.down⟩ : PLift (second = sidecar.owner.channel))
    | _, _ => none) = _
  cases sidecar.channelEq? <;> rfl

/-- Consume the same stored owner residual program as quantitative evidence on the unchanged original channel. -/
def residualCertificate {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial channel :=
  ⟨sidecar.numerical.1, sidecar.numerical.2.transport sidecar.equivalent⟩

/-- Isolated root provenance retains its original source polynomial in the numerical residual view. -/
theorem ofIsolated_residual_polynomial {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) :
    (ofIsolated root input).residualCertificate.1 = polynomial := by
  unfold residualCertificate
  rfl

/-- Isolated root provenance reads the same actual original cache in every residual sample. -/
theorem ofIsolated_residual_sample {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) (index : Nat) :
    (ofIsolated root input).residualCertificate.2.source.sample index = root.approximation.sample index := by
  unfold residualCertificate
  rewrite [PolynomialResidual.transport_source]
  rfl

/-- Retain a computed original result selection on the unchanged original numerical channel.

The owner keeps the full displayed annihilator, its decomposition, selected
factor/root occurrence and source multiplicity. Its numerical residual reads
the same selected factor's actual cached root program. The source equation is
derived by operational transport of the supplied original residual equation;
no coefficient identity follows from semantic equality.
-/
@[expose] def ofSelection {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : PolynomialResidual polynomial channel)
    (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) : Sidecar channel :=
  let equivalent := residual.equivalent.trans selection.namedEquivalent
  have equation : Equivalence.NamedEquivalent (Horner.polynomialEval polynomial selection.channel).name
      (CoherentNamed.Coherence.exact 0).name :=
    (Horner.horner_respects channel selection.channel (CoherentNamed.Coherence.exact 0)
      (CoherentNamed.Coherence.exact 0) equivalent (Equivalence.NamedEquivalent.refl _)
      polynomial.coeffs).symm.trans residual.equation
  let owner : Owner := .selected preparation selection equation
  let numerical := owner.numericalResidual
  ⟨owner, equivalent, numerical, rfl, none⟩

/-- A selected result retains the complete original displayed annihilator independently of its numerical factor. -/
theorem ofSelection_polynomial {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : PolynomialResidual polynomial channel)
    (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) :
    (ofSelection residual preparation selection).owner.polynomial = polynomial := rfl

/-- A selected result retains the same original displayed factor occurrence count. -/
theorem ofSelection_multiplicity {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : PolynomialResidual polynomial channel)
    (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) :
    (ofSelection residual preparation selection).owner.multiplicity = selection.multiplicity := rfl

/-- The selected numerical polynomial is the same original factor chosen by the retained occurrence. -/
theorem ofSelection_residual_polynomial {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : PolynomialResidual polynomial channel)
    (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) :
    (ofSelection residual preparation selection).residualCertificate.1 = selection.factorPolynomial := by
  unfold residualCertificate
  rfl

/-- The selected numerical residual reads the same retained selected root cache at every sample index. -/
theorem ofSelection_residual_sample {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : PolynomialResidual polynomial channel)
    (preparation : Preparation polynomial residual.source)
    (selection : Preparation.Selection preparation) (index : Nat) :
    (ofSelection residual preparation selection).residualCertificate.2.source.sample index =
      selection.residualCertificate.source.sample index := by
  unfold residualCertificate
  rewrite [PolynomialResidual.transport_source]
  rfl

/-- Original-channel transport retains the same actual numerical owner cache rather than rerunning its producer. -/
theorem transport_numerical {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : Equivalence.NamedEquivalent second.name first.name) :
    (sidecar.transport equivalent).numerical = sidecar.numerical := rfl

/-- Project this same owner's actual retained root and compose its original supplied numerical-channel link.

The entire owner, source multiplicity and numerical residual remain in this
sidecar. Only an exact root/input view is returned; no owner, isolation or
root approximation is reconstructed.
-/
@[expose] def view? {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Option (CertifiedName.View channel) :=
  match sidecar.owner.view? with
  | none => none
  | some view => some (view.transport sidecar.equivalent sidecar.channelEq?)

/-- Read the same retained root state through this sidecar's exact transported view.

The supplied accessor belongs to the original owner's projected view. The
sidecar composes its existing channel link while preserving the polynomial,
ambient, track, root and state index; no numerical producer is invoked.
-/
def stateFromView {m : Type → Type} {channel : CoherentNamed} (sidecar : Sidecar channel)
    (read : (view : CertifiedName.View sidecar.owner.channel) → sidecar.owner.view? = some view →
      (index : Nat) → m {current : CoherentRoot.WindingOneState view.polynomial view.ambient //
        current = view.root.stateAt index})
    (view : CertifiedName.View channel) (found : sidecar.view? = some view) (index : Nat) :
    m {current : CoherentRoot.WindingOneState view.polynomial view.ambient // current = view.root.stateAt index} := by
  unfold view? at found
  cases ownerFound : sidecar.owner.view? with
  | none =>
      rewrite [ownerFound] at found
      cases found
  | some original =>
      rewrite [ownerFound] at found
      have same : original.transport sidecar.equivalent sidecar.channelEq? = view := Option.some.inj found
      cases same
      exact read original ownerFound index

/-- Read the retained owner's scalar evidence at the original numerical channel through the same stored comparison. -/
@[expose] def scalar? {channel : CoherentNamed} (sidecar : Sidecar channel) : Option (RationalSidecar channel) :=
  match sidecar.owner.scalar? with
  | none => none
  | some reading => some ⟨reading.value, sidecar.equivalent.trans reading.equivalent⟩

/-- The original selected root view, one actual coordinate certificate/bank and its complete candidate inspection.

This exact dependent tuple stores original owners rather than a second root
or comparison family. Candidate construction and every demanded point attempt
retain their defining equations; the original View identifies the supplied
Sidecar's unchanged root projection.
-/
@[expose] def ExactInspection {channel : CoherentNamed} (sidecar : Sidecar channel) (start : Nat) : Type 1 :=
  Σ view : { view : CertifiedName.View channel // sidecar.view? = some view },
  Σ elimination : AxisEliminationCertificate view.val.polynomial
      (Separated.separatedEliminationDegree view.val.polynomial),
    { size : Nat // size = Candidates.searchSize elimination } ×
    (Σ candidates : { values : List (ExactRoot view.val.polynomial) // values = Candidates.exactRoots elimination },
      { result : CertifiedName.View.CandidateResult view.val start //
        result = view.val.inspectCandidates start candidates.val })

namespace ExactInspection

/-- Read the same complete root View retained by the original Sidecar inspection. -/
@[expose] def view {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : CertifiedName.View channel := inspection.1.val

/-- The retained View is exactly the original Sidecar projection. -/
theorem view_eq {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : sidecar.view? = some inspection.view := inspection.1.property

/-- Read the same original retained axis certificate without rebuilding either coordinate eliminant. -/
@[expose] def elimination {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) :
    AxisEliminationCertificate inspection.view.polynomial
      (Separated.separatedEliminationDegree inspection.view.polynomial) :=
  inspection.2.1

/-- Read the stored finite search budget of the same two actual coordinate eliminants. -/
@[expose] def budget {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : Nat := inspection.2.2.1.val

/-- The retained numeric budget is the original search bound on the same cached eliminants. -/
theorem budget_eq {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : inspection.budget = Candidates.searchSize inspection.elimination :=
  inspection.2.2.1.property

/-- Read the complete stored coefficient-produced candidate bank, preserving duplicate order. -/
@[expose] def candidates {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : List (ExactRoot inspection.view.polynomial) :=
  inspection.2.2.2.1.val

/-- The retained candidate list is constructed from the same original cached coordinate certificate. -/
theorem candidates_eq {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) :
    inspection.candidates = Candidates.exactRoots inspection.elimination :=
  inspection.2.2.2.1.property

/-- Exact filtering retains the stored original coordinate-search budget. -/
theorem candidates_length_le {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : inspection.candidates.length ≤ inspection.budget := by
  rewrite [inspection.candidates_eq, inspection.budget_eq]
  exact Candidates.exactRoots_length_le inspection.elimination

/-- Read every actual original point comparison attempted before the inspection stopped. -/
@[expose] def attempts {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) :
    List (Σ candidate : ExactRoot inspection.view.polynomial,
      CoherentRoot.PointComparison inspection.view.root candidate.point start) := inspection.2.2.2.2.val.1

/-- Read the original candidate suffix left unvisited after a checked equality. -/
@[expose] def remaining {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : List (ExactRoot inspection.view.polynomial) :=
  inspection.2.2.2.2.val.2.1

/-- Consume the same stored original-channel exact reading, with no repeated point comparison or elimination. -/
@[expose] def reading {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) : Option (RationalSidecar channel) := inspection.2.2.2.2.val.2.2

/-- Stored attempts and the unvisited suffix recover the exact complete candidate bank and its multiplicities. -/
theorem partition {channel : CoherentNamed} {sidecar : Sidecar channel} {start : Nat}
    (inspection : ExactInspection sidecar start) :
    (inspection.attempts.map fun entry => entry.1) ++ inspection.remaining = inspection.candidates := by
  have actual := inspection.2.2.2.2.property
  change (inspection.2.2.2.2.val.1.map fun entry => entry.1) ++ inspection.2.2.2.2.val.2.1 = _
  rewrite [actual]
  exact CertifiedName.View.inspectCandidates_partition inspection.view start inspection.candidates

end ExactInspection

/-- Compute exact candidate recognition against the same retained original root View once.

The actual separated axis certificate is stored before its candidate bank is
computed. The original root comparison consumes that bank and retains its
paid states, checked failures and remaining suffix. An unavailable View gives
no scalar identification and causes no replacement isolation.
-/
def inspectExact {channel : CoherentNamed} (sidecar : Sidecar channel) (start : Nat) :
    Option (ExactInspection sidecar start) :=
  match found : sidecar.view? with
  | none => none
  | some view =>
      let elimination := Separated.separatedAxisEliminationCertificate view.polynomial
        view.input.nonzero view.input.degreePositive
      let budget := Candidates.searchSize elimination
      let candidates := Candidates.exactRoots elimination
      let result := view.inspectCandidates start candidates
      some ⟨⟨view, found⟩, elimination, ⟨budget, rfl⟩, ⟨candidates, rfl⟩, ⟨result, rfl⟩⟩

/-- A missing actual root View preserves the absence of exact candidate recognition. -/
theorem inspectExact_no_view {channel : CoherentNamed} (sidecar : Sidecar channel) (start : Nat)
    (absent : sidecar.view? = none) : sidecar.inspectExact start = none := by
  unfold inspectExact
  split
  · rfl
  · rename_i view found
    cases (found.symm.trans absent)

/-- One original exact-inspection request and its literal retained complete result.

The dependent pair retains the original start. Its subtype binds the cached
result to the actual existing-owner procedure, including missing-View and
finite candidate-failure outcomes; it accepts no independent success premise.
-/
@[expose] def PointInspection {channel : CoherentNamed} (sidecar : Sidecar channel) : Type 1 :=
  Σ start : Nat, { result : Option (ExactInspection sidecar start) // result = sidecar.inspectExact start }

namespace PointInspection

/-- Execute and retain one exact-inspection request on the same original Sidecar. -/
@[expose] def build {channel : CoherentNamed} (sidecar : Sidecar channel) (start : Nat) : PointInspection sidecar :=
  let result := sidecar.inspectExact start
  ⟨start, result, rfl⟩

/-- Read the original retained request floor without rerunning its inspection. -/
@[expose] def start {channel : CoherentNamed} {sidecar : Sidecar channel}
    (inspection : PointInspection sidecar) : Nat := inspection.1

/-- Read the literal cached inspection result and its original point-comparison receipts. -/
@[expose] def result {channel : CoherentNamed} {sidecar : Sidecar channel}
    (inspection : PointInspection sidecar) : Option (ExactInspection sidecar inspection.start) := inspection.2.val

/-- The complete retained result is the actual procedure on this same original Sidecar and request. -/
theorem result_eq {channel : CoherentNamed} {sidecar : Sidecar channel} (inspection : PointInspection sidecar) :
    inspection.result = sidecar.inspectExact inspection.start := inspection.2.property

/-- Read the original-channel scalar from the literal retained result; no numerical operation is executed. -/
@[expose] def reading {channel : CoherentNamed} {sidecar : Sidecar channel}
    (inspection : PointInspection sidecar) : Option (RationalSidecar channel) :=
  match inspection.result with
  | none => none
  | some retained => retained.reading

/-- Building an inspection retains exactly its requested start and entire actual result. -/
theorem build_result {channel : CoherentNamed} (sidecar : Sidecar channel) (start : Nat) :
    (build sidecar start).start = start ∧ (build sidecar start).result = sidecar.inspectExact start := ⟨rfl, rfl⟩

end PointInspection

/-- Decide original-channel zero or preparation by consuming the same retained root owner's computed decision. -/
def decide {channel : CoherentNamed} (sidecar : Sidecar channel) : Division.Prepared.Decision channel :=
  match sidecar.owner.decide with
  | .prepared prepared => .prepared (prepared.transport sidecar.equivalent.symm)
  | .excluded zero => .excluded (sidecar.equivalent.trans zero)

/-- The original numerical channel satisfies the original root owner's source polynomial equation operationally. -/
def equation {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Equivalence.NamedEquivalent (Horner.polynomialEval sidecar.owner.polynomial channel).name
      (CoherentNamed.Coherence.exact 0).name :=
  (Horner.horner_respects channel sidecar.owner.channel (CoherentNamed.Coherence.exact 0)
    (CoherentNamed.Coherence.exact 0) sidecar.equivalent (Equivalence.NamedEquivalent.refl _)
    sidecar.owner.polynomial.coeffs).trans sidecar.owner.equation

end Sidecar

open Purelib.RootIsolation.State.WindingOne

set_option genInjectivity false in
/-- A squarefree proposed-box admission with its same checked state, original track and intrinsic sidecar.

The polynomial-only input and retained axis certificate do not assert any
validity of the proposed box. The state is supplied by the finite checker;
the original Newton constructor and root cache consume that exact state once.
-/
structure CheckedBox {polynomial : CoefficientPolynomial} {degreeBound : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial degreeBound)
    (ambient proposed : CoherentRoot.Box) (data : Admission.Data) (budget : Nat) where
  /-- The complete actual checked original-state admission. -/
  checked : Admission.Accepted polynomial ambient proposed data budget
  /-- The same original root cache built around the checked state and supplied elimination. -/
  root : CoherentRoot.CertifiedName
    (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination checked.state)
  /-- The retained root is the actual original constructor on that same track. -/
  root_eq : root = CoherentRoot.certifiedName
    (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination checked.state)
      input.degreePositive
  /-- The intrinsic sidecar retains this same original polynomial, state, track and root cache. -/
  sidecar : Sidecar root.value
  /-- The sidecar is constructed from this same retained original root. -/
  sidecar_eq : sidecar = Sidecar.ofIsolated root input.toPositive

constructive_injectivity CheckedBox

set_option genInjectivity false in
/-- A finite squarefree-box admission constructs an intrinsic root, rejects exact submitted data, or retains open work.

Only the polynomial's existing squarefree higher-degree input is assumed.
The proposed box itself is always checked. General source multiplicities
remain with the separate original multiplicity-site admission constructors.
-/
inductive SquarefreeBoxOutcome {polynomial : CoefficientPolynomial} {degreeBound : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial degreeBound)
    (ambient proposed : CoherentRoot.Box) (data : Admission.Data) (budget : Nat) where
  /-- The checked original state supplies its actual retained root and sidecar. -/
  | ready (result : CheckedBox input elimination ambient proposed data budget)
  /-- Preserve the original source decomposition and exact failed proposal condition. -/
  | invalid (preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing polynomial)
      (failure : Admission.Invalid polynomial ambient proposed data)
  /-- Preserve the original budget, attempted work, event data and unresolved tails. -/
  | pending (result : Admission.Pending polynomial ambient proposed data budget)

constructive_injectivity SquarefreeBoxOutcome

/-- Check a proposed original squarefree box and construct its intrinsic algebraic root only after genuine success.

No valid isolation, successful finite attempt or denominator floor is a
caller hypothesis. This entry keeps the same original polynomial and exact
proposed box; it does not silently replace a repeated source by its squarefree
part. Missing side evidence and finite exhaustion retain their actual request.
-/
def Sidecar.checkSquarefreeBox {polynomial : CoefficientPolynomial} {degreeBound : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial degreeBound)
    (ambient proposed : CoherentRoot.Box) (data : Admission.Data) (budget : Nat) :
    SquarefreeBoxOutcome input elimination ambient proposed data budget :=
  match Admission.check polynomial ambient proposed data budget with
  | .zero zero => False.elim (Bool.noConfusion (input.nonzero.symm.trans zero))
  | .constant _ degreeZero =>
      False.elim (Nat.not_lt_zero _ (degreeZero ▸ input.degreePositive))
  | .invalid preprocessing failure => .invalid preprocessing failure
  | .pending result => .pending result
  | .accepted checked =>
      let track := Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination checked.state
      let root := CoherentRoot.certifiedName track input.degreePositive
      let sidecar := Sidecar.ofIsolated root input.toPositive
      .ready ⟨checked, root, rfl, sidecar, rfl⟩

end Purelib.Approximation.Gaussian.Provenance.PolynomialRoot

end
