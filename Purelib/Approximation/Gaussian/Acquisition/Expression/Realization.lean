module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
public import Purelib.Polynomial.Multivariate.Gaussian.Realization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original binding evidence at a supplied admitted realization

Equal original leaf keys carry equality of their entire source annotations.
Their retained coordinate evidence therefore transports to the actual target
occurrence. Other occurrences use their existing scalar inspection when its
exact value lies on the supplied real-axis coefficient map. Missing links and
nonreal scalar readings remain typed outcomes at their original bindings.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Binding

open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)

variable {arity : Nat} {environment : Fin arity → Annotated}

set_option genInjectivity false in
/-- An actual original occurrence's coordinate evidence or retained unmet scalar or source-link conditions. -/
inductive RealizationOutcome (realization : Realization Rational) (basis target : Binding environment)
    (inspection : Provenance.Inspection target.annotation) where
  /-- Retain explicit coordinate evidence at this same original occurrence and mathematical owner. -/
  | provided (evidence : Realization.Sidecar realization target.channel)
  /-- Equal original leaf keys transport the basis's entire retained coordinate evidence. -/
  | same (leaf_eq : target.leaf = basis.leaf) (evidence : Realization.Sidecar realization target.channel)
  /-- An existing exact real scalar reading supplies evidence at the same original occurrence. -/
  | scalar (reading : RationalSidecar target.channel) (reading_eq : inspection.scalar = some reading)
      (value : Rational) (value_eq : reading.value = Cast.CoordinateTaylor.ofCoordinate value)
      (evidence : Realization.Sidecar realization target.channel)
  /-- The original exact scalar reading violates the real-axis scalar adapter's imaginary-coordinate condition. -/
  | nonreal (reading : RationalSidecar target.channel) (reading_eq : inspection.scalar = some reading)
      (imaginary_ne : reading.value.im ≠ 0)
  /-- Distinct original keys and absence of scalar evidence leave the required coordinate link unresolved. -/
  | unresolved (leaf_ne : target.leaf ≠ basis.leaf) (missing : inspection.scalar = none)

constructive_injectivity RealizationOutcome

/-- Check an original occurrence using its cached inspection and the original basis coordinate certificate. -/
@[noinline, nospecialize] def realizeAs (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel)
    (target : Binding environment) (inspection : Provenance.Inspection target.annotation) :
    RealizationOutcome realization basis target inspection :=
  if same : target.leaf = basis.leaf then
    let original : target.annotation = basis.annotation := target.annotation_eq.trans
      ((congrArg (Leaf.annotation environment) same).trans basis.annotation_eq.symm)
    have channel_eq : target.channel = basis.channel := congrArg Annotated.channel original
    let evidence := basisEvidence.transport (by
      rewrite [channel_eq]
      exact NamedEquivalent.refl _)
    .same same evidence
  else match selected : inspection.scalar with
    | none => .unresolved same selected
    | some reading => match Cast.inspectReal reading.value with
      | .complex imaginary_ne => .nonreal reading selected imaginary_ne
      | .real value value_eq =>
          have compared : NamedEquivalent target.channel.name
              (CoherentNamed.Coherence.exact (realization.coefficient value)).name := by
            have comparison := reading.equivalent
            rewrite [value_eq, ← coefficient_eq value] at comparison
            exact comparison
          .scalar reading selected value value_eq (Realization.Sidecar.scalar realization value target.channel compared)

/-- Read only a retained successful coordinate certificate, leaving every unresolved original outcome available. -/
@[expose] def RealizationOutcome.evidence? {realization : Realization Rational} {basis target : Binding environment}
    {inspection : Provenance.Inspection target.annotation} :
    RealizationOutcome realization basis target inspection → Option (Realization.Sidecar realization target.channel)
  | .provided evidence => some evidence
  | .same _ evidence => some evidence
  | .scalar _ _ _ _ evidence => some evidence
  | .nonreal _ _ _ => none
  | .unresolved _ _ => none

/-- Retained coordinate-link outcomes at every actual occurrence of the original inspected binding table. -/
@[expose] def RealizationChecks (realization : Realization Rational) (basis : Binding environment)
    (bindings : List (Binding environment)) (inspections : Inspections bindings) : Type 1 :=
  DependentProduct bindings (fun index =>
    RealizationOutcome realization basis (read bindings index) (inspections.get bindings index))

/-- Optional explicit coordinate links at the original annotated occurrences and one supplied realization. -/
@[expose] def RealizationLinks (realization : Realization Rational) (bindings : List (Binding environment)) : Type 1 :=
  DependentProduct bindings (fun index => Option (Realization.Sidecar realization (channels bindings index)))

/-- Retain absence of supplied links at every original occurrence, preserving automatic key and scalar inspection. -/
@[expose] def RealizationLinks.empty (realization : Realization Rational)
    (bindings : List (Binding environment)) : RealizationLinks realization bindings :=
  DependentProduct.ofFn bindings (fun _ => none)

/-- Build explicit original-occurrence links from certificates indexed by the same actual bounded table. -/
@[expose] def RealizationLinks.ofEvidence (realization : Realization Rational)
    (bindings : List (Binding environment))
    (evidence : (index : Fin bindings.length) → Option (Realization.Sidecar realization (channels bindings index))) :
    RealizationLinks realization bindings :=
  DependentProduct.ofFn bindings evidence

/-- Read the exact supplied optional certificate at its actual original bounded occurrence. -/
@[expose] def RealizationLinks.get {realization : Realization Rational}
    (bindings : List (Binding environment)) (links : RealizationLinks realization bindings)
    (index : Fin bindings.length) : Option (Realization.Sidecar realization (channels bindings index)) :=
  DependentProduct.get bindings links index

/-- Link construction returns the same supplied certificate at each original bounded table position. -/
theorem RealizationLinks.get_ofEvidence (realization : Realization Rational)
    (bindings : List (Binding environment))
    (evidence : (index : Fin bindings.length) → Option (Realization.Sidecar realization (channels bindings index)))
    (index : Fin bindings.length) : (ofEvidence realization bindings evidence).get bindings index = evidence index :=
  DependentProduct.get_ofFn bindings evidence index

/-- Inspect original occurrences using their same caches and explicitly supplied source-coordinate links. -/
@[noinline, nospecialize] def realizeBindingsWith (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel) :
    (bindings : List (Binding environment)) → (inspections : Inspections bindings) →
    RealizationLinks realization bindings → RealizationChecks realization basis bindings inspections
  | [], _, _ => PUnit.unit
  | first :: remaining, inspections, links =>
      let checked := match links.1 with
        | some supplied => RealizationOutcome.provided supplied
        | none => realizeAs realization coefficient_eq basis basisEvidence first inspections.1
      (checked, realizeBindingsWith realization coefficient_eq basis basisEvidence remaining inspections.2 links.2)

/-- Read a retained coordinate-link outcome at its original bounded table index and cached inspection. -/
@[expose] def RealizationChecks.get {realization : Realization Rational} {basis : Binding environment}
    (bindings : List (Binding environment)) (inspections : Inspections bindings)
    (checks : RealizationChecks realization basis bindings inspections) (index : Fin bindings.length) :
    RealizationOutcome realization basis (read bindings index) (inspections.get bindings index) :=
  DependentProduct.get bindings checks index

/-- Read optional successful coordinates from the same actual occurrence outcomes without another inspection. -/
@[expose] def RealizationChecks.evidence? {realization : Realization Rational} {basis : Binding environment}
    (bindings : List (Binding environment)) (inspections : Inspections bindings)
    (checks : RealizationChecks realization basis bindings inspections) (index : Fin bindings.length) :
    Option (Realization.Sidecar realization (channels bindings index)) :=
  (checks.get bindings inspections index).evidence?

/-- A supplied nonempty link remains available in the same original checked occurrence. -/
theorem realizeBindingsWith_available (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel) :
    (bindings : List (Binding environment)) → (inspections : Inspections bindings) →
    (links : RealizationLinks realization bindings) →
    (index : Fin bindings.length) → (links.get bindings index).isSome = true →
    ((realizeBindingsWith realization coefficient_eq basis basisEvidence bindings inspections links).evidence?
      bindings inspections index).isSome = true
  | [], _, _, index, _ => Fin.elim0 index
  | first :: remaining, inspections, links, index, available => by
      refine Fin.cases ?_ ?_ index available
      · intro available
        change links.1.isSome = true at available
        unfold realizeBindingsWith
        dsimp only [RealizationChecks.evidence?, RealizationChecks.get]
        cases selected : links.1 with
        | none => rewrite [selected] at available; cases available
        | some supplied => rfl
      · intro tail available
        exact realizeBindingsWith_available realization coefficient_eq basis basisEvidence
          remaining inspections.2 links.2 tail available

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Binding

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Multivariate

variable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}

/-- The actual binding outcomes contain evidence at every nonzero exponent of the original cached form. -/
@[expose] def RealizationSupported (normalized : Normalized environment expression)
    (realization : Realization Rational) (basis : Binding environment)
    (checks : Binding.RealizationChecks realization basis normalized.bindings normalized.inspections) : Prop :=
  Terms.Supported (fun index => (checks.evidence? normalized.bindings normalized.inspections index).isSome = true)
    normalized.polynomial.form.terms

/-- Decide support from the same retained original-form and occurrence outcomes. -/
instance realizationSupportedDecidable (normalized : Normalized environment expression)
    (realization : Realization Rational) (basis : Binding environment)
    (checks : Binding.RealizationChecks realization basis normalized.bindings normalized.inspections) :
    Decidable (RealizationSupported normalized realization basis checks) :=
  Terms.supportedDecidable _ normalized.polynomial.form.terms

set_option genInjectivity false in
/-- Exact source evidence or remaining coefficient and original-binding conditions at the same finite attempt. -/
inductive RealizationResult (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment)
    (checks : Binding.RealizationChecks realization basis normalized.bindings normalized.inspections)
    (coefficients : Cast.RealListView (Terms.coefficientEntries normalized.polynomial.form.terms)) where
  /-- Both actual cached inspections supply the evidence needed at the unchanged original source. -/
  | ready (coefficient_complete : coefficients.Complete)
      (supported : RealizationSupported normalized realization basis checks)
      (evidence : Realization.Sidecar realization normalized.compiled.annotation.channel)
      (evidence_eq : evidence = normalized.polynomial.realize realization
        (Terms.coefficientsOfRealView realization coefficient_eq coefficients coefficient_complete)
        (checks.evidence? normalized.bindings normalized.inspections) supported)
  /-- The retained complete attempt has unmet real-coefficient or original-coordinate conditions. -/
  | unresolved (incomplete : ¬ (coefficients.Complete ∧ RealizationSupported normalized realization basis checks))

constructive_injectivity RealizationResult

set_option genInjectivity false in
/-- A complete original-form interpretation attempt with its actual owners, inspections and cached outcome. -/
structure RealizationCheck (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (originalBasis : Binding environment) where
  /-- The entire actual original expression normalization. -/
  source : Normalized environment expression
  /-- The source is the original retained input normalization. -/
  source_eq : source = normalized
  /-- The entire supplied admitted realization retained as executable data. -/
  owner : Realization Rational
  /-- The retained realization is the original mathematical owner. -/
  owner_eq : owner = realization
  /-- The original annotated basis occurrence. -/
  basis : Binding environment
  /-- The retained occurrence is the same supplied original basis. -/
  basis_eq : basis = originalBasis
  /-- The original supplied basis certificate used by automatic key inspection. -/
  basisEvidence : Realization.Sidecar realization originalBasis.channel
  /-- The actual optional coordinate certificates supplied at the original table occurrences. -/
  links : Binding.RealizationLinks realization normalized.bindings
  /-- Every original variable occurrence's actual coordinate-link outcome. -/
  bindings : Binding.RealizationChecks realization originalBasis normalized.bindings normalized.inspections
  /-- The outcomes consume these exact supplied links and original inspection caches. -/
  bindings_eq : bindings = Binding.realizeBindingsWith realization coefficient_eq originalBasis basisEvidence
    normalized.bindings normalized.inspections links
  /-- Every actual coefficient's retained exact real-axis inspection. -/
  coefficients : Cast.RealListView (Terms.coefficientEntries normalized.polynomial.form.terms)
  /-- The exact source evidence or outstanding conditions at these same stored inspections. -/
  outcome : RealizationResult normalized realization coefficient_eq originalBasis bindings coefficients

constructive_injectivity RealizationCheck

/-- Inspect an original cached form at its supplied basis, retaining its conditions and resulting source evidence. -/
@[noinline, nospecialize] def inspectRealizationWith (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel)
    (links : Binding.RealizationLinks realization normalized.bindings) :
    RealizationCheck normalized realization coefficient_eq basis :=
  let bindings := Binding.realizeBindingsWith realization coefficient_eq basis basisEvidence
    normalized.bindings normalized.inspections links
  let coefficients := Cast.inspectRealList (Terms.coefficientEntries normalized.polynomial.form.terms)
  let outcome : RealizationResult normalized realization coefficient_eq basis bindings coefficients :=
    if complete : coefficients.Complete then
      if supported : RealizationSupported normalized realization basis bindings then
        let evidence := normalized.polynomial.realize realization
          (Terms.coefficientsOfRealView realization coefficient_eq coefficients complete)
          (bindings.evidence? normalized.bindings normalized.inspections) supported
        .ready complete supported evidence rfl
      else .unresolved (fun ready => supported ready.2)
    else .unresolved (fun ready => complete ready.1)
  ⟨normalized, rfl, realization, rfl, basis, rfl, basisEvidence, links, bindings, rfl, coefficients, outcome⟩

/-- A supplied-link attempt retains those exact original indexed certificates as its actual cache. -/
theorem inspectRealizationWith_links (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel)
    (links : Binding.RealizationLinks realization normalized.bindings) :
    (normalized.inspectRealizationWith realization coefficient_eq basis basisEvidence links).links = links :=
  (Eq.refl _).trans (Eq.refl _)

/-- The attempt's coefficient cache is its exact original-form real-axis inspection. -/
theorem inspectRealizationWith_coefficients (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel)
    (links : Binding.RealizationLinks realization normalized.bindings) :
    (normalized.inspectRealizationWith realization coefficient_eq basis basisEvidence links).coefficients =
      Cast.inspectRealList (Terms.coefficientEntries normalized.polynomial.form.terms) :=
  (Eq.refl _).trans (Eq.refl _)

/-- Inspect an original cached form with automatic source-key and scalar links at the supplied basis. -/
@[noinline, nospecialize] def inspectRealization (normalized : Normalized environment expression)
    (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    (basis : Binding environment) (basisEvidence : Realization.Sidecar realization basis.channel) :
    RealizationCheck normalized realization coefficient_eq basis :=
  normalized.inspectRealizationWith realization coefficient_eq basis basisEvidence (Binding.RealizationLinks.empty _ _)

/-- Read the same cached successful original-source certificate without rerunning binding or coefficient inspection. -/
@[expose] def RealizationCheck.evidence? {normalized : Normalized environment expression}
    {realization : Realization Rational}
    {coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value}
    {basis : Binding environment} (check : RealizationCheck normalized realization coefficient_eq basis) :
    Option (Realization.Sidecar realization normalized.compiled.annotation.channel) :=
  match check.outcome with
  | .ready _ _ evidence _ => some evidence
  | .unresolved _ => none

/-- Complete original coefficient and coordinate conditions guarantee a cached successful source certificate. -/
theorem RealizationCheck.evidence_of_complete {normalized : Normalized environment expression}
    {realization : Realization Rational}
    {coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value}
    {basis : Binding environment} (check : RealizationCheck normalized realization coefficient_eq basis)
    (coefficients : check.coefficients.Complete)
    (supported : RealizationSupported normalized realization basis check.bindings) :
    ∃ evidence, check.evidence? = some evidence := by
  unfold RealizationCheck.evidence?
  cases check.outcome with
  | ready complete supported evidence evidence_eq => exact ⟨evidence, rfl⟩
  | unresolved incomplete => exact False.elim (incomplete ⟨coefficients, supported⟩)

/-- Fully supplied original-coordinate links and complete real coefficients leave no unresolved interpretation case. -/
theorem RealizationCheck.evidence_of_links {normalized : Normalized environment expression}
    {realization : Realization Rational}
    {coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value}
    {basis : Binding environment} (check : RealizationCheck normalized realization coefficient_eq basis)
    (coefficients : check.coefficients.Complete)
    (available : ∀ index, (check.links.get normalized.bindings index).isSome = true) :
    ∃ evidence, check.evidence? = some evidence := by
  have ready : ∀ index, (check.bindings.evidence? normalized.bindings normalized.inspections index).isSome = true := by
    intro index
    rewrite [check.bindings_eq]
    exact Binding.realizeBindingsWith_available realization coefficient_eq basis check.basisEvidence
      normalized.bindings normalized.inspections check.links index (available index)
  exact check.evidence_of_complete coefficients (Terms.supported_all _ ready _)

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Normalized

end
