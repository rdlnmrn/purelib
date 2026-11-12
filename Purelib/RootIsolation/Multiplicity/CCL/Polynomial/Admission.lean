module

import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial

public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Name
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Admission
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original-source algebraic admission of coefficient-computed polynomial root streams

The retained polynomial root result owns the actual finite dependent root
index, source decomposition, multiplicity, numerical boxes and CCL attachment.
Admission reuses those original owners and stores its source equation and
original-name comparison on one retained coherent numerical channel.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial

open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic (NonzeroResult)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index.NonzeroResult (RootIndex rootMultiplicity)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

set_option genInjectivity false in
/-- One original polynomial root-stream site's retained admission and operational original-source equation.

The original complete result and dependent index remain its parents. The same
side-site admission retains the actual focused multiplicity and exact reading
or cached root realization; the equation evaluates the unreduced polynomial.
-/
structure Admission {polynomial : CoefficientPolynomial} (result : NonzeroResult polynomial)
    (index : RootIndex result) where
  /-- Admission at the original result's actual zero-side observation, attachment and index. -/
  site : Side.CCL.Admission result.rfap.numeratorSites result.numeratorCCL index
  /-- Horner evaluation of the original unreduced polynomial on the retained admitted channel is zero. -/
  equation : Equivalence.NamedEquivalent (Horner.polynomialEval polynomial (Side.CCL.Admission.channel site)).name
    (CoherentNamed.Coherence.exact 0).name

constructive_injectivity Admission

namespace Admission

/-- Read the same retained coherent channel of the original indexed root admission. -/
abbrev channel {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) : CoherentNamed :=
  Side.CCL.Admission.channel admission.site

/-- The retained admitted channel agrees with the original polynomial root name at its same dependent index. -/
def equivalent {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) :
    Equivalence.NamedEquivalent (Name.NonzeroResult.rootName result index) admission.channel.name :=
  Side.CCL.Admission.equivalent admission.site

/-- Read the exact multiplicity at the same original source result and root-site index. -/
abbrev multiplicity {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (_admission : Admission result index) : Nat := rootMultiplicity result index

/-- Admit an original coefficient-computed root site and retain its equation for the unreduced source polynomial.

One actual observation admission supplies its retained channel and root cache.
The original cancellation result's cofactor identity carries the source equation
back to the original polynomial, including its complete original multiplicity.
No additional root isolation, branch selection or search bound is supplied.
-/
@[expose] def ofResult {polynomial : CoefficientPolynomial} (result : NonzeroResult polynomial)
    (index : RootIndex result)
    (cached : Option (Side.CCL.Admission.StateCache result.rfap.numeratorSites result.numeratorCCL index) := none) :
    Admission result index :=
  let site := Side.CCL.Admission.ofSide result.rfap.numeratorSites result.numeratorCCL index cached
  { site := site
    equation := Side.CCL.Admission.sourceEquation site polynomial result.rfap.input.reduction.common
      result.rfap.input.reduction.numerator_eval }

/-- Exact original root-state cache entries preserve the complete original polynomial admission. -/
theorem ofResult_cached_eq_default {polynomial : CoefficientPolynomial} (result : NonzeroResult polynomial)
    (index : RootIndex result)
    (cached : Option (Side.CCL.Admission.StateCache result.rfap.numeratorSites result.numeratorCCL index)) :
    ofResult result index cached = ofResult result index none := by
  unfold ofResult
  rewrite [Side.CCL.Admission.ofSide_cached_eq_default]
  rfl

/-- An absent state cache retains the original source equation and complete original admission. -/
theorem ofResult_none {polynomial : CoefficientPolynomial} (result : NonzeroResult polynomial)
    (index : RootIndex result) : ofResult result index none = ofResult result index := rfl

/-- Read numerical residual data from the same original root-stream admission and retained source multiplicity. -/
def numericalResidual {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) :
    Σ numericalPolynomial : CoefficientPolynomial, PolynomialResidual numericalPolynomial admission.channel :=
  Side.CCL.Admission.numericalResidual admission.site

/-- Decide exact zero or denominator preparation at the original polynomial root-stream admission.

The actual retained observation supplies scalar evidence or its cached
squarefree factor root. Original source multiplicity, channel and name
comparison remain with the same indexed admission throughout the decision.
-/
def decide {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) : Division.Prepared.Decision admission.channel :=
  Side.CCL.Admission.decide admission.site

/-- Project the actual retained higher-site root without replacing the original polynomial result or root index.

The source equation, complete decomposition and original multiplicity remain
with this admission. Absence exposes no track beyond the stored exact evidence.
-/
@[expose] def view? {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) :
    Option (CertifiedName.View admission.channel) := Side.CCL.Admission.view? admission.site

/-- Indexed original-state accessors authenticated by this same admission's exact view getter.

Every supplied view retains its original polynomial, ambient and cached root.
The getter equality binds it to this admission's source result and bounded
site index; the returned complete state keeps its requested numerical index.
-/
abbrev StateReaders (m : Type → Type) {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) : Type 1 :=
  (view : CertifiedName.View admission.channel) → admission.view? = some view → (stage : Nat) →
    m {current : CoherentRoot.WindingOneState view.polynomial view.ambient // current = view.root.stateAt stage}

/-- Read exact scalar provenance already retained by the original polynomial root admission. -/
@[expose] def scalar? {polynomial : CoefficientPolynomial} {result : NonzeroResult polynomial}
    {index : RootIndex result} (admission : Admission result index) :
    Option (Provenance.Rational.Basic.RationalSidecar admission.channel) :=
  Side.CCL.Admission.scalar? admission.site

end Admission

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial

end
