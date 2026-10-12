module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Calculus.Jet.Progressive.First.Transcendental
public import Purelib.Calculus.Jet.Progressive.First.Arithmetic
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Calculus.Jet.Preparation.Diagnostic
import Purelib.Calculus.Jet.Progressive.First.Provenance

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored (AnchoredChart)
open Purelib.Approximation.Gaussian.Name.Basic.Named (Apart)

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.Calculus.Jet.Progressive.First.Preparation
universe u

/-! ## Ordinary progressive first jets -/

open Purelib.Approximation in
open Purelib.Calculus.Jet.Progressive.First in
set_option genInjectivity false in
/-- The supplied or missing apartness evidence for one jet's value name.

The supplied case is indexed by the actual input jet; the missing case records an outstanding obligation without
asserting that apartness is impossible. -/
inductive ReciprocalEvidence (jet : Provenance.JetData) where
  /-- Retain apartness evidence for this jet's value name. -/ | supplied : Apart
      jet.value.name → ReciprocalEvidence jet
  /-- Record that the required apartness evidence is missing. -/ | missing :
    ReciprocalEvidence jet

constructive_injectivity ReciprocalEvidence

open Purelib.Calculus.Jet.Progressive.First in
open Purelib.Calculus.Jet.Preparation in
/-- Prepare a reciprocal jet from supplied apartness, or report missing denominator evidence. -/
def reciprocal (jet : Provenance.JetData) :
    ReciprocalEvidence jet → Diagnostic.Decision Provenance.JetData
  | .supplied apart => .accepted (jet.reciprocal apart)
  | .missing => .rejected .denominatorApartness

open Purelib.Approximation in
open Purelib.Calculus.Jet.Progressive.First in
set_option genInjectivity false in
/-- The supplied or missing apartness evidence for a denominator jet.

Evidence refers to that denominator's actual value name and is reused when constructing its reciprocal. -/
inductive DivisionEvidence (denominator : Provenance.JetData) where
  /-- Retain apartness evidence for the denominator's value name. -/ | supplied : Apart
      denominator.value.name → DivisionEvidence denominator
  /-- Record that denominator apartness evidence is missing. -/ | missing :
    DivisionEvidence denominator

constructive_injectivity DivisionEvidence

open Purelib.Calculus.Jet.Progressive.First in
open Purelib.Calculus.Jet.Preparation in
/-- Prepare a quotient jet from denominator apartness, or report that missing certificate. -/
def div (numerator denominator : Provenance.JetData) :
    DivisionEvidence denominator → Diagnostic.Decision Provenance.JetData
  | .supplied apart => .accepted (numerator.div denominator apart)
  | .missing => .rejected .denominatorApartness

open Purelib.Approximation in
open Purelib.Calculus.Jet.Progressive.First in
set_option genInjectivity false in
/-- The supplied or incomplete anchored-chart and apartness evidence for a jet.

The complete case retains a chart for the actual value channel together with apartness of its name. The
missing-apartness case still retains its available chart. -/
inductive LogarithmEvidence (jet : Provenance.JetData) where
  /-- Retain the anchored chart and apartness evidence for the same jet value. -/ | supplied : (branch :
    AnchoredChart jet.value) →
      Apart jet.value.name →
        LogarithmEvidence jet
  /-- Record that the logarithm chart is missing. -/ | missingChart :
    LogarithmEvidence jet
  /-- Retain the chart while recording missing apartness evidence. -/ | missingApartness :
    AnchoredChart jet.value →
    LogarithmEvidence jet

constructive_injectivity LogarithmEvidence

open Purelib.Calculus.Jet.Progressive.First in
open Purelib.Calculus.Jet.Preparation in
/-- Prepare a logarithm jet or report the missing chart or apartness certificate.

Complete evidence is passed to the logarithm constructor. Incomplete cases return the corresponding diagnostic tag and
assert no impossibility result. -/
def logarithm (jet : Provenance.JetData) :
    LogarithmEvidence jet → Diagnostic.Decision Provenance.JetData
  | .supplied branch apart => .accepted (jet.logarithm branch apart)
  | .missingChart => .rejected .safeLogarithmChart
  | .missingApartness _branch => .rejected .denominatorApartness

section
open Purelib.Calculus.Jet.Progressive.First
/-- A missing reciprocal certificate reports denominator apartness. -/
@[simp] theorem reciprocal_missing_exposes_requirement
    (jet : Provenance.JetData) :
    (reciprocal jet .missing).missing? = some .denominatorApartness := rfl

/-- A missing division certificate reports denominator apartness. -/
@[simp] theorem division_missing_exposes_requirement
    (numerator denominator : Provenance.JetData) :
    (div numerator denominator .missing).missing? =
      some .denominatorApartness := rfl

/-- A missing logarithm chart reports the safe-chart requirement. -/
@[simp] theorem logarithm_missing_chart_exposes_requirement
    (jet : Provenance.JetData) :
    (logarithm jet .missingChart).missing? = some .safeLogarithmChart := rfl

end

open Purelib.Approximation in
open Purelib.Calculus.Jet.Progressive.First in
/-- A supplied chart with missing apartness reports denominator apartness. -/
@[simp] theorem
  logarithm_missing_apartness_exposes_requirement
    (jet : Provenance.JetData) (branch : AnchoredChart
      jet.value) :
    (logarithm jet (.missingApartness branch)).missing? =
      some .denominatorApartness := rfl
end Purelib.Calculus.Jet.Progressive.First.Preparation

end
