module

import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial

public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name
public import Purelib.RootIsolation.Multiplicity.Observation.Track
public import Purelib.RootIsolation.Multiplicity.Site.Realization
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
public import Purelib.Riemann.RootContinuation.CoherentRoot.InitialName
public import Purelib.Riemann.RootContinuation.CoherentRoot.PointComparison
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Algebraic admission of original multiplicity-observation arithmetic names

Exact sites retain their original rational reading. Higher sites retain the
original attachment's actual track, focused source occurrence and one cached
root realization. The operational source equation preserves multiplicity
and is accompanied by a comparison to the original productive name.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL

open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.RootIsolation
open Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic (ObservationCCL)
open Purelib.RootIsolation.Multiplicity.Observation.Index (ObservationIndex)
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {context : PositiveContext input.entries}

set_option genInjectivity false in
/-- Exact scalar evidence or the actual original higher-site root realization at one retained observation and index.

The exact branch keeps the original displayed point. The higher branch is
indexed by the same original input, focused occurrence, attachment boxes and
bounded track index; its channel identity uses that retained realization.
-/
inductive Evidence : (observation : FactorObservation input context) → ObservationCCL observation →
    ObservationIndex observation → CoherentNamed → Type 1 where
  /-- The same original exact site supplies a scalar readback on the retained channel. -/
  | exact (root : Dense.Gaussian.Roots.Certificate.ExactRoot context.focus.part.polynomial)
      (degree : context.focus.part.polynomial.natDegree = 1) (oppositeAtRoot : opposite.eval root.point ≠ 0)
      (data : ObservationCCL (.exact root degree oppositeAtRoot)) (index : Unit)
      {channel : CoherentNamed} (reading : RationalSidecar channel) (value_eq : reading.value = root.point) :
      Evidence (.exact root degree oppositeAtRoot) data index channel
  /-- The same original attachment track supplies a cached focused-multiplicity root realization. -/
  | higher (boxes : FTA.Squarefree.BoxResult context.focus.part.polynomial)
      (degree : 2 ≤ context.focus.part.polynomial.natDegree)
      (data : ObservationCCL (.higher boxes degree)) (index : Fin context.focus.part.polynomial.natDegree)
      (realization : Multiplicity.Site.Realization (input.higherTrackInput context data.boxes index))
      {channel : CoherentNamed} (channel_eq : channel = realization.root.value) :
      Evidence (.higher boxes degree) data index channel

constructive_injectivity Evidence

set_option genInjectivity false in
/-- Algebraic evidence for one original productive multiplicity-observation name.

The original observation, attachment and index remain its parents. The same
retained channel has an operational comparison to that exact original name,
its exact or isolated admission evidence and the original source equation.
-/
structure Admission (observation : FactorObservation input context) (data : ObservationCCL observation)
    (index : ObservationIndex observation) where
  /-- The retained coherent arithmetic channel for the same original site. -/
  channel : CoherentNamed
  /-- The original productive arithmetic name agrees with this retained channel. -/
  equivalent : Equivalence.NamedEquivalent (CCL.Name.observationArithmeticName observation data index) channel.name
  /-- The exact scalar or actual original higher-site realization supplying admission. -/
  evidence : Evidence observation data index channel
  /-- Actual Horner evaluation of the original multiplicity source at this channel is operationally zero. -/
  equation : Equivalence.NamedEquivalent (Horner.polynomialEval source channel).name
    (CoherentNamed.Coherence.exact 0).name

constructive_injectivity Admission

namespace Admission

/-- Actual original deterministic root-state entries at this retained observation and site index.

An exact observation has no root-state cache. A higher observation retains
entries of precisely its existing attachment track; no source or selected
root owner is reconstructed by this indexed view.
-/
@[expose] def StateCache (observation : FactorObservation input context) (data : ObservationCCL observation)
    (index : ObservationIndex observation) : Type :=
  match observation, data, index with
  | .exact _ _ _, _, _ => PUnit
  | .higher _ _, data, index =>
      List (CoherentRoot.StateCache.Entry (input.higherTrackInput context data.boxes index).track)

/-- Admit one actual original higher-site realization at its existing attachment and bounded index.

The retained realization supplies its original numerical channel, source
equation and productive-name agreement. This shared record assembly consumes
the literal realization, including its exact original root-state cache.
-/
@[expose] def ofRealization (boxes : FTA.Squarefree.BoxResult context.focus.part.polynomial)
    (degree : 2 ≤ context.focus.part.polynomial.natDegree)
    (data : ObservationCCL (.higher boxes degree)) (index : Fin context.focus.part.polynomial.natDegree)
    (realization : Multiplicity.Site.Realization (input.higherTrackInput context data.boxes index)) :
    Admission (.higher boxes degree) data index := by
  have equation := realization.equation
  have normalized : Horner.polynomialEval source.normalize realization.root.value =
      Horner.polynomialEval source realization.root.value :=
    congrArg (fun polynomial => Horner.polynomialEval polynomial realization.root.value) input.sourceNormalized
  rewrite [normalized] at equation
  exact
    { channel := realization.root.value
      equivalent := realization.root.initial_named_equivalent ⟨context.focus.part.squarefree, degree⟩
      evidence := .higher boxes degree data index realization rfl
      equation := equation }

/-- Admit one retained exact or higher site without recomputing its original isolation.

Exact observations retain their original rational channel and source root.
Higher observations build one realization of the original attachment track;
the original box-process sampling comparison links its cached channel to the
existing productive name. Source normalization is transported explicitly.
-/
@[expose] def ofObservation (observation : FactorObservation input context) (data : ObservationCCL observation)
    (index : ObservationIndex observation) (cached : Option (StateCache observation data index) := none) :
    Admission observation data index := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      let channel := CoherentNamed.Coherence.exact root.point
      have sourceRoot := input.exactSourceRoot context root
      have equation := Horner.polynomialEval_exact source root.point
      rewrite [sourceRoot] at equation
      exact
        { channel := channel
          equivalent := Equivalence.NamedEquivalent.refl _
          evidence := .exact root degree oppositeAtRoot data index (RationalSidecar.exact root.point) rfl
          equation := equation }
  | higher boxes degree =>
      let site := input.higherTrackInput context data.boxes index
      let realization := Multiplicity.Site.Realization.ofInput site cached
      exact ofRealization boxes degree data index realization

/-- Supplied exact original state entries preserve the complete original observation admission. -/
theorem ofObservation_cached_eq_default (observation : FactorObservation input context)
    (data : ObservationCCL observation) (index : ObservationIndex observation)
    (cached : Option (StateCache observation data index)) :
    ofObservation observation data index cached = ofObservation observation data index none := by
  cases observation with
  | exact => rfl
  | higher boxes degree =>
      dsimp only [ofObservation]
      exact congrArg (ofRealization boxes degree data index)
        (Multiplicity.Site.Realization.ofInput_cached_eq_default _ cached)

/-- An absent cache retains the original exact branch and original higher-site realization procedure. -/
theorem ofObservation_none (observation : FactorObservation input context)
    (data : ObservationCCL observation) (index : ObservationIndex observation) :
    ofObservation observation data index none = ofObservation observation data index := rfl

/-- Project an actual retained higher-site root and its original factor input, without another realization.

Exact evidence has no stored track view and remains available through its
original scalar reader. Higher evidence retains the original admission,
attachment, bounded site index and actual same cached realization.
-/
@[expose] def view? {observation : FactorObservation input context} {data : ObservationCCL observation}
    {index : ObservationIndex observation} (admission : Admission observation data index) :
    Option (CertifiedName.View admission.channel) :=
  match admission.evidence with
  | .exact _ _ _ _ _ _ _ => none
  | .higher _ _ _ _ realization channelEq =>
      some ((CertifiedName.View.ofRoot realization.root realization.factorInput).transport (by
        rewrite [channelEq]
        exact Equivalence.NamedEquivalent.refl _) (some ⟨channelEq⟩))

/-- Read exact scalar provenance from the same retained admission without another inspection or root construction. -/
@[expose] def scalar? {observation : FactorObservation input context} {data : ObservationCCL observation}
    {index : ObservationIndex observation} (admission : Admission observation data index) :
    Option (RationalSidecar admission.channel) :=
  match admission.evidence with
  | .exact _ _ _ _ _ reading _ => some reading
  | .higher _ _ _ _ _ _ => none

/-- Lift the retained original site to a displayed source polynomial through its actual ordered cofactor identity.

The exact branch transports its scalar reading and original source root. The
higher branch combines the retained site cofactor with the supplied multiplier,
computes its box bound once and consumes that same bound in the original cached
root's residual comparison. The admitted numerical channel is unchanged.
-/
def sourceEquation {observation : FactorObservation input context} {data : ObservationCCL observation}
    {index : ObservationIndex observation} (admission : Admission observation data index)
    (target multiplier : CoefficientPolynomial)
    (identity : ∀ point, target.eval point = multiplier.eval point * source.eval point) :
    Equivalence.NamedEquivalent (Horner.polynomialEval target admission.channel).name
      (CoherentNamed.Coherence.exact 0).name := by
  cases admission.evidence with
  | exact root _ _ _ _ reading same =>
      have zero : target.eval reading.value = 0 := by
        rewrite [same, identity root.point, input.exactSourceRoot context root,
          Purelib.Data.Gaussian.Basic.mul_zero]
        rfl
      have exactValue := Horner.polynomialEval_exact target reading.value
      rewrite [zero] at exactValue
      let exactChannel := CoherentNamed.Coherence.exact reading.value
      let exactZero := CoherentNamed.Coherence.exact 0
      have respects := Horner.horner_respects admission.channel exactChannel exactZero exactZero
        reading.equivalent (Equivalence.NamedEquivalent.refl _) target.coeffs
      exact respects.trans exactValue
  | higher _ _ _ _ realization channelEq =>
      have cofactorEq : realization.cofactor = context.singleCofactor input.preprocessing.decomposition :=
        realization.cofactor_eq
      let cofactor := multiplier * realization.cofactor
      let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox context.focus.part.polynomial
      let bound := Dense.Gaussian.Bounds.Box.denseEvalNormBound cofactor ambient
      have factorization : ∀ point, target.eval point = context.focus.part.polynomial.eval point *
          cofactor.eval point := by
        intro point
        have original := Dense.Gaussian.Factorization.Identity.eval_factorization
          (input.focusFactorization context) point
        rewrite [← cofactorEq] at original
        rewrite [identity point, original, Dense.Basic.DensePolynomial.eval_mul]
        exact (Purelib.Data.Gaussian.Basic.mul_assoc _ _ _).symm.trans
          ((congrArg (fun value => value * realization.cofactor.eval point)
            (Purelib.Data.Gaussian.Basic.mul_comm _ _)).trans
            (Purelib.Data.Gaussian.Basic.mul_assoc _ _ _))
      have boundNonnegative := (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg cofactor ambient).1
      have bounded := fun index => Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound cofactor
        (realization.root.sample_inside index)
      rewrite [channelEq]
      exact realization.root.factor_zero target cofactor factorization bound boundNonnegative bounded

/-- Read quantitative numerical residual data from the same original exact or focused-factor root admission.

The numerical polynomial may be the retained squarefree factor or the exact
reading's monic linear factor. The original source polynomial, multiplicity,
attachment and source equation remain with the same admission owner.
-/
def numericalResidual {observation : FactorObservation input context} {data : ObservationCCL observation}
    {index : ObservationIndex observation} (admission : Admission observation data index) :
    Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial admission.channel := by
  cases admission.evidence with
  | exact _ _ _ _ _ reading _ =>
      exact ⟨Dense.Gaussian.LinearFactor.linearFactor reading.value,
        (PolynomialResidual.exact reading.value).transport reading.equivalent⟩
  | higher _ _ _ _ realization channelEq =>
      have equivalent : Equivalence.NamedEquivalent admission.channel.name realization.root.value.name := by
        rewrite [channelEq]
        exact Equivalence.NamedEquivalent.refl _
      exact ⟨context.focus.part.polynomial, realization.root.residualCertificate.transport equivalent⟩

/-- Decide exact zero or a prepared presentation of the same original admitted site channel.

Exact observations consume their retained scalar reading. Higher observations
consume the same cached original factor root and its squarefree certificate;
the coefficient-computed point comparison at zero supplies all finite work.
-/
def decide {observation : FactorObservation input context} {data : ObservationCCL observation}
    {index : ObservationIndex observation} (admission : Admission observation data index) :
    Division.Prepared.Decision admission.channel := by
  cases admission.evidence with
  | exact _ _ _ _ _ reading _ => exact reading.decide
  | higher _ _ _ _ realization channelEq =>
      rewrite [channelEq]
      exact CoherentRoot.PointComparison.decide realization.root realization.factorInput 0

end Admission

end Purelib.RootIsolation.Multiplicity.Observation.CCL

end
