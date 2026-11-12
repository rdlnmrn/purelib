module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted
public import Purelib.Data.Vector.Dependent
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Bounds

/-! # Joint parameter and spatial payments on actual point-owner Taylor banks

The primary request remains the exact increment-fourth request. Each original
root first pays its independent additional spatial tolerance, then selects its
primary observation after that actual stage. The complete comparison pairs,
primary observations, sampled scalar caches and actual arithmetic readings are
retained once. Finite weighted banks consume those stored arithmetic entries.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point}

namespace Joint

/-- The original scalar Taylor-cache type retains this exact source, transported target and admitted increment. -/
@[expose] def Core (step : Step source increment) :=
  Sampling.SampledJet parameter increment point
    (source.certificate.castParameter (radicand_eq parameter point))
    (step.root.castParameter (radicand_eq (parameter + increment) point)) step.unit

/-- Construct the original scalar cache from the actual selected primary observations of both joint requests.

The original requests, states and comparison indices are inputs. Exact
parameter casts and the original seed-box clearance preserve those same
observations throughout the inverse/cubic Taylor construction.
-/
@[expose] def sample (step : Step source increment) (nonzero : increment ≠ 0)
    {sourceAdditional targetAdditional : AccuracyRequest}
    (first : CertifiedSquareRoot.Sampling.JointRequest source.certificate
      (Sampling.incrementRequest increment nonzero) sourceAdditional)
    (last : CertifiedSquareRoot.Sampling.JointRequest step.root
      (Sampling.incrementRequest increment nonzero) targetAdditional) : Core step :=
  Sampling.ofObservations parameter increment point _ _ (Sampling.incrementRequest increment nonzero) rfl
    (first.2.val.castParameter (radicand_eq parameter point))
    (last.2.val.castParameter (radicand_eq (parameter + increment) point))
    ((step.clearance first.2.val last.2.val).castParameters
      (radicand_eq parameter point) (radicand_eq (parameter + increment) point)) step.unit

end Joint

/-- Joint residual comparisons and one actual arithmetic Taylor cache on the same two full-cubic root processes.

Each request pair stores both its additional observation and actual later
primary observation. The scalar core contains precisely those primary caches,
transported only by exact parameter equality. The arithmetic readings consume
that one core and remain separate actual coefficient observations.
-/
@[expose] def Joint (step : Step source increment) (nonzero : increment ≠ 0)
    (sourceAdditional targetAdditional : AccuracyRequest) :=
  Σ first : CertifiedSquareRoot.Sampling.JointRequest source.certificate
      (Sampling.incrementRequest increment nonzero) sourceAdditional,
    Σ last : CertifiedSquareRoot.Sampling.JointRequest step.root
        (Sampling.incrementRequest increment nonzero) targetAdditional,
      Σ core : { retained : Joint.Core step // retained = Joint.sample step nonzero first last },
        { arithmetic : Arithmetic.Observations core.val // arithmetic = Arithmetic.request core.val }

namespace Joint

variable {step : Step source increment} {nonzero : increment ≠ 0}
    {sourceAdditional targetAdditional : AccuracyRequest}

section Readback

variable (retained : Joint step nonzero sourceAdditional targetAdditional)

/-- Read the complete source request pair, preserving both original comparisons and actual selected states. -/
@[expose] def sourceRequest : CertifiedSquareRoot.Sampling.JointRequest source.certificate
    (Sampling.incrementRequest increment nonzero) sourceAdditional := retained.1

/-- Read the complete target request pair without selecting another root observation. -/
@[expose] def targetRequest : CertifiedSquareRoot.Sampling.JointRequest step.root
    (Sampling.incrementRequest increment nonzero) targetAdditional := retained.2.1

/-- Read the same original scalar cache constructed on the two retained primary observations. -/
@[expose] def core : Core step := retained.2.2.1.val

/-- The whole scalar cache is the original factory on these exact two retained request pairs. -/
theorem core_eq : retained.core = sample step nonzero retained.sourceRequest retained.targetRequest :=
  retained.2.2.1.property

/-- Read the whole arithmetic-observation cache on this same retained scalar core. -/
@[expose] def arithmetic : Arithmetic.Observations retained.core := retained.2.2.2.val

/-- The entire arithmetic cache is the original request factory on the unchanged retained core. -/
theorem arithmetic_eq : retained.arithmetic = Arithmetic.request retained.core := retained.2.2.2.property

end Readback

/-- Pay parameter and independent spatial residuals, then cache the original scalar and arithmetic Taylor banks.

Each original root executes requestJoint once. The primary observations keep
their exact increment-fourth requests and also inherit the additional actual
comparison payments. No coarse observation is relabelled as a finer one.
-/
def build (step : Step source increment) (nonzero : increment ≠ 0)
    (sourceAdditional targetAdditional : AccuracyRequest) : Joint step nonzero sourceAdditional targetAdditional := by
  let primary := Sampling.incrementRequest increment nonzero
  let sourceRequest := CertifiedSquareRoot.Sampling.requestJoint source.certificate primary sourceAdditional
  let targetRequest := CertifiedSquareRoot.Sampling.requestJoint step.root primary targetAdditional
  let core := sample step nonzero sourceRequest targetRequest
  let arithmetic := Arithmetic.request core
  exact ⟨sourceRequest, targetRequest, ⟨core, rfl⟩, ⟨arithmetic, rfl⟩⟩

/-- Selected source candidates retain the independent spatial residual payment on their original process. -/
theorem source_additional (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.sourceRequest.2.val.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - (Paths.polynomial parameter).eval point) <
      sourceAdditional.tolerance :=
  retained.sourceRequest.1.residual_lt_after retained.sourceRequest.2.val retained.sourceRequest.2.property possible

/-- The selected target candidates retain their independent spatial residual payment on that original target process. -/
theorem target_additional (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.targetRequest.2.val.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - (Paths.polynomial (parameter + increment)).eval point) <
      targetAdditional.tolerance :=
  retained.targetRequest.1.residual_lt_after retained.targetRequest.2.val retained.targetRequest.2.property possible

/-- The exact scalar source-core observation also pays the independent spatial request after parameter reindexing. -/
theorem core_source_additional (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.core.sourceSample.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - Polynomials.curveValue parameter point) <
      sourceAdditional.tolerance := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_sourceSample,
    CertifiedSquareRoot.Sampling.ResidualObservation.castParameter_observation] at possible
  have bound := retained.source_additional possible
  rewrite [radicand_eq] at bound
  exact bound

/-- The exact scalar target-core observation pays the independent target spatial request on the changed radicand. -/
theorem core_target_additional (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.core.targetSample.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - Polynomials.curveValue (parameter + increment) point) <
      targetAdditional.tolerance := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_targetSample,
    CertifiedSquareRoot.Sampling.ResidualObservation.castParameter_observation] at possible
  have bound := retained.target_additional possible
  rewrite [radicand_eq] at bound
  exact bound

/-- The same selected source-core observation pays the additional radius request used for spatial sensitivity. -/
theorem core_source_spread (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.sourceSample.observation.spread <
      4 * (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_sourceSample,
    CertifiedSquareRoot.Sampling.ResidualObservation.castParameter_observation]
  exact retained.sourceRequest.1.spread_lt_after retained.sourceRequest.2.val retained.sourceRequest.2.property

/-- The same selected target-core observation pays its independently requested spatial radius bound. -/
theorem core_target_spread (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.targetSample.observation.spread <
      4 * (CertifiedSquareRoot.Sampling.radiusRequest step.root targetAdditional).tolerance := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_targetSample,
    CertifiedSquareRoot.Sampling.ResidualObservation.castParameter_observation]
  exact retained.targetRequest.1.spread_lt_after retained.targetRequest.2.val retained.targetRequest.2.property

section Nodes

variable {size : Nat} {points : Data.Vector Canonical size}
    {patches : (node : Fin size) → ContinuedNeighborhood (Paths.polynomial parameter) count}
    {sources : (node : Fin size) → ContinuedNeighborhood.Point (patches node) (points node)}
    (steps : Data.Vector.DependentVector (fun node => Step (sources node) increment))
    (unit : Norm.Basic.normSq increment ≤ 1) (nonzero : increment ≠ 0)
    (sourceAdditional targetAdditional : AccuracyRequest)

/-- Read the same stored sampled core at every original bounded node under the common unit-increment proof. -/
@[expose] def cores
    (retained : Data.Vector.DependentVector
      (fun node => Joint (steps.get node) nonzero sourceAdditional targetAdditional)) :
    (node : Fin size) → Sampling.SampledJet parameter increment (points node)
      ((sources node).certificate.castParameter (radicand_eq parameter (points node)))
      ((steps.get node).root.castParameter (radicand_eq (parameter + increment) (points node))) unit :=
  fun node => (retained.get node).core

/-- Read the identical retained arithmetic observation banks without another request at any node. -/
@[expose] def observations
    (retained : Data.Vector.DependentVector
      (fun node => Joint (steps.get node) nonzero sourceAdditional targetAdditional)) :
    Arithmetic.Weighted.NodeObservations (cores steps unit nonzero sourceAdditional targetAdditional retained) :=
  fun node => (retained.get node).arithmetic

/-- Materialize every original node's joint request once, then construct both actual weighted Taylor banks.

The original dependent-vector spine stores each complete joint cache.
The bank reads those stored cores and arithmetic observations; both row
families consume the same original point and weight indices, with no root,
coefficient request or node factory repeated for a row.
-/
def weighted (weights : Data.Vector Canonical size) :
    (retained : Data.Vector.DependentVector
      (fun node => Joint (steps.get node) nonzero sourceAdditional targetAdditional)) ×
      Arithmetic.Weighted.Bank (observations steps unit nonzero sourceAdditional targetAdditional retained) weights :=
  let retained := Data.Vector.DependentVector.ofFn
    (fun node => build (steps.get node) nonzero sourceAdditional targetAdditional)
  let bank := Arithmetic.Weighted.Bank.build
    (observations steps unit nonzero sourceAdditional targetAdditional retained) weights
  ⟨retained, bank⟩

variable {steps unit nonzero sourceAdditional targetAdditional}
    (retained : Data.Vector.DependentVector
      (fun node => Joint (steps.get node) nonzero sourceAdditional targetAdditional))
    {weights : Data.Vector Canonical size}
    (bank : Arithmetic.Weighted.Bank
      (observations steps unit nonzero sourceAdditional targetAdditional retained) weights)

include bank

/-- Actual weighted value readings obey the explicitly summed finite fourth-order remainder bound.

Every factor belongs to its retained original arithmetic entry. The source
slope is its actual independently observed first coefficient, and all sums
retain the identical original finite weights and bounded node occurrences.
-/
theorem value_remainder (coordinate : Fin 2) : Canonical.normSq
    (Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.targetValue coordinate).reading) -
      Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.sourceValue coordinate).reading) -
      increment * Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.sourceFirst coordinate).reading)) ≤
    ((size : Fraction.Rational) * Algebra.FiniteSum.Fin.sumFin (fun node => Norm.Basic.normSq (weights node) *
      ((retained.get node).arithmetic.valueCertificate coordinate).factor)) * Canonical.normSq increment ^ 2 := by
  have bound := bank.value_remainder_le coordinate
  rewrite [bank.value_factor coordinate] at bound
  exact bound

/-- Actual weighted first readings retain their independent second slope and explicitly summed fourth-order bound. -/
theorem first_remainder (coordinate : Fin 2) : Canonical.normSq
    (Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.targetFirst coordinate).reading) -
      Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.sourceFirst coordinate).reading) -
      increment * Algebra.FiniteSum.Fin.sumFin (fun node =>
        weights node * ((retained.get node).arithmetic.sourceSecond coordinate).reading)) ≤
    ((size : Fraction.Rational) * Algebra.FiniteSum.Fin.sumFin (fun node => Norm.Basic.normSq (weights node) *
      ((retained.get node).arithmetic.firstCertificate coordinate).factor)) * Canonical.normSq increment ^ 2 := by
  have bound := bank.first_remainder_le coordinate
  rewrite [bank.first_factor coordinate] at bound
  exact bound

end Nodes

end Joint

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end
