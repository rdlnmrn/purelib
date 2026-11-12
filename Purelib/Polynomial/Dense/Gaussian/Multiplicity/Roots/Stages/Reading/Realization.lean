module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Request
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Composed Gaussian readings of original multiplicity stages

Each same original factor tower supplies its actual paid realization. Its
cached final reading is the input of the next original context. A retained
common endpoint and typed trace keep this execution chain explicit without
an executable elimination of its large dependent proof.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading renaming
  Parameters → TowerParameters, Request → TowerRequest, Realization → TowerRealization
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

universe u

/-- The same original common final coefficient algebra with its retained reading weight and scalar map. -/
@[expose] def Endpoint {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
    {radii : Fin contexts.length → Rational} {parent : Weight K} {gain : Rational}
    (parameters : Parameters radii stages parent gain) : Type u :=
  GaussianReading parameters.finalWeight (fun coefficient => stages.embed (function coefficient))

set_option genInjectivity false in
/-- The paid original tower realizations producing one exact retained common endpoint.

The next context consumes the current tower's same cached final reading.
Every input model, gain equation, original request and context remains an
index, so a supplied final reading alone cannot certify a realization.
-/
inductive Trace {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {radii : Fin contexts.length → Rational} : {indices : List (Fin contexts.length)} →
    {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] → {function : Canonical → K} →
    {stages : Stages contexts indices K ring equality function} → {parent : Weight K} →
    {gain target tolerance : Rational} → {parameters : Parameters radii stages parent gain} →
    Budget parameters target tolerance → (reading : GaussianReading parent function) → reading.gain = gain →
    Endpoint parameters → Type (u + 1)
  /-- An empty original context chain retains its same input reading. -/
  | done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {parent : Weight K} {gain target : Rational} {gainNonnegative : 0 ≤ gain} {targetPositive : 0 < target}
      {reading : GaussianReading parent function} {gain_eq : reading.gain = gain} :
      Trace (.done targetPositive : Budget
        (.done gainNonnegative : Parameters radii (.done : Stages contexts [] K ring equality function)
          parent gain) target target) reading gain_eq reading
  /-- The actual current tower endpoint is the same reading consumed by the remaining original contexts. -/
  | adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {index : Fin contexts.length} {indices : List (Fin contexts.length)} {mapped : DensePolynomial K}
      {mappedEq : mapped = Map.map function (factor contexts index)}
      {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor contexts index).natDegree}
      {tower : Tower K ring equality mapped} {roots : List (Dense.Roots.Block tower.Scalar)}
      {rootsEq : roots = tower.blocks}
      {remaining : Stages contexts indices tower.Scalar inferInstance inferInstance
        (fun value => tower.embed (function value))} {parent : Weight K} {gain target tolerance : Rational}
      {current : TowerParameters tower parent gain (radii index)}
      {next : Parameters radii remaining current.finalWeight current.finalGain}
      {reading : GaussianReading parent function} {gain_eq : reading.gain = gain}
      {endpoint : Endpoint next} (tail : Budget next target tolerance) (request : TowerRequest current tolerance)
      (observation : TowerRealization request.budget reading gain_eq)
      (rest : Trace tail observation.finalReading observation.final_gain endpoint) :
      Trace (.adjoin tail request : Budget
        (.adjoin current next : Parameters radii
          (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain)
        target request.tolerance) reading gain_eq endpoint

constructive_injectivity Trace

set_option genInjectivity false in
/-- A cached common final reading with the original paid realization at every factor tower.

The endpoint is stored directly for executable access. Its trace certifies
that the same retained original towers and intermediate readings construct
it, including the precise backward requirements of the fixed budget.
-/
structure Realization {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
    {radii : Fin contexts.length → Rational} {parent : Weight K} {gain target tolerance : Rational}
    {parameters : Parameters radii stages parent gain} (budget : Budget parameters target tolerance)
    (reading : GaussianReading parent function) (gain_eq : reading.gain = gain) where
  /-- The same cached reading of the common original final coefficient algebra. -/
  finalReading : Endpoint parameters
  /-- Every original factor realization produces this same endpoint through the retained budget. -/
  trace : Trace budget reading gain_eq finalReading

constructive_injectivity Realization

namespace Realization

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}

/-- Retain the same input reading when there are no original factor contexts. -/
@[expose] def done {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {radii : Fin contexts.length → Rational} {parent : Weight K}
    {gain target : Rational} {gainNonnegative : 0 ≤ gain}
    (reading : GaussianReading parent function) (gain_eq : reading.gain = gain)
    (targetPositive : 0 < target) : Realization (.done targetPositive : Budget
      (.done gainNonnegative : Parameters radii (.done : Stages contexts [] K ring equality function)
        parent gain) target target) reading gain_eq :=
  { finalReading := reading, trace := .done }

/-- Retain the actual current tower realization and its same next-context endpoint without replay. -/
@[expose] def adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {index : Fin contexts.length} {indices : List (Fin contexts.length)}
    {mapped : DensePolynomial K} {mappedEq : mapped = Map.map function (factor contexts index)}
    {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor contexts index).natDegree}
    {tower : Tower K ring equality mapped} {roots : List (Dense.Roots.Block tower.Scalar)}
    {rootsEq : roots = tower.blocks}
    {remaining : Stages contexts indices tower.Scalar inferInstance inferInstance
      (fun value => tower.embed (function value))} {radii : Fin contexts.length → Rational}
    {parent : Weight K} {gain target tolerance : Rational}
    {current : TowerParameters tower parent gain (radii index)}
    {next : Parameters radii remaining current.finalWeight current.finalGain}
    {reading : GaussianReading parent function} {gain_eq : reading.gain = gain}
    (tail : Budget next target tolerance) (request : TowerRequest current tolerance)
    (observation : TowerRealization request.budget reading gain_eq)
    (rest : Realization tail observation.finalReading observation.final_gain) :
    Realization (.adjoin tail request : Budget
      (.adjoin current next : Parameters radii
        (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain)
      target request.tolerance) reading gain_eq :=
  { finalReading := rest.finalReading, trace := .adjoin tail request observation rest.trace }

variable {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
variable {radii : Fin contexts.length → Rational} {parent : Weight K} {gain target tolerance : Rational}
variable {parameters : Parameters radii stages parent gain} {budget : Budget parameters target tolerance}
variable {reading : GaussianReading parent function} {gain_eq : reading.gain = gain}

/-- The common endpoint has exactly the final gain fixed before observing the original roots. -/
theorem final_gain (realization : Realization budget reading gain_eq) :
    realization.finalReading.gain = parameters.finalGain := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | done => assumption
      | adjoin _ _ _ _ previous => exact previous

/-- The same paid original context realizations compose to the requested final error bound. -/
theorem error_le (realization : Realization budget reading gain_eq) :
    reading.error ≤ tolerance → realization.finalReading.error ≤ target := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | done => intro bounded; exact bounded
      | adjoin _ _ observation _ previous =>
          intro bounded
          exact previous (observation.error_le bounded)

/-- A strict initial error bound remains strict after the original complete context chain. -/
theorem error_lt (realization : Realization budget reading gain_eq) :
    reading.error < tolerance → realization.finalReading.error < target := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | done => intro bounded; exact bounded
      | adjoin _ _ observation _ previous =>
          intro bounded
          exact previous (observation.error_lt bounded)

/-- Every original coefficient retains exactly its same initial reading in the common final algebra. -/
theorem final_read_embed (realization : Realization budget reading gain_eq) :
    ∀ value : K, realization.finalReading.read (stages.embed value) = reading.read value := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | done => intro value; rfl
      | adjoin _ _ observation _ previous =>
          intro value
          exact (previous (Tower.embed _ value)).trans
            (observation.final_read_embed value)

end Realization

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

end
