module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Parameters
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Request
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Backward reading budgets across original multiplicity factors

The requested error in the common final coefficient algebra determines each
original factor tower's sufficient request. The next context's exact input
requirement is retained before preparing the preceding tower's request.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading renaming
  Parameters → TowerParameters, Request → TowerRequest
open Purelib.Algebra.Ring (Weight)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

universe u

set_option genInjectivity false in
/-- A backward budget retaining each same original factor tower's actual request.

The final target and initial tolerance remain indices. Each current tower
request targets the exact retained tail tolerance, rather than an unrelated
bound or a budget inferred after observations.
-/
inductive Budget {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {radii : Fin contexts.length → Rational} : {indices : List (Fin contexts.length)} →
    {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] → {function : Canonical → K} →
    {stages : Stages contexts indices K ring equality function} → {parent : Weight K} → {gain : Rational} →
    Parameters radii stages parent gain → Rational → Rational → Type (u + 1)
  /-- The empty original context chain retains the positive target as its input requirement. -/
  | done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {parent : Weight K} {gain target : Rational} {gainNonnegative : 0 ≤ gain}
      (targetPositive : 0 < target) :
      Budget (.done gainNonnegative : Parameters radii (.done : Stages contexts [] K ring equality function)
        parent gain) target target
  /-- The same actual tower request pays the exact retained next-context requirement. -/
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
      (tail : Budget next target tolerance) (request : TowerRequest current tolerance) :
      Budget (.adjoin current next : Parameters radii
        (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain)
        target request.tolerance

constructive_injectivity Budget

namespace Budget

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
variable {radii : Fin contexts.length → Rational} {parent : Weight K} {gain target tolerance : Rational}
variable {parameters : Parameters radii stages parent gain}

/-- Every complete original context budget has a positive initial tolerance. -/
theorem tolerance_positive (budget : Budget parameters target tolerance) : 0 < tolerance := by
  induction budget with
  | done positive => exact positive
  | adjoin _ request _ => exact request.positive

/-- The requested final target remains positive through the same backward chain. -/
theorem target_positive (budget : Budget parameters target tolerance) : 0 < target := by
  induction budget with
  | done positive => exact positive
  | adjoin _ _ previous => exact previous

end Budget

set_option genInjectivity false in
/-- A computed initial tolerance with all same original factor-tower requests.

The original parameter chain and final error target remain indices. The
cached budget certifies each intermediate target and its exact preceding
input requirement before any root candidates are selected.
-/
structure Request {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
    {radii : Fin contexts.length → Rational} {parent : Weight K} {gain : Rational}
    (parameters : Parameters radii stages parent gain) (target : Rational) where
  /-- The sufficient initial error tolerance computed from the final target. -/
  tolerance : Rational
  /-- The same computed sufficient tolerance is positive. -/
  positive : 0 < tolerance
  /-- Every actual original tower request and its exact next-context requirement. -/
  budget : Budget parameters target tolerance

constructive_injectivity Request

namespace Request

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}

/-- Compute all same original factor requests backwards from the positive final target. -/
@[expose] def prepare {indices : List (Fin contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {stages : Stages contexts indices K ring equality function} {radii : Fin contexts.length → Rational}
    {parent : Weight K} {gain : Rational} (parameters : Parameters radii stages parent gain)
    (target : Rational) (targetPositive : 0 < target) : Request parameters target :=
  match indices, stages, parameters with
  | [], .done, .done _ =>
      { tolerance := target, positive := targetPositive, budget := .done targetPositive }
  | _ :: _, .adjoin _ _ _ _ _ _ _ _, .adjoin current next =>
      let tail := prepare next target targetPositive
      let request := TowerRequest.prepare current tail.tolerance tail.positive
      { tolerance := request.tolerance, positive := request.positive, budget := .adjoin tail.budget request }

end Request

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

end
