module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Parameters
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Reading parameters across original multiplicity factor towers

Each retained original context supplies its own fixed radius. Its same
mapped factor tower is prepared once, and the next context uses that tower's
actual final weight and fixed gain before any roots are observed.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading renaming Parameters → TowerParameters
open Purelib.Algebra.Ring (Weight)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

universe u

set_option genInjectivity false in
/-- Fixed reading caches for the same original sequence of mapped factor towers.

The radius function retains original bounded context indices. Each next
cache is indexed by the preceding original tower's actual final weight and
gain, without rebuilding any factor or adjunction.
-/
inductive Parameters {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    (radii : Fin contexts.length → Rational) : {indices : List (Fin contexts.length)} →
    {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] → {function : Canonical → K} →
    Stages contexts indices K ring equality function → Weight K → Rational → Type (u + 1)
  /-- No original context remains, so its input gain is already the fixed final gain. -/
  | done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {parent : Weight K} {gain : Rational} (gainNonnegative : 0 ≤ gain) :
      Parameters radii (.done : Stages contexts [] K ring equality function) parent gain
  /-- Prepare one original factor tower and continue with its retained endpoint parameters. -/
  | adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {index : Fin contexts.length} {indices : List (Fin contexts.length)} {mapped : DensePolynomial K}
      {mappedEq : mapped = Map.map function (factor contexts index)}
      {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor contexts index).natDegree}
      {tower : Tower K ring equality mapped} {roots : List (Dense.Roots.Block tower.Scalar)}
      {rootsEq : roots = tower.blocks}
      {remaining : Stages contexts indices tower.Scalar inferInstance inferInstance
        (fun value => tower.embed (function value))} {parent : Weight K} {gain : Rational}
      (current : TowerParameters tower parent gain (radii index))
      (next : Parameters radii remaining current.finalWeight current.finalGain) :
      Parameters radii (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain

constructive_injectivity Parameters

namespace Parameters

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}

/-- Prepare each same original factor tower once using its original context's fixed radius. -/
@[expose] def prepare {indices : List (Fin contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    (stages : Stages contexts indices K ring equality function) (parent : Weight K)
    (gain : Rational) (radii : Fin contexts.length → Rational) (gainNonnegative : 0 ≤ gain)
    (radiiNonnegative : ∀ index, 0 ≤ radii index) : Parameters radii stages parent gain :=
  match indices, stages with
  | [], .done => .done gainNonnegative
  | index :: _, .adjoin _ _ _ _ tower _ _ remaining =>
      let current := TowerParameters.prepare tower parent gain (radii index) gainNonnegative (radiiNonnegative index)
      let next := prepare remaining current.finalWeight current.finalGain radii
        current.finalGain_nonnegative radiiNonnegative
      .adjoin current next

/-- The final weight belongs to the same original common coefficient algebra. -/
@[expose] def finalWeight {indices : List (Fin contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {stages : Stages contexts indices K ring equality function} {radii : Fin contexts.length → Rational}
    {parent : Weight K} {gain : Rational} (parameters : Parameters radii stages parent gain) : Weight stages.Scalar :=
  match indices, stages, parameters with
  | [], .done, .done _ => parent
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining, .adjoin _ next => finalWeight (stages := remaining) next

/-- Read the fixed gain retained at the last original context's endpoint. -/
@[expose] def finalGain {indices : List (Fin contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {stages : Stages contexts indices K ring equality function} {radii : Fin contexts.length → Rational}
    {parent : Weight K} {gain : Rational} (parameters : Parameters radii stages parent gain) : Rational :=
  match indices, stages, parameters with
  | [], .done, .done _ => gain
  | _ :: _, .adjoin _ _ _ _ _ _ _ _, .adjoin _ next => finalGain next

variable {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {function : Canonical → K} {stages : Stages contexts indices K ring equality function}
variable {radii : Fin contexts.length → Rational} {parent : Weight K} {gain : Rational}

/-- The same original final fixed gain is nonnegative. -/
theorem finalGain_nonnegative (parameters : Parameters radii stages parent gain) :
    0 ≤ parameters.finalGain := by
  induction parameters with
  | done nonnegative => exact nonnegative
  | adjoin _ _ previous => exact previous

/-- Count cached original context towers, without observing their roots. -/
@[expose] def factors {indices : List (Fin contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {stages : Stages contexts indices K ring equality function} {radii : Fin contexts.length → Rational}
    {parent : Weight K} {gain : Rational} (parameters : Parameters radii stages parent gain) : Nat :=
  match indices, stages, parameters with
  | [], .done, .done _ => 0
  | _ :: _, .adjoin _ _ _ _ _ _ _ _, .adjoin _ next => factors next + 1

/-- Every displayed original context supplies exactly one retained tower cache. -/
theorem factors_eq_indices (parameters : Parameters radii stages parent gain) :
    parameters.factors = indices.length := by
  induction parameters with
  | done => rfl
  | adjoin _ _ previous => exact congrArg Nat.succ previous

end Parameters

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading

end
