module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
public import Purelib.Approximation.Gaussian.Sequence.Selection
-- Complete higher-realization nearby readbacks identify this original owner operation.
public import Purelib.Riemann.RootContinuation.CoherentRoot.Assignment
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring

/-!
# Nearby candidates in original multiplicity root caches

Localization refers to an exact original factor or its original stored
isolation. The nearby candidate is read from that same factor's numerical
cache, then embedded at its unchanged original factor and root indices.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

namespace Realization

/-- Transfer original exact or isolated factor localization to its same retained root approximation cache. -/
def nearby {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (sample : Canonical) {epsilon target : Rational}
    (targetPositive : 0 < target) (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Residual.Multiplicity.Factor.Localized factor sample epsilon) :
    Sequence.Selection.Nearby roots.approximation sample target := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases roots with
    | linear value value_eq geometric geometric_eq =>
      cases localized with
      | linear near =>
        refine ⟨⟨0, show (0 : Nat) < 1 by decide⟩, 0, ?_⟩
        intro later _
        change normSq (geometric.sample later - sample) < target
        rewrite [geometric_eq]
        change normSq (data.point - sample) < target
        have reversed : data.point - sample = -(sample - data.point) := by ring0
        rewrite [reversed, Purelib.Data.Gaussian.Norm.Basic.normSq_neg]
        have targetLe : target / 128 ≤ target := Field.divide_le_self targetPositive.le (by
          change ((1 : Nat) : Rational) ≤ ((128 : Nat) : Rational)
          rewrite [Purelib.Data.Rat.Fraction.Cast.natCast_eq_fromInt 1,
            Purelib.Data.Rat.Fraction.Cast.natCast_eq_fromInt 128]
          decide)
        exact near.trans (radiusSmall.trans_le targetLe)
  | higher degree preparation =>
    cases roots with
    | higher roots =>
      cases localized with
      | higher assignment =>
        exact Assignment.nearby ⟨entry.part.squarefree, degree⟩ preparation.boxes.isolation roots sample
          targetPositive radiusSmall assignment

/-- A higher realization transfers the complete original assignment to its same original owner program. -/
theorem nearby_higher_eq {entry : PositiveEntry} {degree : 2 ≤ entry.part.polynomial.natDegree}
    {preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩}
    (roots : CoherentRoot.Family preparation.boxes.isolation.tracks) (sample : Canonical)
    {epsilon target : Rational} (positive : 0 < target) (small : epsilon ^ 2 < target / 128)
    (assigned : Residual.Global.Assignment.AssignedResult ⟨entry.part.squarefree, degree⟩ sample epsilon
      preparation.boxes.isolation) :
    (Realization.higher roots).nearby sample positive small (Residual.Multiplicity.Factor.Localized.higher assigned) =
      Assignment.nearby ⟨entry.part.squarefree, degree⟩ preparation.boxes.isolation roots sample
        positive small assigned := (rfl)

end Realization

namespace Family

/-- Embed one original factor's retained nearby result at the same original bounded occurrence.

The same factor and root indices determine the output candidate. Its original
stage and all-later bound are transported through the stored candidate
readback, without executing a factor or root locator. -/
@[expose] def embedNearby {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorIndex : Fin entries.length) (sample : Canonical) {target : Rational}
    (nearby : Sequence.Selection.Nearby (roots.get factorIndex).approximation sample target) :
    Sequence.Selection.Nearby roots.candidates sample target := by
  let occurrence := Index.fromFactor preparation factorIndex nearby.owner
  refine ⟨occurrence.toFin, nearby.index, ?_⟩
  intro later order
  have original := roots.candidates_fromFactor factorIndex nearby.owner
  change roots.candidates occurrence.toFin = (roots.get factorIndex).approximation nearby.owner at original
  rewrite [original]
  exact nearby.close later order

/-- Embed a localized factor's same cached nearby root at its original bounded occurrence indices. -/
def nearby {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorIndex : Fin entries.length) (sample : Canonical)
    {epsilon target : Rational} (targetPositive : 0 < target) (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Residual.Multiplicity.Factor.Localized (preparation.get factorIndex) sample epsilon) :
    Sequence.Selection.Nearby roots.candidates sample target :=
  embedNearby roots factorIndex sample ((roots.get factorIndex).nearby sample targetPositive radiusSmall localized)

/-- A retained original factor-nearby result preserves the complete original family-nearby certificate. -/
def nearbyFromFactor {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorIndex : Fin entries.length) (sample : Canonical)
    {epsilon target : Rational} (positive : 0 < target) (small : epsilon ^ 2 < target / 128)
    (localized : Residual.Multiplicity.Factor.Localized (preparation.get factorIndex) sample epsilon)
    (nearby : Sequence.Selection.Nearby (roots.get factorIndex).approximation sample target)
    (same : nearby = (roots.get factorIndex).nearby sample positive small localized) :
    {value : Sequence.Selection.Nearby roots.candidates sample target //
      value = roots.nearby factorIndex sample positive small localized} :=
  ⟨embedNearby roots factorIndex sample nearby, by cases same; rfl⟩

end Family

end Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

end
