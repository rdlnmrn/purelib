module

public import Purelib.Polynomial.Approximation.Gaussian.Localization
public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Localization
-- Public request readbacks retain this exact original localization-radius procedure.
public import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field

/-!
# Complete finite coverage by original multiplicity root candidates

Every positive point-comparison request computes a localization radius and a
sufficient residual stage. All later original samples have nearby candidates
from the same stored factor preparations and coherent root caches.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Localization.Preparation

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
open Purelib.Approximation.Rational.Geometric
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Compute all-later original-sample coverage using the same retained polynomial, multiplicities and root caches.

The budget reads only the retained scale and threshold. Original sample
localization is deferred to the returned locator at its actual requested index;
computing the sufficient stage does not evaluate an unused observation. -/
def coverage {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) :
    Sequence.Selection.Coverage preparation.source.toApproximation preparation.roots.candidates where
  prepare current target targetPositive := by
    let epsilon := Geometric.dyadicSquareRadius (target / 128)
    have epsilonPositive := Geometric.dyadicSquareRadius_positive (target / 128)
    have radiusSmall := Geometric.dyadicSquareRadius_sq_lt
      (Fraction.Order.Field.div_pos_direct targetPositive
        (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)) : 0 < target / 128)
    let observation := preparation.observe current (epsilon := epsilon) epsilonPositive
    let index := Search.firstQuarterBelow preparation.residualScale current (preparation.factors.threshold epsilon)
    have same : observation.index = index := by
      rewrite [observation.index_eq, observation.target_eq]
      rfl
    refine ⟨index, same ▸ observation.index_ge, ?_⟩
    intro later order
    let localized := observation.localizeLater epsilonPositive later (same.symm ▸ order)
    exact preparation.roots.nearby localized.selected.index (preparation.source.sample later)
      targetPositive radiusSmall localized.localized

/-- Coverage retains the complete original observation-based stage and every later localization result.

Both records have the same original candidate family, computed index and
later-sample locator. The equality preserves the complete returned value,
including requests whose source refinement advances beyond that first stage. -/
private theorem coverage_prepare_eq_observe {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) (current : Nat) (target : Fraction.Rational)
    (targetPositive : 0 < target) :
    preparation.coverage.prepare current target targetPositive = (by
      let epsilon := Geometric.dyadicSquareRadius (target / 128)
      have epsilonPositive := Geometric.dyadicSquareRadius_positive (target / 128)
      have radiusSmall := Geometric.dyadicSquareRadius_sq_lt
        (Fraction.Order.Field.div_pos_direct targetPositive
          (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)) : 0 < target / 128)
      let observation := preparation.observe current (epsilon := epsilon) epsilonPositive
      refine ⟨observation.index, observation.index_ge, ?_⟩
      intro later order
      let localized := observation.localizeLater epsilonPositive later order
      exact preparation.roots.nearby localized.selected.index (preparation.source.sample later)
        targetPositive radiusSmall localized.localized) := by
  unfold coverage
  dsimp only
  let epsilon := Geometric.dyadicSquareRadius (target / 128)
  have epsilonPositive := Geometric.dyadicSquareRadius_positive (target / 128)
  have radiusSmall := Geometric.dyadicSquareRadius_sq_lt
    (Fraction.Order.Field.div_pos_direct targetPositive
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)) : 0 < target / 128)
  let index := Search.firstQuarterBelow preparation.residualScale current (preparation.factors.threshold epsilon)
  have complete (observation : preparation.Observation current epsilon) (same : observation.index = index) :
      (⟨index, same ▸ observation.index_ge, fun later order =>
        let localized := observation.localizeLater epsilonPositive later (same.symm ▸ order)
        preparation.roots.nearby localized.selected.index (preparation.source.sample later)
          targetPositive radiusSmall localized.localized⟩ :
        Sequence.Selection.CoverAt preparation.source.toApproximation preparation.roots.candidates current target) =
      ⟨observation.index, observation.index_ge, fun later order =>
        let localized := observation.localizeLater epsilonPositive later order
        preparation.roots.nearby localized.selected.index (preparation.source.sample later)
          targetPositive radiusSmall localized.localized⟩ := by
    rcases observation with ⟨_, thresholdEq, _, indexEq, _, _, _, _, _, _, _⟩
    cases thresholdEq
    cases indexEq
    rfl
  exact complete (preparation.observe current epsilonPositive) (by
    rewrite [(preparation.observe current epsilonPositive).index_eq,
      (preparation.observe current epsilonPositive).target_eq]
    rfl)

/-- Every requested source reading meets its same original multiplicity threshold. -/
theorem request_residualSmall {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target) :
    normSq (polynomial.normalize.eval (preparation.source.sample request.index)) <
      preparation.factors.threshold (Geometric.dyadicSquareRadius (target / 128)) := by
  let epsilon := Geometric.dyadicSquareRadius (target / 128)
  let threshold := preparation.factors.threshold epsilon
  have thresholdPositive := preparation.factors.threshold_positive
    (Geometric.dyadicSquareRadius_positive (target / 128))
  have budget := Search.firstQuarterBelow_accurate preparation.residualScale
    preparation.residualScale_nonnegative current threshold thresholdPositive
  have order : Search.firstQuarterBelow preparation.residualScale current threshold ≤ request.index := by
    change (preparation.coverage.prepare current target request.positive).index ≤ request.index
    rewrite [← request.cover_eq]
    exact request.index_ge
  rewrite [Dense.Basic.DensePolynomial.eval_normalize]
  exact (preparation.residual request.index).trans_lt
    ((Basic.quarterRadius_antitone preparation.residualScale_nonnegative order).trans_lt budget)

/-- A requested locator is the complete original localization of that same source sample. -/
theorem request_locate_eq {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target) :
    request.locate = (by
      let localized := preparation.factors.localize (preparation.source.sample request.index)
        (Geometric.dyadicSquareRadius_positive (target / 128)) (preparation.request_residualSmall request)
      exact preparation.roots.nearby localized.selected.index (preparation.source.sample request.index)
        request.positive (Geometric.dyadicSquareRadius_sq_lt
          (Fraction.Order.Field.div_pos_direct request.positive
            (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))) localized.localized) := by
  rcases request with ⟨positive, cover, coverEq, index, indexEq⟩
  cases coverEq
  cases indexEq
  dsimp only [Sequence.Selection.Coverage.Request.locate, coverage]
  rewrite [Observation.localizeLater_eq]
  rfl

/-- Restore an original requested nearby result from an authenticated source scalar and complete cached locator.

The source identity transports the actual returned nearby certificate. Its
whole-value equality is to the same request's original factor localization
and root-family operation, preserving every original occurrence and payment. -/
def nearbyFromLocalized {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target)
    (sample : {value : Canonical // value = preparation.source.sample request.index})
    (value : Sequence.Selection.Nearby preparation.roots.candidates sample.val target)
    (same : value = (by
      let localized := preparation.factors.localize sample.val
        (Geometric.dyadicSquareRadius_positive (target / 128)) (by
          rewrite [sample.property]
          exact preparation.request_residualSmall request)
      exact preparation.roots.nearby localized.selected.index sample.val request.positive
        (Geometric.dyadicSquareRadius_sq_lt (Fraction.Order.Field.div_pos_direct request.positive
          (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))) localized.localized)) :
    {result : Sequence.Selection.Nearby preparation.roots.candidates
      (preparation.source.sample request.index) target // result = request.locate} := by
  refine ⟨sample.property ▸ value, ?_⟩
  rcases sample with ⟨_, sampleEq⟩
  cases sampleEq
  exact same.trans (preparation.request_locate_eq request).symm

/-- Localize an authenticated cached source reading through its exact original coverage request.

The original preparation, candidate family, requested index and target are
unchanged. Only the supplied scalar is evaluated; its readback transports the
complete nearby result to the original source without rereading that source. -/
def nearbyFromSample {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Preparation polynomial original) {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target)
    (sample : { value : Canonical // value = preparation.source.sample request.index }) :
    { value : Sequence.Selection.Nearby preparation.roots.candidates
        (preparation.source.sample request.index) target // value = request.locate } := by
  let epsilon := Geometric.dyadicSquareRadius (target / 128)
  have epsilonPositive := Geometric.dyadicSquareRadius_positive (target / 128)
  have small : normSq (polynomial.normalize.eval sample.val) < preparation.factors.threshold epsilon := by
    rewrite [sample.property]
    exact preparation.request_residualSmall request
  let localized := preparation.factors.localize sample.val epsilonPositive small
  let nearby := preparation.roots.nearby localized.selected.index sample.val request.positive
    (Geometric.dyadicSquareRadius_sq_lt (Fraction.Order.Field.div_pos_direct request.positive
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))) localized.localized
  refine ⟨sample.property ▸ nearby, ?_⟩
  rcases sample with ⟨value, same⟩
  cases same
  exact (preparation.request_locate_eq request).symm

end Purelib.Polynomial.Approximation.Gaussian.Localization.Preparation

end
