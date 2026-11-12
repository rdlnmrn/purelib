module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Samples

/-!
# Original higher-owner scheduled sampling clients

These retained clients prepare the residual schedule before selecting any
new point, then consume the same actual source expansion and original
geometric bounds. Restoration supplies the cached data and their full
original-procedure equations rather than rerunning their producers.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Samples

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Dense.Gaussian
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation
open Purelib.RootIsolation.Multiplicity.Circle
open CenterProduct (Approximation)

variable {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
variable {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}

/-- Prepare the same positive original target list before reading a new point. -/
private def scheduled (argument : Approximation locations) (targets : List Fraction.Rational)
    (positive : ∀ target ∈ targets, 0 < target) :=
  Interpolation.Schedule.prepare argument.request.gaps.bound argument.request.gaps.positive targets positive

/-- Consume that same prepaid schedule in the original higher-owner source constructor. -/
private def prepared (argument : Approximation locations) (targets : List Fraction.Rational)
    (positive : ∀ target ∈ targets, 0 < target) (count : targets.length = polynomial.natDegree) :
    Roots.Samples argument (scheduled argument targets positive).val :=
  let schedule := scheduled argument targets positive
  Roots.Samples.prepare argument schedule.val schedule.property count

/-- The complete construction pays every actual original quotient target and preserves the same node geometry. -/
private theorem actual_chain {targets : List Fraction.Rational} (argument : Approximation locations)
    (positive : ∀ target ∈ targets, 0 < target) (count : targets.length = polynomial.natDegree) :
    let samples := prepared argument targets positive count
    samples.expansion.Pays targets ∧ samples.nodes.length = polynomial.natDegree ∧
      samples.nodes.Pairwise (fun left right =>
        argument.request.gaps.bound ≤ Gaussian.Norm.Basic.normSq (left - right)) ∧
      (∀ point ∈ samples.nodes, Gaussian.Norm.Basic.normSq point ≤ argument.request.radius) := by
  let samples := prepared argument targets positive count
  exact ⟨samples.payment, samples.nodes_count, samples.separated, samples.node_bounds⟩

/-- The actual source chain belongs to the original factor, with its complete canonical construction equality. -/
private theorem source_chain {targets : List Fraction.Rational} (argument : Approximation locations)
    (positive : ∀ target ∈ targets, 0 < target) (count : targets.length = polynomial.natDegree) :
    let samples := prepared argument targets positive count
    samples.expansion = Interpolation.Expansion.prepare polynomial samples.nodes :=
  (prepared argument targets positive count).expansion_eq

/-- Same original sample indices preserve the quantitative collar gap after the new source request. -/
private theorem original_gap {targets : List Fraction.Rational} (argument : Approximation locations)
    (positive : ∀ target ∈ targets, 0 < target) (count : targets.length = polynomial.natDegree)
    (index : Fin argument.request.regions.length) :
    let samples := prepared argument targets positive count
    locations.request.collar.width ^ 2 < ((samples.sampleAt index).point.normSq - 1) ^ 2 :=
  (prepared argument targets positive count).radial_gap index

/-- Retained source data restore the entire original sampling result with no replacement division or observation. -/
private theorem restore_source {targets : List Fraction.Rational} (argument : Approximation locations)
    (positive : ∀ target ∈ targets, 0 < target) (count : targets.length = polynomial.natDegree) :
    let samples := prepared argument targets positive count
    Roots.Samples.ofExpansion argument (scheduled argument targets positive).val samples.schedule_paid
        samples.targets_length_eq_degree samples.request samples.request_eq samples.entries samples.entries_eq
        samples.nodes samples.nodes_eq samples.expansion samples.expansion_eq =
      Roots.Samples.prepare argument (scheduled argument targets positive).val samples.schedule_paid
        samples.targets_length_eq_degree := by
  let samples := prepared argument targets positive count
  exact Roots.Samples.ofExpansion_eq_prepare argument (scheduled argument targets positive).val samples.schedule_paid
    samples.targets_length_eq_degree samples.request samples.request_eq samples.entries samples.entries_eq
    samples.nodes samples.nodes_eq samples.expansion samples.expansion_eq

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Samples
