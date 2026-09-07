import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments
import FiniteMeasure.Stochastic

/-!
# Moments through explicit finite kernels

The familiar total-variance and total-covariance decompositions are finite
identities here.  A kernel is only a function returning a displayed finite
rational table, and `bind` only scales, concatenates, and evaluates those
tables.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact finite law of total variance for a displayed transition kernel. -/
theorem bind_variance {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) (value : β → Coordinate) :
    (source.bind transition).variance value =
      source.expectation (fun item => (transition item).variance value) +
        source.variance (fun item => (transition item).expectation value) := by
  rw [(source.bind transition).variance_eq_secondMoment_sub_sq,
    source.bind_expectation transition,
    source.bind_expectation transition,
    source.variance_eq_secondMoment_sub_sq]
  have conditionalVariance :
      source.expectation
          (fun item => (transition item).variance value) =
        source.expectation (fun item =>
          (transition item).expectation (fun result => value result ^ 2) -
            (transition item).expectation value ^ 2) :=
    source.expectation_congr _ _ (fun item =>
      (transition item).variance_eq_secondMoment_sub_sq value)
  rw [conditionalVariance, source.expectation_sub]
  ring1

/-- Exact finite law of total covariance for a displayed transition
kernel. -/
theorem bind_covariance {α β : Type} (source : Distribution α)
    (transition : α → Distribution β)
    (left right : β → Coordinate) :
    (source.bind transition).covariance left right =
      source.expectation (fun item =>
        (transition item).covariance left right) +
      source.covariance
        (fun item => (transition item).expectation left)
        (fun item => (transition item).expectation right) := by
  rw [(source.bind transition).covariance_eq_productMoment_sub_means,
    source.bind_expectation transition,
    source.bind_expectation transition,
    source.bind_expectation transition,
    source.covariance_eq_productMoment_sub_means]
  have conditionalCovariance :
      source.expectation
          (fun item => (transition item).covariance left right) =
        source.expectation (fun item =>
          (transition item).expectation
              (fun result => left result * right result) -
            (transition item).expectation left *
              (transition item).expectation right) :=
    source.expectation_congr _ _ (fun item =>
      (transition item).covariance_eq_productMoment_sub_means left right)
  rw [conditionalCovariance, source.expectation_sub]
  ring1

end Distribution

end FiniteMeasure
