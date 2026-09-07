import FiniteMeasure.Moments
import FiniteMeasure.LpAlmostEverywhere

/-!
# Variance as finite powered-L2 distance

Variance is exactly the rational powered-L2 distance from a displayed
observable to its rational mean.  This identifies its zero set and relates
the moment and finite-almost-everywhere APIs without constructing an `L2`
completion.
-/

namespace FiniteMeasure

namespace Distribution

/-- Squared dispersion around any rational center is powered-L2 distance to
the corresponding constant observable. -/
theorem varianceAround_eq_poweredL2Distance_constant {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (center : Coordinate) :
    distribution.varianceAround value center =
      distribution.poweredL2Distance value (fun _ => center) := rfl

/-- Variance is powered-L2 distance to the exact rational mean. -/
theorem variance_eq_poweredL2Distance_expectation {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.variance value =
      distribution.poweredL2Distance value
        (fun _ => distribution.expectation value) := rfl

/-- Variance is bounded by the raw powered second moment. -/
theorem variance_le_poweredL2 {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.variance value ≤ distribution.poweredL2 value := by
  change distribution.variance value ≤
    distribution.expectation (fun item => value item ^ 2)
  exact distribution.variance_le_secondMoment value

/-- Definiteness modulo displayed zero-weight rows: variance vanishes exactly
when the observable equals its rational mean almost everywhere in the finite
sense. -/
theorem variance_eq_zero_iff_equalAlmostEverywhere_expectation {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.variance value = 0 ↔
      distribution.EqualAlmostEverywhere value
        (fun _ => distribution.expectation value) := by
  rw [distribution.variance_eq_poweredL2Distance_expectation,
    distribution.poweredL2Distance_eq_zero_iff]

end Distribution

end FiniteMeasure
