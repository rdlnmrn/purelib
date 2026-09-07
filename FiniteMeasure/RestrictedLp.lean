import FiniteMeasure.NaturalLp
import FiniteMeasure.PartitionExpectation

/-!
# Powered Lp under finite restriction and conditioning

Restricting a displayed finite content multiplies the powered integrand by
an executable indicator and therefore cannot increase a nonnegative powered
quantity.  Normalized conditioning evaluates the same powered integrands by
the existing rational conditional mean.
-/

namespace FiniteMeasure

namespace FiniteContent

theorem restrict_poweredLp {α : Type} (content : FiniteContent α)
    (event : α → Bool) (exponent : Nat) (value : α → Coordinate) :
    (content.restrict event).poweredLp exponent value =
      content.integral (fun item => Distribution.indicator event item *
        rationalSeparation (value item) 0 ^ exponent) := by
  change (content.restrict event).integral (fun item =>
      rationalSeparation (value item) 0 ^ exponent) = _
  exact content.restrict_integral event _

theorem restrict_poweredLpDistance {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (exponent : Nat) (left right : α → Coordinate) :
    (content.restrict event).poweredLpDistance exponent left right =
      content.integral (fun item => Distribution.indicator event item *
        rationalSeparation (left item) (right item) ^ exponent) := by
  change (content.restrict event).integral (fun item =>
      rationalSeparation (left item) (right item) ^ exponent) = _
  exact content.restrict_integral event _

/-- Restriction cannot increase a natural-powered magnitude. -/
theorem restrict_poweredLp_le {α : Type} (content : FiniteContent α)
    (event : α → Bool) (exponent : Nat) (value : α → Coordinate) :
    (content.restrict event).poweredLp exponent value ≤
      content.poweredLp exponent value := by
  rw [content.restrict_poweredLp]
  apply content.integral_mono
  intro atom member
  cases selected : event atom.item
  · simp only [Distribution.indicator, selected, zero_mul]
    exact RFAP.ConstructiveFraction.pow_nonneg_direct
      (rationalSeparation_nonneg _ _) exponent
  · simp only [Distribution.indicator, selected, one_mul]
    exact le_rfl

/-- Restriction cannot increase a natural-powered distance. -/
theorem restrict_poweredLpDistance_le {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (exponent : Nat) (left right : α → Coordinate) :
    (content.restrict event).poweredLpDistance exponent left right ≤
      content.poweredLpDistance exponent left right := by
  rw [content.restrict_poweredLpDistance]
  apply content.integral_mono
  intro atom member
  cases selected : event atom.item
  · simp only [Distribution.indicator, selected, zero_mul]
    exact RFAP.ConstructiveFraction.pow_nonneg_direct
      (rationalSeparation_nonneg _ _) exponent
  · simp only [Distribution.indicator, selected, one_mul]
    exact le_rfl

theorem restrict_poweredL1_le {α : Type} (content : FiniteContent α)
    (event : α → Bool) (value : α → Coordinate) :
    (content.restrict event).poweredL1 value ≤ content.poweredL1 value := by
  have bound := content.restrict_poweredLp_le event 1 value
  rw [(content.restrict event).poweredLp_one,
    content.poweredLp_one] at bound
  exact bound

theorem restrict_l1Distance_le {α : Type} (content : FiniteContent α)
    (event : α → Bool) (left right : α → Coordinate) :
    (content.restrict event).l1Distance left right ≤
      content.l1Distance left right := by
  have bound := content.restrict_poweredLpDistance_le event 1 left right
  rw [(content.restrict event).poweredLpDistance_one,
    content.poweredLpDistance_one] at bound
  exact bound

theorem restrict_poweredL2_le {α : Type} (content : FiniteContent α)
    (event : α → Bool) (value : α → Coordinate) :
    (content.restrict event).poweredL2 value ≤ content.poweredL2 value := by
  have bound := content.restrict_poweredLp_le event 2 value
  rw [(content.restrict event).poweredLp_two,
    content.poweredLp_two] at bound
  exact bound

theorem restrict_poweredL2Distance_le {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (left right : α → Coordinate) :
    (content.restrict event).poweredL2Distance left right ≤
      content.poweredL2Distance left right := by
  have bound := content.restrict_poweredLpDistance_le event 2 left right
  rw [(content.restrict event).poweredLpDistance_two,
    content.poweredLpDistance_two] at bound
  exact bound

end FiniteContent

namespace Distribution

theorem conditioned_poweredLp_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (exponent : Nat) (value : α → Coordinate) :
    (distribution.conditioned event positive).poweredLp exponent value =
      distribution.conditionalMean event (fun item =>
        rationalSeparation (value item) 0 ^ exponent) := by
  change (distribution.conditioned event positive).expectation (fun item =>
      rationalSeparation (value item) 0 ^ exponent) = _
  exact distribution.conditioned_expectation_eq_conditionalMean
    event positive _

theorem conditioned_poweredLpDistance_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (exponent : Nat) (left right : α → Coordinate) :
    (distribution.conditioned event positive).poweredLpDistance
        exponent left right =
      distribution.conditionalMean event (fun item =>
        rationalSeparation (left item) (right item) ^ exponent) := by
  change (distribution.conditioned event positive).expectation (fun item =>
      rationalSeparation (left item) (right item) ^ exponent) = _
  exact distribution.conditioned_expectation_eq_conditionalMean
    event positive _

theorem conditioned_poweredL1_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    (distribution.conditioned event positive).poweredL1 value =
      distribution.conditionalMean event (fun item =>
        rationalSeparation (value item) 0) := by
  have identity := distribution.conditioned_poweredLp_eq_conditionalMean
    event positive 1 value
  rw [(distribution.conditioned event positive).poweredLp_one] at identity
  calc
    (distribution.conditioned event positive).poweredL1 value =
        distribution.conditionalMean event (fun item =>
          rationalSeparation (value item) 0 ^ 1) := identity
    _ = distribution.conditionalMean event (fun item =>
          rationalSeparation (value item) 0) :=
      distribution.conditionalMean_congr event _ _ (fun item => pow_one _)

theorem conditioned_l1Distance_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    (distribution.conditioned event positive).l1Distance left right =
      distribution.conditionalMean event (fun item =>
        rationalSeparation (left item) (right item)) := by
  have identity :=
    distribution.conditioned_poweredLpDistance_eq_conditionalMean
      event positive 1 left right
  rw [(distribution.conditioned event positive).poweredLpDistance_one]
    at identity
  calc
    (distribution.conditioned event positive).l1Distance left right =
        distribution.conditionalMean event (fun item =>
          rationalSeparation (left item) (right item) ^ 1) := identity
    _ = distribution.conditionalMean event (fun item =>
          rationalSeparation (left item) (right item)) :=
      distribution.conditionalMean_congr event _ _ (fun item => pow_one _)

theorem conditioned_poweredL2_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    (distribution.conditioned event positive).poweredL2 value =
      distribution.conditionalMean event (fun item => value item ^ 2) := by
  have identity := distribution.conditioned_poweredLp_eq_conditionalMean
    event positive 2 value
  rw [(distribution.conditioned event positive).poweredLp_two] at identity
  calc
    (distribution.conditioned event positive).poweredL2 value =
        distribution.conditionalMean event (fun item =>
          rationalSeparation (value item) 0 ^ 2) := identity
    _ = distribution.conditionalMean event (fun item => value item ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by
        simpa only [sub_zero] using rationalSeparation_sq (value item) 0)

theorem conditioned_poweredL2Distance_eq_conditionalMean {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    (distribution.conditioned event positive).poweredL2Distance left right =
      distribution.conditionalMean event (fun item =>
        (left item - right item) ^ 2) := by
  have identity :=
    distribution.conditioned_poweredLpDistance_eq_conditionalMean
      event positive 2 left right
  rw [(distribution.conditioned event positive).poweredLpDistance_two]
    at identity
  calc
    (distribution.conditioned event positive).poweredL2Distance left right =
        distribution.conditionalMean event (fun item =>
          rationalSeparation (left item) (right item) ^ 2) := identity
    _ = distribution.conditionalMean event (fun item =>
          (left item - right item) ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item =>
        rationalSeparation_sq (left item) (right item))

end Distribution

end FiniteMeasure
