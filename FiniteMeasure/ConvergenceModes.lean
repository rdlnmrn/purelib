import FiniteMeasure.AlmostEverywhere

/-!
# Finite convergence-mode certificates

Instead of asserting convergence of a sequence, this module records one
finite accuracy claim: at a positive rational tolerance, the probability of
a larger error is bounded by an explicit rational failure budget.  L1 error,
almost-everywhere equality, and exceptional-event control all produce such
certificates.
-/

namespace FiniteMeasure

namespace Distribution

/-- One explicit finite convergence-in-measure certificate. -/
structure InMeasureBudget {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) where
  threshold : Coordinate
  threshold_positive : 0 < threshold
  failure : Coordinate
  failure_nonnegative : 0 ≤ failure
  probability_le :
    distribution.probability (separationAtLeast threshold left right) ≤
      failure

namespace InMeasureBudget

/-- Exact L1 error supplies the usual finite Markov failure budget. -/
def ofL1 {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold) : InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := distribution.l1Distance left right / threshold
  failure_nonnegative := RFAP.ConstructiveFraction.div_nonneg_direct
    (distribution.l1Distance_nonneg left right) positive.le
  probability_le :=
    distribution.probability_separationAtLeast_le_l1
      threshold positive left right

/-- Swapping the two observables preserves the same tolerance and failure
budget. -/
def symm {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : InMeasureBudget distribution left right) :
    InMeasureBudget distribution right left where
  threshold := budget.threshold
  threshold_positive := budget.threshold_positive
  failure := budget.failure
  failure_nonnegative := budget.failure_nonnegative
  probability_le := by
    calc
      distribution.probability
            (separationAtLeast budget.threshold right left) =
          distribution.probability
            (separationAtLeast budget.threshold left right) :=
        distribution.probability_congr _ _ (fun item => by
          unfold separationAtLeast
          rw [rationalSeparation_symm])
      _ ≤ budget.failure := budget.probability_le

/-- A displayed failure budget below the requested tolerance certifies the
requested probabilistic accuracy. -/
theorem accurate {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : InMeasureBudget distribution left right)
    (epsilon : Coordinate) (small : budget.failure < epsilon) :
    distribution.probability
        (separationAtLeast budget.threshold left right) < epsilon :=
  budget.probability_le.trans_lt small

end InMeasureBudget

/-- Almost-everywhere equal finite observables have zero probability of any
strictly positive displayed separation. -/
theorem probability_separationAtLeast_eq_zero_of_equalAlmostEverywhere
    {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate)
    (equal : distribution.EqualAlmostEverywhere left right)
    (threshold : Coordinate) (positive : 0 < threshold) :
    distribution.probability (separationAtLeast threshold left right) = 0 := by
  calc
    distribution.probability (separationAtLeast threshold left right) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      rcases equal atom member with zero | same
      · exact Or.inl zero
      · apply Or.inr
        change decide (threshold ≤
          rationalSeparation (left atom.item) (right atom.item)) = false
        apply decide_eq_false_iff_not.mpr
        intro thresholdLe
        have separationZero :
            rationalSeparation (left atom.item) (right atom.item) = 0 :=
          (rationalSeparation_eq_zero_iff _ _).mpr same
        rw [separationZero] at thresholdLe
        exact (not_le_of_gt positive) thresholdLe
    _ = 0 := distribution.probability_false

/-- Almost-everywhere equality gives a zero-failure in-measure certificate at
every supplied positive rational threshold. -/
def InMeasureBudget.ofEqualAlmostEverywhere {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (equal : distribution.EqualAlmostEverywhere left right)
    (threshold : Coordinate) (positive : 0 < threshold) :
    InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := 0
  failure_nonnegative := le_rfl
  probability_le := by
    rw [distribution.probability_separationAtLeast_eq_zero_of_equalAlmostEverywhere
      left right equal threshold positive]

/-- If error below the threshold holds outside one displayed exceptional
event, its exact probability is a failure budget.  This is the finite
exceptional-set bridge between pointwise and in-measure accuracy. -/
def InMeasureBudget.ofExceptionalEvent {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (threshold : Coordinate) (positive : 0 < threshold)
    (exceptional : α → Bool)
    (outside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = false →
        rationalSeparation (left atom.item) (right atom.item) < threshold) :
    InMeasureBudget distribution left right where
  threshold := threshold
  threshold_positive := positive
  failure := distribution.probability exceptional
  failure_nonnegative := distribution.probability_nonneg exceptional
  probability_le := by
    apply eventWeight_mono
    intro atom member selected
    cases exceptionalSelected : exceptional atom.item
    · have thresholdLe : threshold ≤
          rationalSeparation (left atom.item) (right atom.item) :=
        of_decide_eq_true selected
      exact ((outside atom member exceptionalSelected).2 thresholdLe).elim
    · rfl

end Distribution

end FiniteMeasure
