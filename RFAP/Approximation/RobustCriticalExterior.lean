import RFAP.Approximation.ErrorComparisonStability
import RFAP.Approximation.RobustCriticalCylinder

/-!
# One common finite radius preserving a transported critical window

The perturbative cylinder cutoff reduces every possible new mixed-cylinder
competitor to 20,736 displayed coefficient pairs.  Each pair whose
denominator is not already exterior receives its computed strict-error
comparison budget.  Their finite minimum, together with the basis error
order and cutoff budget, gives one positive rational squared-distance on
which the entire consecutive-best certificate persists.
-/

namespace RFAP.RobustCriticalExterior

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair
abbrev Coefficients := GaussianInt × GaussianInt

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

def coefficientCandidate (targetStage : Nat)
    (coefficients : Coefficients) : Pair :=
  linearCombination
    (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
    (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
    coefficients.1 coefficients.2

/-- These are exactly the bounded coefficient pairs for which the
source-dependent error wall, rather than the source-independent denominator
wall, must be kept strict. -/
def RequiresErrorComparison (targetStage : Nat)
    (coefficients : Coefficients) : Prop :=
  coefficients.1 ≠ 0 ∧ coefficients.2 ≠ 0 ∧
    ¬ denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) <
      denominatorQuadrance (coefficientCandidate targetStage coefficients)

instance requiresErrorComparisonDecidable
    (targetStage : Nat) (coefficients : Coefficients) :
    Decidable (RequiresErrorComparison targetStage coefficients) := by
  unfold RequiresErrorComparison
  infer_instance

theorem exact_error_exterior
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients)
    (requires : RequiresErrorComparison targetStage coefficients) :
    errorQuadrance source.value
        (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage) <
      errorQuadrance source.value
        (coefficientCandidate targetStage coefficients) := by
  rcases normal.strictExteriorCertificate.bothNonzeroExterior
      coefficients.1 coefficients.2 requires.1 requires.2.1 with
    errorExterior | denominatorExterior
  · exact errorExterior
  · exact (requires.2.2 denominatorExterior).elim

/-- A positive budget for one bounded coefficient pair.  Pairs already
settled by a zero coefficient or the denominator wall receive the harmless
default budget one. -/
def coefficientComparisonDistanceSq
    {source : Fraction} {errorStage targetStage : Nat}
    (_normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients) : Coordinate :=
  if RequiresErrorComparison targetStage coefficients then
    RFAP.ErrorComparisonStability.comparisonDistanceSq source.value
      (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
      (coefficientCandidate targetStage coefficients)
  else 1

theorem coefficientComparisonDistanceSq_pos
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients) :
    0 < coefficientComparisonDistanceSq normal coefficients := by
  unfold coefficientComparisonDistanceSq
  split
  · rename_i requires
    exact RFAP.ErrorComparisonStability.comparisonDistanceSq_pos
      (exact_error_exterior normal coefficients requires)
  · exact (show (0 : Coordinate) < 1 by decide)

private def minimumCoefficientComparisonDistanceSq
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) : List Coefficients → Coordinate
  | [] => 1
  | coefficients :: remaining =>
      min (coefficientComparisonDistanceSq normal coefficients)
        (minimumCoefficientComparisonDistanceSq normal remaining)

private theorem minimumCoefficientComparisonDistanceSq_pos
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : List Coefficients) :
    0 < minimumCoefficientComparisonDistanceSq normal coefficients := by
  induction coefficients with
  | nil => exact (show (0 : Coordinate) < 1 by decide)
  | cons head remaining inductionHypothesis =>
      unfold minimumCoefficientComparisonDistanceSq
      exact lt_min (coefficientComparisonDistanceSq_pos normal head)
        inductionHypothesis

private theorem minimumCoefficientComparisonDistanceSq_le_of_mem
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    {coefficients : Coefficients} (list : List Coefficients)
    (member : coefficients ∈ list) :
    minimumCoefficientComparisonDistanceSq normal list ≤
      coefficientComparisonDistanceSq normal coefficients := by
  induction list with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

def basisErrorDistanceSq
    {source : Fraction} {errorStage targetStage : Nat}
    (_normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) : Coordinate :=
  RFAP.ErrorComparisonStability.comparisonDistanceSq source.value
    (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
    (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)

theorem basisErrorDistanceSq_pos
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) :
    0 < basisErrorDistanceSq normal := by
  exact RFAP.ErrorComparisonStability.comparisonDistanceSq_pos
    normal.strictExteriorCertificate.errorOrder

/-- One positive rational squared-distance budget retaining the full strict
exterior certificate, not only its threshold violation. -/
def robustExteriorDistanceSq
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) : Coordinate :=
  min (RFAP.RobustCriticalCylinder.coefficientCutoffDistanceSq normal)
    (min (basisErrorDistanceSq normal)
      (minimumCoefficientComparisonDistanceSq normal
        RFAP.RobustCriticalCylinder.boundedCoefficientPairs))

theorem robustExteriorDistanceSq_pos
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) :
    0 < robustExteriorDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact lt_min
    (RFAP.RobustCriticalCylinder.coefficientCutoffDistanceSq_pos normal)
    (lt_min (basisErrorDistanceSq_pos normal)
      (minimumCoefficientComparisonDistanceSq_pos normal _))

private theorem robustExteriorDistanceSq_le_cutoff
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) :
    robustExteriorDistanceSq normal ≤
      RFAP.RobustCriticalCylinder.coefficientCutoffDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact min_le_left _ _

private theorem robustExteriorDistanceSq_le_basis
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) :
    robustExteriorDistanceSq normal ≤ basisErrorDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact (min_le_right _ _).trans (min_le_left _ _)

private theorem robustExteriorDistanceSq_le_coefficient
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    {coefficients : Coefficients}
    (member : coefficients ∈
      RFAP.RobustCriticalCylinder.boundedCoefficientPairs) :
    robustExteriorDistanceSq normal ≤
      coefficientComparisonDistanceSq normal coefficients := by
  unfold robustExteriorDistanceSq
  have outerBound := min_le_right
    (RFAP.RobustCriticalCylinder.coefficientCutoffDistanceSq normal)
    (min (basisErrorDistanceSq normal)
      (minimumCoefficientComparisonDistanceSq normal
        RFAP.RobustCriticalCylinder.boundedCoefficientPairs))
  have innerBound := min_le_right (basisErrorDistanceSq normal)
    (minimumCoefficientComparisonDistanceSq normal
      RFAP.RobustCriticalCylinder.boundedCoefficientPairs)
  have memberBound :
      minimumCoefficientComparisonDistanceSq normal
          RFAP.RobustCriticalCylinder.boundedCoefficientPairs ≤
        coefficientComparisonDistanceSq normal coefficients := by
    apply minimumCoefficientComparisonDistanceSq_le_of_mem normal
    exact member
  exact outerBound.trans (innerBound.trans memberBound)

private theorem error_exterior_of_distance
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian) (coefficients : Coefficients)
    (requires : RequiresErrorComparison targetStage coefficients)
    (member : coefficients ∈
      RFAP.RobustCriticalCylinder.boundedCoefficientPairs)
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    errorQuadrance sample
        (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage) <
      errorQuadrance sample
        (coefficientCandidate targetStage coefficients) := by
  apply RFAP.ErrorComparisonStability.errorQuadrance_lt_of_distance
    (exact_error_exterior normal coefficients requires)
  have globalLe := robustExteriorDistanceSq_le_coefficient normal member
  have distanceLePair := distanceSmall.trans_le globalLe
  unfold coefficientComparisonDistanceSq at distanceLePair
  rw [if_pos requires] at distanceLePair
  exact distanceLePair

/-- Every rational Gaussian sample in the common distance budget retains the
complete strict exterior certificate for this transported critical basis. -/
theorem strictExteriorCertificate_of_distance
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian)
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    RFAP.BasisCylinder.StrictExteriorCertificate sample
      (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) := by
  let lower := RFAP.FiniteWindowSharpness.criticalLowerPair targetStage
  let upper := RFAP.FiniteWindowSharpness.criticalUpperPair targetStage
  refine
    { indexOne := RFAP.FiniteWindowSharpness.criticalPair_indexOne targetStage
      lowerDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalLower_denominator_ne_zero targetStage
      upperDenominatorNonzero :=
        RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero targetStage
      errorOrder := ?_
      denominatorOrder :=
        RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered
          targetStage
      bothNonzeroExterior := ?_ }
  · apply RFAP.ErrorComparisonStability.errorQuadrance_lt_of_distance
      normal.strictExteriorCertificate.errorOrder
    exact distanceSmall.trans_le (robustExteriorDistanceSq_le_basis normal)
  · intro left right leftNonzero rightNonzero
    let coefficients : Coefficients := (left, right)
    let candidate := coefficientCandidate targetStage coefficients
    by_cases denominatorExterior :
        denominatorQuadrance upper < denominatorQuadrance candidate
    · exact Or.inr denominatorExterior
    · left
      by_contra errorNotExterior
      have sampleErrorBound :
          errorQuadrance sample candidate ≤ errorQuadrance sample lower :=
        le_of_not_gt errorNotExterior
      have denominatorBound :
          denominatorQuadrance candidate ≤ denominatorQuadrance upper :=
        Nat.le_of_not_gt denominatorExterior
      have coefficientBounds :=
        RFAP.RobustCriticalCylinder.coefficient_normNat_lt_thirtyTwo_of_nearby_competitor
          normal sample left right sampleErrorBound denominatorBound
          ((distanceSmall.trans_le
            (robustExteriorDistanceSq_le_cutoff normal)).le)
      have member : coefficients ∈
          RFAP.RobustCriticalCylinder.boundedCoefficientPairs :=
        RFAP.RobustCriticalCylinder.mem_boundedCoefficientPairs_of_normNat_lt_thirtyTwo
          coefficientBounds.1 coefficientBounds.2
      have requires : RequiresErrorComparison targetStage coefficients := by
        exact ⟨leftNonzero, rightNonzero, denominatorExterior⟩
      exact errorNotExterior
        (error_exterior_of_distance normal sample coefficients requires member
          distanceSmall)

/-- Hence the transported pair remains consecutive best throughout the
explicit finite rational neighborhood. -/
theorem transportedPairs_areConsecutiveBest_of_distance
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian)
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    AreConsecutiveBest sample
      (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) :=
  (strictExteriorCertificate_of_distance normal sample distanceSmall).areConsecutiveBest

end RFAP.RobustCriticalExterior
