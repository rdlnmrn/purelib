module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Cylinder.Basis
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.Stability.ErrorComparison
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.CoefficientBound
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.NumberTheory.Approximation.Best.Stability

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# One common finite radius preserving a transported critical window

The perturbative cylinder cutoff reduces every possible new mixed-cylinder
competitor to 20,736 displayed coefficient pairs.  Each pair whose
denominator is not already exterior receives its computed strict-error
comparison budget.  Their finite minimum, together with the basis error
order and cutoff budget, gives one positive rational squared-distance on
which the entire consecutive-best certificate persists.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Exterior
/-- The two Gaussian integer coefficients of a critical-basis combination. -/
abbrev Coefficients := GaussianInt × GaussianInt

/-- The exact convergent pair obtained by a coefficient combination in the target critical basis. -/
@[expose] def coefficientCandidate (targetStage : Nat)
    (coefficients : Coefficients) : GaussianInt.Pair.Basic.ConvergentPair :=
  GaussianInt.Pair.LinearCombination.linearCombination
    (Pair.criticalLowerPair targetStage)
    (Pair.criticalUpperPair targetStage)
    coefficients.1 coefficients.2

/-- These are exactly the bounded coefficient pairs for which the
source-dependent error wall, rather than the source-independent denominator
wall, must be kept strict. -/
@[expose] def RequiresErrorComparison (targetStage : Nat)
    (coefficients : Coefficients) : Prop :=
  coefficients.1 ≠ 0 ∧ coefficients.2 ≠ 0 ∧
    ¬ Best.Error.denominatorQuadrance
        (Pair.criticalUpperPair targetStage) <
      Best.Error.denominatorQuadrance (coefficientCandidate targetStage coefficients)

/-- Decide whether both coefficients are nonzero and their candidate fails the strict denominator exterior test. -/
instance requiresErrorComparisonDecidable
    (targetStage : Nat) (coefficients : Coefficients) :
    Decidable (RequiresErrorComparison targetStage coefficients) := by
  unfold RequiresErrorComparison
  infer_instance

/-- A coefficient pair requiring error comparison lies beyond the error wall at the retained exact source.

The transported strict exterior certificate gives error or denominator exclusion; the defining requirement rules out the
denominator alternative. -/
theorem exact_error_exterior
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients)
    (requires : RequiresErrorComparison targetStage coefficients) :
    Best.Error.errorQuadrance source.value
        (Pair.criticalLowerPair targetStage) <
      Best.Error.errorQuadrance source.value
        (coefficientCandidate targetStage coefficients) := by
  rcases normal.strictExteriorCertificate.bothNonzeroExterior
      coefficients.1 coefficients.2 requires.1 requires.2.1 with
    errorExterior | denominatorExterior
  · exact errorExterior
  · exact (requires.2.2 denominatorExterior).elim

/-- A positive budget for one bounded coefficient pair.  Pairs already
settled by a zero coefficient or the denominator wall receive the harmless
default budget one. -/
@[expose] def coefficientComparisonDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients) : Fraction.Rational :=
  if RequiresErrorComparison targetStage coefficients then
    ErrorComparison.comparisonDistanceSq source.value
      (Pair.criticalLowerPair targetStage)
      (coefficientCandidate targetStage coefficients)
  else 1

/-- Every coefficient pair receives a positive error-comparison distance budget. -/
theorem coefficientComparisonDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : Coefficients) :
    0 < coefficientComparisonDistanceSq normal coefficients := by
  unfold coefficientComparisonDistanceSq
  split
  · rename_i requires
    exact ErrorComparison.comparisonDistanceSq_pos
      (exact_error_exterior normal coefficients requires)
  · exact (show (0 : Fraction.Rational) < 1 by decide)

/-- The recursive minimum of finitely many coefficient comparison budgets, capped by one.

The empty list returns one; each list entry lowers the retained budget by its own exact rational comparison bound. -/
@[expose] def minimumCoefficientComparisonDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) : List Coefficients → Fraction.Rational
  | [] => 1
  | coefficients :: remaining =>
      min (coefficientComparisonDistanceSq normal coefficients)
        (Exterior.minimumCoefficientComparisonDistanceSq
          normal remaining)

/-- The finite minimum of coefficient comparison budgets is positive. -/
private theorem minimumCoefficientComparisonDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (coefficients : List Coefficients) :
    0 < minimumCoefficientComparisonDistanceSq normal coefficients := by
  induction coefficients with
  | nil => exact (show (0 : Fraction.Rational) < 1 by decide)
  | cons head remaining inductionHypothesis =>
      unfold minimumCoefficientComparisonDistanceSq
      exact Fraction.Order.Basic.lt_min (coefficientComparisonDistanceSq_pos normal
        head)
        inductionHypothesis

/-- The finite minimum is no larger than the budget of each listed coefficient pair. -/
private theorem minimumCoefficientComparisonDistanceSq_le_of_mem
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    {coefficients : Coefficients} (list : List
      Coefficients)
    (member : coefficients ∈ list) :
    minimumCoefficientComparisonDistanceSq normal list ≤
      coefficientComparisonDistanceSq normal coefficients := by
  induction list with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact Fraction.Order.Basic.min_le_left _ _
      · exact (Fraction.Order.Basic.min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- The squared-distance budget preserving strict upper-to-lower error order in the target basis. -/
@[expose] def basisErrorDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (_normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) : Fraction.Rational :=
  ErrorComparison.comparisonDistanceSq source.value
    (Pair.criticalUpperPair targetStage)
    (Pair.criticalLowerPair targetStage)

/-- The basis error-order distance budget is positive for every transported normal form. -/
theorem basisErrorDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) :
    0 < basisErrorDistanceSq normal := by
  exact ErrorComparison.comparisonDistanceSq_pos
    normal.strictExteriorCertificate.errorOrder

/-- One positive rational squared-distance budget retaining the full strict
exterior certificate, not only its threshold violation. -/
@[expose] def robustExteriorDistanceSq
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) : Fraction.Rational :=
  min (CoefficientBound.coefficientCutoffDistanceSq normal)
    (min (basisErrorDistanceSq normal)
      (minimumCoefficientComparisonDistanceSq normal
        CoefficientBound.boundedCoefficientPairs))

/-- The common coefficient-cutoff and error-comparison budget is strictly positive. -/
theorem robustExteriorDistanceSq_pos
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) :
    0 < robustExteriorDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact Fraction.Order.Basic.lt_min
    (CoefficientBound.coefficientCutoffDistanceSq_pos normal)
    (Fraction.Order.Basic.lt_min (basisErrorDistanceSq_pos normal)
      (minimumCoefficientComparisonDistanceSq_pos normal _))

/-- The common exterior budget is bounded by the coefficient cutoff budget. -/
private theorem robustExteriorDistanceSq_le_cutoff
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) :
    robustExteriorDistanceSq normal ≤
      CoefficientBound.coefficientCutoffDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact Fraction.Order.Basic.min_le_left _ _

/-- The common exterior budget is bounded by the basis error-order budget. -/
private theorem robustExteriorDistanceSq_le_basis
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage) :
    robustExteriorDistanceSq normal ≤
      basisErrorDistanceSq normal := by
  unfold robustExteriorDistanceSq
  exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The common exterior budget is bounded by the comparison budget of each enumerated coefficient pair. -/
private theorem robustExteriorDistanceSq_le_coefficient
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    {coefficients : Coefficients}
    (member : coefficients ∈
      CoefficientBound.boundedCoefficientPairs) :
    robustExteriorDistanceSq normal ≤
      coefficientComparisonDistanceSq normal coefficients := by
  unfold robustExteriorDistanceSq
  have outerBound := Fraction.Order.Basic.min_le_right
    (CoefficientBound.coefficientCutoffDistanceSq normal)
    (min (basisErrorDistanceSq normal)
      (minimumCoefficientComparisonDistanceSq normal
        CoefficientBound.boundedCoefficientPairs))
  have innerBound := Fraction.Order.Basic.min_le_right (basisErrorDistanceSq normal)
    (minimumCoefficientComparisonDistanceSq normal
      CoefficientBound.boundedCoefficientPairs)
  have memberBound :
      minimumCoefficientComparisonDistanceSq normal
          CoefficientBound.boundedCoefficientPairs ≤
        coefficientComparisonDistanceSq normal coefficients := by
    apply minimumCoefficientComparisonDistanceSq_le_of_mem normal
    exact member
  exact outerBound.trans (innerBound.trans memberBound)

/-- The strict error exterior persists inside the common distance budget.

The coefficient pair must belong to the finite domain and require error comparison; its individual comparison budget
then preserves the strict inequality at the sampled source. -/
private theorem error_exterior_of_distance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian.Basic.Canonical) (coefficients : Coefficients)
    (requires : RequiresErrorComparison targetStage coefficients)
    (member : coefficients ∈
      CoefficientBound.boundedCoefficientPairs)
    (distanceSmall :
      Gaussian.Norm.Basic.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    Best.Error.errorQuadrance sample
        (Pair.criticalLowerPair targetStage) <
      Best.Error.errorQuadrance sample
        (coefficientCandidate targetStage coefficients) := by
  apply ErrorComparison.errorQuadrance_lt_of_distance
    (exact_error_exterior normal coefficients requires)
  have globalLe := robustExteriorDistanceSq_le_coefficient normal member
  have distanceLePair := distanceSmall.trans_le globalLe
  unfold coefficientComparisonDistanceSq at distanceLePair
  rw [if_pos requires] at distanceLePair
  exact distanceLePair

/-- Every rational Gaussian sample in the common distance budget retains the
complete strict exterior certificate for this transported critical basis. -/
theorem strictExteriorCertificate_of_distance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian.Basic.Canonical)
    (distanceSmall :
      Gaussian.Norm.Basic.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    Best.Cylinder.Basis.StrictExteriorCertificate sample
      (Pair.criticalLowerPair targetStage)
      (Pair.criticalUpperPair targetStage) := by
  let lower := Pair.criticalLowerPair targetStage
  let upper := Pair.criticalUpperPair targetStage
  refine
    { indexOne := Pair.criticalPair_indexOne targetStage
      lowerDenominatorNonzero :=
        Pair.criticalLower_denominator_ne_zero targetStage
      upperDenominatorNonzero :=
        Pair.criticalUpper_denominator_ne_zero targetStage
      errorOrder := ?_
      denominatorOrder :=
        Pair.critical_denominatorQuadrance_ordered
          targetStage
      bothNonzeroExterior := ?_ }
  · apply ErrorComparison.errorQuadrance_lt_of_distance
      normal.strictExteriorCertificate.errorOrder
    exact distanceSmall.trans_le (robustExteriorDistanceSq_le_basis normal)
  · intro left right leftNonzero rightNonzero
    let coefficients : Coefficients := (left, right)
    let candidate := coefficientCandidate targetStage coefficients
    by_cases denominatorExterior :
        Best.Error.denominatorQuadrance upper < Best.Error.denominatorQuadrance candidate
    · exact Or.inr denominatorExterior
    · left
      by_contra errorNotExterior
      have sampleErrorBound :
          Best.Error.errorQuadrance sample candidate ≤ Best.Error.errorQuadrance sample lower :=
        le_of_not_gt errorNotExterior
      have denominatorBound :
          Best.Error.denominatorQuadrance candidate ≤ Best.Error.denominatorQuadrance upper :=
        Nat.le_of_not_gt denominatorExterior
      have coefficientBounds :=
        CoefficientBound.coefficient_normNat_lt_thirtyTwo_of_nearby_competitor
          normal sample left right sampleErrorBound denominatorBound
          ((distanceSmall.trans_le
            (robustExteriorDistanceSq_le_cutoff normal)).le)
      have member : coefficients ∈
          CoefficientBound.boundedCoefficientPairs :=
        CoefficientBound.mem_boundedCoefficientPairs_of_normNat_lt_thirtyTwo
          coefficientBounds.1 coefficientBounds.2
      have requires : RequiresErrorComparison targetStage coefficients := by
        exact ⟨leftNonzero, rightNonzero, denominatorExterior⟩
      exact errorNotExterior
        (error_exterior_of_distance normal sample coefficients requires member
          distanceSmall)

/-- Hence the transported pair remains consecutive best throughout the
explicit finite rational neighborhood. -/
theorem transportedPairs_areConsecutiveBest_of_distance
    {source : GaussianInt.Fraction} {errorStage targetStage : Nat}
    (normal : Adjacent.Tower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian.Basic.Canonical)
    (distanceSmall :
      Gaussian.Norm.Basic.normSq (sample - source.value) <
        robustExteriorDistanceSq normal) :
    Best.Consecutive.Basic.AreConsecutiveBest sample
      (Pair.criticalLowerPair targetStage)
      (Pair.criticalUpperPair targetStage) :=
  (strictExteriorCertificate_of_distance normal sample
    distanceSmall).areConsecutiveBest

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Exterior

end
