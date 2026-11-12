module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Shifted
public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # One original seed box over a whole parameter strip

The actual neighborhood's retained movement ceiling leaves a positive slack
below its original contour-and-side allowance, including accepted growth.
Two capped rational allocations pay the weighted norm estimate without a
square root. The resulting fixed-box budget uses that identical original
seed owner for every physical point and every interpolated increment.
Actual retained Point.Step owners compare with this reference through their
own certified box refinements. No reconditioned spatial trace owner is
assumed to refine this box or to agree with the reference.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)

/-- The retained original allowance exceeds the actual computed whole-box movement ceiling. -/
@[expose] def slack : Rational := patch.continuationAllowance - range.movement

/-- The actual accepted or rejected neighborhood growth leaves strictly positive movement slack. -/
theorem slack_positive : 0 < range.slack := Order.Arithmetic.sub_pos_direct range.movement_small

/-- The retained whole-box movement ceiling is nonnegative. -/
theorem movement_nonnegative : 0 ≤ range.movement := by
  rewrite [range.movement_eq]
  exact CheckedPrimitiveNeighborhoods.movementCeiling_nonnegative patch

/-- Allocate a positive rational weight whose product with the retained movement costs less than a quarter slack. -/
@[expose] def weight : Rational := min 1 ((range.slack / 4) / (range.movement + 1))

/-- The first capped inverse allocation is positive. -/
theorem weight_positive : 0 < range.weight :=
  Order.Basic.lt_min (by decide +kernel)
    (Order.Field.div_pos_direct (Order.Field.div_pos_direct range.slack_positive (by decide +kernel))
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct range.movement_nonnegative (by decide +kernel)))

/-- The reciprocal coefficient is the exact second weight in the original Gaussian weighted sum bound. -/
@[expose] def reciprocalWeight : Rational := (range.weight + 1) / range.weight

/-- The original positive weight gives a positive reciprocal coefficient. -/
theorem reciprocalWeight_positive : 0 < range.reciprocalWeight :=
  Order.Field.div_pos_direct
    (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct range.weight_positive
      (by decide +kernel : (0 : Rational) ≤ 1)) range.weight_positive

/-- Allocate a positive radicand perturbation ceiling whose reciprocal-weighted cost is less than a quarter slack. -/
@[expose] def perturbation : Rational := min 1 ((range.slack / 4) / (range.reciprocalWeight + 1))

/-- The second capped inverse allocation is positive. -/
theorem perturbation_positive : 0 < range.perturbation :=
  Order.Basic.lt_min (by decide +kernel)
    (Order.Field.div_pos_direct (Order.Field.div_pos_direct range.slack_positive (by decide +kernel))
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct range.reciprocalWeight_positive.le
        (by decide +kernel)))

/-- Tighten the original common increment allocation by the exact finite slack of its original seed contour. -/
@[expose] def stripBound : Rational :=
  min range.shiftedBound (min 1 (range.perturbation / (range.coefficient + 1)))

/-- The original shifted allocation and positive slack allocation make the strip increment bound positive. -/
theorem stripBound_positive : 0 < range.stripBound :=
  Order.Basic.lt_min range.shiftedBound_positive
    (Order.Basic.lt_min (by decide +kernel)
      (Order.Field.div_pos_direct range.perturbation_positive
        (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct range.coefficient_nonnegative (by decide +kernel))))

/-- Every strip-admitted increment also satisfies the original shifted whole-box clearance payment. -/
theorem stripBound_le_shiftedBound : range.stripBound ≤ range.shiftedBound := Order.Basic.min_le_left _ _

/-- The computed original-seed movement ceiling retains the exact Gaussian weighted-sum coefficients. -/
@[expose] def stripMovement : Rational :=
  (range.weight + 1) * range.movement + range.reciprocalWeight * range.perturbation

/-- Both retained weighted movement contributions are nonnegative. -/
theorem stripMovement_nonnegative : 0 ≤ range.stripMovement := by
  unfold stripMovement
  have first := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct range.weight_positive
      (by decide +kernel : (0 : Rational) ≤ 1)).le range.movement_nonnegative
  have second := Order.Arithmetic.mul_nonneg_direct range.reciprocalWeight_positive.le
    range.perturbation_positive.le
  calc
    0 = 0 + 0 := by ring1
    _ ≤ _ := Order.Arithmetic.add_le_add_direct first second

/-- The first capped allocation consumes less than a quarter of the exact retained slack. -/
private theorem weight_payment : range.weight * range.movement < range.slack / 4 := by
  have paid := Order.Field.mul_min_one_div_lt range.movement_nonnegative
    (Order.Field.div_pos_direct range.slack_positive (by decide +kernel : (0 : Rational) < 4))
  exact (Field.mul_comm _ _).trans_lt paid

/-- The second capped allocation consumes less than a quarter of the exact retained slack. -/
private theorem perturbation_payment : range.reciprocalWeight * range.perturbation < range.slack / 4 :=
  Order.Field.mul_min_one_div_lt range.reciprocalWeight_positive.le
    (Order.Field.div_pos_direct range.slack_positive (by decide +kernel : (0 : Rational) < 4))

/-- The computed uniform strip movement stays strictly below the same original continuation allowance. -/
theorem stripMovement_lt_allowance : range.stripMovement < patch.continuationAllowance := by
  have paid := Order.Arithmetic.add_lt_add_direct range.weight_payment range.perturbation_payment
  have halfSlack : range.slack / 4 + range.slack / 4 < range.slack := by
    have quarterPositive := Order.Field.div_pos_direct range.slack_positive
      (by decide +kernel : (0 : Rational) < 4)
    have doubledPositive := Order.Arithmetic.add_pos_of_pos_of_nonneg_direct quarterPositive quarterPositive.le
    have strict := Order.Arithmetic.add_lt_add_left_direct doubledPositive (range.slack / 4 + range.slack / 4)
    calc
      range.slack / 4 + range.slack / 4 = (range.slack / 4 + range.slack / 4) + 0 := by ring1
      _ < (range.slack / 4 + range.slack / 4) + (range.slack / 4 + range.slack / 4) := strict
      _ = range.slack := by
        rewrite [Field.div_eq_mul_inv_direct]
        have fourths : (4 : Rational)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1 := by decide +kernel
        calc
          _ = range.slack * (4⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹) := by ring1
          _ = range.slack := by
            rewrite [fourths, Field.mul_one_direct]
            rfl
  have translated := Order.Arithmetic.add_lt_add_left_direct (paid.trans halfSlack) range.movement
  calc
    range.stripMovement = range.movement +
        (range.weight * range.movement + range.reciprocalWeight * range.perturbation) := by
          unfold stripMovement
          ring1
    _ < range.movement + range.slack := translated
    _ = patch.continuationAllowance := by unfold slack; ring1

/-- The exact same original seed box has positive contour margin after paying the entire parameter strip. -/
theorem stripMovement_lt_contour :
    range.stripMovement < patch.base.seed.owner.track.initial.clearance.bound :=
  range.stripMovement_lt_allowance.trans_le (by
    rewrite [patch.continuationAllowance_eq]
    exact Order.Basic.min_le_left _ _)

/-- The actual affine Legendre coefficient pays the computed perturbation ceiling uniformly on the identical box. -/
theorem perturbation_lt (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point) < range.perturbation := by
  have identity : (Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point = increment * Polynomials.baseValue point := by
    rewrite [radicand_eq, radicand_eq, Variation.radicand_step]
    ring1
  have allocated := Order.Field.mul_min_one_div_lt range.coefficient_nonnegative range.perturbation_positive
  have incrementBound := admitted.trans (Order.Basic.min_le_right _ _)
  have paid := Order.Arithmetic.mul_le_mul_direct incrementBound (range.coefficient_upper inside)
    (Norm.Basic.normSq_nonneg (Polynomials.baseValue point))
    (Order.Basic.lt_min (by decide +kernel)
      (Order.Field.div_pos_direct range.perturbation_positive
        (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct range.coefficient_nonnegative
          (by decide +kernel)))).le
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (paid.trans_eq (Field.mul_comm _ _)).trans_lt allocated

/-- Every point and admitted increment obey one uniform movement ceiling from the literal original seed radicand. -/
theorem seed_movement_le (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval patch.base.site.center -
      (Paths.polynomial (parameter + increment)).eval point) ≤ range.stripMovement := by
  have original : Norm.Basic.normSq ((Paths.polynomial parameter).eval patch.base.site.center -
      (Paths.polynomial parameter).eval point) ≤ range.movement := by
    rewrite [range.movement_eq, Norm.Basic.normSq_eq_canonical]
    exact CheckedPrimitiveNeighborhoods.movement_le_ceiling patch inside
  have shifted := (range.perturbation_lt inside increment admitted).le
  have weighted := Norm.Weighted.normSq_add_le_parameter range.weight range.weight_positive
    ((Paths.polynomial parameter).eval patch.base.site.center - (Paths.polynomial parameter).eval point)
    ((Paths.polynomial parameter).eval point - (Paths.polynomial (parameter + increment)).eval point)
  have identity : ((Paths.polynomial parameter).eval patch.base.site.center -
      (Paths.polynomial parameter).eval point) + ((Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point) =
        (Paths.polynomial parameter).eval patch.base.site.center -
          (Paths.polynomial (parameter + increment)).eval point := by ring1
  rewrite [identity] at weighted
  exact weighted.trans (Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct original
      (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct range.weight_positive
        (by decide +kernel : (0 : Rational) ≤ 1)).le)
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shifted range.reciprocalWeight_positive.le))

/-- Construct one uniform fixed-box budget on the identical original seed Owner, without re-isolation or a new patch. -/
def seedBudget : FixedRootBoxBudget.Budget patch.base.seed.owner :=
  FixedRootBoxBudget.Budget.acquire patch.base.seed.owner range.stripMovement
    range.stripMovement_nonnegative range.stripMovement_lt_contour

/-- The fixed-box budget retains exactly the computed whole-strip movement ceiling. -/
theorem seedBudget_movement : range.seedBudget.movement = range.stripMovement := by rfl

/-- The actual shifted whole-box clearance proves nonzeroness at every retained physical point. -/
theorem strip_nonzero (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    (Paths.polynomial (parameter + increment)).eval point ≠ 0 := by
  intro zero
  have lower := range.shifted_lower inside increment (admitted.trans range.stripBound_le_shiftedBound)
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (Order.Field.div_pos_direct
    (Order.Field.div_pos_direct patch.base.site.denominatorValue_positive
      (by decide +kernel : (0 : Rational) < 4))
    (by decide +kernel : (0 : Rational) < 4)).2 lower

/-- A retained fixed original seed budget constructs a signed reference Owner at the exact shifted point.

The supplied whole factory equation identifies the already cached budget.
Its majorant and clearance are consumed directly, without rebuilding them
inside the point or parameter callback.
-/
def seedOwner (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (budget_eq : budget = range.seedBudget) (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    FixedRootBoxBudget.Owner ((Paths.polynomial (parameter + increment)).eval point) :=
  budget.ownerAt (range.strip_nonzero inside increment admitted) (by
    have movement := range.seed_movement_le inside increment admitted
    rewrite [Norm.Basic.normSq_eq_canonical] at movement
    rewrite [budget_eq, range.seedBudget_movement]
    exact movement)

/-- The uniform reference Owner has exactly the literal original seed box. -/
theorem seedOwner_box (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (budget_eq : budget = range.seedBudget) (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    (range.seedOwner budget budget_eq inside increment admitted).track.initial.box =
      patch.base.seed.owner.track.initial.box := by
  unfold seedOwner
  exact FixedRootBoxBudget.Budget.ownerAt_box _ _ _

/-- The same original strip reference retains the full cached budget clearance at every admitted point. -/
theorem seedOwner_clearance (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (budget_eq : budget = range.seedBudget) (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    (range.seedOwner budget budget_eq inside increment admitted).track.initial.clearance.bound = budget.clearance := by
  unfold seedOwner
  exact FixedRootBoxBudget.Budget.ownerAt_clearance _ _ _

/-- Compare the signed whole-strip reference with an actual retained Point.Step, preserving both complete Owners.

The old Point's certified seed refinement and its actual Step refinement
are consumed directly. Neither the selected root readings nor their stages
are replaced, and no desired operational comparison is an input.
-/
def seedOwner_stepEquivalent (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (budget_eq : budget = range.seedBudget) (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    {source : ContinuedNeighborhood.Point patch point} (step : Step source increment) :
    NamedEquivalent
      (ownerRootName (range.seedOwner budget budget_eq inside increment admitted).parameterNonzero
        (range.seedOwner budget budget_eq inside increment admitted)) step.root.value.name := by
  have refines := step.refines.trans source.refines
  have compared := budget.retainedEquivalent (range.strip_nonzero inside increment admitted)
    (by
      rewrite [budget_eq, range.seedBudget_movement]
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact range.seed_movement_le inside increment admitted) step.owner refines
  have name_eq : ownerRootName step.owner.parameterNonzero step.owner = step.root.value.name := by
    rewrite [step.root_eq]
    rfl
  unfold seedOwner
  exact NamedEquivalent.transport rfl name_eq compared

/-- The identical strip allocation pays every interpolated increment, without a minimum over sampled nodes. -/
theorem interpolated_admitted (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ range.stripBound := by
  have scalar : Norm.Basic.normSq (⟨time, 0⟩ : Canonical) ≤ 1 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact RationalEmbedding.Bounds.unit_parameter inside.1 inside.2
  have multiplied := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalar
    (Norm.Basic.normSq_nonneg increment)
  rewrite [Norm.Basic.normSq_mul]
  exact (multiplied.trans_eq (Field.one_mul _)).trans admitted

/-- Every horizontal section of the actual parameter strip has quantitative clearance on the identical old box. -/
def interpolated_clearance (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    Polynomial.Clearance.Box.Region.RegionClearance
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)) patch.box :=
  range.shiftedClearance ((⟨time, 0⟩ : Canonical) * increment)
    ((range.interpolated_admitted time inside increment admitted).trans range.stripBound_le_shiftedBound)

/-- Every retained section uses the same computed positive polynomial floor, independent of both coordinates. -/
theorem interpolated_clearance_bound (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.stripBound) :
    (range.interpolated_clearance time inside increment admitted).bound =
      (patch.base.site.denominatorValue / 4) / 4 := by
  unfold interpolated_clearance
  exact range.shiftedClearance_bound _ _

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
