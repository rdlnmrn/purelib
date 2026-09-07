import FTA.CCLCanonicalEvent
import FTA.CCLSectorInteriorSelection

/-!
# Rational convergence data for unfinished sector boundaries

An algebraic event cell classifies every relevant Hermitian face as either
canonically zero or canonically strict.  This module transfers that finite
classification to the center of an independently refined winding box.
Canonically zero faces acquire a linear residual bound; canonically strict
faces retain their classified sign.  These are precisely the two numerical
inputs consumed by the residual-tolerant sector sampler.
-/

namespace FTA
namespace CCLSectorBoundaryConvergence

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLCanonicalEvent
open FTA.CCLClearanceExclusion
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLGeometry
open FTA.CCLHermitianBox
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLParserGeometry
open FTA.CCLSectorBoxGrid
open FTA.CCLSectorInteriorCone
open FTA.CCLSectorInteriorSelection
open FTA.CCLSectorTangent
open FTA.CCLTangentStability
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootTrackSeparation
open FTA.GaussianPolynomialBounds

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Faces whose exact algebraic value on the classified event is zero. -/
def canonicalActiveForms
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (forms : List HermitianForm) :
    List HermitianForm :=
  forms.filter fun form => decide (inputEventCanonicalValue cell form = 0)

theorem canonicalActiveForms_value_zero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    {cell : InputEventCell state event} {forms : List HermitianForm}
    {form : HermitianForm} (member : form ∈ canonicalActiveForms cell forms) :
    inputEventCanonicalValue cell form = 0 :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem canonicalActiveForms_source
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    {cell : InputEventCell state event} {forms : List HermitianForm}
    {form : HermitianForm} (member : form ∈ canonicalActiveForms cell forms) :
    form ∈ forms :=
  (List.mem_filter.mp member).1

theorem canonicalValue_ne_zero_of_not_mem_active
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    {cell : InputEventCell state event} {forms : List HermitianForm}
    {form : HermitianForm} (source : form ∈ forms)
    (inactive : form ∉ canonicalActiveForms cell forms) :
    inputEventCanonicalValue cell form ≠ 0 := by
  intro zero
  apply inactive
  exact List.mem_filter.mpr ⟨source, by simp [zero]⟩

/-- The center of the requested-width refinement lies strictly inside the
unrefined requested box. -/
theorem convergentBoxCenter_strictContains
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    CCLSectorBoxGrid.StrictContains next.box
      (convergentBoxCenter squarefree elimination next radius
        radiusPositive) := by
  let inner := refineState squarefree elimination next radius radiusPositive
  have strict : StrictInterior inner.box next.box :=
    refineState_strictInterior squarefree elimination next radius
      radiusPositive
  have center : inner.box.Contains inner.box.center := inner.box.contains_center
  simpa only [CCLSectorBoxGrid.StrictContains, convergentBoxCenter, inner] using
    (show next.box.xLower < inner.box.center.re ∧
        inner.box.center.re < next.box.xUpper ∧
        next.box.yLower < inner.box.center.im ∧
        inner.box.center.im < next.box.yUpper from
      ⟨strict.left.trans_le center.1,
        center.2.1.trans_lt strict.right,
        strict.bottom.trans_le center.2.2.1,
        center.2.2.2.trans_lt strict.top⟩)

/-- Linear coefficient transferring one canonically-zero event face from
the shrinking event point to the independently refined box center. -/
def convergentFormCoefficient
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm) : ℚ :=
  inputEventFormCoefficient cell form + 10 * variationMajorant form box

theorem convergentFormCoefficient_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm) :
    0 < convergentFormCoefficient cell form := by
  unfold convergentFormCoefficient
  exact add_pos_of_nonneg_of_pos (inputEventFormCoefficient_nonneg cell form)
    (mul_pos (by norm_num) (variationMajorant_pos form box))

/-- The Hermitian variation majorant also bounds each gradient coordinate at
every point of the same rational box. -/
theorem abs_gradientX_le_variationMajorant
    (form : HermitianForm) {box : RatBox} {point : QI}
    (inside : box.Contains point) :
    |gradientX form point| ≤ variationMajorant form box := by
  have coordinate := (box.abs_coordinates_le_radius inside).1
  calc
    |gradientX form point| =
        |2 * form.radial * point.re + form.realLinear| := rfl
    _ ≤ |2 * form.radial * point.re| + |form.realLinear| :=
      abs_add_le _ _
    _ = 2 * |form.radial| * |point.re| + |form.realLinear| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * |form.radial| * box.coordinateRadius +
        |form.realLinear| := by
      gcongr
    _ ≤ 2 * |form.radial| * box.coordinateRadius +
        |form.realLinear| + |form.imagLinear| := by
      linarith [abs_nonneg form.imagLinear]
    _ ≤ variationMajorant form box := le_max_right _ _

theorem abs_gradientY_le_variationMajorant
    (form : HermitianForm) {box : RatBox} {point : QI}
    (inside : box.Contains point) :
    |gradientY form point| ≤ variationMajorant form box := by
  have coordinate := (box.abs_coordinates_le_radius inside).2
  calc
    |gradientY form point| =
        |2 * form.radial * point.im + form.imagLinear| := rfl
    _ ≤ |2 * form.radial * point.im| + |form.imagLinear| :=
      abs_add_le _ _
    _ = 2 * |form.radial| * |point.im| + |form.imagLinear| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * |form.radial| * box.coordinateRadius +
        |form.imagLinear| := by
      gcongr
    _ ≤ 2 * |form.radial| * box.coordinateRadius +
        |form.realLinear| + |form.imagLinear| := by
      linarith [abs_nonneg form.realLinear]
    _ ≤ variationMajorant form box := le_max_right _ _

/-- Static common compass-slope floor for an active list of cardinality at
most two.  The fallback branch keeps the definition total; it is unreachable
under the accompanying length certificate. -/
def tangentSlopeBudget (box : RatBox) : List HermitianForm → ℚ
  | [] => 1
  | [form] =>
      (-boundaryDiscriminant form) /
        (8 * variationMajorant form box)
  | [left, right] =>
      let upper := variationMajorant left box + variationMajorant right box
      (boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2) /
        (80 * upper ^ 3)
  | _ :: _ :: _ :: _ => 1

theorem tangentSlopeBudget_pos_of_length_le_two
    (box : RatBox) (forms : List HermitianForm)
    (length : forms.length ≤ 2)
    (discriminantNegative : ∀ form ∈ forms,
      boundaryDiscriminant form < 0)
    (pairGap : ∀ left right, forms = [left, right] →
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    0 < tangentSlopeBudget box forms := by
  cases forms with
  | nil => norm_num [tangentSlopeBudget]
  | cons first tail =>
      cases tail with
      | nil =>
          unfold tangentSlopeBudget
          exact div_pos (neg_pos.mpr (discriminantNegative first (by simp)))
            (mul_pos (by norm_num) (variationMajorant_pos first box))
      | cons second rest =>
          have restNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons third further => simp at length
          subst rest
          unfold tangentSlopeBudget
          exact div_pos (pairGap first second rfl)
            (mul_pos (by norm_num) (pow_pos
              (add_pos (variationMajorant_pos first box)
                (variationMajorant_pos second box)) 3))

/-- Residual control plus the invariant discriminant/angle gaps makes the
thresholded executable compass search succeed, with the static slope floor
above. -/
theorem tangentDirectionAboveCertificate?_isSome_of_residual_lt_budget
    (box : RatBox) (forms : List HermitianForm) (point : QI) (epsilon : ℚ)
    (length : forms.length ≤ 2) (inside : box.Contains point)
    (epsilonPositive : 0 < epsilon)
    (epsilonSmall : epsilon < tangentResidualBudget forms)
    (residual : ∀ form ∈ forms, |form.eval point| < epsilon)
    (discriminantNegative : ∀ form ∈ forms,
      boundaryDiscriminant form < 0)
    (pairGap : ∀ left right, forms = [left, right] →
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (tangentDirectionAboveCertificate? forms point
      (tangentSlopeBudget box forms)).isSome := by
  cases forms with
  | nil =>
      apply tangentDirectionAboveCertificate?_isSome_of_mem
        (direction := ⟨1, 0⟩) (by simp [coordinateDirections])
      simp
  | cons first tail =>
      cases tail with
      | nil =>
          let coefficient := gradientNormResidualCoefficient first
          let invariant := -boundaryDiscriminant first
          let upper := variationMajorant first box
          let lower := tangentSlopeBudget box [first]
          have coefficientPositive : 0 < coefficient := by
            simpa only [coefficient] using
              gradientNormResidualCoefficient_pos first
          have invariantPositive : 0 < invariant := by
            dsimp only [invariant]
            exact neg_pos.mpr (discriminantNegative first (by simp))
          have upperPositive : 0 < upper := by
            simpa only [upper] using variationMajorant_pos first box
          have lowerNonnegative : 0 ≤ lower := by
            exact (tangentSlopeBudget_pos_of_length_le_two box [first]
              (by simp) (by simpa using discriminantNegative)
              (by intro left right impossible; simp at impossible)).le
          have coefficientEpsilonSmall : coefficient * epsilon <
              invariant / 2 := by
            have scaled := mul_lt_mul_of_pos_left epsilonSmall
              coefficientPositive
            apply scaled.trans_le
            have budgetLe : tangentResidualBudget [first] ≤
                invariant / (2 * coefficient) := min_le_right _ _
            calc
              coefficient * tangentResidualBudget [first] ≤
                  coefficient * (invariant / (2 * coefficient)) :=
                mul_le_mul_of_nonneg_left budgetLe coefficientPositive.le
              _ = invariant / 2 := by
                field_simp [coefficientPositive.ne']
          have normLower :=
            neg_boundaryDiscriminant_div_two_lt_gradientNorm first point
              epsilon epsilonPositive (residual first (by simp)) (by
                simpa only [coefficient, invariant] using
                  coefficientEpsilonSmall)
          have normLarge : 2 * lower * upper <
              normSq (gradientVector first point) := by
            have identity : 2 * lower * upper = invariant / 4 := by
              change 2 * (invariant / (8 * upper)) * upper = invariant / 4
              field_simp [upperPositive.ne']
              norm_num
            rw [identity]
            have halfPositive : 0 < invariant / 4 := by positivity
            nlinarith [normLower]
          rcases exists_coordinateDirection_slope_above_of_norm
              (gradientVector first point) lower upper lowerNonnegative
              (abs_gradientX_le_variationMajorant first inside)
              (abs_gradientY_le_variationMajorant first inside) normLarge with
            ⟨direction, directionMember, slope⟩
          apply tangentDirectionAboveCertificate?_isSome_of_mem
            directionMember
          intro form member
          simp only [List.mem_singleton] at member
          subst form
          simpa [directionalSlope, gradientVector, lower] using slope
      | cons second rest =>
          have restNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons third further => simp at length
          subst rest
          let coefficient := gradientGapResidualCoefficient first second
          let invariant := boundaryDiscriminant first *
              boundaryDiscriminant second -
            2 * gradientPairingConstant first second ^ 2
          let upper := variationMajorant first box +
            variationMajorant second box
          let lower := tangentSlopeBudget box [first, second]
          have coefficientPositive : 0 < coefficient := by
            simpa only [coefficient] using
              gradientGapResidualCoefficient_pos first second
          have invariantPositive : 0 < invariant := by
            simpa only [invariant] using pairGap first second rfl
          have upperPositive : 0 < upper := by
            dsimp only [upper]
            exact add_pos (variationMajorant_pos first box)
              (variationMajorant_pos second box)
          have lowerNonnegative : 0 ≤ lower := by
            exact (tangentSlopeBudget_pos_of_length_le_two box
              [first, second] (by simp) (by simpa using discriminantNegative)
              (by
                intro left right pair
                simp only [List.cons.injEq] at pair
                rw [← pair.1, ← pair.2.1]
                exact pairGap first second rfl)).le
          have twiceCoefficientEpsilonSmall :
              2 * coefficient * epsilon < invariant := by
            have twoCoefficientPositive : 0 < 2 * coefficient :=
              mul_pos (by norm_num) coefficientPositive
            have scaled := mul_lt_mul_of_pos_left epsilonSmall
              twoCoefficientPositive
            apply scaled.trans_le
            have budgetLe : tangentResidualBudget [first, second] ≤
                invariant / (2 * coefficient) := min_le_right _ _
            calc
              (2 * coefficient) * tangentResidualBudget [first, second] ≤
                  (2 * coefficient) * (invariant / (2 * coefficient)) :=
                mul_le_mul_of_nonneg_left budgetLe
                  (mul_pos (by norm_num) coefficientPositive).le
              _ = invariant := by
                field_simp [coefficientPositive.ne']
          have epsilonLeOne : epsilon ≤ 1 :=
            (epsilonSmall.trans_le
              (tangentResidualBudget_le_one [first, second])).le
          have gapLower := angleGap_div_two_lt_gradientGap first second point
            epsilon epsilonPositive epsilonLeOne
            (residual first (by simp)) (residual second (by simp)) (by
              simpa only [coefficient, invariant] using
                twiceCoefficientEpsilonSmall)
          have gapLarge : 20 * lower * upper ^ 3 <
              normSq (gradientVector first point) *
                  normSq (gradientVector second point) -
                2 * ((gradientVector first point).re *
                      (gradientVector second point).re +
                    (gradientVector first point).im *
                      (gradientVector second point).im) ^ 2 := by
            have identity : 20 * lower * upper ^ 3 = invariant / 4 := by
              change 20 * (invariant / (80 * upper ^ 3)) * upper ^ 3 =
                invariant / 4
              field_simp [upperPositive.ne']
              norm_num
            rw [identity]
            nlinarith [gapLower, invariantPositive]
          have firstReal : |(gradientVector first point).re| ≤ upper :=
            (abs_gradientX_le_variationMajorant first inside).trans
              (le_add_of_nonneg_right
                (variationMajorant_pos second box).le)
          have firstImag : |(gradientVector first point).im| ≤ upper :=
            (abs_gradientY_le_variationMajorant first inside).trans
              (le_add_of_nonneg_right
                (variationMajorant_pos second box).le)
          have secondReal : |(gradientVector second point).re| ≤ upper :=
            (abs_gradientX_le_variationMajorant second inside).trans (by
              dsimp only [upper]
              linarith [variationMajorant_pos first box])
          have secondImag : |(gradientVector second point).im| ≤ upper :=
            (abs_gradientY_le_variationMajorant second inside).trans (by
              dsimp only [upper]
              linarith [variationMajorant_pos first box])
          rcases exists_coordinateDirection_slopes_above_of_angleGap
              (gradientVector first point) (gradientVector second point)
              lower upper lowerNonnegative upperPositive firstReal firstImag
              secondReal secondImag gapLarge with
            ⟨direction, directionMember, slopes⟩
          apply tangentDirectionAboveCertificate?_isSome_of_mem
            directionMember
          intro form member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · simpa [directionalSlope, gradientVector, lower] using slopes.1
          · simpa [directionalSlope, gradientVector, lower] using slopes.2

/-- Uniform lower bound for every active entry radius supplied by the static
compass-slope floor. -/
def tangentBoundaryRadiusLower
    (box : RatBox) (forms : List HermitianForm) : ℚ :=
  FTA.Maximality.positiveMinimum (forms.map fun form =>
    tangentSlopeBudget box forms / (|form.radial| + 1))

theorem tangentBoundaryRadiusLower_pos
    {box : RatBox} {forms : List HermitianForm}
    (slopePositive : 0 < tangentSlopeBudget box forms) :
    0 < tangentBoundaryRadiusLower box forms := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos slopePositive (by positivity)

theorem tangentBoundaryRadiusLower_le_one
    (box : RatBox) (forms : List HermitianForm) :
    tangentBoundaryRadiusLower box forms ≤ 1 :=
  FTA.Maximality.positiveMinimum_le_one _

theorem tangentBoundaryRadiusLower_le_entryRadius
    {box : RatBox} {forms : List HermitianForm} {point : QI}
    (direction : TangentDirectionAbove forms point
      (tangentSlopeBudget box forms))
    {form : HermitianForm} (member : form ∈ forms) :
    tangentBoundaryRadiusLower box forms ≤
      entryRadius form point direction.vector := by
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (List.mem_map.mpr ⟨form, member, rfl⟩)).trans
  unfold entryRadius
  exact div_le_div_of_nonneg_right
    (direction.slopesAbove form member).le (by positivity)

/-- Static lower bound for the common active-entry/prior-preservation radius
at a rational convergence anchor. -/
def convergentUniformOwnerRadiusLower
    (box : RatBox) (forms priors : List HermitianForm)
    (priorEvaluationLower : ℚ) : ℚ :=
  min 1 (min (tangentBoundaryRadiusLower box forms)
    (priorRadiusLower priors box priorEvaluationLower))

theorem convergentUniformOwnerRadiusLower_pos
    {box : RatBox} {forms priors : List HermitianForm}
    {priorEvaluationLower : ℚ}
    (slopePositive : 0 < tangentSlopeBudget box forms)
    (priorLowerPositive : 0 < priorEvaluationLower) :
    0 < convergentUniformOwnerRadiusLower box forms priors
      priorEvaluationLower := by
  exact lt_min zero_lt_one
    (lt_min (tangentBoundaryRadiusLower_pos slopePositive)
      (priorRadiusLower_pos priors box priorLowerPositive))

theorem convergentUniformOwnerRadiusLower_le_one
    (box : RatBox) (forms priors : List HermitianForm)
    (priorEvaluationLower : ℚ) :
    convergentUniformOwnerRadiusLower box forms priors
      priorEvaluationLower ≤ 1 :=
  min_le_left _ _

theorem convergentUniformOwnerRadiusLower_le_multiOwnerRadius
    {box : RatBox} {forms priors : List HermitianForm} {point : QI}
    {priorEvaluationLower : ℚ}
    (direction : TangentDirectionAbove forms point
      (tangentSlopeBudget box forms))
    (slopeNonnegative : 0 ≤ tangentSlopeBudget box forms)
    (inside : box.Contains point)
    (priorEvaluationLowerLe : ∀ form ∈ priors,
      priorEvaluationLower ≤ |form.eval point|) :
    convergentUniformOwnerRadiusLower box forms priors
        priorEvaluationLower ≤
      multiOwnerRadius (direction.toTangentDirection slopeNonnegative)
        priors := by
  let ordinary := direction.toTangentDirection slopeNonnegative
  have boundaryLe : tangentBoundaryRadiusLower box forms ≤
      boundaryRadius forms point ordinary.vector := by
    apply FTA.Maximality.le_positiveMinimum
      (tangentBoundaryRadiusLower_le_one box forms)
    intro radius member
    rw [List.mem_map] at member
    rcases member with ⟨form, formMember, rfl⟩
    simpa only [ordinary, TangentDirectionAbove.toTangentDirection] using
      tangentBoundaryRadiusLower_le_entryRadius direction formMember
  have priorLe : priorRadiusLower priors box priorEvaluationLower ≤
      strictRadius priors point ordinary.vector :=
    priorRadiusLower_le_strictRadius inside ordinary.normSq_le_one
      priorEvaluationLowerLe
  unfold convergentUniformOwnerRadiusLower multiOwnerRadius
  apply le_min (min_le_left _ _)
  apply le_min
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans boundaryLe)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans priorLe)

/-- Static cap-independent lower bound for the residual entry budget once
the active slope floor and strict-prior evaluation floor are known. -/
def convergentUniformBoundaryBudgetLower
    (box : RatBox) (forms priors : List HermitianForm)
    (priorEvaluationLower : ℚ) : ℚ :=
  convergentUniformOwnerRadiusLower box forms priors priorEvaluationLower / 3 *
    tangentBoundaryRadiusLower box forms

theorem convergentUniformBoundaryBudgetLower_pos
    {box : RatBox} {forms priors : List HermitianForm}
    {priorEvaluationLower : ℚ}
    (slopePositive : 0 < tangentSlopeBudget box forms)
    (priorLowerPositive : 0 < priorEvaluationLower) :
    0 < convergentUniformBoundaryBudgetLower box forms priors
      priorEvaluationLower := by
  exact mul_pos
    (div_pos
      (convergentUniformOwnerRadiusLower_pos slopePositive priorLowerPositive)
      (by norm_num))
    (tangentBoundaryRadiusLower_pos slopePositive)

theorem convergentUniformBoundaryBudgetLower_le
    {box : RatBox} {forms priors : List HermitianForm} {point : QI}
    {priorEvaluationLower : ℚ}
    (direction : TangentDirectionAbove forms point
      (tangentSlopeBudget box forms))
    (slopePositive : 0 < tangentSlopeBudget box forms)
    (inside : box.Contains point)
    (priorEvaluationLowerPositive : 0 < priorEvaluationLower)
    (priorEvaluationLowerLe : ∀ form ∈ priors,
      priorEvaluationLower ≤ |form.eval point|) :
    convergentUniformBoundaryBudgetLower box forms priors
        priorEvaluationLower ≤
      approximateBoundaryBudget
        (direction.toTangentDirection slopePositive.le) priors := by
  let ordinary := direction.toTangentDirection slopePositive.le
  have priorNonzero : ∀ form ∈ priors, form.eval point ≠ 0 := by
    intro form member zero
    have lower := priorEvaluationLowerLe form member
    rw [zero, abs_zero] at lower
    linarith
  have ownerPositive : 0 < convergentUniformOwnerRadiusLower box forms priors
      priorEvaluationLower :=
    convergentUniformOwnerRadiusLower_pos slopePositive
      priorEvaluationLowerPositive
  have ownerLe := convergentUniformOwnerRadiusLower_le_multiOwnerRadius
    direction slopePositive.le inside priorEvaluationLowerLe
  have epsilonLowerLe :
      convergentUniformOwnerRadiusLower box forms priors
          priorEvaluationLower / 3 ≤
        multiOwnerEpsilon ordinary priors :=
    (radiusLower_div_three_lt_multiOwnerEpsilon ordinary priors ownerPositive
      ownerLe priorNonzero).le
  have epsilonLowerAtMostOne :
      convergentUniformOwnerRadiusLower box forms priors
          priorEvaluationLower / 3 ≤ 1 := by
    have ownerLeOne := convergentUniformOwnerRadiusLower_le_one box forms
      priors priorEvaluationLower
    nlinarith [ownerPositive]
  unfold convergentUniformBoundaryBudgetLower
  exact mul_le_approximateBoundaryBudget_of_lower_bounds ordinary priors
    priorNonzero epsilonLowerLe epsilonLowerAtMostOne
    (tangentBoundaryRadiusLower_pos slopePositive).le
    (tangentBoundaryRadiusLower_le_one box forms)
    (fun form member => by
      simpa only [ordinary, TangentDirectionAbove.toTangentDirection] using
        tangentBoundaryRadiusLower_le_entryRadius direction member)

/-- Canonical equality gives a linear residual bound at the independent box
center. -/
theorem convergentBoxCenter_abs_eval_le_of_canonicalZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (form : HermitianForm)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (canonicalZero : inputEventCanonicalValue cell form = 0) :
    |form.eval (convergentBoxCenter squarefree elimination next radius
      radiusPositive)| ≤ convergentFormCoefficient cell form * radius := by
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  have divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial := by
    apply ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      cell.branch.relations cell.parent
        (cell.branch.computeEventSigns cell.parent) member
    simpa only [inputEventCanonicalValue] using canonicalZero
  have eventResidual : |form.eval eventPoint| ≤
      inputEventFormCoefficient cell form * radius := by
    simpa only [eventPoint] using shrinkingInputEventForm_le_of_dvd cell
      squarefree radius radiusPositive form divides
  have baseInside : output.state.box.Contains base := by
    apply nextRefines.contains
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact convergentBoxCenter_inside_inner squarefree elimination next radius
      radiusPositive
  have eventInside : output.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point cell squarefree elimination
        radius radiusPositive)
  have variation := abs_eval_sub_eval_le form baseInside eventInside
  have distance := convergentBoxCenter_inputEvent_distance cell squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive
  have difference : |form.eval base - form.eval eventPoint| ≤
      10 * variationMajorant form output.state.box * radius := by
    apply variation.trans
    exact (mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form output.state.box).le).trans_eq (by ring)
  have triangle := abs_add_le
    (form.eval base - form.eval eventPoint) (form.eval eventPoint)
  have identity : form.eval base - form.eval eventPoint +
      form.eval eventPoint = form.eval base := by ring
  rw [identity] at triangle
  calc
    |form.eval base| ≤
        |form.eval base - form.eval eventPoint| + |form.eval eventPoint| :=
      triangle
    _ ≤ 10 * variationMajorant form output.state.box * radius +
        inputEventFormCoefficient cell form * radius :=
      add_le_add difference eventResidual
    _ = convergentFormCoefficient cell form * radius := by
      unfold convergentFormCoefficient
      ring

/-- A positive radius on which every canonically strict member of a supplied
finite face list keeps its event-classified sign at the independent center. -/
def convergentStrictRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (forms : List HermitianForm) : ℚ :=
  FTA.Maximality.positiveMinimum (forms.map fun form =>
    inputEventStrictFormMargin cell /
      (20 * variationMajorant form box))

theorem convergentStrictRadius_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (forms : List HermitianForm) :
    0 < convergentStrictRadius cell forms := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  rw [List.mem_map] at member
  rcases member with ⟨form, _source, rfl⟩
  exact div_pos (inputEventStrictFormMargin_pos cell)
    (mul_pos (by norm_num) (variationMajorant_pos form box))

theorem convergentStrictRadius_le_form
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {forms : List HermitianForm}
    {form : HermitianForm} (member : form ∈ forms) :
    convergentStrictRadius cell forms ≤
      inputEventStrictFormMargin cell /
        (20 * variationMajorant form box) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, member, rfl⟩

/-- A canonically nonzero face has the same strict sign at a sufficiently
fine independent box center. -/
theorem canonicalValue_mul_convergentBoxCenter_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (form : HermitianForm) (source : form ∈ forms)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (canonicalNonzero : inputEventCanonicalValue cell form ≠ 0) :
    0 < inputEventCanonicalValue cell form *
      form.eval (convergentBoxCenter squarefree elimination next radius
        radiusPositive) := by
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  have radiusForm : radius < inputEventStrictFormMargin cell /
      (20 * variationMajorant form output.state.box) :=
    radiusSmall.trans_le (convergentStrictRadius_le_form cell source)
  have denominatorPositive : 0 <
      20 * variationMajorant form output.state.box :=
    mul_pos (by norm_num) (variationMajorant_pos form output.state.box)
  have variationSmall :
      10 * variationMajorant form output.state.box * radius <
        inputEventStrictFormMargin cell := by
    have scaled := (lt_div_iff₀ denominatorPositive).mp radiusForm
    nlinarith [radiusPositive]
  have baseInside : output.state.box.Contains base := by
    apply nextRefines.contains
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact convergentBoxCenter_inside_inner squarefree elimination next radius
      radiusPositive
  have eventInside : output.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point cell squarefree elimination
        radius radiusPositive)
  have variation := abs_eval_sub_eval_le form eventInside baseInside
  have distance := convergentBoxCenter_inputEvent_distance cell squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive
  have difference : |form.eval eventPoint - form.eval base| ≤
      10 * variationMajorant form output.state.box * radius := by
    apply variation.trans
    have reversed : |eventPoint.re - base.re| + |eventPoint.im - base.im| ≤
        10 * radius := by
      simpa only [base, eventPoint, abs_sub_comm] using distance
    exact (mul_le_mul_of_nonneg_left reversed
      (variationMajorant_pos form output.state.box).le).trans_eq (by ring)
  have eventMargin : inputEventStrictFormMargin cell ≤
      |form.eval eventPoint| := by
    simpa only [eventPoint] using
      inputEventStrictFormMargin_le_shrinkingPoint cell squarefree radius
        radiusPositive form member canonicalNonzero
  have eventBase : 0 < form.eval eventPoint * form.eval base := by
    apply mul_pos_of_abs_sub_lt_abs_left
    exact difference.trans_lt (variationSmall.trans_le eventMargin)
  have canonicalEvent : 0 < inputEventCanonicalValue cell form *
      form.eval eventPoint := by
    simpa only [eventPoint] using
      inputEventCanonicalValue_mul_shrinkingPoint_pos cell squarefree radius
        radiusPositive form member canonicalNonzero
  exact FTA.CCLPositiveEventGrid.mul_pos_trans canonicalEvent eventBase

/-- A canonically strict source face retains not only its sign but half of
the event-cell's common absolute-value margin at the independent box center. -/
theorem inputEventStrictFormMargin_div_two_lt_abs_convergentBoxCenter
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (form : HermitianForm) (source : form ∈ forms)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (canonicalNonzero : inputEventCanonicalValue cell form ≠ 0) :
    inputEventStrictFormMargin cell / 2 <
      |form.eval (convergentBoxCenter squarefree elimination next radius
        radiusPositive)| := by
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  have radiusForm : radius < inputEventStrictFormMargin cell /
      (20 * variationMajorant form output.state.box) :=
    radiusSmall.trans_le (convergentStrictRadius_le_form cell source)
  have denominatorPositive : 0 <
      20 * variationMajorant form output.state.box :=
    mul_pos (by norm_num) (variationMajorant_pos form output.state.box)
  have variationSmall :
      10 * variationMajorant form output.state.box * radius <
        inputEventStrictFormMargin cell / 2 := by
    have scaled := (lt_div_iff₀ denominatorPositive).mp radiusForm
    nlinarith [radiusPositive]
  have baseInside : output.state.box.Contains base := by
    apply nextRefines.contains
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact convergentBoxCenter_inside_inner squarefree elimination next radius
      radiusPositive
  have eventInside : output.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point cell squarefree elimination
        radius radiusPositive)
  have variation := abs_eval_sub_eval_le form eventInside baseInside
  have distance := convergentBoxCenter_inputEvent_distance cell squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive
  have difference : |form.eval eventPoint - form.eval base| ≤
      10 * variationMajorant form output.state.box * radius := by
    apply variation.trans
    have reversed : |eventPoint.re - base.re| +
        |eventPoint.im - base.im| ≤ 10 * radius := by
      simpa only [base, eventPoint, abs_sub_comm] using distance
    exact (mul_le_mul_of_nonneg_left reversed
      (variationMajorant_pos form output.state.box).le).trans_eq (by ring)
  have eventMargin : inputEventStrictFormMargin cell ≤
      |form.eval eventPoint| := by
    simpa only [eventPoint] using
      inputEventStrictFormMargin_le_shrinkingPoint cell squarefree radius
        radiusPositive form member canonicalNonzero
  have triangle : |form.eval eventPoint| ≤
      |form.eval eventPoint - form.eval base| + |form.eval base| := by
    have bound := abs_add_le
      (form.eval eventPoint - form.eval base) (form.eval base)
    simpa only [sub_add_cancel] using bound
  linarith

/-- Accuracy cap forcing the independently refined winding-box center below
one sixteenth of the original box's boundary clearance. -/
def convergentClearanceRadius
    (p : GaussianPolynomial) {ambient : RatBox}
    (next : WindingOneState p ambient) : ℚ :=
  min 1 (next.clearance.bound /
    (32 * denseLipschitzBound p next.box))

theorem convergentClearanceRadius_pos
    (p : GaussianPolynomial) {ambient : RatBox}
    (next : WindingOneState p ambient) :
    0 < convergentClearanceRadius p next := by
  exact lt_min zero_lt_one
    (div_pos next.clearance.positive
      (mul_pos (by norm_num) (denseLipschitzBound_pos p next.box)))

theorem convergentBoxCenter_residual_le_clearance
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentClearanceRadius p next) :
    normSq (p.eval (convergentBoxCenter squarefree elimination next radius
      radiusPositive)) ≤ next.clearance.bound / 16 := by
  let inner := refineState squarefree elimination next radius radiusPositive
  let L := denseLipschitzBound p next.box
  have radiusLeOne : radius ≤ 1 :=
    radiusSmall.le.trans (min_le_left _ _)
  have radiusLeRatio : radius ≤ next.clearance.bound / (32 * L) :=
    radiusSmall.le.trans (min_le_right _ _)
  have radiusSquareLe : radius ^ 2 ≤ radius := by nlinarith
  have lipschitzPositive : 0 < L := by
    simpa only [L] using denseLipschitzBound_pos p next.box
  have scaled : L * radius ≤ next.clearance.bound / 32 := by
    have multiplied := mul_le_mul_of_nonneg_left radiusLeRatio
      lipschitzPositive.le
    calc
      L * radius ≤ L * (next.clearance.bound / (32 * L)) := multiplied
      _ = next.clearance.bound / 32 := by
        field_simp [lipschitzPositive.ne']
  have centerResidual := center_residual_le_of_boxWinding_ne_zero p
    (refineState_refines squarefree elimination next radius radiusPositive)
    inner.proper inner.winding_ne_zero
  have diagonal := refineState_accurate squarefree elimination next radius
    radiusPositive
  calc
    normSq (p.eval (convergentBoxCenter squarefree elimination next radius
        radiusPositive)) ≤ centerResidualBound p next.box inner.box := by
      simpa only [convergentBoxCenter, inner] using centerResidual
    _ = L * inner.box.diagonalSq := rfl
    _ ≤ L * radius ^ 2 :=
      mul_le_mul_of_nonneg_left diagonal lipschitzPositive.le
    _ ≤ L * radius :=
      mul_le_mul_of_nonneg_left radiusSquareLe lipschitzPositive.le
    _ ≤ next.clearance.bound / 32 := scaled
    _ ≤ next.clearance.bound / 16 := by
      nlinarith [next.clearance.positive]

theorem boundaryInteriorRadius_le_convergentBoxForm
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentClearanceRadius p next)
    {form : HermitianForm} (member : form ∈ boxForms next.box) :
    boundaryInteriorRadius p next.box next.clearance ≤
      |form.eval (convergentBoxCenter squarefree elimination next radius
        radiusPositive)| := by
  let point := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let interior := boundaryInteriorRadius p next.box next.clearance
  have interiorPositive : 0 < interior :=
    boundaryInteriorRadius_pos p next.box next.clearance
  have deep := deepInside_of_small_residual next.clearance
    (convergentBoxCenter_strictContains squarefree elimination next radius
      radiusPositive)
    (convergentBoxCenter_residual_le_clearance squarefree elimination next
      radius radiusPositive radiusSmall)
  change next.box.xLower + 4 * interior < point.re ∧
    point.re < next.box.xUpper - 4 * interior ∧
    next.box.yLower + 4 * interior < point.im ∧
    point.im < next.box.yUpper - 4 * interior at deep
  rcases deep with ⟨left, right, bottom, top⟩
  simp only [boxForms, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp only [eval_boxXLowerForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxXUpperForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxYLowerForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxYUpperForm]
    rw [abs_of_pos (by linarith)]
    linarith

def convergentPriorEvaluationLower
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {ambient : RatBox}
    (next : WindingOneState p ambient) : ℚ :=
  min (inputEventStrictFormMargin cell / 2)
    (boundaryInteriorRadius p next.box next.clearance)

theorem convergentPriorEvaluationLower_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {ambient : RatBox}
    (next : WindingOneState p ambient) :
    0 < convergentPriorEvaluationLower cell next := by
  exact lt_min (div_pos (inputEventStrictFormMargin_pos cell) (by norm_num))
    (boundaryInteriorRadius_pos p next.box next.clearance)

/-- One positive coefficient strictly dominates every individual transferred
zero-face coefficient in a finite list. -/
def convergentCoefficientSum
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (forms : List HermitianForm) : ℚ :=
  1 + (forms.map fun form => convergentFormCoefficient cell form).sum

theorem convergentCoefficientSum_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (forms : List HermitianForm) :
    0 < convergentCoefficientSum cell forms := by
  have sumNonnegative : 0 ≤
      (forms.map fun form => convergentFormCoefficient cell form).sum := by
    apply List.sum_nonneg
    intro coefficient member
    rw [List.mem_map] at member
    rcases member with ⟨form, _source, rfl⟩
    exact (convergentFormCoefficient_pos cell form).le
  unfold convergentCoefficientSum
  linarith

/-- A single static localization radius below both strict-sign stability and
the explicit residual tangent threshold. -/
def convergentTangentRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms :
      List HermitianForm) : ℚ :=
  min (convergentStrictRadius cell sourceForms)
      (tangentResidualBudget activeForms /
        convergentCoefficientSum cell sourceForms) / 2

theorem convergentTangentRadius_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms :
      List HermitianForm)
    (budgetPositive : 0 < tangentResidualBudget activeForms) :
    0 < convergentTangentRadius cell sourceForms activeForms := by
  unfold convergentTangentRadius
  have coefficientPositive := convergentCoefficientSum_pos cell sourceForms
  have capPositive : 0 < min (convergentStrictRadius cell sourceForms)
      (tangentResidualBudget activeForms /
        convergentCoefficientSum cell sourceForms) :=
    lt_min (convergentStrictRadius_pos cell sourceForms)
      (div_pos budgetPositive coefficientPositive)
  linarith

theorem convergentTangentRadius_lt_strictRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms :
      List HermitianForm)
    (budgetPositive : 0 < tangentResidualBudget activeForms) :
    convergentTangentRadius cell sourceForms activeForms <
      convergentStrictRadius cell sourceForms := by
  have radiusPositive := convergentTangentRadius_pos cell sourceForms
    activeForms budgetPositive
  unfold convergentTangentRadius at radiusPositive ⊢
  have capLe := min_le_left (convergentStrictRadius cell sourceForms)
    (tangentResidualBudget activeForms /
      convergentCoefficientSum cell sourceForms)
  nlinarith

theorem convergentCoefficientSum_mul_tangentRadius_lt_budget
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms :
      List HermitianForm)
    (budgetPositive : 0 < tangentResidualBudget activeForms) :
    convergentCoefficientSum cell sourceForms *
        convergentTangentRadius cell sourceForms activeForms <
      tangentResidualBudget activeForms := by
  have radiusPositive := convergentTangentRadius_pos cell sourceForms
    activeForms budgetPositive
  have coefficientPositive := convergentCoefficientSum_pos cell sourceForms
  have capLe := min_le_right (convergentStrictRadius cell sourceForms)
    (tangentResidualBudget activeForms /
      convergentCoefficientSum cell sourceForms)
  have radiusLt : convergentTangentRadius cell sourceForms activeForms <
      tangentResidualBudget activeForms /
        convergentCoefficientSum cell sourceForms := by
    unfold convergentTangentRadius at radiusPositive ⊢
    nlinarith
  calc
    convergentCoefficientSum cell sourceForms *
        convergentTangentRadius cell sourceForms activeForms =
      convergentTangentRadius cell sourceForms activeForms *
        convergentCoefficientSum cell sourceForms := by ring
    _ < tangentResidualBudget activeForms :=
      (lt_div_iff₀ coefficientPositive).mp radiusLt

/-- One static localization radius simultaneously controlling tangent-search
residuals, strict inactive faces, later-box clearance, and the final
approximate-boundary entry budget. -/
def convergentSampleRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms priors :
      List HermitianForm) {ambient : RatBox}
    (next : WindingOneState p ambient) : ℚ :=
  min (convergentTangentRadius cell sourceForms activeForms)
      (min (convergentClearanceRadius p next)
        (convergentUniformBoundaryBudgetLower next.box activeForms priors
            (convergentPriorEvaluationLower cell next) /
          convergentCoefficientSum cell sourceForms)) / 2

theorem convergentSampleRadius_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms priors :
      List HermitianForm) {ambient : RatBox}
    (next : WindingOneState p ambient)
    (tangentResidualPositive : 0 < tangentResidualBudget activeForms)
    (slopePositive : 0 < tangentSlopeBudget next.box activeForms) :
    0 < convergentSampleRadius cell sourceForms activeForms priors next := by
  have tangentPositive := convergentTangentRadius_pos cell sourceForms
    activeForms tangentResidualPositive
  have clearancePositive := convergentClearanceRadius_pos p next
  have boundaryPositive := convergentUniformBoundaryBudgetLower_pos
    (priors := priors) slopePositive
      (convergentPriorEvaluationLower_pos cell next)
  have coefficientPositive := convergentCoefficientSum_pos cell sourceForms
  unfold convergentSampleRadius
  have capPositive : 0 < min
      (convergentTangentRadius cell sourceForms activeForms)
      (min (convergentClearanceRadius p next)
        (convergentUniformBoundaryBudgetLower next.box activeForms priors
            (convergentPriorEvaluationLower cell next) /
          convergentCoefficientSum cell sourceForms)) :=
    lt_min tangentPositive
      (lt_min clearancePositive
        (div_pos boundaryPositive coefficientPositive))
  linarith

theorem convergentSampleRadius_lt_tangentRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms priors :
      List HermitianForm) {ambient : RatBox}
    (next : WindingOneState p ambient)
    (tangentResidualPositive : 0 < tangentResidualBudget activeForms)
    (slopePositive : 0 < tangentSlopeBudget next.box activeForms) :
    convergentSampleRadius cell sourceForms activeForms priors next <
      convergentTangentRadius cell sourceForms activeForms := by
  have radiusPositive := convergentSampleRadius_pos cell sourceForms
    activeForms priors next tangentResidualPositive slopePositive
  have capLe := min_le_left
    (convergentTangentRadius cell sourceForms activeForms)
    (min (convergentClearanceRadius p next)
      (convergentUniformBoundaryBudgetLower next.box activeForms priors
          (convergentPriorEvaluationLower cell next) /
        convergentCoefficientSum cell sourceForms))
  unfold convergentSampleRadius at radiusPositive ⊢
  nlinarith

theorem convergentSampleRadius_lt_clearanceRadius
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms priors :
      List HermitianForm) {ambient : RatBox}
    (next : WindingOneState p ambient)
    (tangentResidualPositive : 0 < tangentResidualBudget activeForms)
    (slopePositive : 0 < tangentSlopeBudget next.box activeForms) :
    convergentSampleRadius cell sourceForms activeForms priors next <
      convergentClearanceRadius p next := by
  have radiusPositive := convergentSampleRadius_pos cell sourceForms
    activeForms priors next tangentResidualPositive slopePositive
  have capLe := (min_le_right
    (convergentTangentRadius cell sourceForms activeForms)
    (min (convergentClearanceRadius p next)
      (convergentUniformBoundaryBudgetLower next.box activeForms priors
          (convergentPriorEvaluationLower cell next) /
        convergentCoefficientSum cell sourceForms))).trans
    (min_le_left _ _)
  unfold convergentSampleRadius at radiusPositive ⊢
  nlinarith

theorem convergentCoefficientSum_mul_sampleRadius_lt_uniformBudget
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (sourceForms activeForms priors :
      List HermitianForm) {ambient : RatBox}
    (next : WindingOneState p ambient)
    (tangentResidualPositive : 0 < tangentResidualBudget activeForms)
    (slopePositive : 0 < tangentSlopeBudget next.box activeForms) :
    convergentCoefficientSum cell sourceForms *
        convergentSampleRadius cell sourceForms activeForms priors next <
      convergentUniformBoundaryBudgetLower next.box activeForms priors
        (convergentPriorEvaluationLower cell next) := by
  let coefficient := convergentCoefficientSum cell sourceForms
  let lower := convergentUniformBoundaryBudgetLower next.box activeForms priors
    (convergentPriorEvaluationLower cell next)
  let radius := convergentSampleRadius cell sourceForms activeForms priors next
  have radiusPositive : 0 < radius := by
    simpa only [radius] using convergentSampleRadius_pos cell sourceForms
      activeForms priors next tangentResidualPositive slopePositive
  have coefficientPositive : 0 < coefficient := by
    simpa only [coefficient] using convergentCoefficientSum_pos cell sourceForms
  have ratioLe : 2 * radius ≤ lower / coefficient := by
    have capLe := (min_le_right
      (convergentTangentRadius cell sourceForms activeForms)
      (min (convergentClearanceRadius p next) (lower / coefficient))).trans
      (min_le_right _ _)
    calc
      2 * radius = min
          (convergentTangentRadius cell sourceForms activeForms)
          (min (convergentClearanceRadius p next) (lower / coefficient)) := by
        dsimp only [radius, convergentSampleRadius, lower, coefficient]
        ring
      _ ≤ lower / coefficient := capLe
  have radiusLtRatio : radius < lower / coefficient := by
    have ratioPositive : 0 < lower / coefficient := div_pos
      (by
        simpa only [lower] using convergentUniformBoundaryBudgetLower_pos
          slopePositive (convergentPriorEvaluationLower_pos cell next))
      coefficientPositive
    nlinarith
  change coefficient * radius < lower
  have product := (lt_div_iff₀ coefficientPositive).mp radiusLtRatio
  simpa only [_root_.mul_comm] using product

/-- The same strict-sign transfer holds for any rational point in the common
requested-width refinement.  This is the form used with a persistent active
sample when proving the closed algebraic phase predicate. -/
theorem canonicalValue_mul_innerPoint_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (point : QI)
    (pointInside : (refineState squarefree elimination next radius
      radiusPositive).box.Contains point)
    (form : HermitianForm) (source : form ∈ forms)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (canonicalNonzero : inputEventCanonicalValue cell form ≠ 0) :
    0 < inputEventCanonicalValue cell form * form.eval point := by
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  let eventState := shrinkingInputEventState cell squarefree elimination radius
    radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have radiusForm : radius < inputEventStrictFormMargin cell /
      (20 * variationMajorant form output.state.box) :=
    radiusSmall.trans_le (convergentStrictRadius_le_form cell source)
  have denominatorPositive : 0 <
      20 * variationMajorant form output.state.box :=
    mul_pos (by norm_num) (variationMajorant_pos form output.state.box)
  have variationSmall :
      10 * variationMajorant form output.state.box * radius <
        inputEventStrictFormMargin cell := by
    have scaled := (lt_div_iff₀ denominatorPositive).mp radiusForm
    nlinarith [radiusPositive]
  have eventPointInside : eventState.box.Contains eventPoint := by
    simpa only [eventState, eventPoint] using
      shrinkingInputEventState_contains_point cell squarefree elimination
        radius radiusPositive
  have notSeparated : ¬eventState.box.Separated inner.box := by
    simpa only [eventState, inner] using shrinkingInputEventState_not_separated
      cell squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive
  have distance : |eventPoint.re - point.re| +
      |eventPoint.im - point.im| ≤ 10 * radius := by
    have bound := coordinateDistanceSum_le eventPointInside pointInside
      notSeparated
      (shrinkingInputEventState_widthX_le cell squarefree elimination radius
        radiusPositive)
      (shrinkingInputEventState_widthY_le cell squarefree elimination radius
        radiusPositive)
      (refineState_widthX_le_request squarefree elimination next radius
        radiusPositive)
      (refineState_widthY_le_request squarefree elimination next radius
        radiusPositive)
    calc
      |eventPoint.re - point.re| + |eventPoint.im - point.im| ≤
          2 * (4 * radius + radius) := by
        simpa only [eventState, inner] using bound
      _ = 10 * radius := by ring
  have eventInside : output.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
    exact strict.refines.contains eventPointInside
  have pointInsideOutput : output.state.box.Contains point := by
    apply nextRefines.contains
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact pointInside
  have variation := abs_eval_sub_eval_le form eventInside pointInsideOutput
  have difference : |form.eval eventPoint - form.eval point| ≤
      10 * variationMajorant form output.state.box * radius := by
    apply variation.trans
    exact (mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form output.state.box).le).trans_eq (by ring)
  have eventMargin : inputEventStrictFormMargin cell ≤
      |form.eval eventPoint| := by
    simpa only [eventPoint] using
      inputEventStrictFormMargin_le_shrinkingPoint cell squarefree radius
        radiusPositive form member canonicalNonzero
  have eventPointSameSign : 0 < form.eval eventPoint * form.eval point := by
    apply mul_pos_of_abs_sub_lt_abs_left
    exact difference.trans_lt (variationSmall.trans_le eventMargin)
  have canonicalEvent : 0 < inputEventCanonicalValue cell form *
      form.eval eventPoint := by
    simpa only [eventPoint] using
      inputEventCanonicalValue_mul_shrinkingPoint_pos cell squarefree radius
        radiusPositive form member canonicalNonzero
  exact FTA.CCLPositiveEventGrid.mul_pos_trans canonicalEvent
    eventPointSameSign

theorem convergentFormCoefficient_lt_sum
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {forms : List HermitianForm}
    {form : HermitianForm} (member : form ∈ forms) :
    convergentFormCoefficient cell form <
      convergentCoefficientSum cell forms := by
  have coefficientLe : convergentFormCoefficient cell form ≤
      (forms.map fun item => convergentFormCoefficient cell item).sum := by
    apply List.single_le_sum
    · intro coefficient coefficientMember
      rw [List.mem_map] at coefficientMember
      rcases coefficientMember with ⟨item, _source, rfl⟩
      exact (convergentFormCoefficient_pos cell item).le
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold convergentCoefficientSum
  linarith

theorem convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (form : HermitianForm) (source : form ∈ forms)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (canonicalZero : inputEventCanonicalValue cell form = 0) :
    |form.eval (convergentBoxCenter squarefree elimination next radius
      radiusPositive)| < convergentCoefficientSum cell forms * radius := by
  have individual := convergentBoxCenter_abs_eval_le_of_canonicalZero cell
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
      form member canonicalZero
  have coefficient := convergentFormCoefficient_lt_sum cell source
  exact individual.trans_lt (mul_lt_mul_of_pos_right coefficient radiusPositive)

/-! ## Event-oriented block faces -/

/-- One inward face together with the unnegated comparison form actually
listed in the event condition table. -/
structure EventOrientedFace where
  source : HermitianForm
  increasing : Bool
deriving DecidableEq

def EventOrientedFace.form (face : EventOrientedFace) : HermitianForm :=
  if face.increasing then face.source else face.source.neg

def EventOrientedFace.canonicalValue
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (face : EventOrientedFace) : ℚ :=
  if face.increasing then inputEventCanonicalValue cell face.source
  else -inputEventCanonicalValue cell face.source

@[simp] theorem EventOrientedFace.eval_form (face : EventOrientedFace)
    (point : QI) :
    face.form.eval point =
      if face.increasing then face.source.eval point
      else -face.source.eval point := by
  cases face with
  | mk source increasing =>
      cases increasing <;> simp [EventOrientedFace.form]

def eventRealFace (increasing : Bool) (matrix : Mat2 QI)
    (threshold : ℚ) : EventOrientedFace :=
  ⟨realComparisonForm matrix threshold, increasing⟩

def eventImagFace (increasing : Bool) (matrix : Mat2 QI)
    (threshold : ℚ) : EventOrientedFace :=
  ⟨imagComparisonForm matrix threshold, increasing⟩

def eventNormFace (increasing : Bool) (matrix : Mat2 QI)
    (radiusSq : ℚ) : EventOrientedFace :=
  ⟨normComparisonForm matrix radiusSq, increasing⟩

def sectorEventFaces : Sector → Mat2 QI → List EventOrientedFace
  | .east, matrix =>
      [eventRealFace true matrix (1 / 2),
        eventImagFace true matrix (-1 / 2),
        eventImagFace false matrix (1 / 2)]
  | .northEast, matrix =>
      [eventRealFace true matrix (1 / 2),
        eventImagFace true matrix (1 / 2)]
  | .north, matrix =>
      [eventImagFace true matrix (1 / 2),
        eventRealFace true matrix (-1 / 2),
        eventRealFace false matrix (1 / 2)]
  | .northWest, matrix =>
      [eventRealFace false matrix (-1 / 2),
        eventImagFace true matrix (1 / 2)]
  | .west, matrix =>
      [eventRealFace false matrix (-1 / 2),
        eventImagFace true matrix (-1 / 2),
        eventImagFace false matrix (1 / 2)]
  | .southWest, matrix =>
      [eventRealFace false matrix (-1 / 2),
        eventImagFace false matrix (-1 / 2)]
  | .south, matrix =>
      [eventImagFace false matrix (-1 / 2),
        eventRealFace true matrix (-1 / 2),
        eventRealFace false matrix (1 / 2)]
  | .southEast, matrix =>
      [eventRealFace true matrix (1 / 2),
        eventImagFace false matrix (-1 / 2)]

/-- The two angular faces of a two-bit sector prefix.  These are precisely
the common walls needed by its pair of remaining full sector rows. -/
def sectorTwoEventFaces : Bool → Bool → Mat2 QI → List EventOrientedFace
  | false, false, matrix =>
      [eventRealFace true matrix (1 / 2),
        eventImagFace true matrix (-1 / 2)]
  | false, true, matrix =>
      [eventRealFace false matrix (1 / 2),
        eventImagFace true matrix (1 / 2)]
  | true, false, matrix =>
      [eventRealFace false matrix (-1 / 2),
        eventImagFace false matrix (1 / 2)]
  | true, true, matrix =>
      [eventRealFace true matrix (-1 / 2),
        eventImagFace false matrix (-1 / 2)]

def radialEventFaces
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    List EventOrientedFace :=
  match kind with
  | .initialHigh | .loop =>
      [eventNormFace true matrix ((2 : ℚ) ^ exponent),
        eventNormFace false matrix ((2 : ℚ) ^ (exponent + 1))]
  | .initialLow =>
      [eventNormFace true matrix (1 / (2 : ℚ) ^ exponent),
        eventNormFace false matrix (2 / (2 : ℚ) ^ exponent)]

def blockEventFaces
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : List EventOrientedFace :=
  radialEventFaces kind exponent matrix ++
    sectorEventFaces sector (normalizedMatrix kind exponent matrix)

def blockSectorTwoEventFaces
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) : List EventOrientedFace :=
  radialEventFaces kind exponent matrix ++
    sectorTwoEventFaces first second (normalizedMatrix kind exponent matrix)

@[simp] theorem sectorEventFaces_map_form
    (sector : Sector) (matrix : Mat2 QI) :
    (sectorEventFaces sector matrix).map EventOrientedFace.form =
      sectorInteriorForms sector matrix := by
  cases sector <;> rfl

@[simp] theorem radialEventFaces_map_form
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    (radialEventFaces kind exponent matrix).map EventOrientedFace.form =
      radialInteriorForms kind exponent matrix := by
  cases kind <;> rfl

@[simp] theorem blockEventFaces_map_form
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) :
    (blockEventFaces kind exponent sector matrix).map
        EventOrientedFace.form =
      blockSectorInteriorForms kind exponent sector matrix := by
  simp [blockEventFaces, blockSectorInteriorForms]

def activeBlockEventForms
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : List HermitianForm :=
  ((blockEventFaces kind exponent sector matrix).filter fun face =>
    decide (face.canonicalValue cell = 0)).map EventOrientedFace.form

def blockEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : List HermitianForm :=
  (blockEventFaces kind exponent sector matrix).map EventOrientedFace.source

/-- A weakly inward oriented value at one sufficiently close persistent
sample transfers to a weakly inward canonical event value.  Canonical zero
is immediate; otherwise the strict sign-transfer estimate fixes the side. -/
theorem EventOrientedFace.canonicalValue_nonnegative_of_inner_eval_nonnegative
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (point : QI)
    (pointInside : (refineState squarefree elimination next radius
      radiusPositive).box.Contains point)
    (face : EventOrientedFace) (source : face.source ∈ forms)
    (classified : clearedForm face.source path ∈
      inputEventPolynomials state path)
    (inward : 0 ≤ face.form.eval point) :
    0 ≤ face.canonicalValue cell := by
  by_cases canonicalZero : inputEventCanonicalValue cell face.source = 0
  · cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.canonicalValue, increasingEq, canonicalZero]
  · have product := canonicalValue_mul_innerPoint_pos cell forms squarefree
      degreeNonzero elimination next nextRefines radius radiusPositive
      radiusSmall point pointInside face.source source classified canonicalZero
    cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.form, EventOrientedFace.canonicalValue,
        increasingEq] at inward product ⊢ <;> nlinarith

def orientedFaceForms (faces : List EventOrientedFace) :
    List HermitianForm :=
  faces.map EventOrientedFace.form

def orientedFaceSourceForms (faces : List EventOrientedFace) :
    List HermitianForm :=
  faces.map EventOrientedFace.source

def activeOrientedFaceForms
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace) :
    List HermitianForm :=
  (faces.filter fun face => decide (face.canonicalValue cell = 0)).map
    EventOrientedFace.form

structure CanonicalOrientedTarget
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace) : Prop
    where
  classified : ∀ face ∈ faces,
    clearedForm face.source path ∈ inputEventPolynomials state path
  canonicalNonnegative : ∀ face ∈ faces,
    0 ≤ face.canonicalValue cell

theorem canonicalOrientedTargetOfInnerSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace)
    (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (point : QI)
    (pointInside : (refineState squarefree elimination next radius
      radiusPositive).box.Contains point)
    (sourceSubset : ∀ face ∈ faces, face.source ∈ forms)
    (classified : ∀ face ∈ faces,
      clearedForm face.source path ∈ inputEventPolynomials state path)
    (inward : ∀ face ∈ faces, 0 ≤ face.form.eval point) :
    CanonicalOrientedTarget cell faces where
  classified := classified
  canonicalNonnegative := by
    intro face faceMember
    exact face.canonicalValue_nonnegative_of_inner_eval_nonnegative cell forms
      squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive radiusSmall point pointInside
      (sourceSubset face faceMember) (classified face faceMember)
      (inward face faceMember)

theorem convergentOrientedPriorEvaluationLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace)
    (target : CanonicalOrientedTarget cell faces)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusStrict : radius < convergentStrictRadius cell
      (orientedFaceSourceForms faces))
    (radiusClear : radius < convergentClearanceRadius p next) :
    ∀ form ∈ approximateOrientedBoxPriors
        (activeOrientedFaceForms cell faces) (orientedFaceForms faces)
          next.box,
      convergentPriorEvaluationLower cell next ≤
        |form.eval (convergentBoxCenter squarefree elimination next radius
          radiusPositive)| := by
  intro form member
  rcases List.mem_append.mp member with inactive | boxForm
  · rcases List.mem_filter.mp inactive with ⟨source, inactiveDecision⟩
    rcases List.mem_map.mp source with ⟨face, faceMember, faceEq⟩
    have inactiveActive : form ∉ activeOrientedFaceForms cell faces :=
      of_decide_eq_true inactiveDecision
    have faceCanonicalNonzero : face.canonicalValue cell ≠ 0 := by
      intro zero
      apply inactiveActive
      exact List.mem_map.mpr
        ⟨face, List.mem_filter.mpr ⟨faceMember, by simp [zero]⟩, faceEq⟩
    have sourceCanonicalNonzero :
        inputEventCanonicalValue cell face.source ≠ 0 := by
      cases increasing : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasing] using
          faceCanonicalNonzero
      · simpa [EventOrientedFace.canonicalValue, increasing] using
          faceCanonicalNonzero
    have sourceMember : face.source ∈ orientedFaceSourceForms faces :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have lower :=
      inputEventStrictFormMargin_div_two_lt_abs_convergentBoxCenter cell
        (orientedFaceSourceForms faces) squarefree degreeNonzero elimination
        next nextRefines radius radiusPositive radiusStrict face.source
        sourceMember (target.classified face faceMember)
          sourceCanonicalNonzero
    subst form
    apply (min_le_left _ _).trans
    cases increasing : face.increasing <;>
      simpa [EventOrientedFace.form, increasing] using lower.le
  · apply (min_le_right _ _).trans
    exact boundaryInteriorRadius_le_convergentBoxForm squarefree elimination
      next radius radiusPositive radiusClear boxForm

/-- Residual-tolerant entry for any finite conjunction of event-oriented
faces. -/
def convergentOrientedBoxData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace)
    (target : CanonicalOrientedTarget cell faces)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell
      (orientedFaceSourceForms faces))
    (direction : TangentDirection (activeOrientedFaceForms cell faces)
      (convergentBoxCenter squarefree elimination next radius radiusPositive))
    (residualBudget :
      convergentCoefficientSum cell (orientedFaceSourceForms faces) * radius <
        approximateBoundaryBudget direction
          (approximateOrientedBoxPriors (activeOrientedFaceForms cell faces)
            (orientedFaceForms faces) next.box)) :
    ApproximateOrientedBoxData (orientedFaceForms faces) next.box
      (activeOrientedFaceForms cell faces) where
  base := convergentBoxCenter squarefree elimination next radius radiusPositive
  baseStrict := convergentBoxCenter_strictContains squarefree elimination next
    radius radiusPositive
  direction := direction
  inactiveStrict := by
    intro form source inactive
    rcases List.mem_map.mp source with ⟨face, faceMember, faceEq⟩
    have faceCanonicalNonzero : face.canonicalValue cell ≠ 0 := by
      intro zero
      apply inactive
      exact List.mem_map.mpr
        ⟨face, List.mem_filter.mpr ⟨faceMember, by simp [zero]⟩, faceEq⟩
    have sourceCanonicalNonzero :
        inputEventCanonicalValue cell face.source ≠ 0 := by
      cases increasingEq : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalNonzero
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalNonzero
    have sourceMember : face.source ∈ orientedFaceSourceForms faces :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have sourceProduct := canonicalValue_mul_convergentBoxCenter_pos cell
      (orientedFaceSourceForms faces) squarefree degreeNonzero elimination next
      nextRefines radius radiusPositive radiusSmall face.source sourceMember
      (target.classified face faceMember) sourceCanonicalNonzero
    have faceCanonicalPositive : 0 < face.canonicalValue cell :=
      lt_of_le_of_ne (target.canonicalNonnegative face faceMember)
        (Ne.symm faceCanonicalNonzero)
    subst form
    cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.canonicalValue, EventOrientedFace.form,
        increasingEq] at faceCanonicalPositive sourceProduct ⊢ <;> nlinarith
  activeResidual := by
    intro form active
    rcases List.mem_map.mp active with ⟨face, filtered, faceEq⟩
    rcases List.mem_filter.mp filtered with ⟨faceMember, zeroDecision⟩
    have faceCanonicalZero : face.canonicalValue cell = 0 :=
      of_decide_eq_true zeroDecision
    have sourceCanonicalZero :
        inputEventCanonicalValue cell face.source = 0 := by
      cases increasingEq : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalZero
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalZero
    have sourceMember : face.source ∈ orientedFaceSourceForms faces :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have residual := convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell
      (orientedFaceSourceForms faces) squarefree degreeNonzero elimination next
      nextRefines radius radiusPositive face.source sourceMember
      (target.classified face faceMember) sourceCanonicalZero
    subst form
    cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.form, increasingEq] <;>
      exact residual.trans residualBudget

def convergentOrientedBoxSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace)
    (target : CanonicalOrientedTarget cell faces)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell
      (orientedFaceSourceForms faces))
    (direction : TangentDirection (activeOrientedFaceForms cell faces)
      (convergentBoxCenter squarefree elimination next radius radiusPositive))
    (residualBudget :
      convergentCoefficientSum cell (orientedFaceSourceForms faces) * radius <
        approximateBoundaryBudget direction
          (approximateOrientedBoxPriors (activeOrientedFaceForms cell faces)
            (orientedFaceForms faces) next.box)) :
    OrientedBoxSample (orientedFaceForms faces) next.box :=
  (convergentOrientedBoxData cell faces target squarefree degreeNonzero
    elimination next nextRefines radius radiusPositive radiusSmall direction
    residualBudget).sample

/-- Every target face's unnegated source is classified by the event table,
and every exact oriented event value is weakly inward. -/
structure CanonicalBlockTarget
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : Prop where
  classified : ∀ face ∈ blockEventFaces kind exponent sector matrix,
    clearedForm face.source path ∈ inputEventPolynomials state path
  canonicalNonnegative : ∀ face ∈
    blockEventFaces kind exponent sector matrix,
      0 ≤ face.canonicalValue cell

/-- Package a full canonical block target from one sufficiently close weakly
inward sample.  Separating this finite transfer from controller-specific
payloads keeps dependent elaboration small. -/
theorem canonicalBlockTargetOfInnerSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (forms : List HermitianForm)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell forms)
    (point : QI)
    (pointInside : (refineState squarefree elimination next radius
      radiusPositive).box.Contains point)
    (sourceSubset : ∀ face ∈ blockEventFaces kind exponent sector matrix,
      face.source ∈ forms)
    (classified : ∀ face ∈ blockEventFaces kind exponent sector matrix,
      clearedForm face.source path ∈ inputEventPolynomials state path)
    (inward : ∀ form ∈ blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval point) :
    CanonicalBlockTarget cell kind exponent sector matrix where
  classified := classified
  canonicalNonnegative := by
    intro face faceMember
    have formMember : face.form ∈
        blockSectorInteriorForms kind exponent sector matrix := by
      rw [← blockEventFaces_map_form]
      exact List.mem_map.mpr ⟨face, faceMember, rfl⟩
    exact face.canonicalValue_nonnegative_of_inner_eval_nonnegative cell forms
      squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive radiusSmall point pointInside
      (sourceSubset face faceMember) (classified face faceMember)
      (inward face.form formMember)

theorem convergentBlockPriorEvaluationLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI)
    (target : CanonicalBlockTarget cell kind exponent sector matrix)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusStrict : radius < convergentStrictRadius cell
      (blockEventSourceForms kind exponent sector matrix))
    (radiusClear : radius < convergentClearanceRadius p next) :
    ∀ form ∈ approximateBlockSectorBoxPriors
        (activeBlockEventForms cell kind exponent sector matrix)
          kind exponent sector matrix next.box,
      convergentPriorEvaluationLower cell next ≤
        |form.eval (convergentBoxCenter squarefree elimination next radius
          radiusPositive)| := by
  intro form member
  rcases List.mem_append.mp member with inactive | boxForm
  · rcases List.mem_filter.mp inactive with ⟨source, inactiveDecision⟩
    rw [← blockEventFaces_map_form] at source
    rcases List.mem_map.mp source with ⟨face, faceMember, faceEq⟩
    have inactiveActive :
        form ∉ activeBlockEventForms cell kind exponent sector matrix :=
      of_decide_eq_true inactiveDecision
    have faceCanonicalNonzero : face.canonicalValue cell ≠ 0 := by
      intro zero
      apply inactiveActive
      exact List.mem_map.mpr
        ⟨face, List.mem_filter.mpr ⟨faceMember, by simp [zero]⟩, faceEq⟩
    have sourceCanonicalNonzero :
        inputEventCanonicalValue cell face.source ≠ 0 := by
      cases increasing : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasing] using
          faceCanonicalNonzero
      · simpa [EventOrientedFace.canonicalValue, increasing] using
          faceCanonicalNonzero
    have sourceMember : face.source ∈
        blockEventSourceForms kind exponent sector matrix :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have lower :=
      inputEventStrictFormMargin_div_two_lt_abs_convergentBoxCenter cell
        (blockEventSourceForms kind exponent sector matrix) squarefree
        degreeNonzero elimination next nextRefines radius radiusPositive
        radiusStrict face.source sourceMember
        (target.classified face faceMember) sourceCanonicalNonzero
    subst form
    apply (min_le_left _ _).trans
    cases increasing : face.increasing <;>
      simpa [EventOrientedFace.form, increasing] using lower.le
  · apply (min_le_right _ _).trans
    exact boundaryInteriorRadius_le_convergentBoxForm squarefree elimination
      next radius radiusPositive radiusClear boxForm

/-- At a sufficiently fine radius, the only remaining numerical hypothesis
is the displayed residual-budget inequality for a concrete tangent
certificate. -/
def convergentBlockData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI)
    (target : CanonicalBlockTarget cell kind exponent sector matrix)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell
      (blockEventSourceForms kind exponent sector matrix))
    (direction : TangentDirection
      (activeBlockEventForms cell kind exponent sector matrix)
      (convergentBoxCenter squarefree elimination next radius radiusPositive))
    (residualBudget :
      convergentCoefficientSum cell
          (blockEventSourceForms kind exponent sector matrix) * radius <
        approximateBoundaryBudget direction
          (approximateBlockSectorBoxPriors
            (activeBlockEventForms cell kind exponent sector matrix)
            kind exponent sector matrix next.box)) :
    ApproximateBlockSectorBoxData kind exponent sector matrix next.box
      (activeBlockEventForms cell kind exponent sector matrix) where
  base := convergentBoxCenter squarefree elimination next radius radiusPositive
  baseStrict := convergentBoxCenter_strictContains squarefree elimination next
    radius radiusPositive
  direction := direction
  inactiveStrict := by
    intro form source inactive
    rw [← blockEventFaces_map_form] at source
    rcases List.mem_map.mp source with ⟨face, faceMember, faceEq⟩
    have faceCanonicalNonzero : face.canonicalValue cell ≠ 0 := by
      intro zero
      apply inactive
      apply List.mem_map.mpr
      exact ⟨face, List.mem_filter.mpr ⟨faceMember, by simp [zero]⟩, faceEq⟩
    have sourceCanonicalNonzero :
        inputEventCanonicalValue cell face.source ≠ 0 := by
      cases increasingEq : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalNonzero
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalNonzero
    have sourceMember : face.source ∈
        blockEventSourceForms kind exponent sector matrix :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have sourceProduct := canonicalValue_mul_convergentBoxCenter_pos cell
      (blockEventSourceForms kind exponent sector matrix) squarefree
      degreeNonzero elimination next nextRefines radius radiusPositive
      radiusSmall face.source sourceMember (target.classified face faceMember)
        sourceCanonicalNonzero
    have faceCanonicalPositive : 0 < face.canonicalValue cell :=
      lt_of_le_of_ne (target.canonicalNonnegative face faceMember)
        (Ne.symm faceCanonicalNonzero)
    subst form
    cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.canonicalValue, EventOrientedFace.form,
        increasingEq] at faceCanonicalPositive sourceProduct ⊢ <;> nlinarith
  activeResidual := by
    intro form active
    rcases List.mem_map.mp active with ⟨face, filtered, faceEq⟩
    rcases List.mem_filter.mp filtered with ⟨faceMember, zeroDecision⟩
    have faceCanonicalZero : face.canonicalValue cell = 0 :=
      of_decide_eq_true zeroDecision
    have sourceCanonicalZero :
        inputEventCanonicalValue cell face.source = 0 := by
      cases increasingEq : face.increasing
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalZero
      · simpa [EventOrientedFace.canonicalValue, increasingEq] using
          faceCanonicalZero
    have sourceMember : face.source ∈
        blockEventSourceForms kind exponent sector matrix :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have residual := convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell
      (blockEventSourceForms kind exponent sector matrix) squarefree
      degreeNonzero elimination next nextRefines radius radiusPositive
      face.source sourceMember (target.classified face faceMember)
        sourceCanonicalZero
    subst form
    cases increasingEq : face.increasing <;>
      simp [EventOrientedFace.form, increasingEq] <;>
      exact residual.trans residualBudget

/-- The convergence data immediately yields a strict annulus/sector sample
inside the requested winding box. -/
def convergentBlockSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI)
    (target : CanonicalBlockTarget cell kind exponent sector matrix)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < convergentStrictRadius cell
      (blockEventSourceForms kind exponent sector matrix))
    (direction : TangentDirection
      (activeBlockEventForms cell kind exponent sector matrix)
      (convergentBoxCenter squarefree elimination next radius radiusPositive))
    (residualBudget :
      convergentCoefficientSum cell
          (blockEventSourceForms kind exponent sector matrix) * radius <
        approximateBoundaryBudget direction
          (approximateBlockSectorBoxPriors
            (activeBlockEventForms cell kind exponent sector matrix)
            kind exponent sector matrix next.box)) :
    BlockSectorBoxSample kind exponent sector matrix next.box :=
  (convergentBlockData cell kind exponent sector matrix target squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive
      radiusSmall direction residualBudget).sample

end CCLSectorBoundaryConvergence
end FTA
