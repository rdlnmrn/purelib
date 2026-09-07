import FTA.CCLOwnerDirection
import FTA.Maximality
import FTA.RationalPolynomialBounds

/-!
# Bounded owner-side perturbation grids

A finite list of earlier strict Hermitian comparisons has a computed positive
perturbation radius.  Combining it with the selected boundary's linear radius
and the explicit reciprocal bound produces a natural number `N`; the rational
step `1/N` enters the requested owner side and preserves every earlier sign.
This is the bounded, rather than semidecidable, grid step in Lemma 10.3.
-/

namespace FTA
namespace CCLOwnerGrid

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.RationalPolynomialBounds

abbrev QI := CCL.GaussianRat

/-- Explicit natural reciprocal index for a positive rational radius. -/
def reciprocalIndex (radius : ℚ) : ℕ := ⌈1 / radius⌉₊ + 1

theorem reciprocalIndex_pos (radius : ℚ) : 0 < reciprocalIndex radius := by
  exact Nat.succ_pos _

/-- Lemma 2.2 in the form used by the owner grid. -/
theorem reciprocal_lt_radius {radius : ℚ} (radiusPositive : 0 < radius) :
    (1 : ℚ) / (reciprocalIndex radius : ℕ) < radius := by
  let ceiling : ℕ := ⌈1 / radius⌉₊
  let index : ℕ := reciprocalIndex radius
  have hceil : 1 / radius ≤ (ceiling : ℚ) := by
    exact Nat.le_ceil (1 / radius)
  have hindex : (ceiling : ℚ) < (index : ℚ) := by
    dsimp only [ceiling, index, reciprocalIndex]
    exact_mod_cast Nat.lt_succ_self ⌈1 / radius⌉₊
  have hinverseIndex : 1 / radius < (index : ℚ) := hceil.trans_lt hindex
  have hone : 1 < (index : ℚ) * radius :=
    (div_lt_iff₀ radiusPositive).mp hinverseIndex
  have hindexPositive : 0 < (index : ℚ) := by
    exact_mod_cast reciprocalIndex_pos radius
  apply (div_lt_iff₀ hindexPositive).2
  simpa only [_root_.mul_comm] using hone

/-- The reciprocal-grid step is also bounded below by one third of any
positive input radius at most one.  This quantitative converse turns a
uniform radius lower bound into a uniform positive perturbation size. -/
theorem radius_div_three_lt_reciprocal
    {radius : ℚ} (radiusPositive : 0 < radius) (radiusAtMostOne : radius ≤ 1) :
    radius / 3 < (1 : ℚ) / (reciprocalIndex radius : ℕ) := by
  let ceiling : ℕ := ⌈1 / radius⌉₊
  let index : ℕ := reciprocalIndex radius
  have inverseNonnegative : 0 ≤ (1 : ℚ) / radius :=
    div_nonneg (by norm_num) radiusPositive.le
  have ceilingLt : (ceiling : ℚ) < 1 / radius + 1 := by
    simpa only [ceiling] using
      (Nat.ceil_lt_add_one inverseNonnegative)
  have indexEq : (index : ℚ) = (ceiling : ℚ) + 1 := by
    simp [index, ceiling, reciprocalIndex]
  have indexLt : (index : ℚ) < 1 / radius + 2 := by
    rw [indexEq]
    linarith
  have productLt : radius * (index : ℚ) < 3 := by
    have scaled := mul_lt_mul_of_pos_left indexLt radiusPositive
    have inverseIdentity : radius * (1 / radius + 2) = 1 + 2 * radius := by
      field_simp
    rw [inverseIdentity] at scaled
    linarith
  have indexPositive : 0 < (index : ℚ) := by
    exact_mod_cast reciprocalIndex_pos radius
  apply (lt_div_iff₀ indexPositive).2
  nlinarith

/-- Positive coefficient bound for one Hermitian form along one unit
coordinate direction. -/
def perturbationMajorant (form : HermitianForm) (z direction : QI) : ℚ :=
  max 1 (|directionalSlope form z direction| + |form.radial|)

theorem perturbationMajorant_pos (form : HermitianForm) (z direction : QI) :
    0 < perturbationMajorant form z direction :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem abs_eval_step_sub_le
    (form : HermitianForm) (z direction : QI) {epsilon : ℚ}
    (directionUnit : normSq direction = 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonAtMostOne : epsilon ≤ 1) :
    |form.eval (step z epsilon direction) - form.eval z| ≤
      epsilon * perturbationMajorant form z direction := by
  rw [eval_step]
  have hidentity :
      form.eval z + epsilon * directionalSlope form z direction +
          form.radial * epsilon ^ 2 * normSq direction - form.eval z =
        epsilon * directionalSlope form z direction +
          form.radial * epsilon ^ 2 := by
    rw [directionUnit]
    ring
  rw [hidentity]
  have hepsilonSq : epsilon ^ 2 ≤ epsilon := by
    nlinarith
  calc
    |epsilon * directionalSlope form z direction +
        form.radial * epsilon ^ 2| ≤
        |epsilon * directionalSlope form z direction| +
          |form.radial * epsilon ^ 2| := abs_add_le _ _
    _ = epsilon * |directionalSlope form z direction| +
          |form.radial| * epsilon ^ 2 := by
      rw [abs_mul, abs_of_nonneg epsilonNonnegative, abs_mul, abs_pow,
        abs_of_nonneg epsilonNonnegative]
    _ ≤ epsilon * |directionalSlope form z direction| +
          |form.radial| * epsilon := by
      gcongr
    _ = epsilon *
          (|directionalSlope form z direction| + |form.radial|) := by ring
    _ ≤ epsilon * perturbationMajorant form z direction := by
      apply mul_le_mul_of_nonneg_left (le_max_right _ _) epsilonNonnegative

private theorem abs_radial_step_term_le
    (radial epsilon directionNorm : ℚ)
    (directionNormNonnegative : 0 ≤ directionNorm)
    (directionNormAtMostOne : directionNorm ≤ 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonAtMostOne : epsilon ≤ 1) :
    |radial * epsilon ^ 2 * directionNorm| ≤ epsilon * |radial| := by
  have epsilonSqAtMost : epsilon ^ 2 ≤ epsilon := by nlinarith
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg epsilonNonnegative,
    abs_of_nonneg directionNormNonnegative]
  calc
    |radial| * epsilon ^ 2 * directionNorm =
        |radial| * (epsilon ^ 2 * directionNorm) := by ring
    _ ≤ |radial| * (epsilon ^ 2 * 1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg radial)
      exact mul_le_mul_of_nonneg_left directionNormAtMostOne (sq_nonneg epsilon)
    _ = |radial| * epsilon ^ 2 := by ring
    _ ≤ |radial| * epsilon :=
      mul_le_mul_of_nonneg_left epsilonSqAtMost (abs_nonneg radial)
    _ = epsilon * |radial| := by ring

private theorem add_add_sub_self (a b c : ℚ) : a + b + c - a = b + c := by
  ring

private theorem abs_linear_radial_step_le
    (slope radial epsilon directionNorm : ℚ)
    (directionNormNonnegative : 0 ≤ directionNorm)
    (directionNormAtMostOne : directionNorm ≤ 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonAtMostOne : epsilon ≤ 1) :
    |epsilon * slope + radial * epsilon ^ 2 * directionNorm| ≤
      epsilon * (|slope| + |radial|) := by
  have radialBound := abs_radial_step_term_le radial epsilon directionNorm
    directionNormNonnegative directionNormAtMostOne epsilonNonnegative epsilonAtMostOne
  calc
    |epsilon * slope + radial * epsilon ^ 2 * directionNorm| ≤
        |epsilon * slope| + |radial * epsilon ^ 2 * directionNorm| :=
      abs_add_le _ _
    _ = epsilon * |slope| + |radial * epsilon ^ 2 * directionNorm| := by
      rw [abs_mul, abs_of_nonneg epsilonNonnegative]
    _ ≤ epsilon * |slope| + epsilon * |radial| :=
      add_le_add_right radialBound _
    _ = epsilon * (|slope| + |radial|) := by ring

/-- The same displacement bound for any rational direction of squared norm at
most one.  This covers the rational half-diagonals needed at sector corners. -/
theorem abs_eval_step_sub_le_of_normSq_le_one
    (form : HermitianForm) (z direction : QI) {epsilon : ℚ}
    (directionNormAtMostOne : normSq direction ≤ 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonAtMostOne : epsilon ≤ 1) :
    |form.eval (step z epsilon direction) - form.eval z| ≤
      epsilon * perturbationMajorant form z direction := by
  rw [eval_step]
  have directionNormNonnegative : 0 ≤ normSq direction := normSq_nonneg direction
  rw [add_add_sub_self]
  exact (abs_linear_radial_step_le
    (directionalSlope form z direction) form.radial epsilon (normSq direction)
    directionNormNonnegative directionNormAtMostOne epsilonNonnegative
    epsilonAtMostOne).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) epsilonNonnegative)

/-- Radius preserving the strict sign of one nonzero Hermitian evaluation. -/
def signRadius (form : HermitianForm) (z direction : QI) : ℚ :=
  |form.eval z| / perturbationMajorant form z direction

theorem signRadius_pos (form : HermitianForm) (z direction : QI)
    (nonzero : form.eval z ≠ 0) : 0 < signRadius form z direction := by
  exact div_pos (abs_pos.mpr nonzero)
    (perturbationMajorant_pos form z direction)

theorem eval_mul_pos_of_lt_signRadius
    (form : HermitianForm) (z direction : QI)
    (directionUnit : normSq direction = 1) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) (epsilonAtMostOne : epsilon ≤ 1)
    (epsilonSmall : epsilon < signRadius form z direction) :
    0 < form.eval z * form.eval (step z epsilon direction) := by
  have hbound := abs_eval_step_sub_le form z direction directionUnit
    epsilonPositive.le epsilonAtMostOne
  have hmargin : epsilon * perturbationMajorant form z direction <
      |form.eval z| :=
    (lt_div_iff₀ (perturbationMajorant_pos form z direction)).mp epsilonSmall
  apply mul_pos_of_abs_sub_lt_abs_left
  rw [abs_sub_comm]
  exact hbound.trans_lt hmargin

theorem eval_mul_pos_of_lt_signRadius_normSq_le_one
    (form : HermitianForm) (z direction : QI)
    (directionNormAtMostOne : normSq direction ≤ 1) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) (epsilonAtMostOne : epsilon ≤ 1)
    (epsilonSmall : epsilon < signRadius form z direction) :
    0 < form.eval z * form.eval (step z epsilon direction) := by
  have hbound := abs_eval_step_sub_le_of_normSq_le_one form z direction
    directionNormAtMostOne epsilonPositive.le epsilonAtMostOne
  have hmargin : epsilon * perturbationMajorant form z direction <
      |form.eval z| :=
    (lt_div_iff₀ (perturbationMajorant_pos form z direction)).mp epsilonSmall
  apply mul_pos_of_abs_sub_lt_abs_left
  rw [abs_sub_comm]
  exact hbound.trans_lt hmargin

/-- A positive linear slope still enters the positive owner side for any
rational direction of squared norm at most one. -/
theorem eval_step_pos_of_normSq_le_one
    (form : HermitianForm) (z direction : QI)
    (directionNormAtMostOne : normSq direction ≤ 1)
    (onBoundary : form.eval z = 0) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (epsilonSmall : epsilon <
      directionalSlope form z direction / (|form.radial| + 1)) :
    0 < form.eval (step z epsilon direction) := by
  have directionNormNonnegative : 0 ≤ normSq direction := normSq_nonneg direction
  have denominatorPositive : 0 < |form.radial| + 1 := by positivity
  have scaledSmall : epsilon * (|form.radial| + 1) <
      directionalSlope form z direction :=
    (lt_div_iff₀ denominatorPositive).mp epsilonSmall
  have radialError : epsilon * |form.radial| <
      directionalSlope form z direction := by
    have strict : epsilon * |form.radial| <
        epsilon * (|form.radial| + 1) := by nlinarith
    exact strict.trans scaledSmall
  have radialLower : -|form.radial| ≤ form.radial * normSq direction := by
    by_cases radialNonnegative : 0 ≤ form.radial
    · have productNonnegative := mul_nonneg radialNonnegative directionNormNonnegative
      exact (neg_nonpos.mpr (abs_nonneg form.radial)).trans productNonnegative
    · have radialNonpositive : form.radial ≤ 0 := le_of_not_ge radialNonnegative
      have productLower : form.radial ≤ form.radial * normSq direction := by
        calc
          form.radial = form.radial * 1 := by ring
          _ ≤ form.radial * normSq direction :=
            mul_le_mul_of_nonpos_left directionNormAtMostOne radialNonpositive
      simpa only [abs_of_nonpos radialNonpositive, neg_neg] using productLower
  have radialScaled :
      -epsilon * |form.radial| ≤
        epsilon * (form.radial * normSq direction) := by
    have := mul_le_mul_of_nonneg_left radialLower epsilonPositive.le
    linarith
  have positiveFactor :
      0 < directionalSlope form z direction +
        form.radial * epsilon * normSq direction := by
    nlinarith
  rw [eval_step, onBoundary]
  have identity :
      0 + epsilon * directionalSlope form z direction +
          form.radial * epsilon ^ 2 * normSq direction =
        epsilon * (directionalSlope form z direction +
          form.radial * epsilon * normSq direction) := by ring
  rw [identity]
  exact mul_pos epsilonPositive positiveFactor

/-- Approximate-boundary variant of `eval_step_pos_of_normSq_le_one`.
The linear owner entry may start at a small nonzero residual, provided the
displayed budget dominates that residual and the worst quadratic error. -/
theorem eval_step_pos_of_abs_eval_lt_of_normSq_le_one
    (form : HermitianForm) (z direction : QI)
    (directionNormAtMostOne : normSq direction ≤ 1) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (epsilonSmall : epsilon <
      directionalSlope form z direction / (|form.radial| + 1))
    (residualSmall : |form.eval z| < epsilon *
      (directionalSlope form z direction - epsilon * |form.radial|)) :
    0 < form.eval (step z epsilon direction) := by
  have directionNormNonnegative : 0 ≤ normSq direction := normSq_nonneg direction
  have radialLower : -|form.radial| ≤
      form.radial * normSq direction := by
    by_cases radialNonnegative : 0 ≤ form.radial
    · have productNonnegative :=
        mul_nonneg radialNonnegative directionNormNonnegative
      exact (neg_nonpos.mpr (abs_nonneg form.radial)).trans productNonnegative
    · have radialNonpositive : form.radial ≤ 0 :=
        le_of_not_ge radialNonnegative
      have productLower : form.radial ≤
          form.radial * normSq direction := by
        calc
          form.radial = form.radial * 1 := by ring
          _ ≤ form.radial * normSq direction :=
            mul_le_mul_of_nonpos_left directionNormAtMostOne radialNonpositive
      simpa only [abs_of_nonpos radialNonpositive, neg_neg] using productLower
  have radialScaled :
      -(epsilon ^ 2 * |form.radial|) ≤
        form.radial * epsilon ^ 2 * normSq direction := by
    have scaled := mul_le_mul_of_nonneg_left radialLower (sq_nonneg epsilon)
    nlinarith
  have evaluationLower : -|form.eval z| ≤ form.eval z := neg_abs_le _
  have denominatorPositive : 0 < |form.radial| + 1 := by positivity
  have linearDominates :
      epsilon * |form.radial| < directionalSlope form z direction := by
    have scaled := (lt_div_iff₀ denominatorPositive).mp epsilonSmall
    nlinarith
  rw [eval_step]
  nlinarith

/-- Positive finite minimum of all earlier strict-sign radii. -/
def strictRadius (forms : List HermitianForm) (z direction : QI) : ℚ :=
  FTA.Maximality.positiveMinimum
    (forms.map fun form => signRadius form z direction)

theorem strictRadius_pos (forms : List HermitianForm) (z direction : QI)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    0 < strictRadius forms z direction := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value hvalue
  rw [List.mem_map] at hvalue
  rcases hvalue with ⟨form, hform, rfl⟩
  exact signRadius_pos form z direction (allNonzero form hform)

theorem strictRadius_le_signRadius
    {forms : List HermitianForm} {form : HermitianForm} (hform : form ∈ forms)
    (z direction : QI) :
    strictRadius forms z direction ≤ signRadius form z direction := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, hform, rfl⟩

/-- Common positive radius for owner entry, earlier strict signs, and the
unit-step hypothesis used by the quadratic displacement bound. -/
def ownerRadius {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI) : ℚ :=
  min 1 (min
    (directionalSlope boundary z increasing.vector / (|boundary.radial| + 1))
    (strictRadius forms z direction))

theorem ownerRadius_pos
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    0 < ownerRadius increasing forms direction := by
  apply lt_min zero_lt_one
  apply lt_min
  · exact div_pos increasing.slopePositive (by positivity)
  · exact strictRadius_pos forms z direction allNonzero

def ownerIndex {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI) : ℕ :=
  reciprocalIndex (ownerRadius increasing forms direction)

def ownerEpsilon {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI) : ℚ :=
  1 / (ownerIndex increasing forms direction : ℕ)

theorem ownerEpsilon_pos
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI) :
    0 < ownerEpsilon increasing forms direction := by
  apply div_pos zero_lt_one
  exact_mod_cast reciprocalIndex_pos (ownerRadius increasing forms direction)

theorem ownerEpsilon_lt_ownerRadius
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    ownerEpsilon increasing forms direction <
      ownerRadius increasing forms direction := by
  exact reciprocal_lt_radius
    (ownerRadius_pos increasing forms direction allNonzero)

theorem ownerEpsilon_le_one
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    ownerEpsilon increasing forms direction ≤ 1 := by
  exact (ownerEpsilon_lt_ownerRadius increasing forms direction allNonzero).le.trans
    (min_le_left _ _)

theorem ownerEpsilon_lt_linearRadius
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm) (direction : QI)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    ownerEpsilon increasing forms direction <
      directionalSlope boundary z increasing.vector / (|boundary.radial| + 1) := by
  apply (ownerEpsilon_lt_ownerRadius increasing forms direction allNonzero).trans_le
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem ownerEpsilon_lt_signRadius
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    {forms : List HermitianForm} {form : HermitianForm} (hform : form ∈ forms)
    (direction : QI)
    (allNonzero : ∀ prior ∈ forms, prior.eval z ≠ 0) :
    ownerEpsilon increasing forms direction < signRadius form z direction := by
  apply (ownerEpsilon_lt_ownerRadius increasing forms direction allNonzero).trans_le
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    (strictRadius_le_signRadius hform z direction))

/-- The positive-owner grid point enters the selected strict side. -/
theorem positiveOwner_enters
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z) (onBoundary : boundary.eval z = 0)
    (forms : List HermitianForm)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    0 < boundary.eval (step z
      (ownerEpsilon increasing forms increasing.vector) increasing.vector) := by
  apply eval_step_pos increasing onBoundary
    (ownerEpsilon_pos increasing forms increasing.vector)
  exact ownerEpsilon_lt_linearRadius increasing forms increasing.vector allNonzero

/-- The negative-owner grid point enters the selected strict side. -/
theorem negativeOwner_enters
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z) (onBoundary : boundary.eval z = 0)
    (forms : List HermitianForm)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    boundary.eval (step z
      (ownerEpsilon increasing forms (-increasing.vector))
        (-increasing.vector)) < 0 := by
  apply eval_step_neg increasing onBoundary
    (ownerEpsilon_pos increasing forms (-increasing.vector))
  exact ownerEpsilon_lt_linearRadius increasing forms (-increasing.vector) allNonzero

theorem positiveOwner_preserves_strict_signs
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    ∀ form ∈ forms, 0 < form.eval z * form.eval (step z
      (ownerEpsilon increasing forms increasing.vector) increasing.vector) := by
  intro form hform
  apply eval_mul_pos_of_lt_signRadius form z increasing.vector increasing.unitNorm
    (ownerEpsilon_pos increasing forms increasing.vector)
    (ownerEpsilon_le_one increasing forms increasing.vector allNonzero)
  exact ownerEpsilon_lt_signRadius increasing hform increasing.vector allNonzero

theorem negativeOwner_preserves_strict_signs
    {boundary : HermitianForm} {z : QI}
    (increasing : IncreasingDirection boundary z)
    (forms : List HermitianForm)
    (allNonzero : ∀ form ∈ forms, form.eval z ≠ 0) :
    ∀ form ∈ forms, 0 < form.eval z * form.eval (step z
      (ownerEpsilon increasing forms (-increasing.vector))
        (-increasing.vector)) := by
  intro form hform
  apply eval_mul_pos_of_lt_signRadius form z (-increasing.vector)
    (by rw [normSq_neg, increasing.unitNorm])
    (ownerEpsilon_pos increasing forms (-increasing.vector))
    (ownerEpsilon_le_one increasing forms (-increasing.vector) allNonzero)
  exact ownerEpsilon_lt_signRadius increasing hform (-increasing.vector) allNonzero

end CCLOwnerGrid
end FTA
