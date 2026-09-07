import FTA.CCLOwnerGrid

/-!
# Simultaneous finite tangent-cone owner sampling

At an intersection of several equality-owned CCL or box boundaries, orient
each Hermitian form so that its selected owner side is positive.  A finite
search through `±1, ±i` decides whether one coordinate direction has positive
linear slope for every active form.  When it does, one coefficient-computed
common reciprocal step enters all active sides and preserves every earlier
strict sign.  Including the four inward box forms proves that the returned
rational point remains in the box.  This is the simultaneous tangent-cone
calculation in Lemma 10.3.
-/

namespace FTA
namespace CCLMultiOwnerGrid

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid

abbrev QI := CCL.GaussianRat

/-- The finite eight-direction table: four axes and four rational
half-diagonals.  Every entry has squared norm at most one. -/
def coordinateDirections : List QI :=
  [⟨1, 0⟩, ⟨1 / 2, 1 / 2⟩, ⟨0, 1⟩, ⟨-1 / 2, 1 / 2⟩,
    ⟨-1, 0⟩, ⟨-1 / 2, -1 / 2⟩, ⟨0, -1⟩, ⟨1 / 2, -1 / 2⟩]

theorem coordinateDirection_normSq_le_one {direction : QI}
    (member : direction ∈ coordinateDirections) : normSq direction ≤ 1 := by
  simp [coordinateDirections] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [normSq]

/-- Executable linear tangent-cone test for a displayed direction. -/
def slopesPositive? (forms : List HermitianForm) (z direction : QI) : Bool :=
  forms.all fun form => decide (0 < directionalSlope form z direction)

theorem slopesPositive?_eq_true_iff
    (forms : List HermitianForm) (z direction : QI) :
    slopesPositive? forms z direction = true ↔
      ∀ form ∈ forms, 0 < directionalSlope form z direction := by
  simp [slopesPositive?]

/-- Exhaustive finite search for the first coordinate direction lying in all
active oriented tangent half-planes. -/
def tangentDirection?
    (forms : List HermitianForm) (z : QI) : Option QI :=
  coordinateDirections.find? fun direction => slopesPositive? forms z direction

theorem tangentDirection?_some_mem
    {forms : List HermitianForm} {z direction : QI}
    (search : tangentDirection? forms z = some direction) :
    direction ∈ coordinateDirections := by
  exact List.mem_of_find?_eq_some search

theorem tangentDirection?_some_slopes
    {forms : List HermitianForm} {z direction : QI}
    (search : tangentDirection? forms z = some direction) :
    ∀ form ∈ forms, 0 < directionalSlope form z direction := by
  exact (slopesPositive?_eq_true_iff forms z direction).mp
    (List.find?_some search)

theorem tangentDirection?_isSome_of_mem
    {forms : List HermitianForm} {z direction : QI}
    (member : direction ∈ coordinateDirections)
    (slopes : ∀ form ∈ forms, 0 < directionalSlope form z direction) :
    (tangentDirection? forms z).isSome := by
  rw [tangentDirection?, List.find?_isSome]
  exact ⟨direction, member,
    (slopesPositive?_eq_true_iff forms z direction).mpr slopes⟩

/-- Proof-bearing successful result of the finite tangent-cone table. -/
structure TangentDirection (forms : List HermitianForm) (z : QI) where
  vector : QI
  normSqLeOne : normSq vector ≤ 1
  slopes : ∀ form ∈ forms, 0 < directionalSlope form z vector

def tangentDirectionCertificate?
    (forms : List HermitianForm) (z : QI) : Option (TangentDirection forms z) :=
  match search : tangentDirection? forms z with
  | none => none
  | some direction => some
      { vector := direction
        normSqLeOne := coordinateDirection_normSq_le_one
          (tangentDirection?_some_mem search)
        slopes := tangentDirection?_some_slopes search }

/-- A tangent certificate carrying a common explicit lower bound for every
active directional slope.  This quantitative variant is what lets a later
localization radius be chosen before the rational anchor is evaluated. -/
structure TangentDirectionAbove
    (forms : List HermitianForm) (z : QI) (lower : ℚ) where
  vector : QI
  normSqLeOne : normSq vector ≤ 1
  slopesAbove : ∀ form ∈ forms,
    lower < directionalSlope form z vector

def TangentDirectionAbove.toTangentDirection
    {forms : List HermitianForm} {z : QI} {lower : ℚ}
    (direction : TangentDirectionAbove forms z lower)
    (lowerNonnegative : 0 ≤ lower) : TangentDirection forms z where
  vector := direction.vector
  normSqLeOne := direction.normSqLeOne
  slopes := by
    intro form member
    exact lowerNonnegative.trans_lt (direction.slopesAbove form member)

/-- Executable thresholded version of the eight-direction compass search. -/
def slopesAbove?
    (forms : List HermitianForm) (z direction : QI) (lower : ℚ) : Bool :=
  forms.all fun form => decide
    (lower < directionalSlope form z direction)

theorem slopesAbove?_eq_true_iff
    (forms : List HermitianForm) (z direction : QI) (lower : ℚ) :
    slopesAbove? forms z direction lower = true ↔
      ∀ form ∈ forms, lower < directionalSlope form z direction := by
  simp [slopesAbove?]

def tangentDirectionAbove?
    (forms : List HermitianForm) (z : QI) (lower : ℚ) : Option QI :=
  coordinateDirections.find? fun direction =>
    slopesAbove? forms z direction lower

theorem tangentDirectionAbove?_some_mem
    {forms : List HermitianForm} {z direction : QI} {lower : ℚ}
    (search : tangentDirectionAbove? forms z lower = some direction) :
    direction ∈ coordinateDirections := by
  exact List.mem_of_find?_eq_some search

theorem tangentDirectionAbove?_some_slopes
    {forms : List HermitianForm} {z direction : QI} {lower : ℚ}
    (search : tangentDirectionAbove? forms z lower = some direction) :
    ∀ form ∈ forms, lower < directionalSlope form z direction := by
  apply (slopesAbove?_eq_true_iff forms z direction lower).1
  have found : coordinateDirections.find? (fun candidate =>
      slopesAbove? forms z candidate lower) = some direction := by
    simpa only [tangentDirectionAbove?] using search
  exact @List.find?_some QI
    (fun candidate => slopesAbove? forms z candidate lower)
    direction coordinateDirections found

def tangentDirectionAboveCertificate?
    (forms : List HermitianForm) (z : QI) (lower : ℚ) :
    Option (TangentDirectionAbove forms z lower) :=
  match search : tangentDirectionAbove? forms z lower with
  | none => none
  | some direction => some
      { vector := direction
        normSqLeOne := coordinateDirection_normSq_le_one
          (tangentDirectionAbove?_some_mem search)
        slopesAbove := tangentDirectionAbove?_some_slopes search }

theorem tangentDirectionAboveCertificate?_isSome_of_mem
    {forms : List HermitianForm} {z direction : QI} {lower : ℚ}
    (member : direction ∈ coordinateDirections)
    (slopes : ∀ form ∈ forms,
      lower < directionalSlope form z direction) :
    (tangentDirectionAboveCertificate? forms z lower).isSome := by
  have found : (tangentDirectionAbove? forms z lower).isSome := by
    rw [tangentDirectionAbove?, List.find?_isSome]
    exact ⟨direction, member,
      (slopesAbove?_eq_true_iff forms z direction lower).2 slopes⟩
  unfold tangentDirectionAboveCertificate?
  split
  · rename_i search
    rw [search] at found
    contradiction
  · rfl

theorem tangentDirectionCertificate?_isSome_of_mem
    {forms : List HermitianForm} {z direction : QI}
    (member : direction ∈ coordinateDirections)
    (slopes : ∀ form ∈ forms, 0 < directionalSlope form z direction) :
    (tangentDirectionCertificate? forms z).isSome := by
  have found := tangentDirection?_isSome_of_mem member slopes
  unfold tangentDirectionCertificate?
  split
  · rename_i search
    rw [search] at found
    contradiction
  · rfl

/-- A successful executable direction search remains successful after
discarding active-form obligations.  The same table entry is reused, so this
is a computational monotonicity statement rather than an existence-only
change of direction. -/
theorem tangentDirectionCertificate?_isSome_of_subset
    {forms supporting : List HermitianForm} {z : QI}
    (subset : ∀ form ∈ forms, form ∈ supporting)
    (success : (tangentDirectionCertificate? supporting z).isSome) :
    (tangentDirectionCertificate? forms z).isSome := by
  unfold tangentDirectionCertificate? at success
  split at success
  · contradiction
  · rename_i direction search
    apply tangentDirectionCertificate?_isSome_of_mem
      (tangentDirection?_some_mem search)
    intro form member
    exact tangentDirection?_some_slopes search form (subset form member)

/-- In particular, prepending only duplicate obligations does not change
success of the executable search. -/
theorem tangentDirectionCertificate?_isSome_append_of_left_subset
    {left right : List HermitianForm} {z : QI}
    (leftSubset : ∀ form ∈ left, form ∈ right)
    (success : (tangentDirectionCertificate? right z).isSome) :
    (tangentDirectionCertificate? (left ++ right) z).isSome := by
  apply tangentDirectionCertificate?_isSome_of_subset _ success
  intro form member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftSubset form leftMember
  · exact rightMember

/-- The four-way gradient selector used for a single boundary returns one of
the axis entries already present in the simultaneous eight-direction table. -/
theorem increasingDirection_mem_coordinateDirections
    (form : HermitianForm) (z : QI)
    (gradientNonzero : gradientX form z ≠ 0 ∨ gradientY form z ≠ 0) :
    (increasingDirection form z gradientNonzero).vector ∈
      coordinateDirections := by
  by_cases xZero : gradientX form z = 0
  · have yNonzero : gradientY form z ≠ 0 := by
      rcases gradientNonzero with xNonzero | yNonzero
      · exact (xNonzero xZero).elim
      · exact yNonzero
    by_cases yNegative : gradientY form z < 0
    · simp [increasingDirection, xZero, yNegative, coordinateDirections]
    · by_cases yPositive : 0 < gradientY form z
      · simp [increasingDirection, xZero, yNegative, yPositive,
          coordinateDirections]
      · have yZero : gradientY form z = 0 :=
          le_antisymm (le_of_not_gt yPositive) (le_of_not_gt yNegative)
        exact (yNonzero yZero).elim
  · by_cases xNegative : gradientX form z < 0
    · simp [increasingDirection, xZero, xNegative, coordinateDirections]
    · by_cases xPositive : 0 < gradientX form z
      · simp [increasingDirection, xZero, xNegative, xPositive,
          coordinateDirections]
      · have contradiction : gradientX form z = 0 :=
          le_antisymm (le_of_not_gt xPositive) (le_of_not_gt xNegative)
        exact (xZero contradiction).elim

/-- Hence the executable simultaneous direction table always succeeds for
one nondegenerate active boundary. -/
theorem tangentDirectionCertificate?_isSome_singleton
    (form : HermitianForm) (z : QI)
    (gradientNonzero : gradientX form z ≠ 0 ∨ gradientY form z ≠ 0) :
    (tangentDirectionCertificate? [form] z).isSome := by
  let direction := increasingDirection form z gradientNonzero
  apply tangentDirectionCertificate?_isSome_of_mem
    (increasingDirection_mem_coordinateDirections form z gradientNonzero)
  intro item member
  simp only [List.mem_singleton] at member
  subst item
  exact direction.slopePositive

/-- With no active boundary, the executable search succeeds vacuously. -/
theorem tangentDirectionCertificate?_isSome_empty (z : QI) :
    (tangentDirectionCertificate? [] z).isSome := by
  apply tangentDirectionCertificate?_isSome_of_mem
    (direction := ⟨1, 0⟩) (by simp [coordinateDirections])
  simp

theorem TangentDirection.normSq_le_one
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) :
    normSq direction.vector ≤ 1 :=
  direction.normSqLeOne

/-- Linear entry radius for one active oriented owner boundary. -/
def entryRadius (form : HermitianForm) (z direction : QI) : ℚ :=
  directionalSlope form z direction / (|form.radial| + 1)

theorem entryRadius_pos
    {form : HermitianForm} {z direction : QI}
    (slope : 0 < directionalSlope form z direction) :
    0 < entryRadius form z direction := by
  exact div_pos slope (by positivity)

/-- Positive finite minimum of all active owner-entry radii. -/
def boundaryRadius
    (forms : List HermitianForm) (z direction : QI) : ℚ :=
  FTA.Maximality.positiveMinimum
    (forms.map fun form => entryRadius form z direction)

theorem boundaryRadius_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) :
    0 < boundaryRadius forms z direction.vector := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, formMember, rfl⟩
  exact entryRadius_pos (direction.slopes form formMember)

theorem boundaryRadius_le_entryRadius
    {forms : List HermitianForm} {form : HermitianForm}
    (formMember : form ∈ forms) (z direction : QI) :
    boundaryRadius forms z direction ≤ entryRadius form z direction := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, formMember, rfl⟩

/-- Common radius for all active owner boundaries, all prior strict forms, and
the unit-step hypothesis of the quadratic perturbation bound. -/
def multiOwnerRadius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℚ :=
  min 1 (min (boundaryRadius forms z direction.vector)
    (strictRadius priors z direction.vector))

theorem multiOwnerRadius_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    0 < multiOwnerRadius direction priors := by
  apply lt_min zero_lt_one
  exact lt_min (boundaryRadius_pos direction)
    (strictRadius_pos priors z direction.vector priorNonzero)

def multiOwnerIndex
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℕ :=
  reciprocalIndex (multiOwnerRadius direction priors)

def multiOwnerEpsilon
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℚ :=
  1 / (multiOwnerIndex direction priors : ℕ)

theorem multiOwnerEpsilon_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) :
    0 < multiOwnerEpsilon direction priors := by
  apply div_pos zero_lt_one
  exact_mod_cast reciprocalIndex_pos (multiOwnerRadius direction priors)

theorem multiOwnerEpsilon_lt_radius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    multiOwnerEpsilon direction priors < multiOwnerRadius direction priors := by
  exact reciprocal_lt_radius
    (multiOwnerRadius_pos direction priors priorNonzero)

theorem multiOwnerEpsilon_le_one
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    multiOwnerEpsilon direction priors ≤ 1 := by
  exact (multiOwnerEpsilon_lt_radius direction priors priorNonzero).le.trans
    (min_le_left _ _)

/-- Any displayed positive lower bound for the common owner radius gives an
explicit lower bound for the executable reciprocal perturbation. -/
theorem radiusLower_div_three_lt_multiOwnerEpsilon
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    {radiusLower : ℚ} (_radiusLowerPositive : 0 < radiusLower)
    (radiusLowerLe : radiusLower ≤ multiOwnerRadius direction priors)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    radiusLower / 3 < multiOwnerEpsilon direction priors := by
  apply (div_le_div_of_nonneg_right radiusLowerLe (by norm_num)).trans_lt
  exact radius_div_three_lt_reciprocal
    (multiOwnerRadius_pos direction priors priorNonzero)
    (min_le_left _ _)

theorem multiOwnerEpsilon_lt_entryRadius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) {form : HermitianForm}
    (formMember : form ∈ forms) (priors : List HermitianForm)
    (priorNonzero : ∀ prior ∈ priors, prior.eval z ≠ 0) :
    multiOwnerEpsilon direction priors <
      entryRadius form z direction.vector := by
  apply (multiOwnerEpsilon_lt_radius direction priors priorNonzero).trans_le
  exact (min_le_right _ _).trans
    ((min_le_left _ _).trans
      (boundaryRadius_le_entryRadius formMember z direction.vector))

theorem multiOwnerEpsilon_lt_signRadius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z)
    {priors : List HermitianForm} {form : HermitianForm}
    (formMember : form ∈ priors)
    (priorNonzero : ∀ prior ∈ priors, prior.eval z ≠ 0) :
    multiOwnerEpsilon direction priors <
      signRadius form z direction.vector := by
  apply (multiOwnerEpsilon_lt_radius direction priors priorNonzero).trans_le
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      (strictRadius_le_signRadius formMember z direction.vector))

/-- One common rational step enters every active oriented owner side. -/
theorem enters_all_boundaries
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (onBoundaries : ∀ form ∈ forms, form.eval z = 0)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    ∀ form ∈ forms, 0 < form.eval (step z
      (multiOwnerEpsilon direction priors) direction.vector) := by
  intro form formMember
  apply eval_step_pos_of_normSq_le_one form z direction.vector
    direction.normSq_le_one (onBoundaries form formMember)
    (multiOwnerEpsilon_pos direction priors)
  exact multiOwnerEpsilon_lt_entryRadius direction formMember priors priorNonzero

/-! ## Entry from a controlled approximate boundary -/

/-- Residual tolerance for replacing exact simultaneous equalities by one
rational approximation.  Every entry has half of the positive linear margin
remaining after the worst quadratic error. -/
def approximateBoundaryBudget
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℚ :=
  let epsilon := multiOwnerEpsilon direction priors
  FTA.Maximality.positiveMinimum (forms.map fun form =>
    epsilon * (directionalSlope form z direction.vector -
      epsilon * |form.radial|))

theorem approximateBoundaryBudget_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    0 < approximateBoundaryBudget direction priors := by
  let epsilon := multiOwnerEpsilon direction priors
  apply FTA.Maximality.positiveMinimum_pos
  intro margin member
  rw [List.mem_map] at member
  rcases member with ⟨form, formMember, rfl⟩
  have epsilonPositive : 0 < epsilon := multiOwnerEpsilon_pos direction priors
  have epsilonSmall := multiOwnerEpsilon_lt_entryRadius direction formMember
    priors priorNonzero
  have denominatorPositive : 0 < |form.radial| + 1 := by positivity
  have scaled := (lt_div_iff₀ denominatorPositive).mp epsilonSmall
  exact mul_pos epsilonPositive (by nlinarith)

/-- Uniform lower bounds for the reciprocal perturbation and every entry
radius give a uniform lower bound for the approximate-boundary budget. -/
theorem mul_le_approximateBoundaryBudget_of_lower_bounds
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0)
    {epsilonLower boundaryLower : ℚ}
    (epsilonLowerLe : epsilonLower ≤
      multiOwnerEpsilon direction priors)
    (epsilonLowerAtMostOne : epsilonLower ≤ 1)
    (boundaryLowerNonnegative : 0 ≤ boundaryLower)
    (boundaryLowerAtMostOne : boundaryLower ≤ 1)
    (boundaryLowerLe : ∀ form ∈ forms,
      boundaryLower ≤ entryRadius form z direction.vector) :
    epsilonLower * boundaryLower ≤
      approximateBoundaryBudget direction priors := by
  apply FTA.Maximality.le_positiveMinimum
  · exact mul_le_one₀ epsilonLowerAtMostOne boundaryLowerNonnegative
      boundaryLowerAtMostOne
  · intro margin member
    rw [List.mem_map] at member
    rcases member with ⟨form, formMember, rfl⟩
    let epsilon := multiOwnerEpsilon direction priors
    let slope := directionalSlope form z direction.vector
    let radial := |form.radial|
    have epsilonNonnegative : 0 ≤ epsilon :=
      (multiOwnerEpsilon_pos direction priors).le
    have epsilonSmall := multiOwnerEpsilon_lt_entryRadius direction formMember
      priors priorNonzero
    have denominatorPositive : 0 < radial + 1 := by
      dsimp only [radial]
      positivity
    have entryIdentity : slope =
        entryRadius form z direction.vector * (radial + 1) := by
      dsimp only [slope, radial, entryRadius]
      field_simp
    have secondLower : entryRadius form z direction.vector ≤
        slope - epsilon * radial := by
      have epsilonLe := epsilonSmall.le
      rw [entryIdentity]
      nlinarith [abs_nonneg form.radial]
    have marginSecond : boundaryLower ≤ slope - epsilon * radial :=
      (boundaryLowerLe form formMember).trans secondLower
    exact mul_le_mul epsilonLowerLe marginSecond boundaryLowerNonnegative
      epsilonNonnegative

theorem approximateBoundaryBudget_le_margin
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    {form : HermitianForm} (formMember : form ∈ forms) :
    approximateBoundaryBudget direction priors ≤
      multiOwnerEpsilon direction priors *
        (directionalSlope form z direction.vector -
          multiOwnerEpsilon direction priors * |form.radial|) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, formMember, rfl⟩

/-- A sufficiently accurate rational approximation enters every active
owner side under the same finite reciprocal step as the exact-boundary
construction. -/
theorem enters_all_boundaries_of_residual
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0)
    (residualSmall : ∀ form ∈ forms,
      |form.eval z| < approximateBoundaryBudget direction priors) :
    ∀ form ∈ forms, 0 < form.eval (step z
      (multiOwnerEpsilon direction priors) direction.vector) := by
  intro form formMember
  apply eval_step_pos_of_abs_eval_lt_of_normSq_le_one form z direction.vector
    direction.normSq_le_one
    (multiOwnerEpsilon_pos direction priors)
    (multiOwnerEpsilon_lt_entryRadius direction formMember priors priorNonzero)
  exact (residualSmall form formMember).trans_le
    (approximateBoundaryBudget_le_margin direction priors formMember)

/-- The same step preserves the sign of every earlier strict form. -/
theorem preserves_all_priors
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    ∀ form ∈ priors, 0 < form.eval z * form.eval (step z
      (multiOwnerEpsilon direction priors) direction.vector) := by
  intro form formMember
  apply eval_mul_pos_of_lt_signRadius_normSq_le_one form z direction.vector
    direction.normSq_le_one
    (multiOwnerEpsilon_pos direction priors)
    (multiOwnerEpsilon_le_one direction priors priorNonzero)
  exact multiOwnerEpsilon_lt_signRadius direction formMember priorNonzero

/-! ## Rational-box tangent constraints -/

def boxXLowerForm (box : RatBox) : HermitianForm := ⟨0, 1, 0, -box.xLower⟩
def boxXUpperForm (box : RatBox) : HermitianForm := ⟨0, -1, 0, box.xUpper⟩
def boxYLowerForm (box : RatBox) : HermitianForm := ⟨0, 0, 1, -box.yLower⟩
def boxYUpperForm (box : RatBox) : HermitianForm := ⟨0, 0, -1, box.yUpper⟩

def boxForms (box : RatBox) : List HermitianForm :=
  [boxXLowerForm box, boxXUpperForm box, boxYLowerForm box, boxYUpperForm box]

@[simp] theorem eval_boxXLowerForm (box : RatBox) (z : QI) :
    (boxXLowerForm box).eval z = z.re - box.xLower := by
  simp [boxXLowerForm, HermitianForm.eval]
  ring

@[simp] theorem eval_boxXUpperForm (box : RatBox) (z : QI) :
    (boxXUpperForm box).eval z = box.xUpper - z.re := by
  simp [boxXUpperForm, HermitianForm.eval]
  ring

@[simp] theorem eval_boxYLowerForm (box : RatBox) (z : QI) :
    (boxYLowerForm box).eval z = z.im - box.yLower := by
  simp [boxYLowerForm, HermitianForm.eval]
  ring

@[simp] theorem eval_boxYUpperForm (box : RatBox) (z : QI) :
    (boxYUpperForm box).eval z = box.yUpper - z.im := by
  simp [boxYUpperForm, HermitianForm.eval]
  ring

theorem box_contains_of_all_forms_pos {box : RatBox} {z : QI}
    (positive : ∀ form ∈ boxForms box, 0 < form.eval z) :
    box.Contains z := by
  have xLower := positive (boxXLowerForm box) (by simp [boxForms])
  have xUpper := positive (boxXUpperForm box) (by simp [boxForms])
  have yLower := positive (boxYLowerForm box) (by simp [boxForms])
  have yUpper := positive (boxYUpperForm box) (by simp [boxForms])
  simp only [eval_boxXLowerForm] at xLower
  simp only [eval_boxXUpperForm] at xUpper
  simp only [eval_boxYLowerForm] at yLower
  simp only [eval_boxYUpperForm] at yUpper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- If every inward box form is either an active equality or an earlier
strict positive form, the simultaneous owner step remains in the box. -/
theorem multiOwner_step_mem_box
    {forms : List HermitianForm} {priors : List HermitianForm}
    {z : QI} (direction : TangentDirection forms z)
    (onBoundaries : ∀ form ∈ forms, form.eval z = 0)
    (priorPositive : ∀ form ∈ priors, 0 < form.eval z)
    (box : RatBox)
    (boxCovered : ∀ form ∈ boxForms box, form ∈ forms ∨ form ∈ priors) :
    box.Contains (step z (multiOwnerEpsilon direction priors)
      direction.vector) := by
  have priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0 := by
    intro form member
    exact (priorPositive form member).ne'
  have entered := enters_all_boundaries direction priors onBoundaries priorNonzero
  have preserved := preserves_all_priors direction priors priorNonzero
  apply box_contains_of_all_forms_pos
  intro form formMember
  rcases boxCovered form formMember with active | prior
  · exact entered form active
  · have product := preserved form prior
    rcases mul_pos_iff.mp product with signs | signs
    · exact signs.2
    · exact (not_lt_of_ge (priorPositive form prior).le signs.1).elim

/-- Approximate-boundary box variant.  In localization applications the
rational anchor is already strictly inside the later box, so all four inward
box forms belong to the protected prior list rather than the active list. -/
theorem multiOwner_step_mem_box_of_strict_priors
    {forms priors : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0)
    (box : RatBox)
    (boxPositive : ∀ form ∈ boxForms box, 0 < form.eval z)
    (boxCovered : ∀ form ∈ boxForms box, form ∈ priors) :
    box.Contains (step z (multiOwnerEpsilon direction priors)
      direction.vector) := by
  have preserved := preserves_all_priors direction priors priorNonzero
  apply box_contains_of_all_forms_pos
  intro form formMember
  have prior := boxCovered form formMember
  have product := preserved form prior
  rcases mul_pos_iff.mp product with signs | signs
  · exact signs.2
  · exact (not_lt_of_ge (boxPositive form formMember).le signs.1).elim

end CCLMultiOwnerGrid
end FTA
