import FTA.CCLMultiOwnerGrid

/-!
# Quantitative stability of finite tangent directions

The event curve and the represented coupled-track sample are computed
independently.  This module supplies the local continuity calculation needed
to reuse one successful finite-table tangent direction at a nearby rational
base.  Every radius is a finite rational expression in the displayed forms,
point, and certificate; no compactness or limiting point is used.
-/

namespace FTA
namespace CCLTangentStability

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid
open FTA.Maximality

abbrev QI := CCL.GaussianRat

/-- Coordinate `L¹` distance used by the linear gradient estimate. -/
def coordinateDistance (left right : QI) : ℚ :=
  |left.re - right.re| + |left.im - right.im|

theorem coordinateDistance_nonneg (left right : QI) :
    0 ≤ coordinateDistance left right := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem abs_re_le_one_of_normSq_le_one
    {direction : QI} (normLe : normSq direction ≤ 1) :
    |direction.re| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  dsimp only [normSq] at normLe
  nlinarith [sq_nonneg direction.im]

theorem abs_im_le_one_of_normSq_le_one
    {direction : QI} (normLe : normSq direction ≤ 1) :
    |direction.im| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  dsimp only [normSq] at normLe
  nlinarith [sq_nonneg direction.re]

/-- Exact affine variation of a directional derivative as its base point
moves. -/
theorem directionalSlope_sub
    (form : HermitianForm) (left right direction : QI) :
    directionalSlope form left direction -
        directionalSlope form right direction =
      2 * form.radial *
        ((left.re - right.re) * direction.re +
          (left.im - right.im) * direction.im) := by
  simp only [directionalSlope, gradientX, gradientY]
  ring

/-- A deliberately positive coefficient for directional-slope variation. -/
def slopeVariationCoefficient (form : HermitianForm) : ℚ :=
  2 * |form.radial| + 1

theorem slopeVariationCoefficient_pos (form : HermitianForm) :
    0 < slopeVariationCoefficient form := by
  unfold slopeVariationCoefficient
  positivity

/-- A unit-bounded rational direction changes slope by at most a computed
multiple of coordinate distance. -/
theorem abs_directionalSlope_sub_le
    (form : HermitianForm) (left right direction : QI)
    (normLe : normSq direction ≤ 1) :
    |directionalSlope form left direction -
        directionalSlope form right direction| ≤
      slopeVariationCoefficient form * coordinateDistance left right := by
  rw [directionalSlope_sub, abs_mul, abs_mul]
  have directionRe := abs_re_le_one_of_normSq_le_one normLe
  have directionIm := abs_im_le_one_of_normSq_le_one normLe
  have realScaled :
      |left.re - right.re| * |direction.re| ≤ |left.re - right.re| := by
    simpa only [_root_.mul_one] using mul_le_mul_of_nonneg_left directionRe
      (abs_nonneg (left.re - right.re))
  have imagScaled :
      |left.im - right.im| * |direction.im| ≤ |left.im - right.im| := by
    simpa only [_root_.mul_one] using mul_le_mul_of_nonneg_left directionIm
      (abs_nonneg (left.im - right.im))
  have inner :
      |(left.re - right.re) * direction.re +
          (left.im - right.im) * direction.im| ≤
        coordinateDistance left right := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add realScaled imagScaled
  have radial :
      |(2 : ℚ)| * |form.radial| *
          |(left.re - right.re) * direction.re +
            (left.im - right.im) * direction.im| ≤
        (2 * |form.radial|) * coordinateDistance left right := by
    norm_num
    exact mul_le_mul_of_nonneg_left inner
      (mul_nonneg (by norm_num) (abs_nonneg form.radial))
  apply radial.trans
  unfold slopeVariationCoefficient
  exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg form.radial])
    (coordinateDistance_nonneg left right)

/-- A positive whole-box upper bound for the perturbation majorant of one
Hermitian form along any direction of squared norm at most one. -/
def boxPerturbationMajorant (form : HermitianForm) (box : RatBox) : ℚ :=
  max 1 ((2 * |form.radial| + 1) * (2 * box.coordinateRadius) +
    |form.realLinear| + |form.imagLinear| + |form.radial|)

theorem boxPerturbationMajorant_pos
    (form : HermitianForm) (box : RatBox) :
    0 < boxPerturbationMajorant form box :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem perturbationMajorant_le_boxPerturbationMajorant
    (form : HermitianForm) {box : RatBox} {z direction : QI}
    (inside : box.Contains z) (normLe : normSq direction ≤ 1) :
    perturbationMajorant form z direction ≤
      boxPerturbationMajorant form box := by
  have coordinates := box.abs_coordinates_le_radius inside
  have distanceLe : coordinateDistance z 0 ≤ 2 * box.coordinateRadius := by
    unfold coordinateDistance
    simp only [zero_re, zero_im, _root_.sub_zero]
    linarith
  have variation := abs_directionalSlope_sub_le form z 0 direction normLe
  have variationLe :
      |directionalSlope form z direction -
          directionalSlope form 0 direction| ≤
        (2 * |form.radial| + 1) * (2 * box.coordinateRadius) :=
    variation.trans (mul_le_mul_of_nonneg_left distanceLe
      (slopeVariationCoefficient_pos form).le)
  have directionRe := abs_re_le_one_of_normSq_le_one normLe
  have directionIm := abs_im_le_one_of_normSq_le_one normLe
  have realScaled : |form.realLinear| * |direction.re| ≤
      |form.realLinear| := by
    simpa only [_root_.mul_one] using
      (mul_le_mul_of_nonneg_left directionRe
        (abs_nonneg form.realLinear))
  have imagScaled : |form.imagLinear| * |direction.im| ≤
      |form.imagLinear| := by
    simpa only [_root_.mul_one] using
      (mul_le_mul_of_nonneg_left directionIm
        (abs_nonneg form.imagLinear))
  have zeroSlope : directionalSlope form 0 direction =
      form.realLinear * direction.re + form.imagLinear * direction.im := by
    simp [directionalSlope, gradientX, gradientY]
  have zeroSlopeLe : |directionalSlope form 0 direction| ≤
      |form.realLinear| + |form.imagLinear| := by
    rw [zeroSlope]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add realScaled imagScaled
  have slopeLe : |directionalSlope form z direction| ≤
      (2 * |form.radial| + 1) * (2 * box.coordinateRadius) +
        |form.realLinear| + |form.imagLinear| := by
    have triangle := abs_add_le
      (directionalSlope form z direction -
        directionalSlope form 0 direction)
      (directionalSlope form 0 direction)
    have identity : directionalSlope form z direction -
          directionalSlope form 0 direction +
          directionalSlope form 0 direction =
        directionalSlope form z direction := by ring
    rw [identity] at triangle
    calc
      |directionalSlope form z direction| ≤
          |directionalSlope form z direction -
            directionalSlope form 0 direction| +
            |directionalSlope form 0 direction| := triangle
      _ ≤ (2 * |form.radial| + 1) * (2 * box.coordinateRadius) +
          (|form.realLinear| + |form.imagLinear|) :=
        add_le_add variationLe zeroSlopeLe
      _ = (2 * |form.radial| + 1) * (2 * box.coordinateRadius) +
          |form.realLinear| + |form.imagLinear| := by ring
  unfold perturbationMajorant boxPerturbationMajorant
  apply max_le_max le_rfl
  linarith

/-- One positive finite upper bound for all prior-form perturbation
majorants in a rational box. -/
def priorPerturbationUpper (priors : List HermitianForm) (box : RatBox) : ℚ :=
  1 + (priors.map fun form => boxPerturbationMajorant form box).sum

theorem priorPerturbationUpper_pos
    (priors : List HermitianForm) (box : RatBox) :
    0 < priorPerturbationUpper priors box := by
  have sumNonnegative : 0 ≤
      (priors.map fun form => boxPerturbationMajorant form box).sum := by
    apply List.sum_nonneg
    intro value member
    rw [List.mem_map] at member
    rcases member with ⟨form, _formMember, rfl⟩
    exact (boxPerturbationMajorant_pos form box).le
  unfold priorPerturbationUpper
  linarith

theorem boxPerturbationMajorant_le_priorPerturbationUpper
    {priors : List HermitianForm} {form : HermitianForm}
    (member : form ∈ priors) (box : RatBox) :
    boxPerturbationMajorant form box ≤ priorPerturbationUpper priors box := by
  have singleLe : boxPerturbationMajorant form box ≤
      (priors.map fun item => boxPerturbationMajorant item box).sum := by
    apply List.single_le_sum
    · intro value valueMember
      rw [List.mem_map] at valueMember
      rcases valueMember with ⟨item, _itemMember, rfl⟩
      exact (boxPerturbationMajorant_pos item box).le
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold priorPerturbationUpper
  linarith

/-- Uniform lower bound for the strict-sign radius when all displayed prior
evaluations share one positive absolute-value margin. -/
def priorRadiusLower
    (priors : List HermitianForm) (box : RatBox) (evaluationLower : ℚ) : ℚ :=
  min 1 (evaluationLower / priorPerturbationUpper priors box)

theorem priorRadiusLower_pos
    (priors : List HermitianForm) (box : RatBox) {evaluationLower : ℚ}
    (evaluationLowerPositive : 0 < evaluationLower) :
    0 < priorRadiusLower priors box evaluationLower := by
  exact lt_min zero_lt_one
    (div_pos evaluationLowerPositive
      (priorPerturbationUpper_pos priors box))

theorem priorRadiusLower_le_one
    (priors : List HermitianForm) (box : RatBox) (evaluationLower : ℚ) :
    priorRadiusLower priors box evaluationLower ≤ 1 :=
  min_le_left _ _

theorem priorRadiusLower_le_strictRadius
    {priors : List HermitianForm} {box : RatBox} {z direction : QI}
    {evaluationLower : ℚ}
    (inside : box.Contains z) (normLe : normSq direction ≤ 1)
    (evaluationLowerLe : ∀ form ∈ priors,
      evaluationLower ≤ |form.eval z|) :
    priorRadiusLower priors box evaluationLower ≤
      strictRadius priors z direction := by
  apply FTA.Maximality.le_positiveMinimum
    (priorRadiusLower_le_one priors box evaluationLower)
  intro radius radiusMember
  rw [List.mem_map] at radiusMember
  rcases radiusMember with ⟨form, formMember, rfl⟩
  apply (min_le_right _ _).trans
  unfold signRadius
  calc
    evaluationLower / priorPerturbationUpper priors box ≤
        |form.eval z| / priorPerturbationUpper priors box :=
      div_le_div_of_nonneg_right (evaluationLowerLe form formMember)
        (priorPerturbationUpper_pos priors box).le
    _ ≤ |form.eval z| / perturbationMajorant form z direction := by
      apply div_le_div_of_nonneg_left (abs_nonneg _)
        (perturbationMajorant_pos form z direction)
      exact (perturbationMajorant_le_boxPerturbationMajorant form inside
        normLe).trans
        (boxPerturbationMajorant_le_priorPerturbationUpper formMember box)

/-- Positive radius on which every form keeps the displayed certificate's
strictly positive slope. -/
def tangentStabilityRadius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) : ℚ :=
  FTA.Maximality.positiveMinimum (forms.map fun form =>
    directionalSlope form z direction.vector /
      (2 * slopeVariationCoefficient form))

theorem tangentStabilityRadius_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) :
    0 < tangentStabilityRadius direction := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, formMember, rfl⟩
  exact div_pos (direction.slopes form formMember)
    (mul_pos (by norm_num) (slopeVariationCoefficient_pos form))

theorem tangentStabilityRadius_le_form
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) {form : HermitianForm}
    (member : form ∈ forms) :
    tangentStabilityRadius direction ≤
      directionalSlope form z direction.vector /
        (2 * slopeVariationCoefficient form) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, member, rfl⟩

/-- The same vector is a tangent certificate at every point in the computed
stability neighborhood. -/
def TangentDirection.atNearby
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (w : QI)
    (near : coordinateDistance w z < tangentStabilityRadius direction) :
    TangentDirection forms w where
  vector := direction.vector
  normSqLeOne := direction.normSqLeOne
  slopes := by
    intro form member
    have slopePositive := direction.slopes form member
    have radiusForm := near.trans_le
      (tangentStabilityRadius_le_form direction member)
    have coefficientPositive := slopeVariationCoefficient_pos form
    have scaled : slopeVariationCoefficient form * coordinateDistance w z <
        directionalSlope form z direction.vector / 2 := by
      have multiplied := (lt_div_iff₀
        (mul_pos (by norm_num) coefficientPositive)).mp radiusForm
      nlinarith
    have variation := abs_directionalSlope_sub_le form w z direction.vector
      direction.normSqLeOne
    have absolute :
        |directionalSlope form w direction.vector -
            directionalSlope form z direction.vector| <
          directionalSlope form z direction.vector := by
      have halfLt : directionalSlope form z direction.vector / 2 <
          directionalSlope form z direction.vector := by
        linarith
      exact variation.trans_lt (lt_trans scaled halfLt)
    have lower := neg_abs_le
      (directionalSlope form w direction.vector -
        directionalSlope form z direction.vector)
    linarith

/-- Nearby stability also permits discarding obligations or repeating forms;
only membership in the reference support matters. -/
def TangentDirection.atNearbySubset
    {supporting forms : List HermitianForm} {z : QI}
    (direction : TangentDirection supporting z) (w : QI)
    (near : coordinateDistance w z < tangentStabilityRadius direction)
    (subset : ∀ form ∈ forms, form ∈ supporting) :
    TangentDirection forms w where
  vector := direction.vector
  normSqLeOne := direction.normSqLeOne
  slopes := by
    intro form member
    exact (FTA.CCLTangentStability.TangentDirection.atNearby
      direction w near).slopes form (subset form member)

/-- Executable-table certificates therefore persist at every point in the
same computed neighborhood. -/
theorem tangentDirectionCertificate?_isSome_atNearby
    {forms : List HermitianForm} {z w : QI}
    {direction : TangentDirection forms z}
    (search : tangentDirectionCertificate? forms z = some direction)
    (near : coordinateDistance w z < tangentStabilityRadius direction) :
    (tangentDirectionCertificate? forms w).isSome := by
  have member : direction.vector ∈ coordinateDirections := by
    unfold tangentDirectionCertificate? at search
    split at search
    · contradiction
    · rename_i vector found
      have vectorMember := tangentDirection?_some_mem found
      cases search
      exact vectorMember
  apply tangentDirectionCertificate?_isSome_of_mem member
  exact (FTA.CCLTangentStability.TangentDirection.atNearby
    direction w near).slopes

/-- Executable form of nearby stability with a changed active list. -/
theorem tangentDirectionCertificate?_isSome_atNearby_of_subset
    {supporting forms : List HermitianForm} {z w : QI}
    {direction : TangentDirection supporting z}
    (search : tangentDirectionCertificate? supporting z = some direction)
    (near : coordinateDistance w z < tangentStabilityRadius direction)
    (subset : ∀ form ∈ forms, form ∈ supporting) :
    (tangentDirectionCertificate? forms w).isSome := by
  apply tangentDirectionCertificate?_isSome_of_subset subset
  exact tangentDirectionCertificate?_isSome_atNearby search near

end CCLTangentStability
end FTA
