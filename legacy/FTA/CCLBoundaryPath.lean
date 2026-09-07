import FTA.ProjectivePath
import FTA.CCLGeometry

/-!
# Polynomial paths for CCL branch boundaries

This module turns the projective parametrizations from Section 10.1 into the
dense one-variable polynomial paths consumed by `FTA.ProjectivePath`.  It
covers the unit and scaled norm circles, both coordinate-boundary lines, and
their inverse images under a finite decoder homography.
-/

namespace FTA
namespace CCLBoundaryPath

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.CCLGeometry
open FTA.ProjectivePath

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

private def qi (re im : ℚ) : QI := ⟨re, im⟩

/-- Polynomial homogeneous form of equation (17). -/
def unitCirclePath : Path where
  numerator := ⟨[qi (-1) 0, qi 0 2, qi 1 0]⟩
  denominator := ⟨[qi 1 0, qi 0 0, qi 1 0]⟩

theorem unitCirclePath_projective (t : ℚ) :
    (⟨unitCirclePath.numerator.eval (PathPolynomial.ofRat t),
      unitCirclePath.denominator.eval (PathPolynomial.ofRat t)⟩ : Proj QI) =
      unitCircleProjective (Proj.affine t) := by
  ext <;>
    simp [unitCirclePath, qi, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat, unitCircleProjective, Proj.affine] <;>
    ring

theorem unitCirclePath_denominator (t : ℚ) :
    unitCirclePath.denominator.eval (PathPolynomial.ofRat t) = qi (1 + t ^ 2) 0 := by
  apply GaussianRat.ext
  · simp [unitCirclePath, qi, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat]
    ring
  · simp [unitCirclePath, qi, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat]

theorem unitCirclePath_denominator_ne (t : ℚ) :
    unitCirclePath.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  rw [unitCirclePath_denominator]
  intro hzero
  have hre := congrArg GaussianRat.re hzero
  dsimp [qi] at hre
  nlinarith [sq_nonneg t]

/-- The primary homogeneous circle pair has a uniform rational norm floor.
The denominator alone already supplies it. -/
theorem unitCirclePath_homogeneousNorm_one_le (t : ℚ) :
    1 ≤
      normSq (unitCirclePath.numerator.eval (PathPolynomial.ofRat t)) +
        normSq (unitCirclePath.denominator.eval
          (PathPolynomial.ofRat t)) := by
  have denominatorLower : 1 ≤
      normSq (unitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)) := by
    rw [unitCirclePath_denominator]
    dsimp only [qi, normSq]
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
  nlinarith [normSq_nonneg
    (unitCirclePath.numerator.eval (PathPolynomial.ofRat t))]

theorem unitCirclePath_value (t : ℚ) : unitCirclePath.value t = unitCircleParam t := by
  rw [Path.value]
  have hprojective := unitCirclePath_projective t
  have hp : unitCirclePath.numerator.eval (PathPolynomial.ofRat t) =
      (unitCircleProjective (Proj.affine t)).p := congrArg Proj.p hprojective
  have hq : unitCirclePath.denominator.eval (PathPolynomial.ofRat t) =
      (unitCircleProjective (Proj.affine t)).q := congrArg Proj.q hprojective
  rw [hp, hq]
  rw [← inv_eq, ← div_eq_mul_inv]
  have hden : (unitCircleProjective (Proj.affine t)).q ≠ 0 := by
    rw [← hq]
    exact unitCirclePath_denominator_ne t
  apply (div_eq_iff hden).2
  simpa only [Proj.Equivalent, Proj.affine, mul_one] using
    unitCircleProjective_affine t

/-! ## Reciprocal chart for the missing projective parameter -/

/-- Affine reciprocal chart `[1:t]` of the same projective unit circle.  Its
parameter `t = 0` is the point omitted by the primary `[t:1]` chart. -/
def reciprocalUnitCircleParam (t : ℚ) : QI :=
  ⟨(t ^ 2 - 1) / (1 + t ^ 2), (2 * t) / (1 + t ^ 2)⟩

theorem normSq_reciprocalUnitCircleParam (t : ℚ) :
    normSq (reciprocalUnitCircleParam t) = 1 := by
  have denominatorNonzero : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  simp only [normSq, reciprocalUnitCircleParam]
  field_simp [denominatorNonzero]
  ring

/-- Polynomial homogeneous path for the reciprocal unit-circle chart. -/
def reciprocalUnitCirclePath : Path where
  numerator := ⟨[qi 1 0, qi 0 2, qi (-1) 0]⟩
  denominator := ⟨[qi 1 0, qi 0 0, qi 1 0]⟩

theorem reciprocalUnitCirclePath_projective (t : ℚ) :
    (⟨reciprocalUnitCirclePath.numerator.eval (PathPolynomial.ofRat t),
      reciprocalUnitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)⟩ : Proj QI) =
      unitCircleProjective (reciprocalAffine t) := by
  apply Proj.ext <;>
    apply GaussianRat.ext <;>
    simp [reciprocalUnitCirclePath, unitCircleProjective, reciprocalAffine,
      qi, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat] <;>
    ring

theorem reciprocalUnitCirclePath_denominator (t : ℚ) :
    reciprocalUnitCirclePath.denominator.eval (PathPolynomial.ofRat t) =
      qi (1 + t ^ 2) 0 := by
  apply GaussianRat.ext
  · simp [reciprocalUnitCirclePath, qi, DensePolynomial.eval,
      DensePolynomial.evalCoeffs, PathPolynomial.ofRat]
    ring
  · simp [reciprocalUnitCirclePath, qi, DensePolynomial.eval,
      DensePolynomial.evalCoeffs, PathPolynomial.ofRat]

theorem reciprocalUnitCirclePath_denominator_ne (t : ℚ) :
    reciprocalUnitCirclePath.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  rw [reciprocalUnitCirclePath_denominator]
  intro zero
  have realZero := congrArg GaussianRat.re zero
  dsimp [qi] at realZero
  nlinarith [sq_nonneg t]

/-- Reciprocal homogeneous circle chart counterpart of the same norm floor. -/
theorem reciprocalUnitCirclePath_homogeneousNorm_one_le (t : ℚ) :
    1 ≤
      normSq (reciprocalUnitCirclePath.numerator.eval
        (PathPolynomial.ofRat t)) +
        normSq (reciprocalUnitCirclePath.denominator.eval
          (PathPolynomial.ofRat t)) := by
  have denominatorLower : 1 ≤
      normSq (reciprocalUnitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)) := by
    rw [reciprocalUnitCirclePath_denominator]
    dsimp only [qi, normSq]
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
  nlinarith [normSq_nonneg
    (reciprocalUnitCirclePath.numerator.eval (PathPolynomial.ofRat t))]

theorem reciprocalUnitCirclePath_value (t : ℚ) :
    reciprocalUnitCirclePath.value t = reciprocalUnitCircleParam t := by
  rw [Path.value]
  have inverseDenominator : inv (qi (1 + t ^ 2) 0) =
      qi (1 / (1 + t ^ 2)) 0 := by
    have denominatorNonzero : 1 + t ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg t]
    apply GaussianRat.ext
    · simp [inv, qi, normSq]
      field_simp [denominatorNonzero]
    · simp [inv, qi, normSq]
  rw [reciprocalUnitCirclePath_denominator, inverseDenominator]
  apply GaussianRat.ext <;>
    simp [reciprocalUnitCirclePath, reciprocalUnitCircleParam, qi,
      DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat] <;>
    ring

/-- Replacing a nonzero primary parameter by its reciprocal gives the same
unit-circle point in the reciprocal chart. -/
theorem unitCircleParam_eq_reciprocalUnitCircleParam_inv
    {t : ℚ} (nonzero : t ≠ 0) :
    unitCircleParam t = reciprocalUnitCircleParam (1 / t) := by
  have primaryDenominator : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have reciprocalDenominator : 1 + (1 / t) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (1 / t)]
  apply GaussianRat.ext <;>
    simp only [unitCircleParam, reciprocalUnitCircleParam] <;>
    unfold unitCircleDenominator <;>
    field_simp [nonzero, primaryDenominator, reciprocalDenominator] <;>
    ring

/-- Multiply the homogeneous numerator of a polynomial path by a Gaussian
scale. -/
def scalePath (scaleValue : QI) (path : Path) : Path where
  numerator := DensePolynomial.scale scaleValue path.numerator
  denominator := path.denominator

theorem scalePath_projective (scaleValue : QI) (path : Path) (t : ℚ) :
    (⟨(scalePath scaleValue path).numerator.eval (PathPolynomial.ofRat t),
      (scalePath scaleValue path).denominator.eval (PathPolynomial.ofRat t)⟩ : Proj QI) =
      ⟨scaleValue * path.numerator.eval (PathPolynomial.ofRat t),
        path.denominator.eval (PathPolynomial.ofRat t)⟩ := by
  ext <;> simp [scalePath, eval_scale]

/-- Polynomial parametrization of the circle of norm `N(scaleValue)`. -/
def scaledCirclePath (scaleValue : QI) : Path := scalePath scaleValue unitCirclePath

/-- Scaling the circle numerator leaves the homogeneous denominator floor
unchanged. -/
theorem scaledCirclePath_homogeneousNorm_one_le
    (scaleValue : QI) (t : ℚ) :
    1 ≤
      normSq ((scaledCirclePath scaleValue).numerator.eval
        (PathPolynomial.ofRat t)) +
        normSq ((scaledCirclePath scaleValue).denominator.eval
          (PathPolynomial.ofRat t)) := by
  have denominatorLower : 1 ≤
      normSq ((scaledCirclePath scaleValue).denominator.eval
        (PathPolynomial.ofRat t)) := by
    simpa [scaledCirclePath, scalePath] using (show 1 ≤
      normSq (unitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)) from by
          rw [unitCirclePath_denominator]
          dsimp only [qi, normSq]
          nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)])
  nlinarith [normSq_nonneg
    ((scaledCirclePath scaleValue).numerator.eval
      (PathPolynomial.ofRat t))]

theorem scaledCirclePath_projective (scaleValue : QI) (t : ℚ) :
    (⟨(scaledCirclePath scaleValue).numerator.eval (PathPolynomial.ofRat t),
      (scaledCirclePath scaleValue).denominator.eval (PathPolynomial.ofRat t)⟩ : Proj QI) =
      scaledCircleProjective scaleValue (Proj.affine t) := by
  rw [scaledCirclePath, scalePath_projective]
  have hprojective := unitCirclePath_projective t
  have hp : unitCirclePath.numerator.eval (PathPolynomial.ofRat t) =
      (unitCircleProjective (Proj.affine t)).p := congrArg Proj.p hprojective
  have hq : unitCirclePath.denominator.eval (PathPolynomial.ofRat t) =
      (unitCircleProjective (Proj.affine t)).q := congrArg Proj.q hprojective
  rw [scaledCircleProjective]
  apply Proj.ext
  · exact congrArg (scaleValue * ·) hp
  · exact hq

theorem scaledCirclePath_value (scaleValue : QI) (t : ℚ) :
    (scaledCirclePath scaleValue).value t = scaleValue * unitCircleParam t := by
  rw [Path.value]
  change (DensePolynomial.scale scaleValue unitCirclePath.numerator).eval
      (PathPolynomial.ofRat t) *
      inv (unitCirclePath.denominator.eval (PathPolynomial.ofRat t)) = _
  rw [eval_scale, mul_assoc]
  change scaleValue * unitCirclePath.value t = _
  rw [unitCirclePath_value]

/-- Scaled reciprocal chart of the same norm circle. -/
def reciprocalScaledCirclePath (scaleValue : QI) : Path :=
  scalePath scaleValue reciprocalUnitCirclePath

/-- Reciprocal scaled-circle charts retain the same homogeneous floor. -/
theorem reciprocalScaledCirclePath_homogeneousNorm_one_le
    (scaleValue : QI) (t : ℚ) :
    1 ≤
      normSq ((reciprocalScaledCirclePath scaleValue).numerator.eval
        (PathPolynomial.ofRat t)) +
        normSq ((reciprocalScaledCirclePath scaleValue).denominator.eval
          (PathPolynomial.ofRat t)) := by
  have denominatorLower : 1 ≤
      normSq ((reciprocalScaledCirclePath scaleValue).denominator.eval
        (PathPolynomial.ofRat t)) := by
    simpa [reciprocalScaledCirclePath, scalePath] using (show 1 ≤
      normSq (reciprocalUnitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)) from by
          rw [reciprocalUnitCirclePath_denominator]
          dsimp only [qi, normSq]
          nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)])
  nlinarith [normSq_nonneg
    ((reciprocalScaledCirclePath scaleValue).numerator.eval
      (PathPolynomial.ofRat t))]

theorem reciprocalScaledCirclePath_projective (scaleValue : QI) (t : ℚ) :
    (⟨(reciprocalScaledCirclePath scaleValue).numerator.eval
        (PathPolynomial.ofRat t),
      (reciprocalScaledCirclePath scaleValue).denominator.eval
        (PathPolynomial.ofRat t)⟩ : Proj QI) =
      scaledCircleProjective scaleValue (reciprocalAffine t) := by
  rw [reciprocalScaledCirclePath, scalePath_projective]
  have projective := reciprocalUnitCirclePath_projective t
  have numerator :
      reciprocalUnitCirclePath.numerator.eval (PathPolynomial.ofRat t) =
        (unitCircleProjective (reciprocalAffine t)).p :=
    congrArg Proj.p projective
  have denominator :
      reciprocalUnitCirclePath.denominator.eval (PathPolynomial.ofRat t) =
        (unitCircleProjective (reciprocalAffine t)).q :=
    congrArg Proj.q projective
  rw [scaledCircleProjective]
  apply Proj.ext
  · exact congrArg (scaleValue * ·) numerator
  · exact denominator

theorem reciprocalScaledCirclePath_value (scaleValue : QI) (t : ℚ) :
    (reciprocalScaledCirclePath scaleValue).value t =
      scaleValue * reciprocalUnitCircleParam t := by
  rw [Path.value]
  change (DensePolynomial.scale scaleValue
      reciprocalUnitCirclePath.numerator).eval (PathPolynomial.ofRat t) *
      inv (reciprocalUnitCirclePath.denominator.eval
        (PathPolynomial.ofRat t)) = _
  rw [eval_scale, mul_assoc]
  change scaleValue * reciprocalUnitCirclePath.value t = _
  rw [reciprocalUnitCirclePath_value]

/-- Polynomial homogeneous form of the affine line `base + t*direction`. -/
def linePath (base direction : QI) : Path where
  numerator := ⟨[direction, base]⟩
  denominator := constant 1

theorem linePath_numerator (base direction : QI) (t : ℚ) :
    (linePath base direction).numerator.eval (PathPolynomial.ofRat t) =
      base + CCLGeometry.ofRat t * direction := by
  apply GaussianRat.ext <;>
    simp [linePath, DensePolynomial.eval, DensePolynomial.evalCoeffs,
      PathPolynomial.ofRat, CCLGeometry.ofRat] <;>
    ring

theorem linePath_denominator (base direction : QI) (t : ℚ) :
    (linePath base direction).denominator.eval (PathPolynomial.ofRat t) = 1 := by
  simp [linePath]

theorem linePath_projective (base direction : QI) (t : ℚ) :
    (⟨(linePath base direction).numerator.eval (PathPolynomial.ofRat t),
      (linePath base direction).denominator.eval (PathPolynomial.ofRat t)⟩ : Proj QI) =
      projectiveLine base direction (Proj.affine t) := by
  rw [projectiveLine_affine]
  apply Proj.ext
  · exact linePath_numerator base direction t
  · exact linePath_denominator base direction t

theorem linePath_denominator_ne (base direction : QI) (t : ℚ) :
    (linePath base direction).denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  simp [linePath]

/-- Every affine line chart has homogeneous norm at least one because its
projective denominator is the constant one. -/
theorem linePath_homogeneousNorm_one_le
    (base direction : QI) (t : ℚ) :
    1 ≤
      normSq ((linePath base direction).numerator.eval
        (PathPolynomial.ofRat t)) +
        normSq ((linePath base direction).denominator.eval
          (PathPolynomial.ofRat t)) := by
  rw [linePath_denominator]
  simp only [normSq_one]
  exact le_add_of_nonneg_left (normSq_nonneg _)

theorem linePath_value (base direction : QI) (t : ℚ) :
    (linePath base direction).value t =
      base + CCLGeometry.ofRat t * direction := by
  rw [Path.value, linePath_numerator, linePath_denominator]
  have inverseOne : inv (1 : QI) = 1 := by
    rw [← inv_eq, inv_one]
  rw [inverseOne, mul_one]

/-- Polynomial action of a two-by-two matrix on a homogeneous path. -/
def actPath (M : Mat2 QI) (path : Path) : Path where
  numerator := DensePolynomial.scale M.a path.numerator +
    DensePolynomial.scale M.b path.denominator
  denominator := DensePolynomial.scale M.c path.numerator +
    DensePolynomial.scale M.d path.denominator

/-- Positive coefficient majorant for the elementary inverse-matrix norm
estimate on homogeneous pairs. -/
def homogeneousMatrixMajorant (M : Mat2 QI) : ℚ :=
  max 1 (normSq M.a + normSq M.b + normSq M.c + normSq M.d)

theorem homogeneousMatrixMajorant_pos (M : Mat2 QI) :
    0 < homogeneousMatrixMajorant M :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Explicit positive homogeneous norm floor transported through an
invertible adjugate action. -/
def adjugateHomogeneousLower (M : Mat2 QI) : ℚ :=
  normSq (determinant M) / (2 * homogeneousMatrixMajorant M)

theorem adjugateHomogeneousLower_pos (M : Mat2 QI)
    (determinantNonzero : determinant M ≠ 0) :
    0 < adjugateHomogeneousLower M :=
  div_pos (normSq_pos determinantNonzero)
    (mul_pos (by norm_num) (homogeneousMatrixMajorant_pos M))

/-- The adjugate action preserves a quantitative homogeneous norm floor.
The proof is the finite two-coordinate inverse-matrix estimate
`M (adj M) = det(M) I`, with a rational coefficient majorant. -/
theorem adjugateHomogeneousLower_le
    (M : Mat2 QI) (path : Path) (t : ℚ)
    (sourceLower : 1 ≤
      normSq (path.numerator.eval (PathPolynomial.ofRat t)) +
        normSq (path.denominator.eval (PathPolynomial.ofRat t))) :
    adjugateHomogeneousLower M ≤
      normSq ((actPath (adjugate M) path).numerator.eval
        (PathPolynomial.ofRat t)) +
        normSq ((actPath (adjugate M) path).denominator.eval
          (PathPolynomial.ofRat t)) := by
  let u := path.numerator.eval (PathPolynomial.ofRat t)
  let v := path.denominator.eval (PathPolynomial.ofRat t)
  let x := (adjugate M).a * u + (adjugate M).b * v
  let y := (adjugate M).c * u + (adjugate M).d * v
  have numeratorEval :
      (actPath (adjugate M) path).numerator.eval
          (PathPolynomial.ofRat t) = x := by
    simp [actPath, x, u, v]
  have denominatorEval :
      (actPath (adjugate M) path).denominator.eval
          (PathPolynomial.ofRat t) = y := by
    simp [actPath, y, u, v]
  have firstIdentity : M.a * x + M.b * y = determinant M * u := by
    apply GaussianRat.ext <;>
      simp only [x, y, adjugate, determinant, mul_re, mul_im,
        add_re, add_im, sub_re, sub_im, neg_re, neg_im] <;>
      ring
  have secondIdentity : M.c * x + M.d * y = determinant M * v := by
    apply GaussianRat.ext <;>
      simp only [x, y, adjugate, determinant, mul_re, mul_im,
        add_re, add_im, sub_re, sub_im, neg_re, neg_im] <;>
      ring
  have firstBound := normSq_add_le_two (M.a * x) (M.b * y)
  have secondBound := normSq_add_le_two (M.c * x) (M.d * y)
  rw [firstIdentity, normSq_mul, normSq_mul, normSq_mul] at firstBound
  rw [secondIdentity, normSq_mul, normSq_mul, normSq_mul] at secondBound
  let coefficientSum :=
    normSq M.a + normSq M.b + normSq M.c + normSq M.d
  let majorant := homogeneousMatrixMajorant M
  have coefficientLe : coefficientSum ≤ majorant := by
    exact le_max_right _ _
  have xNonnegative : 0 ≤ normSq x := normSq_nonneg x
  have yNonnegative : 0 ≤ normSq y := normSq_nonneg y
  have acLe : normSq M.a + normSq M.c ≤ coefficientSum := by
    dsimp only [coefficientSum]
    nlinarith [normSq_nonneg M.b, normSq_nonneg M.d]
  have bdLe : normSq M.b + normSq M.d ≤ coefficientSum := by
    dsimp only [coefficientSum]
    nlinarith [normSq_nonneg M.a, normSq_nonneg M.c]
  have acxLe := mul_le_mul_of_nonneg_right acLe xNonnegative
  have bdyLe := mul_le_mul_of_nonneg_right bdLe yNonnegative
  have detSourceBound :
      normSq (determinant M) * (normSq u + normSq v) ≤
        2 * coefficientSum * (normSq x + normSq y) := by
    nlinarith [firstBound, secondBound, acxLe, bdyLe]
  have coefficientScale :
      2 * coefficientSum * (normSq x + normSq y) ≤
        2 * majorant * (normSq x + normSq y) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left coefficientLe (by norm_num))
      (add_nonneg xNonnegative yNonnegative)
  have determinantFloor : normSq (determinant M) ≤
      normSq (determinant M) * (normSq u + normSq v) := by
    have determinantNonnegative := normSq_nonneg (determinant M)
    change 1 ≤ normSq u + normSq v at sourceLower
    nlinarith
  have scaled : normSq (determinant M) ≤
      2 * majorant * (normSq x + normSq y) :=
    determinantFloor.trans (detSourceBound.trans coefficientScale)
  apply (div_le_iff₀
    (mul_pos (by norm_num) (homogeneousMatrixMajorant_pos M))).2
  rw [numeratorEval, denominatorEval]
  change normSq (determinant M) ≤
    (normSq x + normSq y) * (2 * homogeneousMatrixMajorant M)
  calc
    normSq (determinant M) ≤
        2 * majorant * (normSq x + normSq y) := scaled
    _ = (normSq x + normSq y) *
        (2 * homogeneousMatrixMajorant M) := by
      dsimp only [majorant]
      ring

theorem actPath_projective (M : Mat2 QI) (path : Path) (t : ℚ) :
    (⟨(actPath M path).numerator.eval (PathPolynomial.ofRat t),
      (actPath M path).denominator.eval (PathPolynomial.ofRat t)⟩ : Proj QI) =
      Mat2.act M
        ⟨path.numerator.eval (PathPolynomial.ofRat t),
          path.denominator.eval (PathPolynomial.ofRat t)⟩ := by
  ext <;> simp [actPath, Mat2.act, eval_add, eval_scale]

/-- On an affine parameter cell avoiding the source projective denominator,
polynomial matrix action agrees with the affine homography. -/
theorem actPath_value (M : Mat2 QI) (path : Path) (t : ℚ)
    (sourceDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (actPath M path).value t =
      RatBox.homographic M (path.value t) := by
  simp only [Path.value, actPath, eval_add, eval_scale, RatBox.homographic]
  let p := path.numerator.eval (PathPolynomial.ofRat t)
  let q := path.denominator.eval (PathPolynomial.ofRat t)
  have numeratorIdentity :
      M.a * (p * inv q) + M.b = (M.a * p + M.b * q) * inv q := by
    calc
      M.a * (p * inv q) + M.b =
          M.a * p * inv q + M.b * (q * inv q) := by
            rw [mul_inv q sourceDenominator, mul_one]
            ring
      _ = (M.a * p + M.b * q) * inv q := by ring
  have denominatorIdentity :
      M.c * (p * inv q) + M.d = (M.c * p + M.d * q) * inv q := by
    calc
      M.c * (p * inv q) + M.d =
          M.c * p * inv q + M.d * (q * inv q) := by
            rw [mul_inv q sourceDenominator, mul_one]
            ring
      _ = (M.c * p + M.d * q) * inv q := by ring
  change (M.a * p + M.b * q) * inv (M.c * p + M.d * q) =
    (M.a * (p * inv q) + M.b) * inv (M.c * (p * inv q) + M.d)
  rw [numeratorIdentity, denominatorIdentity]
  change (M.a * p + M.b * q) * (M.c * p + M.d * q)⁻¹ =
    (M.a * p + M.b * q) * q⁻¹ * ((M.c * p + M.d * q) * q⁻¹)⁻¹
  rw [mul_inv_rev, inv_inv]
  rw [_root_.mul_assoc (M.a * p + M.b * q) q⁻¹]
  rw [← _root_.mul_assoc q⁻¹ q]
  have qCancel : q⁻¹ * q = 1 := by
    simpa only [inv_eq] using GaussianRat.inv_mul q sourceDenominator
  rw [qCancel, one_mul]

/-- A nonzero acted polynomial denominator is exactly the nonzero affine
homography denominator after dividing by the source denominator. -/
theorem homographic_denominator_ne_of_actPath
    (M : Mat2 QI) (path : Path) (t : ℚ)
    (sourceDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (targetDenominator :
      (actPath M path).denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    M.c * path.value t + M.d ≠ 0 := by
  let p := path.numerator.eval (PathPolynomial.ofRat t)
  let q := path.denominator.eval (PathPolynomial.ofRat t)
  have qCancel : inv q * q = 1 := GaussianRat.inv_mul q sourceDenominator
  intro zero
  apply targetDenominator
  simp only [actPath, eval_add, eval_scale]
  change M.c * p + M.d * q = 0
  change M.c * (p * inv q) + M.d = 0 at zero
  calc
    M.c * p + M.d * q =
        M.c * p * (inv q * q) + M.d * q := by rw [qCancel, mul_one]
    _ = (M.c * (p * inv q) + M.d) * q := by ring
    _ = 0 := by rw [zero, zero_mul]

/-- Conversely, a nonzero affine homography denominator makes the acted
polynomial denominator nonzero whenever the source path is affine at the
displayed parameter. -/
theorem actPath_denominator_ne_of_homographic
    (M : Mat2 QI) (path : Path) (t : ℚ)
    (sourceDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (homographicDenominator : M.c * path.value t + M.d ≠ 0) :
    (actPath M path).denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  let p := path.numerator.eval (PathPolynomial.ofRat t)
  let q := path.denominator.eval (PathPolynomial.ofRat t)
  have qCancel : inv q * q = 1 := GaussianRat.inv_mul q sourceDenominator
  intro zero
  apply homographicDenominator
  simp only [actPath, eval_add, eval_scale] at zero
  change M.c * p + M.d * q = 0 at zero
  change M.c * (p * inv q) + M.d = 0
  apply mul_right_cancel_of_ne sourceDenominator
  change (M.c * (p * inv q) + M.d) * q = 0 * q
  calc
    (M.c * (p * inv q) + M.d) * q =
        M.c * p * (inv q * q) + M.d * q := by ring
    _ = M.c * p + M.d * q := by rw [qCancel, mul_one]
    _ = 0 * q := by rw [zero, zero_mul]

/-! ## Constructive inverse of the rational unit-circle chart -/

/-- Every rational unit-circle point except the missing point `-1` has the
displayed rational affine parameter. -/
theorem unitCircleParam_inverse
    (point : QI) (normOne : normSq point = 1)
    (notMissing : point.re ≠ -1) :
    unitCircleParam (point.im / (1 + point.re)) = point := by
  have denominatorNonzero : 1 + point.re ≠ 0 := by
    intro zero
    apply notMissing
    linarith
  apply GaussianRat.ext
  · simp only [unitCircleParam, normSq] at normOne ⊢
    unfold unitCircleDenominator
    field_simp [denominatorNonzero]
    nlinarith
  · simp only [unitCircleParam, normSq] at normOne ⊢
    have denominatorIdentity :
        (1 + point.re) ^ 2 + point.im ^ 2 = 2 * (1 + point.re) := by
      nlinarith
    unfold unitCircleDenominator
    field_simp [denominatorNonzero]
    rw [denominatorIdentity]
    ring

/-- The exceptional rational unit-circle point is exactly the zero parameter
of the reciprocal chart. -/
theorem reciprocalUnitCircleParam_zero_of_missing
    (point : QI) (normOne : normSq point = 1)
    (missing : point.re = -1) :
    reciprocalUnitCircleParam 0 = point := by
  have imaginaryZero : point.im = 0 := by
    rw [normSq, missing] at normOne
    nlinarith [sq_nonneg point.im]
  apply GaussianRat.ext
  · simp [reciprocalUnitCircleParam, missing]
  · simp [reciprocalUnitCircleParam, imaginaryZero]

/-- An invertible adjugate action on two projectively independent source
values has a nonzero target denominator at at least one of them. -/
theorem actPath_adjugate_denominator_ne_at_one_of_two
    (M : Mat2 QI) (path : Path) (s t : ℚ)
    (determinantNonzero : determinant M ≠ 0)
    (sourceDenominatorS :
      path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (projectivelyIndependent :
      path.numerator.eval (PathPolynomial.ofRat s) *
          path.denominator.eval (PathPolynomial.ofRat t) -
        path.numerator.eval (PathPolynomial.ofRat t) *
          path.denominator.eval (PathPolynomial.ofRat s) ≠ 0) :
    (actPath (adjugate M) path).denominator.eval
          (PathPolynomial.ofRat s) ≠ 0 ∨
      (actPath (adjugate M) path).denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 := by
  by_cases nonzeroS :
      (actPath (adjugate M) path).denominator.eval
        (PathPolynomial.ofRat s) ≠ 0
  · exact Or.inl nonzeroS
  by_cases nonzeroT :
      (actPath (adjugate M) path).denominator.eval
        (PathPolynomial.ofRat t) ≠ 0
  · exact Or.inr nonzeroT
  have denominatorS :
      (actPath (adjugate M) path).denominator.eval
        (PathPolynomial.ofRat s) = 0 := not_ne_iff.mp nonzeroS
  have denominatorT :
      (actPath (adjugate M) path).denominator.eval
        (PathPolynomial.ofRat t) = 0 := not_ne_iff.mp nonzeroT
  let numeratorS := path.numerator.eval (PathPolynomial.ofRat s)
  let denominatorSValue := path.denominator.eval (PathPolynomial.ofRat s)
  let numeratorT := path.numerator.eval (PathPolynomial.ofRat t)
  let denominatorTValue := path.denominator.eval (PathPolynomial.ofRat t)
  have rawS : (adjugate M).c * numeratorS +
      (adjugate M).d * denominatorSValue = 0 := by
    simpa [actPath, numeratorS, denominatorSValue] using denominatorS
  have rawT : (adjugate M).c * numeratorT +
      (adjugate M).d * denominatorTValue = 0 := by
    simpa [actPath, numeratorT, denominatorTValue] using denominatorT
  have independent :
      numeratorS * denominatorTValue -
        numeratorT * denominatorSValue ≠ 0 := by
    simpa [numeratorS, denominatorSValue, numeratorT,
      denominatorTValue] using projectivelyIndependent
  have productZero :
      (adjugate M).c *
        (numeratorS * denominatorTValue -
          numeratorT * denominatorSValue) = 0 := by
    calc
      (adjugate M).c *
          (numeratorS * denominatorTValue -
            numeratorT * denominatorSValue) =
          ((adjugate M).c * numeratorS +
              (adjugate M).d * denominatorSValue) * denominatorTValue -
            ((adjugate M).c * numeratorT +
              (adjugate M).d * denominatorTValue) * denominatorSValue := by
        apply GaussianRat.ext <;>
          simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im] <;>
          ring
      _ = 0 := by simp only [rawS, rawT, GaussianRat.zero_mul,
        GaussianRat.sub_self]
  have cZero : (adjugate M).c = 0 :=
    (mul_eq_zero.mp productZero).resolve_right independent
  have dZero : (adjugate M).d = 0 := by
    have product : (adjugate M).d * denominatorSValue = 0 := by
      simpa [cZero] using rawS
    exact (mul_eq_zero.mp product).resolve_right (by
      simpa [denominatorSValue] using sourceDenominatorS)
  have matrixCZero : M.c = 0 := by
    change -M.c = 0 at cZero
    exact neg_eq_zero.mp cZero
  have matrixAZero : M.a = 0 := by
    change M.a = 0 at dZero
    exact dZero
  have determinantZero : determinant M = 0 := by
    simp [determinant, matrixAZero, matrixCZero]
  exact (determinantNonzero determinantZero).elim

/-- In particular, the acted target denominator polynomial is not identically
zero. -/
theorem actPath_adjugate_denominator_isZero_false
    (M : Mat2 QI) (path : Path) (s t : ℚ)
    (determinantNonzero : determinant M ≠ 0)
    (sourceDenominatorS :
      path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (projectivelyIndependent :
      path.numerator.eval (PathPolynomial.ofRat s) *
          path.denominator.eval (PathPolynomial.ofRat t) -
        path.numerator.eval (PathPolynomial.ofRat t) *
          path.denominator.eval (PathPolynomial.ofRat s) ≠ 0) :
    (actPath (adjugate M) path).denominator.isZero = false := by
  rcases actPath_adjugate_denominator_ne_at_one_of_two M path s t
    determinantNonzero sourceDenominatorS projectivelyIndependent with
    nonzeroS | nonzeroT
  · exact DensePolynomial.isZero_false_of_eval_ne nonzeroS
  · exact DensePolynomial.isZero_false_of_eval_ne nonzeroT

/-- Polynomial inverse image of a scaled norm circle under decoder `M`. -/
def inverseScaledCirclePath (M : Mat2 QI) (scaleValue : QI) : Path :=
  actPath (adjugate M) (scaledCirclePath scaleValue)

theorem inverseScaledCirclePath_projective
    (M : Mat2 QI) (scaleValue : QI) (t : ℚ) :
    (⟨(inverseScaledCirclePath M scaleValue).numerator.eval (PathPolynomial.ofRat t),
      (inverseScaledCirclePath M scaleValue).denominator.eval
        (PathPolynomial.ofRat t)⟩ :
        Proj QI) =
      Mat2.act (adjugate M)
        (scaledCircleProjective scaleValue (Proj.affine t)) := by
  rw [inverseScaledCirclePath, actPath_projective,
    scaledCirclePath_projective]

/-- Inverse image of the reciprocal chart of a scaled norm circle. -/
def inverseReciprocalScaledCirclePath
    (M : Mat2 QI) (scaleValue : QI) : Path :=
  actPath (adjugate M) (reciprocalScaledCirclePath scaleValue)

theorem inverseReciprocalScaledCirclePath_projective
    (M : Mat2 QI) (scaleValue : QI) (t : ℚ) :
    (⟨(inverseReciprocalScaledCirclePath M scaleValue).numerator.eval
        (PathPolynomial.ofRat t),
      (inverseReciprocalScaledCirclePath M scaleValue).denominator.eval
        (PathPolynomial.ofRat t)⟩ : Proj QI) =
      Mat2.act (adjugate M)
        (scaledCircleProjective scaleValue (reciprocalAffine t)) := by
  rw [inverseReciprocalScaledCirclePath, actPath_projective,
    reciprocalScaledCirclePath_projective]

/-- Polynomial inverse image of an arbitrary rational line. -/
def inverseLinePath (M : Mat2 QI) (base direction : QI) : Path :=
  actPath (adjugate M) (linePath base direction)

theorem inverseLinePath_projective
    (M : Mat2 QI) (base direction : QI) (t : ℚ) :
    (⟨(inverseLinePath M base direction).numerator.eval (PathPolynomial.ofRat t),
      (inverseLinePath M base direction).denominator.eval
        (PathPolynomial.ofRat t)⟩ :
        Proj QI) =
      inverseLineProjective M base direction (Proj.affine t) := by
  rw [inverseLinePath, actPath_projective, linePath_projective]
  rfl

/-- Inverse image of `Re z = threshold`. -/
def inverseRealBoundaryPath (M : Mat2 QI) (threshold : ℚ) : Path :=
  inverseLinePath M ⟨threshold, 0⟩ ⟨0, 1⟩

/-- Inverse image of `Im z = threshold`. -/
def inverseImagBoundaryPath (M : Mat2 QI) (threshold : ℚ) : Path :=
  inverseLinePath M ⟨0, threshold⟩ ⟨1, 0⟩

/-! ## Nonzero inverse-path denominator polynomials -/

theorem inverseScaledCirclePath_denominator_ne_at_zero_or_one
    (M : Mat2 QI) (scaleValue : QI)
    (determinantNonzero : determinant M ≠ 0) (scaleNonzero : scaleValue ≠ 0) :
    (inverseScaledCirclePath M scaleValue).denominator.eval
          (PathPolynomial.ofRat 0) ≠ 0 ∨
      (inverseScaledCirclePath M scaleValue).denominator.eval
          (PathPolynomial.ofRat 1) ≠ 0 := by
  apply actPath_adjugate_denominator_ne_at_one_of_two M
    (scaledCirclePath scaleValue) 0 1 determinantNonzero
    (unitCirclePath_denominator_ne 0)
  have identity :
      (scaledCirclePath scaleValue).numerator.eval (PathPolynomial.ofRat 0) *
          (scaledCirclePath scaleValue).denominator.eval (PathPolynomial.ofRat 1) -
        (scaledCirclePath scaleValue).numerator.eval (PathPolynomial.ofRat 1) *
          (scaledCirclePath scaleValue).denominator.eval (PathPolynomial.ofRat 0) =
        scaleValue * qi 2 (-2) := by
    simp only [scaledCirclePath, scalePath, eval_scale]
    apply GaussianRat.ext
    · simp [unitCirclePath, qi, DensePolynomial.eval,
        DensePolynomial.evalCoeffs, PathPolynomial.ofRat]
      ring_nf
      exact Or.inl trivial
    · simp [unitCirclePath, qi, DensePolynomial.eval,
        DensePolynomial.evalCoeffs, PathPolynomial.ofRat]
      ring_nf
  rw [identity]
  exact mul_ne_zero scaleNonzero (by
    intro zero
    have realZero := congrArg GaussianRat.re zero
    norm_num [qi] at realZero)

theorem inverseScaledCirclePath_denominator_isZero_false
    (M : Mat2 QI) (scaleValue : QI)
    (determinantNonzero : determinant M ≠ 0) (scaleNonzero : scaleValue ≠ 0) :
    (inverseScaledCirclePath M scaleValue).denominator.isZero = false := by
  rcases inverseScaledCirclePath_denominator_ne_at_zero_or_one M scaleValue
    determinantNonzero scaleNonzero with nonzero | nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero

theorem inverseReciprocalScaledCirclePath_denominator_ne_at_zero_or_one
    (M : Mat2 QI) (scaleValue : QI)
    (determinantNonzero : determinant M ≠ 0) (scaleNonzero : scaleValue ≠ 0) :
    (inverseReciprocalScaledCirclePath M scaleValue).denominator.eval
          (PathPolynomial.ofRat 0) ≠ 0 ∨
      (inverseReciprocalScaledCirclePath M scaleValue).denominator.eval
          (PathPolynomial.ofRat 1) ≠ 0 := by
  apply actPath_adjugate_denominator_ne_at_one_of_two M
    (reciprocalScaledCirclePath scaleValue) 0 1 determinantNonzero
    (reciprocalUnitCirclePath_denominator_ne 0)
  have identity :
      (reciprocalScaledCirclePath scaleValue).numerator.eval
          (PathPolynomial.ofRat 0) *
          (reciprocalScaledCirclePath scaleValue).denominator.eval
            (PathPolynomial.ofRat 1) -
        (reciprocalScaledCirclePath scaleValue).numerator.eval
          (PathPolynomial.ofRat 1) *
          (reciprocalScaledCirclePath scaleValue).denominator.eval
            (PathPolynomial.ofRat 0) =
        scaleValue * qi (-2) (-2) := by
    simp only [reciprocalScaledCirclePath, scalePath, eval_scale]
    apply GaussianRat.ext
    · simp [reciprocalUnitCirclePath, qi, DensePolynomial.eval,
        DensePolynomial.evalCoeffs, PathPolynomial.ofRat]
      ring_nf
      exact Or.inl trivial
    · simp [reciprocalUnitCirclePath, qi, DensePolynomial.eval,
        DensePolynomial.evalCoeffs, PathPolynomial.ofRat]
      ring_nf
  rw [identity]
  exact mul_ne_zero scaleNonzero (by
    intro zero
    have realZero := congrArg GaussianRat.re zero
    norm_num [qi] at realZero)

theorem inverseReciprocalScaledCirclePath_denominator_isZero_false
    (M : Mat2 QI) (scaleValue : QI)
    (determinantNonzero : determinant M ≠ 0) (scaleNonzero : scaleValue ≠ 0) :
    (inverseReciprocalScaledCirclePath M scaleValue).denominator.isZero = false := by
  rcases inverseReciprocalScaledCirclePath_denominator_ne_at_zero_or_one
    M scaleValue determinantNonzero scaleNonzero with nonzero | nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero

theorem inverseLinePath_denominator_ne_at_zero_or_one
    (M : Mat2 QI) (base direction : QI)
    (determinantNonzero : determinant M ≠ 0)
    (directionNonzero : direction ≠ 0) :
    (inverseLinePath M base direction).denominator.eval
          (PathPolynomial.ofRat 0) ≠ 0 ∨
      (inverseLinePath M base direction).denominator.eval
          (PathPolynomial.ofRat 1) ≠ 0 := by
  apply actPath_adjugate_denominator_ne_at_one_of_two M
    (linePath base direction) 0 1 determinantNonzero
    (linePath_denominator_ne base direction 0)
  have identity :
      (linePath base direction).numerator.eval (PathPolynomial.ofRat 0) *
          (linePath base direction).denominator.eval (PathPolynomial.ofRat 1) -
        (linePath base direction).numerator.eval (PathPolynomial.ofRat 1) *
          (linePath base direction).denominator.eval (PathPolynomial.ofRat 0) =
        -direction := by
    rw [linePath_numerator base direction 0,
      linePath_denominator base direction 1,
      linePath_numerator base direction 1,
      linePath_denominator base direction 0]
    apply GaussianRat.ext <;>
      simp [CCLGeometry.ofRat]
  rw [identity]
  exact neg_ne_zero.mpr directionNonzero

theorem inverseLinePath_denominator_isZero_false
    (M : Mat2 QI) (base direction : QI)
    (determinantNonzero : determinant M ≠ 0)
    (directionNonzero : direction ≠ 0) :
    (inverseLinePath M base direction).denominator.isZero = false := by
  rcases inverseLinePath_denominator_ne_at_zero_or_one M base direction
    determinantNonzero directionNonzero with nonzero | nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero

theorem inverseRealBoundaryPath_denominator_ne_at_zero_or_one
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    (inverseRealBoundaryPath M threshold).denominator.eval
          (PathPolynomial.ofRat 0) ≠ 0 ∨
      (inverseRealBoundaryPath M threshold).denominator.eval
          (PathPolynomial.ofRat 1) ≠ 0 := by
  apply inverseLinePath_denominator_ne_at_zero_or_one M
    ⟨threshold, 0⟩ ⟨0, 1⟩
    determinantNonzero
  intro zero
  have imaginaryZero := congrArg GaussianRat.im zero
  norm_num at imaginaryZero

theorem inverseRealBoundaryPath_denominator_isZero_false
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    (inverseRealBoundaryPath M threshold).denominator.isZero = false := by
  rcases inverseRealBoundaryPath_denominator_ne_at_zero_or_one M threshold
    determinantNonzero with nonzero | nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero

theorem inverseImagBoundaryPath_denominator_ne_at_zero_or_one
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    (inverseImagBoundaryPath M threshold).denominator.eval
          (PathPolynomial.ofRat 0) ≠ 0 ∨
      (inverseImagBoundaryPath M threshold).denominator.eval
          (PathPolynomial.ofRat 1) ≠ 0 := by
  apply inverseLinePath_denominator_ne_at_zero_or_one M
    ⟨0, threshold⟩ ⟨1, 0⟩
    determinantNonzero
  intro zero
  have realZero := congrArg GaussianRat.re zero
  norm_num at realZero

theorem inverseImagBoundaryPath_denominator_isZero_false
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    (inverseImagBoundaryPath M threshold).denominator.isZero = false := by
  rcases inverseImagBoundaryPath_denominator_ne_at_zero_or_one M threshold
    determinantNonzero with nonzero | nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero
  · exact DensePolynomial.isZero_false_of_eval_ne nonzero

end CCLBoundaryPath
end FTA
