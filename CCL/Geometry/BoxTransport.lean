import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.RawParser

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace CCL.BoxTransport

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Box := RFAP.Boxes.Box
abbrev Block := CCL.Cylinder.Block

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Chordal
open CCL.RawParser

/-! ## Rational boxes around a displayed centre -/

/-- The closed rational square of half-width `radius` about `center`. -/
def centeredBox (center : Gaussian) (radius : Coordinate)
    (radiusNonnegative : 0 ≤ radius) : Box where
  xLower := center.re - radius
  xUpper := center.re + radius
  yLower := center.im - radius
  yUpper := center.im + radius
  x_valid := (sub_le_self center.re radiusNonnegative).trans
    (le_add_of_nonneg_right radiusNonnegative)
  y_valid := (sub_le_self center.im radiusNonnegative).trans
    (le_add_of_nonneg_right radiusNonnegative)

private theorem nonnegative_le_of_sq_le_sq
    {value radius : Coordinate} (radiusNonnegative : 0 ≤ radius)
    (squareBound : value ^ 2 ≤ radius ^ 2) : value ≤ radius := by
  by_cases bounded : value ≤ radius
  · exact bounded
  · have radiusLtValue : radius < value := lt_of_not_ge bounded
    have valuePositive : 0 < value := radiusNonnegative.trans_lt radiusLtValue
    have first : radius * radius ≤ radius * value :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusLtValue.le radiusNonnegative
    have second : radius * value < value * value :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        radiusLtValue valuePositive
    have strictSquare : radius ^ 2 < value ^ 2 := by
      rw [pow_two, pow_two]
      exact first.trans_lt second
    exact ((not_lt_of_ge squareBound) strictSquare).elim

/-- A square comparison against a nonnegative rational radius gives both
coordinate inequalities, without constructing an absolute value or square
root. -/
theorem signed_bounds_of_sq_le_sq
    {value radius : Coordinate} (radiusNonnegative : 0 ≤ radius)
    (squareBound : value ^ 2 ≤ radius ^ 2) :
    -radius ≤ value ∧ value ≤ radius := by
  by_cases valueNonnegative : 0 ≤ value
  · exact
      ⟨(neg_nonpos.mpr radiusNonnegative).trans valueNonnegative,
        nonnegative_le_of_sq_le_sq radiusNonnegative squareBound⟩
  · have valueNonpositive : value ≤ 0 := le_of_not_ge valueNonnegative
    have negativeNonnegative : 0 ≤ -value := neg_nonneg.mpr valueNonpositive
    have negativeSquareBound : (-value) ^ 2 ≤ radius ^ 2 := by
      calc
        (-value) ^ 2 = value ^ 2 := by ring1
        _ ≤ radius ^ 2 := squareBound
    have negativeLe := nonnegative_le_of_sq_le_sq radiusNonnegative
      negativeSquareBound
    have lower := RFAP.ConstructiveFraction.neg_le_neg_direct negativeLe
    exact ⟨by simpa only [neg_neg] using lower,
      valueNonpositive.trans radiusNonnegative⟩

/-- A squared Euclidean error bounded by the half-width squared places the
value in the explicit centred rational box. -/
theorem centeredBox_contains_of_normSq_sub_le
    {center value : Gaussian} {radius : Coordinate}
    (radiusNonnegative : 0 ≤ radius)
    (distanceBound : normSq (value - center) ≤ radius ^ 2) :
    (centeredBox center radius radiusNonnegative).Contains value := by
  have realSquare : (value.re - center.re) ^ 2 ≤ radius ^ 2 :=
    calc
      (value.re - center.re) ^ 2 ≤
          (value.re - center.re) ^ 2 + (value.im - center.im) ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = normSq (value - center) := rfl
      _ ≤ radius ^ 2 := distanceBound
  have imaginarySquare : (value.im - center.im) ^ 2 ≤ radius ^ 2 :=
    calc
      (value.im - center.im) ^ 2 ≤
          (value.re - center.re) ^ 2 + (value.im - center.im) ^ 2 :=
        le_add_of_nonneg_left
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = normSq (value - center) := rfl
      _ ≤ radius ^ 2 := distanceBound
  have realBounds := signed_bounds_of_sq_le_sq radiusNonnegative realSquare
  have imaginaryBounds :=
    signed_bounds_of_sq_le_sq radiusNonnegative imaginarySquare
  exact
    ⟨by
      calc
        center.re - radius = -radius + center.re := by ring1
        _ ≤ (value.re - center.re) + center.re :=
          add_le_add_left realBounds.1 center.re
        _ = value.re := by ring1,
      by
        calc
          value.re = (value.re - center.re) + center.re := by ring1
          _ ≤ radius + center.re := add_le_add_left realBounds.2 center.re
          _ = center.re + radius := by ring1,
      by
        calc
          center.im - radius = -radius + center.im := by ring1
          _ ≤ (value.im - center.im) + center.im :=
            add_le_add_left imaginaryBounds.1 center.im
          _ = value.im := by ring1,
      by
        calc
          value.im = (value.im - center.im) + center.im := by ring1
          _ ≤ radius + center.im :=
            add_le_add_left imaginaryBounds.2 center.im
          _ = center.im + radius := by ring1⟩

theorem centeredBox_diagonalSq
    (center : Gaussian) (radius : Coordinate)
    (radiusNonnegative : 0 ≤ radius) :
    (centeredBox center radius radiusNonnegative).diagonalSq =
      8 * radius ^ 2 := by
  simp only [RFAP.Boxes.Box.diagonalSq, centeredBox]
  ring1

/-- The paper's box of half-width `epsilon / 4`. -/
def epsilonBox (center : Gaussian) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) : Box :=
  centeredBox center (epsilon / 4)
    (RFAP.ConstructiveFraction.div_nonneg_direct epsilonPositive.le (by decide))

theorem epsilonBox_diagonalSq
    (center : Gaussian) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    (epsilonBox center epsilon epsilonPositive).diagonalSq = epsilon ^ 2 / 2 := by
  unfold epsilonBox
  rw [centeredBox_diagonalSq]
  rw [pow_two]
  have squareQuotient :
      (epsilon / 4) * (epsilon / 4) =
        (epsilon * epsilon) / ((4 : Coordinate) * 4) :=
    RFAP.ConstructiveFraction.div_mul_div_direct epsilon 4 epsilon 4
  rw [squareQuotient]
  have fourTimesFour : (4 : Coordinate) * 4 = 16 := by decide
  have eightSixteenths : (8 : Coordinate) / 16 = 1 / 2 := by decide
  rw [fourTimesFour]
  calc
    8 * (epsilon * epsilon / 16) =
        (epsilon * epsilon) * (8 / 16) := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        8 * ((epsilon * epsilon) * (16 : Coordinate)⁻¹) =
            (8 * (epsilon * epsilon)) * (16 : Coordinate)⁻¹ :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
        _ = ((epsilon * epsilon) * 8) * (16 : Coordinate)⁻¹ := by
          rw [RFAP.ConstructiveFraction.mul_comm 8 (epsilon * epsilon)]
        _ = (epsilon * epsilon) * (8 * (16 : Coordinate)⁻¹) :=
          RFAP.ConstructiveFraction.mul_assoc _ _ _
    _ = (epsilon * epsilon) * (1 / 2) := by rw [eightSixteenths]
    _ = epsilon ^ 2 / 2 := by
      rw [pow_two, RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ConstructiveFraction.one_mul]

theorem epsilonBox_diagonalSq_le
    (center : Gaussian) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    (epsilonBox center epsilon epsilonPositive).diagonalSq ≤ epsilon ^ 2 := by
  rw [epsilonBox_diagonalSq]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (show (0 : Coordinate) < 2 by decide)).2
  calc
    epsilon ^ 2 = epsilon ^ 2 * 1 := by ring1
    _ ≤ epsilon ^ 2 * 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (by decide) (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon)

/-! ## Completed-block chordal bounds give affine boxes -/

/-- On a fixed bounded affine chart, a chordal bound converts to an ordinary
squared-distance bound with the explicit factor `(1 + K)^2`. -/
theorem normSq_sub_le_of_chordalSq_le
    {left right : Gaussian} {K Q : Coordinate}
    (KNonnegative : 0 ≤ K) (QNonnegative : 0 ≤ Q)
    (leftNorm : normSq left ≤ K) (rightNorm : normSq right ≤ K)
    (chordalBound : chordalSq (CCL.Proj.affine left)
      (CCL.Proj.affine right) ≤ Q) :
    normSq (left - right) ≤ (1 + K) ^ 2 * Q := by
  let denominator := (1 + normSq left) * (1 + normSq right)
  have leftWeightPositive : (0 : Coordinate) < 1 + normSq left :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg left)
  have rightWeightPositive : (0 : Coordinate) < 1 + normSq right :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg right)
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have exactDistance : normSq (left - right) =
      chordalSq (CCL.Proj.affine left) (CCL.Proj.affine right) * denominator := by
    rw [chordalSq_affine]
    exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
      (normSq (left - right)) denominator denominatorPositive.ne').symm
  have denominatorBound : denominator ≤ (1 + K) * (1 + K) := by
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (add_le_add_right leftNorm 1) (add_le_add_right rightNorm 1)
      (add_nonneg (by decide) (normSq_nonneg right))
      (add_nonneg (by decide) KNonnegative)
  calc
    normSq (left - right) =
        chordalSq (CCL.Proj.affine left)
          (CCL.Proj.affine right) * denominator := exactDistance
    _ ≤ Q * denominator :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        chordalBound denominatorPositive.le
    _ ≤ Q * ((1 + K) * (1 + K)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorBound QNonnegative
    _ = (1 + K) ^ 2 * Q := by ring1

/-- Specialization of the preceding affine estimate to two supplied finite
realizations of the same completed CCL block list. -/
theorem completed_affine_normSq_sub_le
    {blocks : List Block} {left right : Gaussian} {K : Coordinate}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine left))
    (rightRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine right))
    (leftNorm : normSq left ≤ K) (rightNorm : normSq right ≤ K) :
    normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Coordinate) ^ blocks.length := by
  apply normSq_sub_le_of_chordalSq_le KNonnegative
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  exact CCL.Cylinder.Realizes.chordalSq_le_half_pow
    leftRealizes rightRealizes

/-- The same affine estimate for integral decoders which retain their
explicit homogeneous rescaling at every completed block. -/
theorem projectiveCompleted_affine_normSq_sub_le
    {blocks : List Block} {left right : Gaussian} {K : Coordinate}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      (CCL.Proj.affine left))
    (rightRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      (CCL.Proj.affine right))
    (leftNorm : normSq left ≤ K) (rightNorm : normSq right ≤ K) :
    normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Coordinate) ^ blocks.length := by
  apply normSq_sub_le_of_chordalSq_le KNonnegative
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  exact CCL.Cylinder.ProjectiveRealizes.chordalSq_le_half_pow
    leftRealizes rightRealizes

/-- The integral encoder's exact interface: the realized homogeneous pairs
need only be explicitly equivalent to the two affine values. -/
theorem projectiveCompleted_equivalentAffine_normSq_sub_le
    {blocks : List Block} {left right : Gaussian}
    {leftPoint rightPoint : Proj} {K : Coordinate}
    (KNonnegative : 0 ≤ K)
    (leftRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      leftPoint)
    (rightRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      rightPoint)
    (leftEquivalent : leftPoint.Equivalent (CCL.Proj.affine left))
    (rightEquivalent : rightPoint.Equivalent (CCL.Proj.affine right))
    (leftNorm : normSq left ≤ K) (rightNorm : normSq right ≤ K) :
    normSq (left - right) ≤
      (1 + K) ^ 2 * (1 / 2 : Coordinate) ^ blocks.length := by
  apply normSq_sub_le_of_chordalSq_le KNonnegative
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
    leftNorm rightNorm
  have leftValid :=
    CCL.Cylinder.ProjectiveRealizes.valid leftRealizes
  have rightValid :=
    CCL.Cylinder.ProjectiveRealizes.valid rightRealizes
  have affineLeftValid := Proj.affine_hasNonzeroCoordinate left
  have affineRightValid := Proj.affine_hasNonzeroCoordinate right
  calc
    chordalSq (CCL.Proj.affine left) (CCL.Proj.affine right) =
        chordalSq (CCL.Proj.affine left) rightPoint :=
      (chordalSq_eq_of_equivalent_right rightValid affineRightValid
        rightEquivalent (CCL.Proj.affine left)).symm
    _ = chordalSq leftPoint rightPoint :=
      (chordalSq_eq_of_equivalent_left leftValid affineLeftValid
        leftEquivalent rightPoint).symm
    _ ≤ (1 / 2 : Coordinate) ^ blocks.length :=
      CCL.Cylinder.ProjectiveRealizes.chordalSq_le_half_pow
        leftRealizes rightRealizes

/-- The denominator-cleared accuracy test used by the executable boxed-name
constructor. -/
def CompletedBoxBudget (K epsilon Q : Coordinate) : Prop :=
  (1 + K) ^ 2 * Q ≤ (epsilon / 4) ^ 2

instance completedBoxBudgetDecidable (K epsilon Q : Coordinate) :
    Decidable (CompletedBoxBudget K epsilon Q) := by
  unfold CompletedBoxBudget
  infer_instance

theorem quarter_sq (epsilon : Coordinate) :
    (epsilon / 4) ^ 2 = epsilon ^ 2 / 16 := by
  rw [pow_two, pow_two]
  have squareQuotient :
      (epsilon / 4) * (epsilon / 4) =
        (epsilon * epsilon) / ((4 : Coordinate) * 4) :=
    RFAP.ConstructiveFraction.div_mul_div_direct epsilon 4 epsilon 4
  rw [squareQuotient]
  rw [show (4 : Coordinate) * 4 = 16 by decide]

/-- The paper's displayed smallness hypothesis implies the executable
denominator-cleared budget. -/
theorem completedBoxBudget_of_paper_bound
    {K epsilon Q : Coordinate} (KNonnegative : 0 ≤ K)
    (paperBound : Q ≤ epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    CompletedBoxBudget K epsilon Q := by
  let scale := (1 + K) ^ 2
  have onePlusPositive : (0 : Coordinate) < 1 + K :=
    add_pos_of_pos_of_nonneg (by decide) KNonnegative
  have scalePositive : 0 < scale :=
    RFAP.ConstructiveFraction.pow_pos_direct onePlusPositive 2
  have denominatorPositive : (0 : Coordinate) < 16 * scale :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) scalePositive
  have cancelScale :
      scale * (epsilon ^ 2 / (16 * scale)) = epsilon ^ 2 / 16 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      (scale * (epsilon ^ 2 / (16 * scale))) * (16 * scale) =
          scale * ((epsilon ^ 2 / (16 * scale)) * (16 * scale)) := by ring1
      _ = scale * epsilon ^ 2 := by
        exact congrArg (fun value => scale * value)
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            denominatorPositive.ne')
      _ = epsilon ^ 2 * scale := RFAP.ConstructiveFraction.mul_comm _ _
      _ = ((epsilon ^ 2 / 16) * 16) * scale := by
        exact congrArg (fun value => value * scale)
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            (show (16 : Coordinate) ≠ 0 by decide)).symm
      _ = (epsilon ^ 2 / 16) * (16 * scale) := by ring1
  unfold CompletedBoxBudget
  change scale * Q ≤ (epsilon / 4) ^ 2
  calc
    scale * Q ≤ scale * (epsilon ^ 2 / (16 * scale)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        paperBound scalePositive.le
    _ = epsilon ^ 2 / 16 := cancelScale
    _ = (epsilon / 4) ^ 2 := (quarter_sq epsilon).symm

/-- Direct finite form of Proposition 7.25: a pairwise chordal certificate,
a common affine norm bound, and the paper's displayed smallness inequality
place the supplied value in the explicit witness-centred box. -/
theorem epsilonBox_contains_of_chordalSq_le
    {witness value : Gaussian} {K Q epsilon : Coordinate}
    (KNonnegative : 0 ≤ K) (QNonnegative : 0 ≤ Q)
    (epsilonPositive : 0 < epsilon)
    (witnessNorm : normSq witness ≤ K) (valueNorm : normSq value ≤ K)
    (chordalBound : chordalSq (CCL.Proj.affine value)
      (CCL.Proj.affine witness) ≤ Q)
    (paperBound : Q ≤ epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold epsilonBox
  apply centeredBox_contains_of_normSq_sub_le
  exact (normSq_sub_le_of_chordalSq_le KNonnegative QNonnegative
    valueNorm witnessNorm chordalBound).trans
      (completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- A completed-block cylinder satisfying the finite cleared accuracy test is
contained in the paper's explicit rational box about any supplied rational
witness realization. -/
theorem completed_affine_epsilonBox_contains
    {blocks : List Block} {witness value : Gaussian}
    {K epsilon : Coordinate} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine witness))
    (valueRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine value))
    (witnessNorm : normSq witness ≤ K) (valueNorm : normSq value ≤ K)
    (budget : CompletedBoxBudget K epsilon
      ((1 / 2 : Coordinate) ^ blocks.length)) :
    (epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold epsilonBox
  apply centeredBox_contains_of_normSq_sub_le
  exact (completed_affine_normSq_sub_le KNonnegative valueRealizes
    witnessRealizes valueNorm witnessNorm).trans budget

/-- Completed-block specialization using exactly the smallness inequality
printed in the manuscript. -/
theorem completed_affine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Gaussian}
    {K epsilon : Coordinate} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine witness))
    (valueRealizes : CCL.Cylinder.Realizes blocks
      (CCL.Proj.affine value))
    (witnessNorm : normSq witness ≤ K) (valueNorm : normSq value ≤ K)
    (paperBound : (1 / 2 : Coordinate) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (epsilonBox witness epsilon epsilonPositive).Contains value := by
  exact completed_affine_epsilonBox_contains KNonnegative epsilonPositive
    witnessRealizes valueRealizes witnessNorm valueNorm
    (completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- Homogeneously rescaled completed-block specialization of the same paper
bound. -/
theorem projectiveCompleted_affine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Gaussian}
    {K epsilon : Coordinate} (KNonnegative : 0 ≤ K)
    (epsilonPositive : 0 < epsilon)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      (CCL.Proj.affine witness))
    (valueRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      (CCL.Proj.affine value))
    (witnessNorm : normSq witness ≤ K) (valueNorm : normSq value ≤ K)
    (paperBound : (1 / 2 : Coordinate) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold epsilonBox
  apply centeredBox_contains_of_normSq_sub_le
  exact (projectiveCompleted_affine_normSq_sub_le KNonnegative valueRealizes
    witnessRealizes valueNorm witnessNorm).trans
      (completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-- Witness-centred box theorem in the exact equivalence-bearing form
returned by the integral encoder. -/
theorem projectiveCompleted_equivalentAffine_epsilonBox_contains_of_paper_bound
    {blocks : List Block} {witness value : Gaussian}
    {witnessPoint valuePoint : Proj} {K epsilon : Coordinate}
    (KNonnegative : 0 ≤ K) (epsilonPositive : 0 < epsilon)
    (witnessRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      witnessPoint)
    (valueRealizes : CCL.Cylinder.ProjectiveRealizes blocks
      valuePoint)
    (witnessEquivalent : witnessPoint.Equivalent (CCL.Proj.affine witness))
    (valueEquivalent : valuePoint.Equivalent (CCL.Proj.affine value))
    (witnessNorm : normSq witness ≤ K) (valueNorm : normSq value ≤ K)
    (paperBound : (1 / 2 : Coordinate) ^ blocks.length ≤
      epsilon ^ 2 / (16 * (1 + K) ^ 2)) :
    (epsilonBox witness epsilon epsilonPositive).Contains value := by
  unfold epsilonBox
  apply centeredBox_contains_of_normSq_sub_le
  exact (projectiveCompleted_equivalentAffine_normSq_sub_le KNonnegative
    valueRealizes witnessRealizes valueEquivalent witnessEquivalent
    valueNorm witnessNorm).trans
      (completedBoxBudget_of_paper_bound KNonnegative paperBound)

/-! ## Generic finite homographic box transport -/

/-- Computed squared-norm upper bound for the affine numerator `a t + b` on
a rational tail box. -/
def numeratorNormSqBound (matrix : Mat2) (tailBox : Box) : Coordinate :=
  2 * (normSq matrix.a * tailBox.normSqBound + normSq matrix.b)

theorem numeratorNormSqBound_nonneg (matrix : Mat2) (tailBox : Box) :
    0 ≤ numeratorNormSqBound matrix tailBox := by
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (normSq_nonneg matrix.a) tailBox.normSqBound_nonneg)
      (normSq_nonneg matrix.b))

theorem numerator_normSq_le
    (matrix : Mat2) {tailBox : Box} {tail : Gaussian}
    (inside : tailBox.Contains tail) :
    normSq (numerator matrix tail) ≤ numeratorNormSqBound matrix tailBox := by
  calc
    normSq (numerator matrix tail) = normSq (matrix.a * tail + matrix.b) := rfl
    _ ≤ 2 * (normSq (matrix.a * tail) + normSq matrix.b) :=
      normSq_add_le_two _ _
    _ = 2 * (normSq matrix.a * normSq tail + normSq matrix.b) := by
      rw [normSq_mul]
    _ ≤ 2 * (normSq matrix.a * tailBox.normSqBound + normSq matrix.b) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · exact add_le_add_left
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (tailBox.normSq_le_normSqBound inside) (normSq_nonneg matrix.a)) _
      · decide
    _ = numeratorNormSqBound matrix tailBox := rfl

/-- Squared-norm bound for the homographic output after applying the supplied
positive denominator margin. -/
def homographicNormSqBound (matrix : Mat2) (tailBox : Box)
    (denominatorMargin : Coordinate) : Coordinate :=
  numeratorNormSqBound matrix tailBox / denominatorMargin

theorem homographicNormSqBound_nonneg
    (matrix : Mat2) (tailBox : Box) {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin) :
    0 ≤ homographicNormSqBound matrix tailBox denominatorMargin :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (numeratorNormSqBound_nonneg matrix tailBox) marginPositive.le

/-- Square-root-free half-width used by the generic transport box. -/
def homographicRadius (matrix : Mat2) (tailBox : Box)
    (denominatorMargin : Coordinate) : Coordinate :=
  homographicNormSqBound matrix tailBox denominatorMargin + 1

theorem homographicRadius_nonneg
    (matrix : Mat2) (tailBox : Box) {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin) :
    0 ≤ homographicRadius matrix tailBox denominatorMargin :=
  add_nonneg
    (homographicNormSqBound_nonneg matrix tailBox marginPositive) (by decide)

/-- A total rational output box computed from a tail box and positive
denominator separation. -/
def homographicBox (matrix : Mat2) (tailBox : Box)
    (denominatorMargin : Coordinate) (marginPositive : 0 < denominatorMargin) :
    Box :=
  centeredBox 0 (homographicRadius matrix tailBox denominatorMargin)
    (homographicRadius_nonneg matrix tailBox marginPositive)

theorem homographic_normSq_le
    (matrix : Mat2) {tailBox : Box} {tail : Gaussian}
    {denominatorMargin : Coordinate} (inside : tailBox.Contains tail)
    (marginPositive : 0 < denominatorMargin)
    (denominatorLower : denominatorMargin ≤
      normSq (denominator matrix tail)) :
    normSq (homographic matrix tail) ≤
      homographicNormSqBound matrix tailBox denominatorMargin := by
  have denominatorNormPositive : 0 < normSq (denominator matrix tail) :=
    marginPositive.trans_le denominatorLower
  have denominatorNonzero : denominator matrix tail ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at denominatorNormPositive
    exact (lt_irrefl _ denominatorNormPositive).elim
  have numeratorBound := numerator_normSq_le matrix inside
  have quotientIdentity : normSq (homographic matrix tail) =
      normSq (numerator matrix tail) / normSq (denominator matrix tail) := by
    rw [homographic, normSq_mul, inv_eq,
      normSq_inv _ denominatorNonzero]
    rfl
  rw [quotientIdentity]
  have first : normSq (numerator matrix tail) /
      normSq (denominator matrix tail) ≤
      numeratorNormSqBound matrix tailBox /
        normSq (denominator matrix tail) := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      denominatorNormPositive).2
    calc
      normSq (numerator matrix tail) ≤
          numeratorNormSqBound matrix tailBox := numeratorBound
      _ = (numeratorNormSqBound matrix tailBox /
          normSq (denominator matrix tail)) *
            normSq (denominator matrix tail) :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          denominatorNormPositive.ne').symm
  exact first.trans
    (RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (numeratorNormSqBound_nonneg matrix tailBox) marginPositive
      denominatorLower)

/-- Constructive finite rational box transport.  Every hypothesis concerns
one displayed tail and finite certificates; no set of compatible tails or
completed value is formed. -/
theorem homographicBox_contains
    (matrix : Mat2) {tailBox : Box} {tail : Gaussian}
    {denominatorMargin : Coordinate} (inside : tailBox.Contains tail)
    (marginPositive : 0 < denominatorMargin)
    (denominatorLower : denominatorMargin ≤
      normSq (denominator matrix tail)) :
    (homographicBox matrix tailBox denominatorMargin marginPositive).Contains
      (homographic matrix tail) := by
  let bound := homographicNormSqBound matrix tailBox denominatorMargin
  let radius := homographicRadius matrix tailBox denominatorMargin
  have boundNonnegative : 0 ≤ bound :=
    homographicNormSqBound_nonneg matrix tailBox marginPositive
  have radiusNonnegative : 0 ≤ radius :=
    homographicRadius_nonneg matrix tailBox marginPositive
  have boundLeRadiusSq : bound ≤ radius ^ 2 := by
    have boundLeRadius : bound ≤ radius := le_add_of_nonneg_right (by decide)
    have oneLeRadius : (1 : Coordinate) ≤ radius := by
      exact le_add_of_nonneg_left boundNonnegative
    calc
      bound = bound * 1 := by ring1
      _ ≤ radius * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct boundLeRadius oneLeRadius
          (by decide) radiusNonnegative
      _ = radius ^ 2 := by ring1
  unfold homographicBox
  apply centeredBox_contains_of_normSq_sub_le radiusNonnegative
  have normBound := homographic_normSq_le matrix inside marginPositive
    denominatorLower
  calc
    normSq (homographic matrix tail - 0) =
        normSq (homographic matrix tail) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero]
    _ ≤ bound := normBound
    _ ≤ radius ^ 2 := boundLeRadiusSq

/-! ## Finite coordinatewise hulls -/

/-- Coordinatewise rational hull of two boxes. -/
def hull (left right : Box) : Box where
  xLower := min left.xLower right.xLower
  xUpper := max left.xUpper right.xUpper
  yLower := min left.yLower right.yLower
  yUpper := max left.yUpper right.yUpper
  x_valid := (min_le_left _ _).trans (left.x_valid.trans (le_max_left _ _))
  y_valid := (min_le_left _ _).trans (left.y_valid.trans (le_max_left _ _))

theorem hull_contains_left {left right : Box} {value : Gaussian}
    (inside : left.Contains value) : (hull left right).Contains value :=
  ⟨(min_le_left _ _).trans inside.1,
    inside.2.1.trans (le_max_left _ _),
    (min_le_left _ _).trans inside.2.2.1,
    inside.2.2.2.trans (le_max_left _ _)⟩

theorem hull_contains_right {left right : Box} {value : Gaussian}
    (inside : right.Contains value) : (hull left right).Contains value :=
  ⟨(min_le_right _ _).trans inside.1,
    inside.2.1.trans (le_max_right _ _),
    (min_le_right _ _).trans inside.2.2.1,
    inside.2.2.2.trans (le_max_right _ _)⟩

/-- Hull a finite candidate list, using an explicit fallback for the empty
list.  In the parser application the fallback is the previous coarse box. -/
def hullList (fallback : Box) : List Box → Box
  | [] => fallback
  | box :: remaining => hull box (hullList fallback remaining)

theorem hullList_contains_of_mem
    {fallback candidate : Box} {candidates : List Box} {value : Gaussian}
    (member : candidate ∈ candidates) (inside : candidate.Contains value) :
    (hullList fallback candidates).Contains value := by
  induction candidates with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact hull_contains_left inside
      · exact hull_contains_right (inductionHypothesis member)

end CCL.BoxTransport
