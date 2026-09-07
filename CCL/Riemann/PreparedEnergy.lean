import CCL.Riemann.HyperellipticCells
import CCL.Riemann.PreparedCycleModels
import CCL.Riemann.SynchronizedNormalization
import CCL.Geometry.BoxTransport
import RFAP.Measure.BoxContent
import RFAP.Polynomial.Bounds
import mathlib.RFAP.ConstructiveFiniteRoots

/-!
# Geometry-backed finite surface energy

The second bilinear relation consumes lower sums on finitely many rational
surface boxes.  This module prevents those lower sums from being supplied as
unattached pairs of rational numbers: every raw cell names one face of the
explicit hyperelliptic cell complex, carries one proper rational box, uses its
exact rational content as area, proves the curve denominator apart throughout
that box, and verifies a lower bound for the displayed algebraic differential
density.

The remaining global comparison is precisely the finite cut-surface
second-relation calculation: the sum of these checked local contributions is
bounded by the synchronized A/B period pairing.  Once that comparison and the
already finite normalization comparison are displayed, the generic transport
layer derives pointwise positivity.
-/

namespace CCL.Riemann.PreparedEnergy

open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev GaussianVector (size : Nat) :=
  CCL.Riemann.FiniteEnergy.GaussianVector size
abbrev RationalVector (size : Nat) :=
  CCL.Riemann.PeriodMatrix.RationalVector size
abbrev NonzeroVector {size : Nat} (vector : RationalVector size) :=
  CCL.Riemann.PeriodMatrix.NonzeroVector vector
abbrev Box := RFAP.Boxes.Box
abbrev Face := CCL.Riemann.HyperellipticCells.Face

/-- Dense numerator polynomial of a Gaussian-rational combination of the
standard basis `dx/y, x dx/y, ...`.  Dense polynomials store their finite
coefficients in high-to-low order, hence the explicit reversal. -/
def coefficientPolynomial {genus : Nat}
    (coefficients : GaussianVector genus) : GaussianPolynomial where
  coeffs := (List.ofFn coefficients).reverse

@[simp] theorem coefficientPolynomial_coeffs {genus : Nat}
    (coefficients : GaussianVector genus) :
    (coefficientPolynomial coefficients).coeffs =
      (List.ofFn coefficients).reverse := rfl

/-- A displayed nonzero differential coefficient remains visibly present in
the finite dense numerator representation. -/
theorem coefficientPolynomial_contains_nonzero {genus : Nat}
    {coefficients : GaussianVector genus}
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    exists coefficient,
      coefficient ∈ (coefficientPolynomial coefficients).coeffs /\
        coefficient ≠ 0 := by
  refine ⟨coefficients nonzero.index, ?_, nonzero.coefficient_nonzero⟩
  rw [coefficientPolynomial_coeffs, List.mem_reverse]
  exact List.mem_ofFn.mpr ⟨nonzero.index, rfl⟩

private theorem dropWhile_not_empty_of_mem_nonzero
    (coefficients : List Gaussian) {coefficient : Gaussian}
    (member : coefficient ∈ coefficients) (nonzero : coefficient ≠ 0) :
    (coefficients.dropWhile (· = 0)).isEmpty = false := by
  induction coefficients with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with headEqual | tailMember
      · subst coefficient
        simp [List.dropWhile, nonzero]
      · by_cases headZero : head = 0
        · simp only [List.dropWhile, headZero, decide_true]
          exact inductionHypothesis tailMember
        · simp [List.dropWhile, headZero]

/-- A nonzero coefficient witness proves that the finite dense numerator is
not the zero polynomial, by direct inspection of the stored coefficient list. -/
theorem coefficientPolynomial_nonzero {genus : Nat}
    {coefficients : GaussianVector genus}
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    (coefficientPolynomial coefficients).isZero = false := by
  rcases coefficientPolynomial_contains_nonzero nonzero with
    ⟨coefficient, member, coefficientNonzero⟩
  exact dropWhile_not_empty_of_mem_nonzero
    (coefficientPolynomial coefficients).coeffs member coefficientNonzero

/-- A finite bounded scan finds a rational point at which both the numerator
combination and the curve polynomial are nonzero. -/
structure ClearEvaluation {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) where
  point : Gaussian
  numerator_nonzero : (coefficientPolynomial coefficients).eval point ≠ 0
  denominator_nonzero : curve.polynomial.eval point ≠ 0

/-- Compute a common clear point by scanning the bounded candidate list of
the finite product polynomial. -/
def findClearEvaluation {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    ClearEvaluation curve coefficients := by
  let numerator := coefficientPolynomial coefficients
  let product := numerator * curve.polynomial
  have numeratorNonzero : numerator.isZero = false :=
    coefficientPolynomial_nonzero nonzero
  have productNonzero : product.isZero = false :=
    RFAP.ConstructivePolynomial.product_isZero_false numeratorNonzero
      curve.nonzero
  let evaluation :=
    RFAP.ConstructiveFiniteRoots.findNonzeroEvaluation product productNonzero
  have productValueNonzero :
      numerator.eval evaluation.point *
          curve.polynomial.eval evaluation.point ≠ 0 := by
    simpa only [product,
      RFAP.ComputablePolynomial.DensePolynomial.eval_mul] using
      evaluation.valueNonzero
  refine
    { point := evaluation.point
      numerator_nonzero := ?_
      denominator_nonzero := ?_ }
  · intro numeratorZero
    apply productValueNonzero
    rw [numeratorZero]
    exact zero_mul _
  · intro denominatorZero
    apply productValueNonzero
    rw [denominatorZero]
    exact mul_zero _

/-- Square-root-free uniform lower bound for the squared norm of a finite
dense polynomial on one rational box.  It is computed from the value at the
fixed lower-left anchor and the finite Horner Lipschitz scan. -/
def uniformNormLower (polynomial : GaussianPolynomial) (box : Box) :
    Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval box.anchor) / 2 -
    RFAP.PolynomialBounds.denseLipschitzBound polynomial box * box.diagonalSq

/-- The computed anchor-minus-oscillation quantity is a valid uniform norm
lower bound throughout the displayed rational box. -/
theorem uniformNormLower_le (polynomial : GaussianPolynomial) {box : Box}
    {point : Gaussian} (inside : box.Contains point) :
    uniformNormLower polynomial box <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval point) := by
  have anchorInside : box.Contains box.anchor := box.contains_anchor
  have distance :
      RFAP.ConstructiveGaussian.Gaussian.normSq (box.anchor - point) <=
        box.diagonalSq := by
    have reverseDistance := box.normSq_sub_anchor_le inside
    have reverse : box.anchor - point = -(point - box.anchor) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact reverseDistance
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval box.anchor - polynomial.eval point) <=
        RFAP.PolynomialBounds.denseLipschitzBound polynomial box *
          box.diagonalSq :=
    (RFAP.PolynomialBounds.normSq_eval_sub_eval_le_denseLipschitzBound
      polynomial anchorInside inside).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distance
          (RFAP.PolynomialBounds.denseLipschitzBound_pos polynomial box).le)
  have triangle :=
    RFAP.ConstructiveGaussian.Gaussian.half_normSq_sub_le_normSq_sub
      (polynomial.eval box.anchor) (polynomial.eval point)
  unfold uniformNormLower
  apply (sub_le_iff_le_add).2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval box.anchor) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval box.anchor - polynomial.eval point) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval point) :=
      (sub_le_iff_le_add).1 triangle
    _ <=
        (RFAP.PolynomialBounds.denseLipschitzBound polynomial box *
            box.diagonalSq) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval point) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct differenceBound _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval point) +
        RFAP.PolynomialBounds.denseLipschitzBound polynomial box *
          box.diagonalSq :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- Uniform norm lower bound based on an arbitrary displayed sample and an
ambient box.  This form supports constructing a smaller positive box while
reusing one finite Lipschitz scan of its ambient box. -/
def sampledNormLower (polynomial : GaussianPolynomial) (sample : Gaussian)
    (ambient cell : Box) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval sample) / 2 -
    RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
      cell.diagonalSq

/-- The sample-based lower bound is valid throughout the refined cell. -/
theorem sampledNormLower_le (polynomial : GaussianPolynomial)
    (sample : Gaussian) {ambient cell : Box}
    (sampleInside : cell.Contains sample) (refines : cell.Refines ambient)
    {point : Gaussian} (inside : cell.Contains point) :
    sampledNormLower polynomial sample ambient cell <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval point) := by
  have sampleAmbient := refines.contains sampleInside
  have pointAmbient := refines.contains inside
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval sample - polynomial.eval point) <=
        RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
          cell.diagonalSq :=
    (RFAP.PolynomialBounds.normSq_eval_sub_eval_le_denseLipschitzBound
      polynomial sampleAmbient pointAmbient).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (cell.normSq_sub_le_diagonalSq sampleInside inside)
          (RFAP.PolynomialBounds.denseLipschitzBound_pos
            polynomial ambient).le)
  have triangle :=
    RFAP.ConstructiveGaussian.Gaussian.half_normSq_sub_le_normSq_sub
      (polynomial.eval sample) (polynomial.eval point)
  unfold sampledNormLower
  apply (sub_le_iff_le_add).2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval sample) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval sample - polynomial.eval point) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval point) :=
      (sub_le_iff_le_add).1 triangle
    _ <=
        (RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
            cell.diagonalSq) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval point) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct differenceBound _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval point) +
        RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
          cell.diagonalSq :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- Positive radius threshold used for a sampled polynomial norm. -/
def sampledSafeRadius (valueNorm lipschitz : Coordinate) : Coordinate :=
  valueNorm / (8 * lipschitz) / 4

private theorem sampledNormLower_positive_of_radius
    {valueNorm lipschitz radius : Coordinate}
    (valuePositive : 0 < valueNorm) (lipschitzPositive : 0 < lipschitz)
    (radiusPositive : 0 < radius) (radius_le_one : radius <= 1)
    (radius_le_safe : radius <= sampledSafeRadius valueNorm lipschitz) :
    0 < valueNorm / 2 - lipschitz * (8 * radius ^ 2) := by
  have radiusSq_le_radius : radius ^ 2 <= radius := by
    rw [pow_two]
    calc
      radius * radius <= radius * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radius_le_one radiusPositive.le
      _ = radius := by ring1
  have eightLipschitzPositive : 0 < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have error_le_quarter :
      lipschitz * (8 * radius ^ 2) <= valueNorm / 4 := by
    calc
      lipschitz * (8 * radius ^ 2) =
          (8 * lipschitz) * radius ^ 2 := by ring1
      _ <= (8 * lipschitz) * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusSq_le_radius eightLipschitzPositive.le
      _ <= (8 * lipschitz) * sampledSafeRadius valueNorm lipschitz :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radius_le_safe eightLipschitzPositive.le
      _ = valueNorm / 4 := by
        unfold sampledSafeRadius
        calc
          (8 * lipschitz) * (valueNorm / (8 * lipschitz) / 4) =
              (valueNorm / (8 * lipschitz) * (8 * lipschitz)) / 4 := by
            simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
            ring1
          _ = valueNorm / 4 := by
            rw [RFAP.ExplicitField.div_mul_cancel valueNorm
              (ne_of_gt eightLipschitzPositive)]
  have quarter_lt_half : valueNorm / 4 < valueNorm / 2 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 4)).2
    calc
      valueNorm = valueNorm * 1 := by ring1
      _ < valueNorm * 2 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          valuePositive (by decide)
      _ = (valueNorm / 2) * 4 := by
        calc
          valueNorm * 2 =
              (valueNorm / 2 * 2) * 2 := by
            rw [RFAP.ExplicitField.div_mul_cancel valueNorm
              (by decide : (2 : Coordinate) ≠ 0)]
          _ = (valueNorm / 2) * 4 := by ring1
  exact RFAP.ConstructiveFraction.sub_pos_direct
    (error_le_quarter.trans_lt quarter_lt_half)

/-- One checked rational surface box for the algebraic differential
`p(x) dx/y`.  The two division-free density inequalities cover the two
possible sizes of the sheet norm: below one, `density_below_numerator`
controls the quotient, while above one `density_valid` does.  Together they
give a square-root-free lower bound for `‖p(x)/y‖²` whenever `y² = f(x)`.
The positive denominator bound also keeps the whole box clear of branch
points. -/
structure SurfaceCell {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) where
  face : Face
  box : Box
  proper : box.Proper
  densityLower : Coordinate
  densityLower_nonnegative : 0 <= densityLower
  denominatorLower : Coordinate
  denominatorLower_positive : 0 < denominatorLower
  denominator_apart : forall point : Gaussian, box.Contains point ->
    denominatorLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (curve.polynomial.eval point)
  density_below_numerator : forall point : Gaussian, box.Contains point ->
    densityLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((coefficientPolynomial coefficients).eval point)
  density_valid : forall point : Gaussian, box.Contains point ->
    densityLower *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (curve.polynomial.eval point) <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((coefficientPolynomial coefficients).eval point)

/-- One surface cell together with the strict density fact needed to make its
exact positive box area contribute strictly positive energy. -/
structure PositiveSurfaceCell {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) where
  cell : SurfaceCell curve coefficients
  density_positive : 0 < cell.densityLower

namespace SurfaceCell

/-- Build a fully checked surface cell from a face, a proper rational box,
and two decidable rational positivity checks.  All denominator-apartness and
density-validity fields follow from the finite polynomial bounds above. -/
def ofBox {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) (face : Face) (box : Box)
    (proper : box.Proper)
    (numeratorPositive :
      0 < uniformNormLower (coefficientPolynomial coefficients) box)
    (denominatorPositive :
      0 < uniformNormLower curve.polynomial box) :
    SurfaceCell curve coefficients where
  face := face
  box := box
  proper := proper
  densityLower :=
    uniformNormLower (coefficientPolynomial coefficients) box /
      (1 + RFAP.PolynomialBounds.denseEvalNormMajorant curve.polynomial box)
  densityLower_nonnegative :=
    RFAP.ConstructiveFraction.div_nonneg_direct numeratorPositive.le
      ((by decide : (0 : Coordinate) < 1).trans
        (lt_add_of_pos_right 1
          (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
            curve.polynomial box))).le
  denominatorLower := uniformNormLower curve.polynomial box
  denominatorLower_positive := denominatorPositive
  denominator_apart := fun point inside =>
    uniformNormLower_le curve.polynomial inside
  density_below_numerator := by
    intro point inside
    let numeratorLower :=
      uniformNormLower (coefficientPolynomial coefficients) box
    let denominatorScale :=
      1 + RFAP.PolynomialBounds.denseEvalNormMajorant curve.polynomial box
    have denominatorScalePositive : 0 < denominatorScale :=
      (by decide : (0 : Coordinate) < 1).trans
        (lt_add_of_pos_right 1
          (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
            curve.polynomial box))
    have numeratorNonnegative : 0 <= numeratorLower := numeratorPositive.le
    have one_le_scale : (1 : Coordinate) <= denominatorScale :=
      le_add_of_nonneg_right
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
          curve.polynomial box).le
    calc
      numeratorLower / denominatorScale <= numeratorLower :=
        (RFAP.ConstructiveFraction.div_le_iff_pos
          denominatorScalePositive).2 (by
            calc
              numeratorLower = numeratorLower * 1 := by ring1
              _ <= numeratorLower * denominatorScale :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  one_le_scale numeratorNonnegative)
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
          ((coefficientPolynomial coefficients).eval point) :=
        uniformNormLower_le (coefficientPolynomial coefficients) inside
  density_valid := by
    intro point inside
    let numeratorLower :=
      uniformNormLower (coefficientPolynomial coefficients) box
    let denominatorScale :=
      1 + RFAP.PolynomialBounds.denseEvalNormMajorant curve.polynomial box
    have denominatorScalePositive : 0 < denominatorScale :=
      (by decide : (0 : Coordinate) < 1).trans
        (lt_add_of_pos_right 1
          (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
            curve.polynomial box))
    have quotientNonnegative : 0 <= numeratorLower / denominatorScale :=
      RFAP.ConstructiveFraction.div_nonneg_direct numeratorPositive.le
        denominatorScalePositive.le
    calc
      numeratorLower / denominatorScale *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (curve.polynomial.eval point) <=
        numeratorLower / denominatorScale * denominatorScale :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (calc
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (curve.polynomial.eval point) <=
              RFAP.PolynomialBounds.denseEvalNormMajorant
                curve.polynomial box :=
            RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
              curve.polynomial inside
          _ <= denominatorScale := le_add_of_nonneg_left (by decide))
        quotientNonnegative
      _ = numeratorLower :=
        RFAP.ExplicitField.div_mul_cancel numeratorLower
          (ne_of_gt denominatorScalePositive)
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
          ((coefficientPolynomial coefficients).eval point) :=
        uniformNormLower_le (coefficientPolynomial coefficients) inside

/-- The same two rational checks automatically make the constructed density
lower bound strictly positive. -/
theorem ofBox_density_positive {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) (face : Face) (box : Box)
    (proper : box.Proper)
    (numeratorPositive :
      0 < uniformNormLower (coefficientPolynomial coefficients) box)
    (denominatorPositive :
      0 < uniformNormLower curve.polynomial box) :
    0 < (ofBox curve coefficients face box proper numeratorPositive
      denominatorPositive).densityLower :=
  RFAP.ConstructiveFraction.div_pos_direct numeratorPositive
    ((by decide : (0 : Coordinate) < 1).trans
      (lt_add_of_pos_right 1
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
          curve.polynomial box)))

/-- Construct one strictly positive surface box for every displayed nonzero
differential combination.  A bounded coefficient-count scan chooses a common
clear rational point, and an explicit minimum of two rational safe radii
shrinks a proper square around it. -/
def findPositive {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients)
    (face : Face) : PositiveSurfaceCell curve coefficients := by
  let numerator := coefficientPolynomial coefficients
  let clear := findClearEvaluation curve coefficients nonzero
  let ambient := CCL.BoxTransport.centeredBox clear.point 1 (by decide)
  let numeratorValue :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (numerator.eval clear.point)
  let denominatorValue :=
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval clear.point)
  let numeratorLipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound numerator ambient
  let denominatorLipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound curve.polynomial ambient
  let numeratorRadius := sampledSafeRadius numeratorValue numeratorLipschitz
  let denominatorRadius :=
    sampledSafeRadius denominatorValue denominatorLipschitz
  let radius := min 1 (min numeratorRadius denominatorRadius)
  have numeratorValuePositive : 0 < numeratorValue :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos clear.numerator_nonzero
  have denominatorValuePositive : 0 < denominatorValue :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos clear.denominator_nonzero
  have numeratorLipschitzPositive : 0 < numeratorLipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos numerator ambient
  have denominatorLipschitzPositive : 0 < denominatorLipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos curve.polynomial ambient
  have numeratorRadiusPositive : 0 < numeratorRadius := by
    unfold numeratorRadius sampledSafeRadius
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct numeratorValuePositive
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          numeratorLipschitzPositive)) (by decide)
  have denominatorRadiusPositive : 0 < denominatorRadius := by
    unfold denominatorRadius sampledSafeRadius
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct denominatorValuePositive
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          denominatorLipschitzPositive)) (by decide)
  have radiusPositive : 0 < radius := by
    unfold radius
    exact lt_min (by decide) (lt_min numeratorRadiusPositive
      denominatorRadiusPositive)
  have radius_le_one : radius <= 1 := by
    unfold radius
    exact min_le_left _ _
  have radius_le_numerator : radius <= numeratorRadius := by
    unfold radius
    exact (min_le_right _ _).trans (min_le_left _ _)
  have radius_le_denominator : radius <= denominatorRadius := by
    unfold radius
    exact (min_le_right _ _).trans (min_le_right _ _)
  let cellBox := CCL.BoxTransport.centeredBox clear.point radius
    radiusPositive.le
  have cellProper : cellBox.Proper := by
    change clear.point.re - radius < clear.point.re + radius /\
      clear.point.im - radius < clear.point.im + radius
    constructor
    · exact (sub_lt_self clear.point.re radiusPositive).trans
        (lt_add_of_pos_right clear.point.re radiusPositive)
    · exact (sub_lt_self clear.point.im radiusPositive).trans
        (lt_add_of_pos_right clear.point.im radiusPositive)
  have clearInside : cellBox.Contains clear.point := by
    exact
      ⟨sub_le_self clear.point.re radiusPositive.le,
        le_add_of_nonneg_right radiusPositive.le,
        sub_le_self clear.point.im radiusPositive.le,
        le_add_of_nonneg_right radiusPositive.le⟩
  have cellRefines : cellBox.Refines ambient := by
    exact
      ⟨RFAP.ConstructiveFraction.sub_le_sub_left_direct radius_le_one
          clear.point.re,
        by
          calc
            clear.point.re + radius = radius + clear.point.re :=
              RFAP.ConstructiveFraction.add_comm _ _
            _ <= 1 + clear.point.re :=
              add_le_add_left radius_le_one clear.point.re
            _ = clear.point.re + 1 :=
              RFAP.ConstructiveFraction.add_comm _ _,
        RFAP.ConstructiveFraction.sub_le_sub_left_direct radius_le_one
          clear.point.im,
        by
          calc
            clear.point.im + radius = radius + clear.point.im :=
              RFAP.ConstructiveFraction.add_comm _ _
            _ <= 1 + clear.point.im :=
              add_le_add_left radius_le_one clear.point.im
            _ = clear.point.im + 1 :=
              RFAP.ConstructiveFraction.add_comm _ _⟩
  have numeratorLowerPositive :
      0 < sampledNormLower numerator clear.point ambient cellBox := by
    unfold sampledNormLower
    rw [CCL.BoxTransport.centeredBox_diagonalSq]
    exact sampledNormLower_positive_of_radius numeratorValuePositive
      numeratorLipschitzPositive radiusPositive radius_le_one
      radius_le_numerator
  have denominatorLowerPositive :
      0 < sampledNormLower curve.polynomial clear.point ambient cellBox := by
    unfold sampledNormLower
    rw [CCL.BoxTransport.centeredBox_diagonalSq]
    exact sampledNormLower_positive_of_radius denominatorValuePositive
      denominatorLipschitzPositive radiusPositive radius_le_one
      radius_le_denominator
  let denominatorScale :=
    1 + RFAP.PolynomialBounds.denseEvalNormMajorant curve.polynomial ambient
  have denominatorScalePositive : 0 < denominatorScale :=
    (by decide : (0 : Coordinate) < 1).trans
      (lt_add_of_pos_right 1
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
          curve.polynomial ambient))
  let cell : SurfaceCell curve coefficients :=
    { face := face
      box := cellBox
      proper := cellProper
      densityLower :=
        sampledNormLower numerator clear.point ambient cellBox /
          denominatorScale
      densityLower_nonnegative :=
        RFAP.ConstructiveFraction.div_nonneg_direct
          numeratorLowerPositive.le denominatorScalePositive.le
      denominatorLower :=
        sampledNormLower curve.polynomial clear.point ambient cellBox
      denominatorLower_positive := denominatorLowerPositive
      denominator_apart := fun point inside =>
        sampledNormLower_le curve.polynomial clear.point clearInside
          cellRefines inside
      density_below_numerator := by
        intro point inside
        have numeratorNonnegative :
            0 <= sampledNormLower numerator clear.point ambient cellBox :=
          numeratorLowerPositive.le
        have one_le_scale : (1 : Coordinate) <= denominatorScale := by
          unfold denominatorScale
          exact le_add_of_nonneg_right
            (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
              curve.polynomial ambient).le
        calc
          sampledNormLower numerator clear.point ambient cellBox /
                denominatorScale <=
              sampledNormLower numerator clear.point ambient cellBox :=
            (RFAP.ConstructiveFraction.div_le_iff_pos
              denominatorScalePositive).2 (by
                calc
                  sampledNormLower numerator clear.point ambient cellBox =
                      sampledNormLower numerator clear.point ambient cellBox *
                        1 := by ring1
                  _ <= sampledNormLower numerator clear.point ambient cellBox *
                        denominatorScale :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      one_le_scale numeratorNonnegative)
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
                (numerator.eval point) :=
            sampledNormLower_le numerator clear.point clearInside cellRefines
              inside
      density_valid := by
        intro point inside
        have pointAmbient := cellRefines.contains inside
        have quotientNonnegative :
            0 <= sampledNormLower numerator clear.point ambient cellBox /
              denominatorScale :=
          RFAP.ConstructiveFraction.div_nonneg_direct
            numeratorLowerPositive.le denominatorScalePositive.le
        calc
          sampledNormLower numerator clear.point ambient cellBox /
                denominatorScale *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (curve.polynomial.eval point) <=
            sampledNormLower numerator clear.point ambient cellBox /
              denominatorScale * denominatorScale :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (calc
                RFAP.ConstructiveGaussian.Gaussian.normSq
                    (curve.polynomial.eval point) <=
                    RFAP.PolynomialBounds.denseEvalNormMajorant
                      curve.polynomial ambient :=
                  RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
                    curve.polynomial pointAmbient
                _ <= denominatorScale := by
                  unfold denominatorScale
                  exact le_add_of_nonneg_left (by decide))
              quotientNonnegative
          _ = sampledNormLower numerator clear.point ambient cellBox :=
            RFAP.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorScalePositive)
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
              (numerator.eval point) :=
            sampledNormLower_le numerator clear.point clearInside cellRefines
              inside }
  exact
    { cell := cell
      density_positive :=
        RFAP.ConstructiveFraction.div_pos_direct numeratorLowerPositive
          denominatorScalePositive }

/-- Forget the geometric sidecar only at the generic rational-energy layer.
The area is computed from the displayed box rather than supplied separately. -/
def toEnergyCell {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.FiniteEnergy.Cell where
  areaLower := RFAP.FiniteMeasure.boxContent cell.box
  densityLower := cell.densityLower
  areaLower_nonnegative := RFAP.FiniteMeasure.boxContent_nonneg cell.box
  densityLower_nonnegative := cell.densityLower_nonnegative

/-- The displayed denominator is uniformly nonzero on the whole rational
box. -/
theorem denominator_normSq_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) {point : Gaussian}
    (inside : cell.box.Contains point) :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval point) :=
  cell.denominatorLower_positive.trans_le (cell.denominator_apart point inside)

/-- The stronger-denominator branch of the division-free local check is a
lower bound for `‖p‖²/‖f‖²`.  The actual `p/y` density is handled below by
combining this fact with `density_below_numerator`. -/
theorem densityLower_le_quotient {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) {point : Gaussian}
    (inside : cell.box.Contains point) :
    cell.densityLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((coefficientPolynomial coefficients).eval point) /
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (curve.polynomial.eval point) :=
  (RFAP.ConstructiveFraction.le_div_iff_pos
    (cell.denominator_normSq_positive inside)).2
      (cell.density_valid point inside)

/-- Square-root-free physical-density comparison.  If `sheetNorm` is the
squared norm of a sheet value, so that its square is `‖f(x)‖²`, the two local
density checks imply `densityLower * sheetNorm ≤ ‖p(x)‖²`.  The proof splits
at one and uses only ordered rational arithmetic. -/
theorem densityLower_mul_sheetNorm_le_numerator {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) {point : Gaussian}
    (inside : cell.box.Contains point) (sheetNorm : Coordinate)
    (sheetNormNonnegative : 0 <= sheetNorm)
    (sheetNorm_sq : sheetNorm ^ 2 =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (curve.polynomial.eval point)) :
    cell.densityLower * sheetNorm <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((coefficientPolynomial coefficients).eval point) := by
  by_cases small : sheetNorm <= 1
  · calc
      cell.densityLower * sheetNorm <= cell.densityLower * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct small
          cell.densityLower_nonnegative
      _ = cell.densityLower := by ring1
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
          ((coefficientPolynomial coefficients).eval point) :=
        cell.density_below_numerator point inside
  · have one_le_sheetNorm : (1 : Coordinate) <= sheetNorm :=
      (lt_of_not_ge small).le
    have sheetNorm_le_sq : sheetNorm <= sheetNorm ^ 2 := by
      calc
        sheetNorm = 1 * sheetNorm := by ring1
        _ <= sheetNorm * sheetNorm :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            one_le_sheetNorm sheetNormNonnegative
        _ = sheetNorm ^ 2 := by ring1
    calc
      cell.densityLower * sheetNorm <=
          cell.densityLower * sheetNorm ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sheetNorm_le_sq cell.densityLower_nonnegative
      _ = cell.densityLower *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (curve.polynomial.eval point) := by rw [sheetNorm_sq]
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
          ((coefficientPolynomial coefficients).eval point) :=
        cell.density_valid point inside

/-- Every checked cell density is therefore a genuine lower bound for the
standard hyperelliptic differential density `‖p(x)/y‖²` at an exact sheet
value `y`. -/
theorem densityLower_le_differentialNormSq {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) {point sheet : Gaussian}
    (inside : cell.box.Contains point)
    (sheet_square : sheet * sheet = curve.polynomial.eval point) :
    cell.densityLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((coefficientPolynomial coefficients).eval point / sheet) := by
  have denominatorNonzero : curve.polynomial.eval point ≠ 0 := by
    intro denominatorZero
    have positive := cell.denominator_normSq_positive inside
    rw [denominatorZero,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at positive
    exact (lt_irrefl 0 positive)
  have sheetNonzero : sheet ≠ 0 := by
    intro sheetZero
    apply denominatorNonzero
    rw [← sheet_square, sheetZero,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  have sheetNormPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq sheet :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos sheetNonzero
  have sheetNormSquare :
      RFAP.ConstructiveGaussian.Gaussian.normSq sheet ^ 2 =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (curve.polynomial.eval point) := by
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq sheet ^ 2 =
          RFAP.ConstructiveGaussian.Gaussian.normSq sheet *
            RFAP.ConstructiveGaussian.Gaussian.normSq sheet := by ring1
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq (sheet * sheet) :=
        (RFAP.ConstructiveGaussian.Gaussian.normSq_mul sheet sheet).symm
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (curve.polynomial.eval point) := by rw [sheet_square]
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _ sheetNonzero]
  exact (RFAP.ConstructiveFraction.le_div_iff_pos sheetNormPositive).2
    (cell.densityLower_mul_sheetNorm_le_numerator inside _
      sheetNormPositive.le sheetNormSquare)

/-- Properness supplies strict positivity of the exact box area. -/
theorem area_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    0 < cell.toEnergyCell.areaLower :=
  RFAP.FiniteMeasure.boxContent_pos_of_proper cell.proper

end SurfaceCell

/-- Generic energy cells obtained from a finite family of checked surface
boxes. -/
def energyCells {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cells : Fin cellCount -> SurfaceCell curve coefficients) :
    Fin cellCount -> CCL.Riemann.FiniteEnergy.Cell :=
  fun index => (cells index).toEnergyCell

/-- Exact finite lower surface sum of the geometry-backed rational boxes. -/
def surfaceEnergy {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cells : Fin cellCount -> SurfaceCell curve coefficients) : Coordinate :=
  CCL.Riemann.FiniteEnergy.cellEnergy (energyCells cells)

/-- A singleton geometry-backed surface sum is exactly its box content times
its checked density lower bound. -/
theorem surfaceEnergy_one {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    surfaceEnergy (fun _ : Fin 1 => cell) =
      RFAP.FiniteMeasure.boxContent cell.box * cell.densityLower := by
  unfold surfaceEnergy CCL.Riemann.FiniteEnergy.cellEnergy energyCells
    SurfaceCell.toEnergyCell CCL.Riemann.FiniteEnergy.Cell.contribution
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change _ + 0 = _
  ring1

/-- Exact rational contribution of displayed reversed internal-edge pairs.
Every pair is represented by one value and its additive inverse. -/
def pairedBoundarySum {edgePairCount : Nat}
    (edgePairValues : Fin edgePairCount -> Coordinate) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
    edgePairValues index + -edgePairValues index

/-- All displayed internal-edge pairs cancel by finite rational arithmetic. -/
theorem pairedBoundarySum_zero {edgePairCount : Nat}
    (edgePairValues : Fin edgePairCount -> Coordinate) :
    pairedBoundarySum edgePairValues = 0 := by
  unfold pairedBoundarySum
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun _ => (0 : Coordinate)) (fun index => by ring1)]
  exact RFAP.ConstructiveFiniteMatrix.sumFin_zero

/-- Exact finite cut-surface decomposition for an arbitrary displayed
Gaussian-rational differential combination.  Unlike the normalized transport
record below, this interface does not presuppose an inverse of the A-period
matrix. -/
structure RawBoundaryReduction {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> SurfaceCell curve coefficients) where
  edgePairCount : Nat
  edgePairValues : Fin edgePairCount -> Coordinate
  remainder : Coordinate
  remainder_nonnegative : 0 <= remainder
  raw_eq_decomposition :
    CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) =
      surfaceEnergy cells + pairedBoundarySum edgePairValues + remainder

namespace RawBoundaryReduction

/-- Paired internal edges cancel, leaving the checked local surface sum below
the raw A/B boundary pairing at the same finite sample. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (reduction : RawBoundaryReduction data coefficients sampleIndex cells) :
    surfaceEnergy cells <= CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
      coefficients (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  have raw_eq :
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) =
        surfaceEnergy cells + reduction.remainder := by
    calc
      _ = surfaceEnergy cells +
          pairedBoundarySum reduction.edgePairValues + reduction.remainder :=
        reduction.raw_eq_decomposition
      _ = surfaceEnergy cells + reduction.remainder := by
        rw [pairedBoundarySum_zero]
        ring1
  calc
    surfaceEnergy cells <= surfaceEnergy cells + reduction.remainder :=
      le_add_of_nonneg_right reduction.remainder_nonnegative
    _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := raw_eq.symm

end RawBoundaryReduction

/-- Exact finite cut-surface decomposition of the raw second-relation
pairing.  The local lower sum is accompanied by explicitly paired internal
edges and a nonnegative rational remainder for the difference between lower
cell bounds and the complete finite surface computation. -/
structure BoundaryReduction {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (vector : RationalVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)) where
  edgePairCount : Nat
  edgePairValues : Fin edgePairCount -> Coordinate
  remainder : Coordinate
  remainder_nonnegative : 0 <= remainder
  raw_eq_decomposition :
    CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) =
      surfaceEnergy cells + pairedBoundarySum edgePairValues + remainder

namespace BoundaryReduction

/-- The exact decomposition, automatic edge cancellation, and nonnegative
remainder derive the surface lower bound consumed by energy transport. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : BoundaryReduction data vector sampleIndex cells) :
    surfaceEnergy cells <= CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
        vector)
      (sampledMatrix data.aMatrix sampleIndex)
      (sampledMatrix data.bMatrix sampleIndex) := by
  have raw_eq :
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
          (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) =
        surfaceEnergy cells + reduction.remainder := by
    calc
      _ = surfaceEnergy cells +
          pairedBoundarySum reduction.edgePairValues + reduction.remainder :=
        reduction.raw_eq_decomposition
      _ = surfaceEnergy cells + reduction.remainder := by
        rw [pairedBoundarySum_zero]
        ring1
  calc
    surfaceEnergy cells <= surfaceEnergy cells + reduction.remainder :=
      le_add_of_nonneg_right reduction.remainder_nonnegative
    _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
          (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := raw_eq.symm

end BoundaryReduction

/-! ## Controlled finite boundary error

At a finite quadrature index the boundary calculation need not be literally
exact.  The operational second relation instead supplies a displayed
nonnegative rational error which can be driven below the positive local
surface contribution. -/

/-- Finite cut-surface decomposition with an explicit rational boundary
error.  Every quantity in the identity is a displayed rational at the chosen
sample index. -/
structure ControlledBoundaryReduction {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (vector : RationalVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)) where
  edgePairCount : Nat
  edgePairValues : Fin edgePairCount -> Coordinate
  boundaryError : Coordinate
  boundaryError_nonnegative : 0 <= boundaryError
  remainder : Coordinate
  remainder_nonnegative : 0 <= remainder
  raw_add_error_eq_decomposition :
    CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
          (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) + boundaryError =
      surfaceEnergy cells + pairedBoundarySum edgePairValues + remainder

namespace ControlledBoundaryReduction

/-- The surface contribution after paying the displayed finite boundary
error. -/
def effectiveSurfaceEnergy {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells) :
    Coordinate :=
  surfaceEnergy cells - reduction.boundaryError

/-- Automatic paired-edge cancellation turns the controlled decomposition
into the usable raw-energy lower bound. -/
theorem effectiveSurfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells) :
    reduction.effectiveSurfaceEnergy <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  have decomposition :
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
            (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
              vector)
            (sampledMatrix data.aMatrix sampleIndex)
            (sampledMatrix data.bMatrix sampleIndex) + reduction.boundaryError =
        surfaceEnergy cells + reduction.remainder := by
    calc
      _ = surfaceEnergy cells +
          pairedBoundarySum reduction.edgePairValues + reduction.remainder :=
        reduction.raw_add_error_eq_decomposition
      _ = surfaceEnergy cells + reduction.remainder := by
        rw [pairedBoundarySum_zero]
        ring1
  have surface_le_raw_add_error :
      surfaceEnergy cells <=
        CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
              (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data
                sampleIndex vector)
              (sampledMatrix data.aMatrix sampleIndex)
              (sampledMatrix data.bMatrix sampleIndex) +
            reduction.boundaryError := by
    calc
      surfaceEnergy cells <= surfaceEnergy cells + reduction.remainder :=
        le_add_of_nonneg_right reduction.remainder_nonnegative
      _ = _ := decomposition.symm
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    surface_le_raw_add_error (-reduction.boundaryError)
  unfold effectiveSurfaceEnergy
  simpa only [RFAP.ConstructiveFraction.sub_eq_add_neg_direct] using
    (shifted.trans (le_of_eq (by ring1)))

/-- Once the controlled error is smaller than the positive surface sum, the
effective raw-energy lower bound is strictly positive. -/
theorem effectiveSurfaceEnergy_positive {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells)
    (error_lt_surface : reduction.boundaryError < surfaceEnergy cells) :
    0 < reduction.effectiveSurfaceEnergy := by
  unfold effectiveSurfaceEnergy
  exact RFAP.ConstructiveFraction.sub_pos_direct error_lt_surface

/-- Package the positive effective lower bound as the singleton cell consumed
by the generic normalization transport.  Its area is derived from the
geometry-backed surface family and boundary error, not supplied separately. -/
def effectiveCell {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells)
    (error_lt_surface : reduction.boundaryError < surfaceEnergy cells) :
    CCL.Riemann.FiniteEnergy.Cell where
  areaLower := reduction.effectiveSurfaceEnergy
  densityLower := 1
  areaLower_nonnegative :=
    (reduction.effectiveSurfaceEnergy_positive error_lt_surface).le
  densityLower_nonnegative := by decide

/-- Singleton effective-energy family used after paying the controlled
boundary error. -/
def effectiveCells {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells)
    (error_lt_surface : reduction.boundaryError < surfaceEnergy cells) :
    Fin 1 -> CCL.Riemann.FiniteEnergy.Cell :=
  fun _ => reduction.effectiveCell error_lt_surface

@[simp] theorem cellEnergy_effectiveCells {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : ControlledBoundaryReduction data vector sampleIndex cells)
    (error_lt_surface : reduction.boundaryError < surfaceEnergy cells) :
    CCL.Riemann.FiniteEnergy.cellEnergy
        (reduction.effectiveCells error_lt_surface) =
      reduction.effectiveSurfaceEnergy := by
  unfold CCL.Riemann.FiniteEnergy.cellEnergy
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change reduction.effectiveSurfaceEnergy * 1 + 0 =
    reduction.effectiveSurfaceEnergy
  rw [RFAP.ConstructiveFraction.mul_one_direct, _root_.add_zero]

end ControlledBoundaryReduction

namespace BoundaryReduction

/-- An exact decomposition is the zero-error special case of the controlled
finite boundary interface. -/
def toControlled {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      SurfaceCell curve
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : BoundaryReduction data vector sampleIndex cells) :
    ControlledBoundaryReduction data vector sampleIndex cells where
  edgePairCount := reduction.edgePairCount
  edgePairValues := reduction.edgePairValues
  boundaryError := 0
  boundaryError_nonnegative := by decide
  remainder := reduction.remainder
  remainder_nonnegative := reduction.remainder_nonnegative
  raw_add_error_eq_decomposition := by
    rw [_root_.add_zero]
    exact reduction.raw_eq_decomposition

end BoundaryReduction

/-- Fixed face used for the automatically constructed positive local box.
Either lifted upper face is an actual face of both degree-shape cell models;
the zero lift gives one canonical finite choice. -/
def canonicalSurfaceFace : Face where
  hemisphere := .upper
  lift := CCL.Riemann.HyperellipticCells.sheetZero

/-- Canonical positive local surface cell for any explicitly nonzero raw
differential combination.  Its construction precedes period normalization. -/
def canonicalRawPositiveCell {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    PositiveSurfaceCell curve coefficients :=
  SurfaceCell.findPositive curve coefficients nonzero canonicalSurfaceFace

/-- The fixed singleton lower-sum family associated with a raw coefficient
vector.  In particular, it does not vary with the period sample index. -/
def rawRequestCells {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    Fin 1 -> SurfaceCell curve coefficients :=
  fun _ => (canonicalRawPositiveCell curve coefficients nonzero).cell

/-- The canonical raw singleton has a fixed strictly positive rational lower
energy before any boundary comparison or matrix inverse is used. -/
theorem rawRequestSurfaceEnergy_positive {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector coefficients) :
    0 < surfaceEnergy (rawRequestCells curve coefficients nonzero) := by
  unfold surfaceEnergy
  apply CCL.Riemann.FiniteEnergy.cellEnergy_positive_of_cell _ 0
  · exact (canonicalRawPositiveCell curve coefficients nonzero).cell.area_positive
  · exact (canonicalRawPositiveCell curve coefficients nonzero).density_positive

/-- One global pre-normalization second-relation certificate.  For every raw
coefficient vector and synchronized sample, it may isolate any one checked
surface box in the finite boundary decomposition.  Restricting this interface
to a singleton prevents duplicated cells from asserting an artificial lower
sum larger than the total raw energy. -/
structure RawCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  boundaryReduction : forall (coefficients : GaussianVector genus)
    (sampleIndex : Nat) (cell : SurfaceCell curve coefficients),
    RawBoundaryReduction data coefficients sampleIndex (fun _ : Fin 1 => cell)

/-- Minimal raw second-relation statement.  Every one checked surface box is
bounded by the synchronized period-pairing energy for the same coefficient
vector and sample.  The cancellable edge-pair list and nonnegative remainder
of `RawCertificate` are reconstructed from this inequality. -/
structure RawSurfaceLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  lower : forall (coefficients : GaussianVector genus) (sampleIndex : Nat)
    (cell : SurfaceCell curve coefficients),
    surfaceEnergy (fun _ : Fin 1 => cell) <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex)

namespace RawSurfaceLowerCertificate

/-- The raw finite surface theorem already forces every synchronized
`A`-period sample to have trivial left kernel, in arbitrary genus and before
any inverse certificate is supplied.  A purported nonzero kernel vector has
zero boundary energy, while its canonically constructed rational surface box
has strictly positive lower energy. -/
theorem aPeriodSample_leftKernel_trivial {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) (sampleIndex : Nat)
    (coefficients : GaussianVector genus)
    (kernel : forall cycle,
      CCL.Riemann.FiniteEnergy.periodCombination coefficients
        (sampledMatrix data.aMatrix sampleIndex) cycle = 0) :
    forall row, coefficients row = 0 := by
  intro row
  by_cases coefficientZero : coefficients row = 0
  · exact coefficientZero
  · let nonzero : CCL.Riemann.FiniteEnergy.NonzeroGaussianVector
        coefficients :=
      { index := row
        coefficient_nonzero := coefficientZero }
    let positiveCell := canonicalRawPositiveCell curve coefficients nonzero
    have localPositive :
        0 < surfaceEnergy (fun _ : Fin 1 => positiveCell.cell) := by
      unfold surfaceEnergy
      apply CCL.Riemann.FiniteEnergy.cellEnergy_positive_of_cell _ 0
      · exact positiveCell.cell.area_positive
      · exact positiveCell.density_positive
    have localLower := certificate.lower coefficients sampleIndex
      positiveCell.cell
    have rawZero :=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm_eq_zero_of_aPeriods_zero
        coefficients (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) kernel
    rw [rawZero] at localLower
    exact (not_lt_of_ge localLower localPositive).elim

/-- The all-pivots fraction-free inverse calculation therefore returns a
nonzero scalar at every synchronized finite sample.  This is a genuine
generic-genus consequence of raw surface energy; the still-separate uniform
tail lower bound is needed only to apartify the persistent inverse name. -/
theorem sampledCompleteScaledInverse_scalar_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) (sampleIndex : Nat) :
    (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
      (sampledMatrix data.aMatrix sampleIndex)).scalar ≠ 0 := by
  apply CCL.Riemann.PivotedScaledInverse.completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
  intro coefficients kernel row
  exact certificate.aPeriodSample_leftKernel_trivial sampleIndex coefficients
    kernel row

/-- The same nonvanishing statement for the canonical geometric inverse
approximation used by persistent normalization. -/
theorem canonicalInverseScalar_sample_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) (sampleIndex : Nat) :
    (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex ≠ 0 := by
  let sampled := sampledMatrix data.aMatrix sampleIndex
  let computed :=
    CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex =
        computed.scalar := by
    unfold canonicalScaledInverse computed sampled
    have samples :=
      CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) sampleIndex
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply certificate.sampledCompleteScaledInverse_scalar_nonzero sampleIndex
  rw [← scalarSample, scalarZero]

/-- Raw surface energy computes the complete finite prefix of inverse-scalar
separation.  Consequently one finite anchor/tail clearance check constructs
the uniform persistent inverse certificate in every genus. -/
def toFiniteScalarSeparationCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          CCL.FiniteGeometric.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    FiniteScalarSeparationCertificate data.aMatrix :=
  FiniteScalarSeparationCertificate.ofSampleNonzero anchor
    certificate.canonicalInverseScalar_sample_nonzero tailPositive

/-- Apartification-ready inverse lower bound obtained from raw energy and one
tail-clearance check. -/
def toScalarCandidateLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          CCL.FiniteGeometric.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  (certificate.toFiniteScalarSeparationCertificate anchor
    tailPositive).toScalarCandidateLowerCertificate

/-- Materialize the exact legacy decomposition with no artificial boundary
pairs and with the displayed difference as its nonnegative remainder. -/
def toRawCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : RawSurfaceLowerCertificate data) : RawCertificate data where
  boundaryReduction := by
    intro coefficients sampleIndex cell
    let raw := CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
      (sampledMatrix data.aMatrix sampleIndex)
      (sampledMatrix data.bMatrix sampleIndex)
    let localEnergy := surfaceEnergy (fun _ : Fin 1 => cell)
    exact
      { edgePairCount := 0
        edgePairValues := fun index => Fin.elim0 index
        remainder := raw - localEnergy
        remainder_nonnegative :=
          RFAP.ConstructiveFraction.sub_nonneg_direct
            (certificate.lower coefficients sampleIndex cell)
        raw_eq_decomposition := by
          rw [pairedBoundarySum_zero]
          unfold raw localEnergy
          ring1 }

end RawSurfaceLowerCertificate

namespace RawCertificate

/-- Forget the redundant decomposition fields while retaining precisely the
surface lower theorem they prove. -/
theorem toRawSurfaceLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : RawCertificate data) :
    RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.boundaryReduction coefficients sampleIndex cell).surfaceEnergy_le_raw

/-- The decomposed raw certificate has the same generic finite-sample
nondegeneracy consequence as its minimal surface-lower presentation. -/
theorem aPeriodSample_leftKernel_trivial {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (sampleIndex : Nat) (coefficients : GaussianVector genus)
    (kernel : forall cycle,
      CCL.Riemann.FiniteEnergy.periodCombination coefficients
        (sampledMatrix data.aMatrix sampleIndex) cycle = 0) :
    forall row, coefficients row = 0 :=
  certificate.toRawSurfaceLowerCertificate.aPeriodSample_leftKernel_trivial
    sampleIndex coefficients kernel

/-- Every complete fraction-free scalar sample is nonzero under the legacy
raw decomposition as well. -/
theorem sampledCompleteScaledInverse_scalar_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (sampleIndex : Nat) :
    (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
      (sampledMatrix data.aMatrix sampleIndex)).scalar ≠ 0 :=
  certificate.toRawSurfaceLowerCertificate.sampledCompleteScaledInverse_scalar_nonzero
    sampleIndex

/-- Raw decompositions also compute all finite prefix separation data; one
tail-clearance check produces the persistent inverse lower bound. -/
def toScalarCandidateLowerCertificate_of_tail {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          CCL.FiniteGeometric.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toRawSurfaceLowerCertificate.toScalarCandidateLowerCertificate
    anchor tailPositive

end RawCertificate

/-- The standard genus-one differential coefficient is explicitly nonzero. -/
def genusOneUnitNonzero :
    CCL.Riemann.FiniteEnergy.NonzeroGaussianVector
      CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients where
  index := 0
  coefficient_nonzero := by
    rw [CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients_apply]
    decide

/-- Fixed positive local energy for the sole standard genus-one
differential.  It depends only on the curve, not on a period sample index. -/
def genusOneRawEnergy
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1) :
    Coordinate :=
  surfaceEnergy
    (rawRequestCells curve
      CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
      genusOneUnitNonzero)

theorem genusOneRawEnergy_positive
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1) :
    0 < genusOneRawEnergy curve :=
  rawRequestSurfaceEnergy_positive curve
    CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
    genusOneUnitNonzero

/-- A one-entry coefficient polynomial is constant. -/
@[simp] theorem coefficientPolynomial_one_eval
    (coefficients : GaussianVector 1) (point : Gaussian) :
    (coefficientPolynomial coefficients).eval point = coefficients 0 := by
  unfold coefficientPolynomial
  rw [QuotientFreeList.ofFn_succ, List.ofFn_zero]
  simp [RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs]

/-- Fixed curve-dependent reference box used for all genus-one coefficient
samples. -/
def genusOneReferenceCell
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1) :
    PositiveSurfaceCell curve
      CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients :=
  canonicalRawPositiveCell curve
    CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients genusOneUnitNonzero

/-- Reuse the canonical unit-differential box for an arbitrary genus-one
coefficient.  Its density is the unit density scaled by any displayed lower
bound for the coefficient squared norm. -/
def genusOneScaledReferenceSurfaceCell
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    SurfaceCell curve coefficients := by
  let reference := (genusOneReferenceCell curve).cell
  exact
    { face := reference.face
      box := reference.box
      proper := reference.proper
      densityLower := coefficientLower * reference.densityLower
      densityLower_nonnegative :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          coefficientLowerNonnegative reference.densityLower_nonnegative
      denominatorLower := reference.denominatorLower
      denominatorLower_positive := reference.denominatorLower_positive
      denominator_apart := reference.denominator_apart
      density_below_numerator := by
        intro point inside
        have unitDensity := reference.density_below_numerator point inside
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            unitDensity coefficientLowerNonnegative
        calc
          coefficientLower * reference.densityLower <=
              coefficientLower *
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  ((coefficientPolynomial
                    CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients).eval
                      point) := scaled
          _ = coefficientLower := by
            rw [coefficientPolynomial_one_eval,
              CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients_apply,
              RFAP.ConstructiveGaussian.Gaussian.normSq_one]
            ring1
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) :=
            coefficient_lower
          _ = RFAP.ConstructiveGaussian.Gaussian.normSq
                ((coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval]
      density_valid := by
        intro point inside
        have unitDensity := reference.density_valid point inside
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            unitDensity coefficientLowerNonnegative
        calc
          (coefficientLower * reference.densityLower) *
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  (curve.polynomial.eval point) =
              coefficientLower *
                (reference.densityLower *
                  RFAP.ConstructiveGaussian.Gaussian.normSq
                    (curve.polynomial.eval point)) := by ring1
          _ <= coefficientLower *
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  ((coefficientPolynomial
                    CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients).eval
                      point) := scaled
          _ = coefficientLower := by
            rw [coefficientPolynomial_one_eval,
              CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients_apply,
              RFAP.ConstructiveGaussian.Gaussian.normSq_one]
            ring1
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) :=
            coefficient_lower
          _ = RFAP.ConstructiveGaussian.Gaussian.normSq
                ((coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval] }

def genusOneScaledReferenceSurfaceCells
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    Fin 1 -> SurfaceCell curve coefficients :=
  fun _ => genusOneScaledReferenceSurfaceCell curve coefficients
    coefficientLower coefficientLowerNonnegative coefficient_lower

/-- Exact homogeneity of the reused singleton surface lower sum. -/
theorem surfaceEnergy_genusOneScaledReferenceSurfaceCells
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    surfaceEnergy
        (genusOneScaledReferenceSurfaceCells curve coefficients
          coefficientLower coefficientLowerNonnegative coefficient_lower) =
      coefficientLower * genusOneRawEnergy curve := by
  unfold genusOneScaledReferenceSurfaceCells
  rw [surfaceEnergy_one]
  unfold genusOneScaledReferenceSurfaceCell
  dsimp only
  unfold genusOneRawEnergy rawRequestCells
  rw [surfaceEnergy_one]
  change
    RFAP.FiniteMeasure.boxContent (genusOneReferenceCell curve).cell.box *
        (coefficientLower *
          (genusOneReferenceCell curve).cell.densityLower) =
      coefficientLower *
        (RFAP.FiniteMeasure.boxContent
            (genusOneReferenceCell curve).cell.box *
          (genusOneReferenceCell curve).cell.densityLower)
  ring1

theorem genusOneScaledReferenceSurfaceCell_density_positive
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) {coefficientLower : Coordinate}
    (coefficientLowerPositive : 0 < coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    0 < (genusOneScaledReferenceSurfaceCell curve coefficients
      coefficientLower coefficientLowerPositive.le
        coefficient_lower).densityLower :=
  RFAP.ConstructiveFraction.mul_pos_direct coefficientLowerPositive
    (genusOneReferenceCell curve).density_positive

def genusOneDenominatorUpper
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1) :
    Coordinate :=
  1 + RFAP.PolynomialBounds.denseEvalNormMajorant curve.polynomial
    (genusOneReferenceCell curve).cell.box

theorem genusOneDenominatorUpper_positive
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1) :
    0 < genusOneDenominatorUpper curve :=
  (by decide : (0 : Coordinate) < 1).trans
    (lt_add_of_pos_right 1
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos curve.polynomial
        (genusOneReferenceCell curve).cell.box))

/-- Reuse one fixed denominator-clear box for an arbitrary genus-one
coefficient whose squared norm has the displayed rational lower bound. -/
def genusOneUniformSurfaceCell
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    SurfaceCell curve coefficients := by
  let reference := (genusOneReferenceCell curve).cell
  let denominatorUpper := genusOneDenominatorUpper curve
  have denominatorUpperPositive : 0 < denominatorUpper :=
    genusOneDenominatorUpper_positive curve
  exact
    { face := reference.face
      box := reference.box
      proper := reference.proper
      densityLower := coefficientLower / denominatorUpper
      densityLower_nonnegative :=
        RFAP.ConstructiveFraction.div_nonneg_direct
          coefficientLowerNonnegative denominatorUpperPositive.le
      denominatorLower := reference.denominatorLower
      denominatorLower_positive := reference.denominatorLower_positive
      denominator_apart := reference.denominator_apart
      density_below_numerator := by
        intro point inside
        have coefficientNonnegative : 0 <= coefficientLower :=
          coefficientLowerNonnegative
        have one_le_upper : (1 : Coordinate) <= denominatorUpper := by
          unfold denominatorUpper genusOneDenominatorUpper
          exact le_add_of_nonneg_right
            (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
              curve.polynomial reference.box).le
        calc
          coefficientLower / denominatorUpper <= coefficientLower :=
            (RFAP.ConstructiveFraction.div_le_iff_pos
              denominatorUpperPositive).2 (by
                calc
                  coefficientLower = coefficientLower * 1 := by ring1
                  _ <= coefficientLower * denominatorUpper :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      one_le_upper coefficientNonnegative)
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) :=
            coefficient_lower
          _ = RFAP.ConstructiveGaussian.Gaussian.normSq
                ((coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval]
      density_valid := by
        intro point inside
        have quotientNonnegative :
            0 <= coefficientLower / denominatorUpper :=
          RFAP.ConstructiveFraction.div_nonneg_direct
            coefficientLowerNonnegative denominatorUpperPositive.le
        calc
          coefficientLower / denominatorUpper *
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  (curve.polynomial.eval point) <=
              coefficientLower / denominatorUpper * denominatorUpper :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (calc
                RFAP.ConstructiveGaussian.Gaussian.normSq
                    (curve.polynomial.eval point) <=
                    RFAP.PolynomialBounds.denseEvalNormMajorant
                      curve.polynomial reference.box :=
                  RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
                    curve.polynomial inside
                _ <= denominatorUpper := by
                  unfold denominatorUpper genusOneDenominatorUpper
                  exact le_add_of_nonneg_left (by decide))
              quotientNonnegative
          _ = coefficientLower :=
            RFAP.ExplicitField.div_mul_cancel coefficientLower
              (ne_of_gt denominatorUpperPositive)
          _ <= RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) :=
            coefficient_lower
          _ = RFAP.ConstructiveGaussian.Gaussian.normSq
                ((coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval] }

def genusOneUniformSurfaceCells
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    Fin 1 -> SurfaceCell curve coefficients :=
  fun _ => genusOneUniformSurfaceCell curve coefficients coefficientLower
    coefficientLowerNonnegative coefficient_lower

theorem genusOneUniformSurfaceCell_density_positive
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) {coefficientLower : Coordinate}
    (coefficientLowerPositive : 0 < coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    0 < (genusOneUniformSurfaceCell curve coefficients coefficientLower
      coefficientLowerPositive.le coefficient_lower).densityLower :=
  RFAP.ConstructiveFraction.div_pos_direct coefficientLowerPositive
    (genusOneDenominatorUpper_positive curve)

/-- Exact fixed-box lower energy as a function of only the coefficient norm
lower. -/
def genusOneUniformSurfaceEnergy
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficientLower : Coordinate) : Coordinate :=
  RFAP.FiniteMeasure.boxContent (genusOneReferenceCell curve).cell.box *
    (coefficientLower / genusOneDenominatorUpper curve)

theorem surfaceEnergy_genusOneUniformSurfaceCells
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    (coefficients : GaussianVector 1) (coefficientLower : Coordinate)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0)) :
    surfaceEnergy
        (genusOneUniformSurfaceCells curve coefficients coefficientLower
          coefficientLowerNonnegative coefficient_lower) =
      genusOneUniformSurfaceEnergy curve coefficientLower := by
  unfold surfaceEnergy CCL.Riemann.FiniteEnergy.cellEnergy
    energyCells genusOneUniformSurfaceCells genusOneUniformSurfaceCell
    genusOneUniformSurfaceEnergy SurfaceCell.toEnergyCell
    CCL.Riemann.FiniteEnergy.Cell.contribution
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change _ + 0 = _
  ring1

theorem genusOneUniformSurfaceEnergy_positive
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1)
    {coefficientLower : Coordinate} (positive : 0 < coefficientLower) :
    0 < genusOneUniformSurfaceEnergy curve coefficientLower :=
  RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.FiniteMeasure.boxContent_pos_of_proper
      (genusOneReferenceCell curve).cell.proper)
    (RFAP.ConstructiveFraction.div_pos_direct positive
      (genusOneDenominatorUpper_positive curve))

/-- Uniform squared-norm bound already carried by the sole B-period sampler. -/
def genusOneBPeriodBound
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  (oneByOneEntryApproximation data.bMatrix).centerBound

theorem genusOneBPeriodBound_nonnegative
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) :
    0 <= genusOneBPeriodBound data :=
  (oneByOneEntryApproximation data.bMatrix).centerBound_nonneg

/-- Explicit genus-one A-period lower bound obtained by dividing the square
of the fixed raw surface energy by one plus the uniform B-period bound. -/
def genusOneAPeriodLowerSq
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  genusOneRawEnergy curve ^ 2 / (1 + genusOneBPeriodBound data)

@[simp] theorem normSq_gaussianOfRational (value : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FiniteEnergy.gaussianOfRational value) = value ^ 2 := by
  simp only [CCL.Riemann.FiniteEnergy.gaussianOfRational,
    RFAP.ConstructiveGaussian.Gaussian.normSq]
  ring1

/-- A nonzero one-entry real vector has a nonzero zeroth coefficient. -/
theorem nonzeroVector_one_coefficient
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    vector 0 ≠ 0 := by
  have indexZero : nonzero.index = 0 := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ nonzero.index.isLt)
  have coefficientNonzero := nonzero.coefficient_nonzero
  rw [indexZero] at coefficientNonzero
  exact coefficientNonzero

/-- In dimension one the adjugate-scaled coefficient has squared norm
`v² ‖A‖⁶`.  The proof uses only the scaled identity and the already finite
one-by-one scalar calculation. -/
theorem normSq_scaledNormalizedCoefficients_one
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : RationalVector 1)
    (aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index
          vector 0) =
      vector 0 ^ 2 *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (sampledMatrix data.aMatrix index 0 0) ^ 3 := by
  let sampled := sampledMatrix data.aMatrix index
  let inverse := CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampled
  let coefficients :=
    CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector
  have entryIdentity :
      coefficients 0 * sampled 0 0 =
        CCL.Riemann.FiniteEnergy.gaussianOfRational (vector 0) *
          inverse.scalar := by
    have identity := CCL.Riemann.FiniteEnergy.periodCombination_scaled_a
      vector sampled inverse
    have entry := congrArg (fun result => result 0) identity
    change CCL.Riemann.FiniteEnergy.periodCombination coefficients sampled 0 =
      CCL.Riemann.FiniteEnergy.gaussianOfRational (vector 0) *
        inverse.scalar at entry
    rw [CCL.Riemann.FiniteEnergy.periodCombination,
      RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply,
      RFAP.ConstructiveFiniteMatrix.sumFin_succ] at entry
    change coefficients 0 * sampled 0 0 + 0 = _ at entry
    rw [RFAP.ConstructiveGaussian.Gaussian.add_zero] at entry
    exact entry
  have normIdentity := congrArg
    RFAP.ConstructiveGaussian.Gaussian.normSq entryIdentity
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
    normSq_gaussianOfRational,
    CCL.Riemann.PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
      at normIdentity
  let aNorm := RFAP.ConstructiveGaussian.Gaussian.normSq (sampled 0 0)
  change RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) =
    vector 0 ^ 2 * aNorm ^ 3
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show aNorm ≠ 0 by
      intro normZero
      exact aNonzero
        (RFAP.ConstructiveGaussian.Gaussian.normSq_eq_zero.mp normZero))
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) * aNorm =
        vector 0 ^ 2 * aNorm ^ 4 := normIdentity
    _ = (vector 0 ^ 2 * aNorm ^ 3) * aNorm := by ring1

/-- Uniform lower bound for every adjugate-scaled genus-one coefficient at a
synchronized sample. -/
def genusOneScaledCoefficientLower
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : RationalVector 1) : Coordinate :=
  vector 0 ^ 2 * genusOneAPeriodLowerSq data ^ 3

def genusOneAPeriodBound
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  (oneByOneEntryApproximation data.aMatrix).centerBound

theorem genusOneAPeriodBound_nonnegative
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : 0 <= genusOneAPeriodBound data :=
  (oneByOneEntryApproximation data.aMatrix).centerBound_nonneg

/-- A strictly positive bound larger than every squared norm of the
one-by-one complete inverse scalar. -/
def genusOneScalarNormUpper
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  1 + genusOneAPeriodBound data ^ 4

theorem genusOneScalarNormUpper_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : 0 < genusOneScalarNormUpper data :=
  (by decide : (0 : Coordinate) < 1).trans_le
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (genusOneAPeriodBound_nonnegative data) 4))

theorem synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data index).scalar <=
      genusOneScalarNormUpper data := by
  rw [CCL.Riemann.FiniteEnergy.synchronizedScaledInverse,
    CCL.Riemann.PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
  have entryBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (sampledMatrix data.aMatrix index 0 0) <=
        genusOneAPeriodBound data :=
    (oneByOneEntryApproximation data.aMatrix).sample_bounded index
  exact (RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) entryBound 4).trans
    (le_add_of_nonneg_left (by decide))

/-- Index-independent normalized energy lower obtained from the fixed surface
box and the uniform inverse-scalar upper bound. -/
def genusOneUniformNormalizedEnergyLower
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : RationalVector 1) : Coordinate :=
  genusOneUniformSurfaceEnergy curve
      (genusOneScaledCoefficientLower data vector) /
    genusOneScalarNormUpper data

/-- Sample-independent normalized lower based only on the canonical unit box
and exact genus-one coefficient homogeneity. -/
def genusOneScaledReferenceNormalizedEnergyLower
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : RationalVector 1) : Coordinate :=
  (genusOneScaledCoefficientLower data vector * genusOneRawEnergy curve) /
    genusOneScalarNormUpper data

/-- Exact normalized lower contributed by the scaled canonical box at one
synchronized sample. -/
def genusOneScaledReferenceNormalizedEnergyAt
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : RationalVector 1) :
    Coordinate :=
  (genusOneScaledCoefficientLower data vector * genusOneRawEnergy curve) /
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data index).scalar

/-- Minimal genus-one global surface theorem.  It compares the one canonical
positive box for the standard differential `dx/y` with the synchronized raw
period pairing.  Exact one-dimensional homogeneity derives every other
coefficient case; no arbitrary-box quantifier is included. -/
structure GenusOneUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  lower : forall sampleIndex : Nat,
    genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex)

namespace GenusOneUnitSurfaceLowerCertificate

/-- The unit surface inequality forces a uniform lower bound for the sole
genus-one A-period.  The proof uses only the finite Lagrange identity and the
already carried uniform B-period bound. -/
def toOneByOneEntryCandidateLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data) :
    OneByOneEntryCandidateLowerCertificate data.aMatrix where
  lowerSq := genusOneAPeriodLowerSq data
  positive := by
    unfold genusOneAPeriodLowerSq
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        (genusOneRawEnergy_positive curve) 2)
      ((by decide : (0 : Coordinate) < 1).trans_le
        (le_add_of_nonneg_right (genusOneBPeriodBound_nonnegative data)))
  sample_lower := by
    intro index
    let coefficients := CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
    let energy := genusOneRawEnergy curve
    let a := sampledMatrix data.aMatrix index 0 0
    let b := sampledMatrix data.bMatrix index 0 0
    let bBound := genusOneBPeriodBound data
    let denominator := 1 + bBound
    have energyPositive : 0 < energy := genusOneRawEnergy_positive curve
    have energyLeRaw :
        energy <= CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) :=
      certificate.lower index
    have energySqLeRawSq :
        energy ^ 2 <=
          CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct energyPositive.le
        energyLeRaw 2
    have rawSqLeProduct :
        CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
              (sampledMatrix data.aMatrix index)
              (sampledMatrix data.bMatrix index) ^ 2 <=
          RFAP.ConstructiveGaussian.Gaussian.normSq a *
            RFAP.ConstructiveGaussian.Gaussian.normSq b := by
      exact CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm_genusOne_unit_sq_le
        (sampledMatrix data.aMatrix index) (sampledMatrix data.bMatrix index)
    have bLeBound :
        RFAP.ConstructiveGaussian.Gaussian.normSq b <= bBound :=
      (oneByOneEntryApproximation data.bMatrix).sample_bounded index
    have bLeDenominator :
        RFAP.ConstructiveGaussian.Gaussian.normSq b <= denominator :=
      bLeBound.trans (le_add_of_nonneg_left (by decide))
    have productLe :
        RFAP.ConstructiveGaussian.Gaussian.normSq a *
              RFAP.ConstructiveGaussian.Gaussian.normSq b <=
          RFAP.ConstructiveGaussian.Gaussian.normSq a * denominator :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        bLeDenominator
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg a)
    have energySqLe :
        energy ^ 2 <=
          RFAP.ConstructiveGaussian.Gaussian.normSq a * denominator :=
      energySqLeRawSq.trans (rawSqLeProduct.trans productLe)
    have denominatorPositive : 0 < denominator :=
      (by decide : (0 : Coordinate) < 1).trans_le
        (le_add_of_nonneg_right (genusOneBPeriodBound_nonnegative data))
    change genusOneAPeriodLowerSq data <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((oneByOneEntryApproximation data.aMatrix).sample index)
    unfold genusOneAPeriodLowerSq
    apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    exact energySqLe

/-- Fraction-free inverse separation derived from the single unit surface
comparison. -/
def toScalarCandidateLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toOneByOneEntryCandidateLowerCertificate.toScalarCandidateLowerCertificate

theorem genusOneScaledCoefficientLower_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneScaledCoefficientLower data vector := by
  have vectorSqPositive : 0 < vector 0 ^ 2 := by
    have gaussianPositive := RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      (CCL.Riemann.FiniteEnergy.gaussianOfRational_ne_zero
        (nonzeroVector_one_coefficient nonzero))
    simpa only [normSq_gaussianOfRational] using gaussianPositive
  exact RFAP.ConstructiveFraction.mul_pos_direct vectorSqPositive
    (RFAP.ConstructiveFraction.pow_pos_direct
      certificate.toOneByOneEntryCandidateLowerCertificate.positive 3)

theorem genusOneScaledCoefficientLower_le
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1) :
    genusOneScaledCoefficientLower data vector <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index
          vector 0) := by
  let lowerCertificate :=
    certificate.toOneByOneEntryCandidateLowerCertificate
  let aNorm := RFAP.ConstructiveGaussian.Gaussian.normSq
    (sampledMatrix data.aMatrix index 0 0)
  have aLower : genusOneAPeriodLowerSq data <= aNorm :=
    lowerCertificate.sample_lower index
  have aNormPositive : 0 < aNorm :=
    lowerCertificate.positive.trans_le aLower
  have aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0 := by
    intro entryZero
    change 0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (sampledMatrix data.aMatrix index 0 0) at aNormPositive
    rw [entryZero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at aNormPositive
    exact lt_irrefl 0 aNormPositive
  rw [normSq_scaledNormalizedCoefficients_one data index vector aNonzero]
  unfold genusOneScaledCoefficientLower
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.pow_le_pow_direct
      lowerCertificate.positive.le aLower 3)
    (RFAP.ConstructiveFraction.sq_nonneg_direct (vector 0))

/-- Canonical reused-box cells for one adjugate-scaled genus-one
coefficient. -/
def scaledReferenceRequestCells
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) : Fin 1 -> SurfaceCell curve
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector) :=
  genusOneScaledReferenceSurfaceCells curve
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector)
    (genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)

/-- Unit surface energy, Gaussian homogeneity, and the coefficient lower bound
give the complete raw-energy comparison for the reused request box. -/
theorem scaledReferenceRequestSurfaceEnergy_le_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    surfaceEnergy (certificate.scaledReferenceRequestCells index vector
      nonzero) <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index
          vector)
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) := by
  let coefficients :=
    CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector
  let coefficientLower := genusOneScaledCoefficientLower data vector
  have coefficientLowerLe : coefficientLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) :=
    certificate.genusOneScaledCoefficientLower_le index vector
  have unitLower := certificate.lower index
  rw [show surfaceEnergy
      (certificate.scaledReferenceRequestCells index vector nonzero) =
        coefficientLower * genusOneRawEnergy curve by
    exact surfaceEnergy_genusOneScaledReferenceSurfaceCells curve coefficients
      coefficientLower
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      coefficientLowerLe]
  rw [CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm_one_eq_normSq_mul_unit]
  calc
    coefficientLower * genusOneRawEnergy curve <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) *
          genusOneRawEnergy curve :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLowerLe (genusOneRawEnergy_positive curve).le
    _ <= RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) *
          CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
            CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct unitLower
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)

/-- Materialize the exact zero-edge-pair decomposition consumed by normalized
energy transport. -/
def scaledReferenceBoundaryReduction
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    BoundaryReduction data vector index
      (certificate.scaledReferenceRequestCells index vector nonzero) := by
  let raw := CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector)
    (sampledMatrix data.aMatrix index) (sampledMatrix data.bMatrix index)
  let localEnergy := surfaceEnergy
    (certificate.scaledReferenceRequestCells index vector nonzero)
  exact
    { edgePairCount := 0
      edgePairValues := fun edge => Fin.elim0 edge
      remainder := raw - localEnergy
      remainder_nonnegative :=
        RFAP.ConstructiveFraction.sub_nonneg_direct
          (certificate.scaledReferenceRequestSurfaceEnergy_le_raw index vector
            nonzero)
      raw_eq_decomposition := by
        rw [pairedBoundarySum_zero]
        unfold raw localEnergy
        ring1 }

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

/-- The legacy arbitrary-cell theorem contains, in particular, the one unit
surface inequality actually needed for genus-one inverse separation. -/
theorem toGenusOneUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data) :
    GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.boundaryReduction
      CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients sampleIndex
      (rawRequestCells curve
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        genusOneUnitNonzero 0)).surfaceEnergy_le_raw

/-- A single raw cut-surface certificate forces uniform separation of the
sole genus-one A-period through its minimal unit theorem. -/
def toOneByOneEntryCandidateLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data) :
    OneByOneEntryCandidateLowerCertificate data.aMatrix :=
  certificate.toGenusOneUnitSurfaceLowerCertificate.toOneByOneEntryCandidateLowerCertificate

/-- The exact one-by-one scalar calculation converts the raw-energy A-period
lower bound into the canonical fraction-free inverse certificate. -/
def toScalarCandidateLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toOneByOneEntryCandidateLowerCertificate.toScalarCandidateLowerCertificate

theorem genusOneScaledCoefficientLower_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneScaledCoefficientLower data vector := by
  have vectorSqPositive : 0 < vector 0 ^ 2 := by
    have gaussianPositive := RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      (CCL.Riemann.FiniteEnergy.gaussianOfRational_ne_zero
        (nonzeroVector_one_coefficient nonzero))
    simpa only [normSq_gaussianOfRational] using gaussianPositive
  exact RFAP.ConstructiveFraction.mul_pos_direct vectorSqPositive
    (RFAP.ConstructiveFraction.pow_pos_direct
      certificate.toOneByOneEntryCandidateLowerCertificate.positive 3)

theorem genusOneScaledCoefficientLower_le
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (index : Nat) (vector : RationalVector 1) :
    genusOneScaledCoefficientLower data vector <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index
          vector 0) := by
  let lowerCertificate :=
    certificate.toOneByOneEntryCandidateLowerCertificate
  let aNorm := RFAP.ConstructiveGaussian.Gaussian.normSq
    (sampledMatrix data.aMatrix index 0 0)
  have aLower : genusOneAPeriodLowerSq data <= aNorm := by
    exact lowerCertificate.sample_lower index
  have aNormPositive : 0 < aNorm :=
    lowerCertificate.positive.trans_le aLower
  have aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0 := by
    intro entryZero
    change 0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (sampledMatrix data.aMatrix index 0 0) at aNormPositive
    rw [entryZero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at aNormPositive
    exact lt_irrefl 0 aNormPositive
  rw [normSq_scaledNormalizedCoefficients_one data index vector aNonzero]
  unfold genusOneScaledCoefficientLower
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.pow_le_pow_direct
      lowerCertificate.positive.le aLower 3)
    (RFAP.ConstructiveFraction.sq_nonneg_direct (vector 0))

theorem genusOneUniformNormalizedEnergyLower_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneUniformNormalizedEnergyLower data vector :=
  RFAP.ConstructiveFraction.div_pos_direct
    (genusOneUniformSurfaceEnergy_positive curve
      (certificate.genusOneScaledCoefficientLower_positive nonzero))
    (genusOneScalarNormUpper_positive data)

/-- Fixed-box cells for the scaled coefficient at one synchronized sample. -/
def genusOneUniformRequestCells
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) : Fin 1 -> SurfaceCell curve
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector) :=
  genusOneUniformSurfaceCells curve
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector)
    (genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)

/-- Exact normalized energy of the fixed-box cell at one synchronized sample. -/
def genusOneUniformNormalizedEnergyAt
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : RationalVector 1) :
    Coordinate :=
  genusOneUniformSurfaceEnergy curve
      (genusOneScaledCoefficientLower data vector) /
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data index).scalar

theorem genusOneUniformNormalizedEnergyAt_eq
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    genusOneUniformNormalizedEnergyAt data index vector =
      CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower data index
        (energyCells
          (certificate.genusOneUniformRequestCells index vector nonzero)) := by
  unfold genusOneUniformNormalizedEnergyAt
    CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower
  rw [← surfaceEnergy_genusOneUniformSurfaceCells curve
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector)
    (genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)]
  rfl

end RawCertificate

private theorem div_le_div_of_denominator_le
    {numerator denominator upper : Coordinate}
    (numeratorNonnegative : 0 <= numerator)
    (denominatorPositive : 0 < denominator)
    (upperPositive : 0 < upper) (denominatorLe : denominator <= upper) :
    numerator / upper <= numerator / denominator := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).2
  have quotientNonnegative : 0 <= numerator / upper :=
    RFAP.ConstructiveFraction.div_nonneg_direct numeratorNonnegative
      upperPositive.le
  calc
    numerator / upper * denominator <= numerator / upper * upper :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct denominatorLe
        quotientNonnegative
    _ = numerator := RFAP.ExplicitField.div_mul_cancel numerator
      (ne_of_gt upperPositive)

namespace GenusOneUnitSurfaceLowerCertificate

theorem genusOneScaledReferenceNormalizedEnergyLower_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneScaledReferenceNormalizedEnergyLower data vector :=
  RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct
      (certificate.genusOneScaledCoefficientLower_positive nonzero)
      (genusOneRawEnergy_positive curve))
    (genusOneScalarNormUpper_positive data)

/-- The exact scaled reference-box quotient is the normalized cell energy
consumed by transport at the synchronized sample. -/
theorem genusOneScaledReferenceNormalizedEnergyAt_eq
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    genusOneScaledReferenceNormalizedEnergyAt data index vector =
      CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower data index
        (energyCells
          (certificate.scaledReferenceRequestCells index vector nonzero)) := by
  unfold genusOneScaledReferenceNormalizedEnergyAt
    CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower
  rw [show CCL.Riemann.FiniteEnergy.cellEnergy
      (energyCells
        (certificate.scaledReferenceRequestCells index vector nonzero)) =
        genusOneScaledCoefficientLower data vector * genusOneRawEnergy curve by
    exact surfaceEnergy_genusOneScaledReferenceSurfaceCells curve
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data index vector)
      (genusOneScaledCoefficientLower data vector)
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      (certificate.genusOneScaledCoefficientLower_le index vector)]

/-- The sample-independent scaled reference energy survives every synchronized
genus-one inverse denominator. -/
theorem genusOneScaledReferenceNormalizedEnergyLower_le
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    genusOneScaledReferenceNormalizedEnergyLower data vector <=
      genusOneScaledReferenceNormalizedEnergyAt data index vector := by
  have numeratorNonnegative :
      0 <= genusOneScaledCoefficientLower data vector *
        genusOneRawEnergy curve :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      (genusOneRawEnergy_positive curve).le
  have scalarPositive : 0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data index).scalar :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse_scalar_nonzero data
        certificate.toScalarCandidateLowerCertificate index)
  exact div_le_div_of_denominator_le numeratorNonnegative scalarPositive
    (genusOneScalarNormUpper_positive data)
    (synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper data index)

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

/-- The fixed positive normalized lower survives every synchronized sample. -/
theorem genusOneUniformNormalizedEnergyLower_le
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (index : Nat) (vector : RationalVector 1)
    (nonzero : NonzeroVector vector) :
    genusOneUniformNormalizedEnergyLower data vector <=
      genusOneUniformNormalizedEnergyAt data index vector := by
  have surfacePositive : 0 < genusOneUniformSurfaceEnergy curve
      (genusOneScaledCoefficientLower data vector) :=
    genusOneUniformSurfaceEnergy_positive curve
      (certificate.genusOneScaledCoefficientLower_positive nonzero)
  have scalarPositive : 0 < RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data index).scalar :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse_scalar_nonzero data
        certificate.toScalarCandidateLowerCertificate index)
  exact div_le_div_of_denominator_le surfacePositive.le scalarPositive
    (genusOneScalarNormUpper_positive data)
    (synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper data index)

end RawCertificate

/-- The synchronized scaled coefficients are nonzero by the finite inverse
identity, so the bounded clear-point search constructs a positive box without
additional analytic input. -/
def canonicalPositiveCell {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) :
    PositiveSurfaceCell curve
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
        vector) :=
  SurfaceCell.findPositive curve
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
      vector)
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients_nonzero data
      inverseLower sampleIndex vector nonzero)
    canonicalSurfaceFace

/-- Singleton finite surface family generated canonically for one request. -/
def requestCells {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) :
    Fin 1 -> SurfaceCell curve
      (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
        vector) :=
  fun _ => (canonicalPositiveCell data inverseLower sampleIndex vector
    nonzero).cell

/-- The generated singleton has strictly positive finite lower energy before
any global surface-to-boundary comparison is used. -/
theorem requestSurfaceEnergy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) :
    0 < surfaceEnergy
      (requestCells data inverseLower sampleIndex vector nonzero) := by
  unfold surfaceEnergy
  apply CCL.Riemann.FiniteEnergy.cellEnergy_positive_of_cell _ 0
  · exact (canonicalPositiveCell data inverseLower sampleIndex vector
      nonzero).cell.area_positive
  · exact (canonicalPositiveCell data inverseLower sampleIndex vector
      nonzero).density_positive

namespace RawCertificate

/-- Specialize the inverse-independent raw boundary theorem to the
adjugate-scaled coefficients used by one normalized positivity request. -/
def normalizedBoundaryReduction {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) :
    BoundaryReduction data vector sampleIndex
      (requestCells data inverseLower sampleIndex vector nonzero) := by
  let coefficients :=
    CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex vector
  let coefficientsNonzero :=
    CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients_nonzero data
      inverseLower sampleIndex vector nonzero
  let reduction := certificate.boundaryReduction coefficients sampleIndex
    (rawRequestCells curve coefficients coefficientsNonzero 0)
  exact
    { edgePairCount := reduction.edgePairCount
      edgePairValues := reduction.edgePairValues
      remainder := reduction.remainder
      remainder_nonnegative := reduction.remainder_nonnegative
      raw_eq_decomposition := by
        change
          CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
                (sampledMatrix data.aMatrix sampleIndex)
                (sampledMatrix data.bMatrix sampleIndex) =
            surfaceEnergy
                (rawRequestCells curve coefficients coefficientsNonzero) +
              pairedBoundarySum reduction.edgePairValues + reduction.remainder
        exact reduction.raw_eq_decomposition }

end RawCertificate

/-- Radius-independent coefficient of the automatic quadratic-form
perturbation budget. -/
def budgetSlope {genus : Nat} (vector : RationalVector genus) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
    RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
      (vector row * vector column) ^ 2 + 1

theorem budgetSlope_nonnegative {genus : Nat}
    (vector : RationalVector genus) : 0 <= budgetSlope vector := by
  unfold budgetSlope
  calc
    0 = RFAP.ConstructiveFiniteMatrix.sumFin
        (fun _ : Fin genus => (0 : Coordinate)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_zero.symm
    _ <= RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
        RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
          (vector row * vector column) ^ 2 + 1) := by
      apply CCL.Riemann.FinitePositivity.sumFin_mono
      intro row
      calc
        0 = RFAP.ConstructiveFiniteMatrix.sumFin
            (fun _ : Fin genus => (0 : Coordinate)) :=
          RFAP.ConstructiveFiniteMatrix.sumFin_zero.symm
        _ <= RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
            (vector row * vector column) ^ 2 + 1) := by
          apply CCL.Riemann.FinitePositivity.sumFin_mono
          intro column
          exact add_nonneg
            (RFAP.ConstructiveFraction.sq_nonneg_direct
              (vector row * vector column)) (by decide)

/-- For a constant entrywise radius, the entire automatically generated
finite double-sum budget is exactly linear in that radius. -/
theorem automaticBudget_eq_budgetSlope_mul {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : CCL.Riemann.PeriodMatrix.NormalizedPeriodData curve)
    (vector : RationalVector genus) (radius : Coordinate)
    (positive : 0 < radius) :
    CCL.Riemann.FinitePositivity.totalBudget
        (CCL.Riemann.FinitePositivity.automaticBudget vector
          (CCL.Riemann.FinitePositivity.automaticRadius data radius positive)) =
      budgetSlope vector * radius := by
  unfold CCL.Riemann.FinitePositivity.totalBudget budgetSlope
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun row => RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
      ((vector row * vector column) ^ 2 + 1) * radius)
    (fun row => by
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro column
      rw [CCL.Riemann.FinitePositivity.automaticBudget_apply,
        CCL.Riemann.FinitePositivity.automaticRadius_apply])]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr (fun row =>
    RFAP.ConstructiveFiniteMatrix.sumFin_mul_right
      (fun column => (vector row * vector column) ^ 2 + 1) radius)]
  exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_right _ _

/-- Canonical linear radius whose square lies below a positive public target. -/
def targetRadius (target : Coordinate) : Coordinate :=
  min 1 (target / 2)

theorem targetRadius_positive {target : Coordinate} (positive : 0 < target) :
    0 < targetRadius target := by
  unfold targetRadius
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))

theorem targetRadius_le_one (target : Coordinate) : targetRadius target <= 1 :=
  min_le_left _ _

private theorem half_lt_self {value : Coordinate} (positive : 0 < value) :
    value / 2 < value := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    value = value * 1 := by ring1
    _ < value * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct positive
        (by decide)

theorem targetRadius_sq_lt_target {target : Coordinate}
    (positive : 0 < target) : targetRadius target ^ 2 < target := by
  have radiusPositive := targetRadius_positive positive
  have square_le_radius : targetRadius target ^ 2 <= targetRadius target := by
    rw [pow_two]
    calc
      targetRadius target * targetRadius target <= targetRadius target * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (targetRadius_le_one target) radiusPositive.le
      _ = targetRadius target := by ring1
  exact square_le_radius.trans_lt
    ((min_le_right (1 : Coordinate) (target / 2)).trans_lt
      (half_lt_self positive))

/-- Comparison budget for transporting one synchronized exact matrix to the
persistent normalized centre. -/
def comparisonBudget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (radius : Coordinate)
    (positive : 0 < radius) : Coordinate :=
  CCL.Riemann.FinitePositivity.totalBudget
    (CCL.Riemann.FinitePositivity.automaticBudget vector
      (CCL.Riemann.FinitePositivity.automaticRadius
        (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
        radius positive))

/-- Exact normalized lower energy of the automatically generated positive
surface singleton. -/
def requestNormalizedEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) : Coordinate :=
  CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower data sampleIndex
    (energyCells (requestCells data inverseLower sampleIndex vector nonzero))

/-- Positive energy left after paying the exact-sample-to-centre comparison
budget. -/
def requestClearance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (comparisonRadius : Coordinate)
    (comparisonPositive : 0 < comparisonRadius) : Coordinate :=
  requestNormalizedEnergy data inverseLower sampleIndex vector nonzero -
    comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive

/-- A persistent-table refinement radius small enough for the automatically
derived operational comparison with the raw synchronized matrix. -/
def comparisonRefinementRadius (comparisonRadius : Coordinate) : Coordinate :=
  comparisonRadius / 16

theorem comparisonRefinementRadius_positive {comparisonRadius : Coordinate}
    (positive : 0 < comparisonRadius) :
    0 < comparisonRefinementRadius comparisonRadius := by
  unfold comparisonRefinementRadius
  exact RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

theorem comparisonRefinementRadius_sq_lt_target
    {comparisonRadius : Coordinate} (positive : 0 < comparisonRadius) :
    comparisonRefinementRadius comparisonRadius ^ 2 <
      CCL.Riemann.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let small := comparisonRefinementRadius comparisonRadius
  let large := comparisonRadius / 8
  have largePositive : 0 < large :=
    RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
  have smallPositive : 0 < small :=
    comparisonRefinementRadius_positive positive
  have smallEq : small = large / 2 := by
    unfold small large comparisonRefinementRadius
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    rw [show (16 : Coordinate)⁻¹ = (8 : Coordinate)⁻¹ *
        (2 : Coordinate)⁻¹ by decide]
    ring1
  have smallLtLarge : small < large := by
    rw [smallEq]
    exact half_lt_self largePositive
  have squares : small ^ 2 < large ^ 2 := by
    simp only [pow_two]
    calc
      small * small < large * small :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          smallLtLarge smallPositive
      _ < large * large :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          largePositive smallLtLarge
  calc
    comparisonRefinementRadius comparisonRadius ^ 2 = small ^ 2 := rfl
    _ < large ^ 2 := squares
    _ = CCL.Riemann.SynchronizedNormalization.comparisonTarget
          comparisonRadius := by
      unfold large CCL.Riemann.SynchronizedNormalization.comparisonTarget
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      calc
        (comparisonRadius * (8 : Coordinate)⁻¹) ^ 2 =
            comparisonRadius ^ 2 * ((8 : Coordinate)⁻¹ ^ 2) := by ring1
        _ = comparisonRadius ^ 2 * (64 : Coordinate)⁻¹ := by
          rw [← RFAP.ConstructiveFraction.inv_pow_direct]
          rw [show (8 : Coordinate) ^ 2 = 64 by ring1]

/-- Canonical output radius, simultaneously restricted by the public target
and by both the operational-comparison and positive-energy budgets. -/
def requestOutputRadius {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (comparisonRadius : Coordinate)
    (comparisonPositive : 0 < comparisonRadius) : Coordinate :=
  min (targetRadius target)
    (min (comparisonRefinementRadius comparisonRadius)
      (requestClearance data inverseLower sampleIndex vector nonzero
        comparisonRadius comparisonPositive /
          (1 + budgetSlope vector) / 2))

theorem requestOutputRadius_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target comparisonRadius : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector nonzero) :
    0 < requestOutputRadius data inverseLower sampleIndex vector nonzero target
      comparisonRadius comparisonPositive := by
  have clearancePositive :
      0 < requestClearance data inverseLower sampleIndex vector nonzero
        comparisonRadius comparisonPositive :=
    RFAP.ConstructiveFraction.sub_pos_direct comparison_lt_energy
  have slopeDenominatorPositive : 0 < 1 + budgetSlope vector :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right (budgetSlope_nonnegative vector))
  unfold requestOutputRadius
  exact lt_min (targetRadius_positive targetPositive)
    (lt_min (comparisonRefinementRadius_positive comparisonPositive)
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.div_pos_direct clearancePositive
          slopeDenominatorPositive) (by decide)))

theorem requestOutputRadius_sq_lt_target {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target comparisonRadius : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector nonzero) :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget
        (requestOutputRadius data inverseLower sampleIndex vector nonzero target
          comparisonRadius comparisonPositive) <
      target := by
  let radius := requestOutputRadius data inverseLower sampleIndex vector nonzero
    target comparisonRadius comparisonPositive
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_targetRadius : radius <= targetRadius target := by
    unfold radius requestOutputRadius
    exact min_le_left _ _
  unfold CCL.Riemann.FinitePositivity.squaredRefinementTarget
  exact
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radius_le_targetRadius 2).trans_lt
        (targetRadius_sq_lt_target targetPositive)

/-- The automatically chosen table refinement is also fine enough for the
operational synchronized-normalization comparison. -/
theorem requestOutputRadius_sq_lt_comparisonTarget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target comparisonRadius : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector nonzero) :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget
        (requestOutputRadius data inverseLower sampleIndex vector nonzero target
          comparisonRadius comparisonPositive) <
      CCL.Riemann.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let radius := requestOutputRadius data inverseLower sampleIndex vector nonzero
    target comparisonRadius comparisonPositive
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_comparison :
      radius <= comparisonRefinementRadius comparisonRadius := by
    unfold radius requestOutputRadius
    exact (min_le_right _ _).trans (min_le_left _ _)
  unfold CCL.Riemann.FinitePositivity.squaredRefinementTarget
  exact
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radius_le_comparison 2).trans_lt
        (comparisonRefinementRadius_sq_lt_target comparisonPositive)

/-- The chosen output radius automatically leaves a strict positive margin
after both finite perturbation budgets. -/
theorem requestBudgets_lt_energy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target comparisonRadius : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector nonzero) :
    let radius := requestOutputRadius data inverseLower sampleIndex vector
      nonzero target comparisonRadius comparisonPositive
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
              radius
              (requestOutputRadius_positive targetPositive comparisonPositive
                comparison_lt_energy))) +
        comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
      requestNormalizedEnergy data inverseLower sampleIndex vector nonzero := by
  let clearance := requestClearance data inverseLower sampleIndex vector nonzero
    comparisonRadius comparisonPositive
  let slope := budgetSlope vector
  let energyRadius := clearance / (1 + slope) / 2
  let radius := requestOutputRadius data inverseLower sampleIndex vector nonzero
    target comparisonRadius comparisonPositive
  have clearancePositive : 0 < clearance :=
    RFAP.ConstructiveFraction.sub_pos_direct comparison_lt_energy
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have slopeDenominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right slopeNonnegative)
  have energyRadiusPositive : 0 < energyRadius := by
    unfold energyRadius
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct clearancePositive
        slopeDenominatorPositive) (by decide)
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_energyRadius : radius <= energyRadius := by
    unfold radius requestOutputRadius energyRadius clearance slope
    exact (min_le_right _ _).trans (min_le_right _ _)
  have slope_le_denominator : slope <= 1 + slope := by
    exact le_add_of_nonneg_left (by decide)
  have scaled_le_half : slope * radius <= clearance / 2 := by
    calc
      slope * radius <= (1 + slope) * energyRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct slope_le_denominator
          radius_le_energyRadius radiusPositive.le
          slopeDenominatorPositive.le
      _ = clearance / 2 := by
        unfold energyRadius
        calc
          (1 + slope) * (clearance / (1 + slope) / 2) =
              (clearance / (1 + slope) * (1 + slope)) / 2 := by
            simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
            ring1
          _ = clearance / 2 := by
            rw [RFAP.ExplicitField.div_mul_cancel clearance
              (ne_of_gt slopeDenominatorPositive)]
  have output_lt_clearance : slope * radius < clearance :=
    scaled_le_half.trans_lt (half_lt_self clearancePositive)
  have outputBudget_lt_clearance :
      CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
              radius radiusPositive)) < clearance := by
    rw [automaticBudget_eq_budgetSlope_mul]
    exact output_lt_clearance
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    outputBudget_lt_clearance
    (comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive)
  simpa only [radius,
    show requestOutputRadius_positive targetPositive comparisonPositive
        comparison_lt_energy = radiusPositive from rfl] using
    (shifted.trans_le (le_of_eq (by
      unfold clearance requestClearance
      ring1)))

/-- Output radius for an explicitly supplied positive energy.  This is the
same finite budget calculation as `requestOutputRadius`, separated from the
canonical positive-cell search so fixed certified cells can reuse it. -/
def outputRadiusFromEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (target comparisonRadius : Coordinate)
    (comparisonPositive : 0 < comparisonRadius) (energy : Coordinate) :
    Coordinate :=
  min (targetRadius target)
    (min (comparisonRefinementRadius comparisonRadius)
      ((energy - comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive) / (1 + budgetSlope vector) / 2))

theorem outputRadiusFromEnergy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {target comparisonRadius energy : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    0 < outputRadiusFromEnergy data inverseLower vector target comparisonRadius
      comparisonPositive energy := by
  have clearancePositive :
      0 < energy - comparisonBudget data inverseLower vector comparisonRadius
        comparisonPositive :=
    RFAP.ConstructiveFraction.sub_pos_direct comparison_lt_energy
  have slopeDenominatorPositive : 0 < 1 + budgetSlope vector :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right (budgetSlope_nonnegative vector))
  unfold outputRadiusFromEnergy
  exact lt_min (targetRadius_positive targetPositive)
    (lt_min (comparisonRefinementRadius_positive comparisonPositive)
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.div_pos_direct clearancePositive
          slopeDenominatorPositive) (by decide)))

theorem outputRadiusFromEnergy_sq_lt_target {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {target comparisonRadius energy : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget
        (outputRadiusFromEnergy data inverseLower vector target comparisonRadius
          comparisonPositive energy) < target := by
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_targetRadius : radius <= targetRadius target := by
    unfold radius outputRadiusFromEnergy
    exact min_le_left _ _
  unfold CCL.Riemann.FinitePositivity.squaredRefinementTarget
  exact
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radius_le_targetRadius 2).trans_lt
        (targetRadius_sq_lt_target targetPositive)

theorem outputRadiusFromEnergy_sq_lt_comparisonTarget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {target comparisonRadius energy : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget
        (outputRadiusFromEnergy data inverseLower vector target comparisonRadius
          comparisonPositive energy) <
      CCL.Riemann.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_comparison :
      radius <= comparisonRefinementRadius comparisonRadius := by
    unfold radius outputRadiusFromEnergy
    exact (min_le_right _ _).trans (min_le_left _ _)
  unfold CCL.Riemann.FinitePositivity.squaredRefinementTarget
  exact
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radius_le_comparison 2).trans_lt
        (comparisonRefinementRadius_sq_lt_target comparisonPositive)

theorem outputRadiusFromEnergy_budgets_lt_energy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {target comparisonRadius energy : Coordinate}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    let radius := outputRadiusFromEnergy data inverseLower vector target
      comparisonRadius comparisonPositive energy
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
              radius
              (outputRadiusFromEnergy_positive targetPositive
                comparisonPositive comparison_lt_energy))) +
        comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy := by
  let clearance := energy - comparisonBudget data inverseLower vector
    comparisonRadius comparisonPositive
  let slope := budgetSlope vector
  let energyRadius := clearance / (1 + slope) / 2
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have clearancePositive : 0 < clearance :=
    RFAP.ConstructiveFraction.sub_pos_direct comparison_lt_energy
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have slopeDenominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right slopeNonnegative)
  have energyRadiusPositive : 0 < energyRadius := by
    unfold energyRadius
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct clearancePositive
        slopeDenominatorPositive) (by decide)
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_energyRadius : radius <= energyRadius := by
    unfold radius outputRadiusFromEnergy energyRadius clearance slope
    exact (min_le_right _ _).trans (min_le_right _ _)
  have slope_le_denominator : slope <= 1 + slope :=
    le_add_of_nonneg_left (by decide)
  have scaled_le_half : slope * radius <= clearance / 2 := by
    calc
      slope * radius <= (1 + slope) * energyRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct slope_le_denominator
          radius_le_energyRadius radiusPositive.le
          slopeDenominatorPositive.le
      _ = clearance / 2 := by
        unfold energyRadius
        calc
          (1 + slope) * (clearance / (1 + slope) / 2) =
              (clearance / (1 + slope) * (1 + slope)) / 2 := by
            simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
            ring1
          _ = clearance / 2 := by
            rw [RFAP.ExplicitField.div_mul_cancel clearance
              (ne_of_gt slopeDenominatorPositive)]
  have outputBudget_lt_clearance :
      CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
              radius radiusPositive)) < clearance := by
    rw [automaticBudget_eq_budgetSlope_mul]
    exact scaled_le_half.trans_lt (half_lt_self clearancePositive)
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    outputBudget_lt_clearance
    (comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive)
  simpa only [radius,
    show outputRadiusFromEnergy_positive targetPositive comparisonPositive
        comparison_lt_energy = radiusPositive from rfl] using
    (shifted.trans_le (le_of_eq (by
      unfold clearance
      ring1)))

/-- One prepared second-relation request.  Local area, denominator apartness,
and density validity live in `SurfaceCell`; the global cut-surface identity
is displayed by `BoundaryReduction`. -/
def requestSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Coordinate) (comparisonPositive : 0 < comparisonRadius) :
    Nat :=
  CCL.Riemann.SynchronizedNormalization.synchronizedSampleIndex data
    inverseLower comparisonRadius comparisonPositive

/-- The comparison radius determines, rather than merely accompanies, the
one shared raw normalization index. -/
structure ComparisonSchedule {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (_inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  radius : Coordinate
  positive : 0 < radius
  sampleIndex : Nat
  sampleIndex_eq : sampleIndex =
    requestSampleIndex data _inverseLower radius positive

namespace ComparisonSchedule

def ofRadius {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (radius : Coordinate) (positive : 0 < radius) :
    ComparisonSchedule data inverseLower where
  radius := radius
  positive := positive
  sampleIndex := requestSampleIndex data inverseLower radius positive
  sampleIndex_eq := rfl

end ComparisonSchedule

/-- A comparison radius computed solely from the sample-independent
genus-one normalized energy lower. -/
def genusOneComparisonRadius
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : RationalVector 1) : Coordinate :=
  genusOneUniformNormalizedEnergyLower data vector /
    (1 + budgetSlope vector) / 2

/-- Comparison radius computed from the sharper unit-surface homogeneity
lower, without an arbitrary-coefficient surface theorem. -/
def genusOneScaledReferenceComparisonRadius
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : RationalVector 1) : Coordinate :=
  genusOneScaledReferenceNormalizedEnergyLower data vector /
    (1 + budgetSlope vector) / 2

namespace GenusOneUnitSurfaceLowerCertificate

theorem genusOneScaledReferenceComparisonRadius_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneScaledReferenceComparisonRadius data vector := by
  unfold genusOneScaledReferenceComparisonRadius
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct
      (certificate.genusOneScaledReferenceNormalizedEnergyLower_positive
        nonzero)
      ((by decide : (0 : Coordinate) < 1).trans_le
        (le_add_of_nonneg_right (budgetSlope_nonnegative vector))))
    (by decide)

/-- The automatic comparison budget is strictly below the scaled reference
energy before selecting the synchronized sample. -/
theorem genusOneScaledReferenceComparisonBudget_lt_energy
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    comparisonBudget data certificate.toScalarCandidateLowerCertificate vector
        (genusOneScaledReferenceComparisonRadius data vector)
        (certificate.genusOneScaledReferenceComparisonRadius_positive nonzero) <
      genusOneScaledReferenceNormalizedEnergyLower data vector := by
  let energy := genusOneScaledReferenceNormalizedEnergyLower data vector
  let slope := budgetSlope vector
  let radius := genusOneScaledReferenceComparisonRadius data vector
  have energyPositive : 0 < energy :=
    certificate.genusOneScaledReferenceNormalizedEnergyLower_positive nonzero
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have denominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right slopeNonnegative)
  have radiusPositive : 0 < radius :=
    certificate.genusOneScaledReferenceComparisonRadius_positive nonzero
  have slope_le_denominator : slope <= 1 + slope :=
    le_add_of_nonneg_left (by decide)
  have budget_le_half : slope * radius <= energy / 2 := by
    calc
      slope * radius <= (1 + slope) * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          slope_le_denominator radiusPositive.le
      _ = energy / 2 := by
        unfold radius genusOneScaledReferenceComparisonRadius energy slope
        calc
          (1 + budgetSlope vector) *
                (genusOneScaledReferenceNormalizedEnergyLower data vector /
                  (1 + budgetSlope vector) / 2) =
              (genusOneScaledReferenceNormalizedEnergyLower data vector /
                (1 + budgetSlope vector) *
                  (1 + budgetSlope vector)) / 2 := by
            simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
            ring1
          _ = genusOneScaledReferenceNormalizedEnergyLower data vector / 2 := by
            rw [RFAP.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorPositive)]
  unfold comparisonBudget
  rw [automaticBudget_eq_budgetSlope_mul]
  exact budget_le_half.trans_lt (half_lt_self energyPositive)

/-- The unit surface theorem determines the normalization comparison schedule
for every nonzero genus-one rational vector. -/
def genusOneScaledReferenceComparisonSchedule
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (vector : RationalVector 1) (nonzero : NonzeroVector vector) :
    ComparisonSchedule data certificate.toScalarCandidateLowerCertificate :=
  ComparisonSchedule.ofRadius
    (genusOneScaledReferenceComparisonRadius data vector)
    (certificate.genusOneScaledReferenceComparisonRadius_positive nonzero)

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

theorem genusOneComparisonRadius_positive
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    0 < genusOneComparisonRadius data vector := by
  unfold genusOneComparisonRadius
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct
      (certificate.genusOneUniformNormalizedEnergyLower_positive nonzero)
      ((by decide : (0 : Coordinate) < 1).trans_le
        (le_add_of_nonneg_right (budgetSlope_nonnegative vector))))
    (by decide)

/-- The automatically chosen comparison budget is strictly smaller than the
fixed normalized energy lower, before any sample index is selected. -/
theorem genusOneComparisonBudget_lt_uniformEnergy
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    {vector : RationalVector 1} (nonzero : NonzeroVector vector) :
    comparisonBudget data certificate.toScalarCandidateLowerCertificate vector
        (genusOneComparisonRadius data vector)
        (certificate.genusOneComparisonRadius_positive nonzero) <
      genusOneUniformNormalizedEnergyLower data vector := by
  let energy := genusOneUniformNormalizedEnergyLower data vector
  let slope := budgetSlope vector
  let radius := genusOneComparisonRadius data vector
  have energyPositive : 0 < energy :=
    certificate.genusOneUniformNormalizedEnergyLower_positive nonzero
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have denominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Coordinate) < 1).trans_le
      (le_add_of_nonneg_right slopeNonnegative)
  have radiusPositive : 0 < radius :=
    certificate.genusOneComparisonRadius_positive nonzero
  have slope_le_denominator : slope <= 1 + slope :=
    le_add_of_nonneg_left (by decide)
  have budget_le_half : slope * radius <= energy / 2 := by
    calc
      slope * radius <= (1 + slope) * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          slope_le_denominator radiusPositive.le
      _ = energy / 2 := by
        unfold radius genusOneComparisonRadius energy slope
        calc
          (1 + budgetSlope vector) *
                (genusOneUniformNormalizedEnergyLower data vector /
                  (1 + budgetSlope vector) / 2) =
              (genusOneUniformNormalizedEnergyLower data vector /
                (1 + budgetSlope vector) *
                  (1 + budgetSlope vector)) / 2 := by
            simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
            ring1
          _ = genusOneUniformNormalizedEnergyLower data vector / 2 := by
            rw [RFAP.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorPositive)]
  unfold comparisonBudget
  rw [automaticBudget_eq_budgetSlope_mul]
  exact budget_le_half.trans_lt (half_lt_self energyPositive)

/-- The radius and synchronized index needed for genus-one normalization are
fully determined by the raw certificate and the requested vector. -/
def genusOneComparisonSchedule
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (vector : RationalVector 1) (nonzero : NonzeroVector vector) :
    ComparisonSchedule data certificate.toScalarCandidateLowerCertificate :=
  ComparisonSchedule.ofRadius (genusOneComparisonRadius data vector)
    (certificate.genusOneComparisonRadius_positive nonzero)

end RawCertificate

structure RequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  comparison : ComparisonSchedule data inverseLower
  boundaryReduction : BoundaryReduction data vector comparison.sampleIndex
    (requestCells data inverseLower
      comparison.sampleIndex vector nonzero)
  comparisonBudget_lt_energy :
    comparisonBudget data inverseLower vector comparison.radius
        comparison.positive <
      requestNormalizedEnergy data inverseLower
        comparison.sampleIndex vector nonzero

/-- Once a global raw cut-surface theorem is available, one normalized
request only has to exhibit a finite normalization-comparison radius whose
budget clears the automatically generated positive local energy. -/
structure RawRequestSchedule {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  comparison : ComparisonSchedule data inverseLower
  comparisonBudget_lt_energy :
    comparisonBudget data inverseLower vector comparison.radius
        comparison.positive <
      requestNormalizedEnergy data inverseLower
        comparison.sampleIndex vector nonzero

/-- The computed comparison schedule discharges the exact-sample-to-centre
closeness proposition required by the generic energy transport layer. -/
theorem requestCenter_close {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (comparison : ComparisonSchedule data inverseLower)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparison.radius
          comparison.positive <
        requestNormalizedEnergy data inverseLower comparison.sampleIndex
          vector nonzero)
    (row column : Fin genus) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePositivity.centerMatrix
            (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget
              (requestOutputRadius data inverseLower comparison.sampleIndex
                vector nonzero target comparison.radius comparison.positive))
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
              (requestOutputRadius_positive positive comparison.positive
                comparison_lt_energy)) row column -
          CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data
            comparison.sampleIndex row column) <
      comparison.radius ^ 2 :=
  CCL.Riemann.SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
    data inverseLower comparison.radius comparison.positive
      comparison.sampleIndex comparison.sampleIndex_eq
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget
        (requestOutputRadius data inverseLower comparison.sampleIndex vector
          nonzero target comparison.radius comparison.positive))
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
        (requestOutputRadius_positive positive comparison.positive
          comparison_lt_energy))
      (requestOutputRadius_sq_lt_comparisonTarget positive comparison.positive
        comparison_lt_energy) row column

namespace RequestCertificate

/-- Expand the geometry-backed request into the generic finite transport
interface.  All local positivity fields are derived from box properness and
the checked density bound. -/
def toTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RequestCertificate data inverseLower vector nonzero target
      positive) :
    CCL.Riemann.FiniteEnergy.TransportRequestCertificate data inverseLower
      vector nonzero target positive where
  sampleIndex := certificate.comparison.sampleIndex
  cellCount := 1
  cells := energyCells (requestCells data inverseLower
    certificate.comparison.sampleIndex vector nonzero)
  positiveCell := 0
  positiveCell_area :=
    (canonicalPositiveCell data inverseLower
      certificate.comparison.sampleIndex vector nonzero).cell.area_positive
  positiveCell_density :=
    (canonicalPositiveCell data inverseLower
      certificate.comparison.sampleIndex vector nonzero).density_positive
  energy_le_raw := certificate.boundaryReduction.surfaceEnergy_le_raw
  refinementRadius := requestOutputRadius data inverseLower
    certificate.comparison.sampleIndex vector nonzero target
      certificate.comparison.radius certificate.comparison.positive
  refinementRadiusPositive :=
    requestOutputRadius_positive positive certificate.comparison.positive
      certificate.comparisonBudget_lt_energy
  refinementTarget_lt_target :=
    requestOutputRadius_sq_lt_target positive
      certificate.comparison.positive
      certificate.comparisonBudget_lt_energy
  comparisonRadius := certificate.comparison.radius
  comparisonRadiusPositive := certificate.comparison.positive
  synchronized_close := requestCenter_close (positive := positive)
    certificate.comparison certificate.comparisonBudget_lt_energy
  margin := by
    simpa only [comparisonBudget, requestNormalizedEnergy] using
      requestBudgets_lt_energy positive certificate.comparison.positive
        certificate.comparisonBudget_lt_energy

end RequestCertificate

namespace RawCertificate

/-- In genus one the raw cut-surface theorem itself constructs every finite
normalization request: a fixed box supplies energy, its uniform lower chooses
the comparison radius, and the persistent samplers choose the shared index. -/
def genusOneTransportRequestCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data)
    (vector : RationalVector 1) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FiniteEnergy.TransportRequestCertificate data
      certificate.toScalarCandidateLowerCertificate vector nonzero target
        positive := by
  let inverseLower := certificate.toScalarCandidateLowerCertificate
  let comparison := certificate.genusOneComparisonSchedule vector nonzero
  let sampleIndex := comparison.sampleIndex
  let cells := certificate.genusOneUniformRequestCells sampleIndex vector nonzero
  let energy := genusOneUniformNormalizedEnergyAt data sampleIndex vector
  have comparison_lt_energy :
      comparisonBudget data inverseLower vector comparison.radius
          comparison.positive < energy := by
    exact (certificate.genusOneComparisonBudget_lt_uniformEnergy nonzero).trans_le
      (certificate.genusOneUniformNormalizedEnergyLower_le sampleIndex vector
        nonzero)
  let refinementRadius := outputRadiusFromEnergy data inverseLower vector target
    comparison.radius comparison.positive energy
  have refinementPositive : 0 < refinementRadius :=
    outputRadiusFromEnergy_positive positive comparison.positive
      comparison_lt_energy
  let reduction := certificate.boundaryReduction
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
      vector) sampleIndex (cells 0)
  exact
    { sampleIndex := sampleIndex
      cellCount := 1
      cells := energyCells cells
      positiveCell := 0
      positiveCell_area := (cells 0).area_positive
      positiveCell_density := by
        exact genusOneUniformSurfaceCell_density_positive curve
          (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data
            sampleIndex vector)
          (certificate.genusOneScaledCoefficientLower_positive nonzero)
          (certificate.genusOneScaledCoefficientLower_le sampleIndex vector)
      energy_le_raw := reduction.surfaceEnergy_le_raw
      refinementRadius := refinementRadius
      refinementRadiusPositive := refinementPositive
      refinementTarget_lt_target :=
        outputRadiusFromEnergy_sq_lt_target positive comparison.positive
          comparison_lt_energy
      comparisonRadius := comparison.radius
      comparisonRadiusPositive := comparison.positive
      synchronized_close := by
        intro row column
        exact
          CCL.Riemann.SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
            data inverseLower comparison.radius comparison.positive
              sampleIndex comparison.sampleIndex_eq
              (CCL.Riemann.FinitePositivity.squaredRefinementTarget
                refinementRadius)
              (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
                refinementPositive)
              (outputRadiusFromEnergy_sq_lt_comparisonTarget positive
                comparison.positive comparison_lt_energy) row column
      margin := by
        rw [← certificate.genusOneUniformNormalizedEnergyAt_eq sampleIndex
          vector nonzero]
        simpa only [comparisonBudget,
          show outputRadiusFromEnergy_positive positive comparison.positive
              comparison_lt_energy = refinementPositive from rfl] using
          outputRadiusFromEnergy_budgets_lt_energy positive comparison.positive
            comparison_lt_energy }

/-- A raw genus-one cut-surface certificate therefore supplies the complete
finite normalized positivity transport, with no separate radius schedule. -/
def genusOneTransportCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : RawCertificate data) :
    CCL.Riemann.FiniteEnergy.TransportCertificate data
      certificate.toScalarCandidateLowerCertificate where
  certify := fun vector nonzero target positive =>
    certificate.genusOneTransportRequestCertificate vector nonzero target
      positive

end RawCertificate

namespace GenusOneUnitSurfaceLowerCertificate

/-- The single unit-differential surface inequality constructs one complete
normalized positivity request.  Genus-one homogeneity supplies the requested
coefficient cells and the synchronized comparison schedule. -/
def genusOneTransportRequestCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data)
    (vector : RationalVector 1) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FiniteEnergy.TransportRequestCertificate data
      certificate.toScalarCandidateLowerCertificate vector nonzero target
        positive := by
  let inverseLower := certificate.toScalarCandidateLowerCertificate
  let comparison :=
    certificate.genusOneScaledReferenceComparisonSchedule vector nonzero
  let sampleIndex := comparison.sampleIndex
  let cells := certificate.scaledReferenceRequestCells sampleIndex vector
    nonzero
  let energy := genusOneScaledReferenceNormalizedEnergyAt data sampleIndex
    vector
  have comparison_lt_energy :
      comparisonBudget data inverseLower vector comparison.radius
          comparison.positive < energy := by
    exact
      (certificate.genusOneScaledReferenceComparisonBudget_lt_energy
        nonzero).trans_le
      (certificate.genusOneScaledReferenceNormalizedEnergyLower_le sampleIndex
        vector nonzero)
  let refinementRadius := outputRadiusFromEnergy data inverseLower vector target
    comparison.radius comparison.positive energy
  have refinementPositive : 0 < refinementRadius :=
    outputRadiusFromEnergy_positive positive comparison.positive
      comparison_lt_energy
  exact
    { sampleIndex := sampleIndex
      cellCount := 1
      cells := energyCells cells
      positiveCell := 0
      positiveCell_area := (cells 0).area_positive
      positiveCell_density := by
        exact genusOneScaledReferenceSurfaceCell_density_positive curve
          (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data
            sampleIndex vector)
          (certificate.genusOneScaledCoefficientLower_positive nonzero)
          (certificate.genusOneScaledCoefficientLower_le sampleIndex vector)
      energy_le_raw :=
        (certificate.scaledReferenceBoundaryReduction sampleIndex vector
          nonzero).surfaceEnergy_le_raw
      refinementRadius := refinementRadius
      refinementRadiusPositive := refinementPositive
      refinementTarget_lt_target :=
        outputRadiusFromEnergy_sq_lt_target positive comparison.positive
          comparison_lt_energy
      comparisonRadius := comparison.radius
      comparisonRadiusPositive := comparison.positive
      synchronized_close := by
        intro row column
        exact
          CCL.Riemann.SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
            data inverseLower comparison.radius comparison.positive
              sampleIndex comparison.sampleIndex_eq
              (CCL.Riemann.FinitePositivity.squaredRefinementTarget
                refinementRadius)
              (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
                refinementPositive)
              (outputRadiusFromEnergy_sq_lt_comparisonTarget positive
                comparison.positive comparison_lt_energy) row column
      margin := by
        rw [← certificate.genusOneScaledReferenceNormalizedEnergyAt_eq
          sampleIndex vector nonzero]
        simpa only [comparisonBudget,
          show outputRadiusFromEnergy_positive positive comparison.positive
              comparison_lt_energy = refinementPositive from rfl] using
          outputRadiusFromEnergy_budgets_lt_energy positive comparison.positive
            comparison_lt_energy }

/-- A genus-one unit surface inequality supplies the entire finite normalized
energy transport, so no arbitrary coefficient or box family remains in the
public analytic input. -/
def genusOneTransportCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitSurfaceLowerCertificate data) :
    CCL.Riemann.FiniteEnergy.TransportCertificate data
      certificate.toScalarCandidateLowerCertificate where
  certify := fun vector nonzero target positive =>
    certificate.genusOneTransportRequestCertificate vector nonzero target
      positive

end GenusOneUnitSurfaceLowerCertificate

namespace RawRequestSchedule

/-- Supply the boundary reduction from the inverse-independent raw theorem;
the schedule supplies only the remaining finite normalization comparison. -/
def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (schedule : RawRequestSchedule data inverseLower vector nonzero target
      positive)
    (raw : RawCertificate data) :
    RequestCertificate data inverseLower vector nonzero target positive where
  comparison := schedule.comparison
  boundaryReduction := raw.normalizedBoundaryReduction inverseLower
    schedule.comparison.sampleIndex vector nonzero
  comparisonBudget_lt_energy := schedule.comparisonBudget_lt_energy

end RawRequestSchedule

/-- Pointwise prepared surface data for every nonzero rational vector and
positive output request. -/
structure Certificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    RequestCertificate data inverseLower vector nonzero target positive

namespace Certificate

/-- Forget geometry only after constructing every field of the established
raw-cell transport certificate. -/
def toTransportCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : Certificate data inverseLower) :
    CCL.Riemann.FiniteEnergy.TransportCertificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toTransportRequestCertificate

end Certificate

/-- Pointwise normalization schedules kept separate from the global raw
cut-surface theorem.  This contains no local cells or boundary identity. -/
structure RawTransportSchedule {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  schedule : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    RawRequestSchedule data inverseLower vector nonzero target positive

namespace RawTransportSchedule

/-- Combine one raw second-relation theorem with the finite normalization
schedules to recover the established prepared energy certificate. -/
def toCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (schedule : RawTransportSchedule data inverseLower)
    (raw : RawCertificate data) : Certificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (schedule.schedule vector nonzero target positive).toRequestCertificate raw

/-- The same combination directly constructs persistent normalized
pointwise positivity through the generic transport layer. -/
def toTransportCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (schedule : RawTransportSchedule data inverseLower)
    (raw : RawCertificate data) :
    CCL.Riemann.FiniteEnergy.TransportCertificate data inverseLower :=
  (schedule.toCertificate raw).toTransportCertificate

end RawTransportSchedule

/-! ## Controlled-error request interface -/

/-- One second-relation request whose finite cut-surface calculation may have
a displayed rational boundary error.  The error is paid before normalization,
and the remaining strictly positive energy is the only lower bound passed to
the generic transport layer. -/
structure ControlledRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  comparison : ComparisonSchedule data inverseLower
  boundaryReduction : ControlledBoundaryReduction data vector
    comparison.sampleIndex
    (requestCells data inverseLower comparison.sampleIndex vector nonzero)
  boundaryError_lt_surface : boundaryReduction.boundaryError <
    surfaceEnergy
      (requestCells data inverseLower comparison.sampleIndex vector nonzero)
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  refinementTarget_lt_comparisonTarget :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      CCL.Riemann.SynchronizedNormalization.comparisonTarget comparison.radius
  margin :
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
              refinementRadius refinementRadiusPositive)) +
        comparisonBudget data inverseLower vector comparison.radius
          comparison.positive <
      CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower data
        comparison.sampleIndex
        (boundaryReduction.effectiveCells boundaryError_lt_surface)

namespace ControlledRequestCertificate

/-- Pay the finite boundary error and erase the geometric sidecars only after
constructing the positive singleton lower cell. -/
def toTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : ControlledRequestCertificate data inverseLower vector
      nonzero target positive) :
    CCL.Riemann.FiniteEnergy.TransportRequestCertificate data inverseLower
      vector nonzero target positive where
  sampleIndex := certificate.comparison.sampleIndex
  cellCount := 1
  cells := certificate.boundaryReduction.effectiveCells
    certificate.boundaryError_lt_surface
  positiveCell := 0
  positiveCell_area :=
    certificate.boundaryReduction.effectiveSurfaceEnergy_positive
      certificate.boundaryError_lt_surface
  positiveCell_density := by
    change (0 : Coordinate) < 1
    decide
  energy_le_raw := by
    rw [ControlledBoundaryReduction.cellEnergy_effectiveCells]
    exact certificate.boundaryReduction.effectiveSurfaceEnergy_le_raw
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparison.radius
  comparisonRadiusPositive := certificate.comparison.positive
  synchronized_close := by
    intro row column
    exact
      CCL.Riemann.SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
        data inverseLower certificate.comparison.radius
          certificate.comparison.positive certificate.comparison.sampleIndex
            certificate.comparison.sampleIndex_eq
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)
          certificate.refinementTarget_lt_comparisonTarget row column
  margin := by
    simpa only [comparisonBudget] using certificate.margin

end ControlledRequestCertificate

/-- Pointwise geometry-backed energy data with a controlled finite boundary
error at every rational request. -/
structure ControlledCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    ControlledRequestCertificate data inverseLower vector nonzero target
      positive

namespace ControlledCertificate

/-- Controlled finite boundary errors construct the generic pointwise energy
transport certificate. -/
def toTransportCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : ControlledCertificate data inverseLower) :
    CCL.Riemann.FiniteEnergy.TransportCertificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toTransportRequestCertificate

end ControlledCertificate

/-! ## Tail-compatible controlled energy transport -/

/-- A retained synchronized raw sample has nonzero complete inverse scalar.
This uses only the tail anchor estimate and makes no assertion about any
discarded coarse centre. -/
theorem tailSynchronizedScaledInverse_scalar_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix)
    (sampleIndex : Nat) (anchor_le : inverseTail.anchor <= sampleIndex) :
    (CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data sampleIndex).scalar
      ≠ 0 := by
  let inverse :=
    CCL.Riemann.FiniteEnergy.synchronizedScaledInverse data sampleIndex
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex =
        inverse.scalar := by
    unfold canonicalScaledInverse inverse
      CCL.Riemann.FiniteEnergy.synchronizedScaledInverse
    have samples :=
      CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) sampleIndex
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply inverseTail.sample_nonzero_of_anchor_le sampleIndex anchor_le
  rw [scalarSample, scalarZero]

/-- One geometry-backed second-relation request for a tail-apartified inverse.
The selected raw sample lies after the certified anchor.  A finite boundary
error is subtracted from the displayed surface cells before exact
normalization and entrywise transport to the persistent centre. -/
structure TailControlledRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  sampleIndex : Nat
  anchor_le : inverseTail.anchor <= sampleIndex
  cellCount : Nat
  cells : Fin cellCount -> SurfaceCell curve
    (CCL.Riemann.FiniteEnergy.scaledNormalizedCoefficients data sampleIndex
      vector)
  boundaryReduction : ControlledBoundaryReduction data vector sampleIndex cells
  boundaryError_lt_surface :
    boundaryReduction.boundaryError < surfaceEnergy cells
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  comparisonRadius : Coordinate
  comparisonRadiusPositive : 0 < comparisonRadius
  synchronized_close : forall row column : Fin genus,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePositivity.centerMatrix
            (NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget
              refinementRadius)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data
            sampleIndex row column) <
      comparisonRadius ^ 2
  margin :
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (NormalizedPeriodData.ofScaledInverse data
                inverseTail.toScaledInverseCertificate)
              refinementRadius refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (NormalizedPeriodData.ofScaledInverse data
                inverseTail.toScaledInverseCertificate)
              comparisonRadius comparisonRadiusPositive)) <
      CCL.Riemann.FiniteEnergy.synchronizedNormalizedEnergyLower data
        sampleIndex
        (boundaryReduction.effectiveCells boundaryError_lt_surface)

namespace TailControlledRequestCertificate

/-- Convert the controlled cut-surface calculation into the generic
presentation-independent raw-sample transport. -/
def toSampleTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TailControlledRequestCertificate data inverseTail vector
      nonzero target positive) :
    CCL.Riemann.FiniteEnergy.SampleTransportRequestCertificate
      (NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate)
      vector nonzero target positive where
  sampleIndex := certificate.sampleIndex
  scalarNonzero := tailSynchronizedScaledInverse_scalar_nonzero inverseTail
    certificate.sampleIndex certificate.anchor_le
  cellCount := 1
  cells := certificate.boundaryReduction.effectiveCells
    certificate.boundaryError_lt_surface
  positiveCell := 0
  positiveCell_area :=
    certificate.boundaryReduction.effectiveSurfaceEnergy_positive
      certificate.boundaryError_lt_surface
  positiveCell_density := by
    change (0 : Coordinate) < 1
    decide
  energy_le_raw := by
    rw [ControlledBoundaryReduction.cellEnergy_effectiveCells]
    exact certificate.boundaryReduction.effectiveSurfaceEnergy_le_raw
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparisonRadius
  comparisonRadiusPositive := certificate.comparisonRadiusPositive
  synchronized_close := certificate.synchronized_close
  margin := certificate.margin

def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TailControlledRequestCertificate data inverseTail vector
      nonzero target positive) :
    CCL.Riemann.FiniteEnergy.RequestCertificate
      (NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate)
      vector nonzero target positive :=
  certificate.toSampleTransportRequestCertificate.toRequestCertificate

end TailControlledRequestCertificate

/-- Pointwise controlled surface calculations for a tail-normalized period
matrix. -/
structure TailControlledCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    TailControlledRequestCertificate data inverseTail vector nonzero target
      positive

namespace TailControlledCertificate

/-- All public normalized energy fields are derived after paying the finite
boundary error and transporting one retained exact quotient sample. -/
def toEnergyCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    (certificate : TailControlledCertificate data inverseTail) :
    CCL.Riemann.FiniteEnergy.Certificate
      (NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate) where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

end TailControlledCertificate

/-- Prepared schedules retain the geometry-backed surface interface at the
same synchronized period data used by their A/B programs. -/
abbrev CompatibleCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix) :=
  Certificate schedules.toPeriodData inverseLower

/-- Prepared schedules retain the controlled-error surface interface at the
same synchronized period data used by their A/B programs. -/
abbrev CompatibleControlledCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix) :=
  ControlledCertificate schedules.toPeriodData inverseLower

end CCL.Riemann.PreparedEnergy
