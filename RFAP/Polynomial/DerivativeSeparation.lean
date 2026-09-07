import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Bounds
import RFAP.Polynomial.Squarefree

/-!
# Finite derivative-separation certificates

A derivative-separation certificate is the exact quantitative fragment of a
squarefree Bézout argument used by the local Newton construction.  It says
that, throughout one displayed rational box, a sufficiently small polynomial
value forces a displayed positive lower bound for the derivative.

The second constructor below deliberately accepts an *approximate* Bézout
identity.  This is useful when the exact rational coefficients of a
polynomial are one finite reading of progressive coefficient channels: an
exact Bézout identity for one reference reading remains quantitatively useful
for every sufficiently close later reading, without pretending that the two
displayed polynomials are equal.
-/

namespace RFAP.DerivativeSeparation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate := RFAP.Squarefree.SquarefreeCertificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds

/-- Finite quantitative separation of a polynomial from its derivative on a
displayed rational box. -/
structure Certificate (p : GaussianPolynomial) (ambient : Box) where
  threshold : Coordinate
  threshold_pos : 0 < threshold
  margin : Coordinate
  margin_pos : 0 < margin
  lower : ∀ {z : Gaussian}, ambient.Contains z →
    normSq (p.eval z) ≤ threshold →
      margin ≤ normSq ((RFAP.ConstructiveGCD.derivative p).eval z)

namespace Certificate

/-- Restrict the same quantitative certificate to a displayed subbox. -/
def restrict
    {p : GaussianPolynomial} {ambient small : Box}
    (certificate : Certificate p ambient) (refines : small.Refines ambient) :
    Certificate p small where
  threshold := certificate.threshold
  threshold_pos := certificate.threshold_pos
  margin := certificate.margin
  margin_pos := certificate.margin_pos
  lower := fun inside residual => certificate.lower
    (refines.contains inside) residual

@[simp] theorem restrict_threshold
    {p : GaussianPolynomial} {ambient small : Box}
    (certificate : Certificate p ambient) (refines : small.Refines ambient) :
    (certificate.restrict refines).threshold = certificate.threshold := rfl

@[simp] theorem restrict_margin
    {p : GaussianPolynomial} {ambient small : Box}
    (certificate : Certificate p ambient) (refines : small.Refines ambient) :
    (certificate.restrict refines).margin = certificate.margin := rfl

end Certificate

private theorem majorant_mul_sixteenth_inverse_le
    {majorant : Coordinate} (positive : 0 < majorant) :
    majorant * (1 / (16 * majorant)) ≤ (1 / 16 : Coordinate) := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 16 by decide)).mpr
  calc
    (majorant * (1 / (16 * majorant))) * 16 =
        (1 / (16 * majorant)) * (16 * majorant) := by ring1
    _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
      (16 * majorant)
      (ne_of_gt (RFAP.ConstructiveFraction.mul_pos_direct
        (by decide) positive))
    _ ≤ 1 := le_rfl

/-- The conservative residual scale used by an approximate displayed
Bézout identity. -/
def approximateThreshold (left : GaussianPolynomial)
    (ambient : Box) : Coordinate :=
  1 / (16 * denseEvalNormMajorant left ambient)

/-- The conservative derivative margin used by an approximate displayed
Bézout identity. -/
def approximateMargin (right : GaussianPolynomial)
    (ambient : Box) : Coordinate :=
  1 / (16 * denseEvalNormMajorant right ambient)

theorem approximateThreshold_pos (left : GaussianPolynomial)
    (ambient : Box) : 0 < approximateThreshold left ambient := by
  apply RFAP.ConstructiveFraction.div_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (denseEvalNormMajorant_pos left ambient)

theorem approximateMargin_pos (right : GaussianPolynomial)
    (ambient : Box) : 0 < approximateMargin right ambient := by
  apply RFAP.ConstructiveFraction.div_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (denseEvalNormMajorant_pos right ambient)

/-- The quantitative estimate underlying `ofApproximateBezout`, kept outside
the certificate constructor so that every intermediate rational bound is
checked separately. -/
theorem approximateMargin_le
    (p left right : GaussianPolynomial) (ambient : Box)
    (approximateIdentity : ∀ {z : Gaussian}, ambient.Contains z →
      normSq
        (1 - (left.eval z * p.eval z + right.eval z *
          (RFAP.ConstructiveGCD.derivative p).eval z)) ≤
        (1 / 16 : Coordinate))
    {z : Gaussian} (inside : ambient.Contains z)
    (small : normSq (p.eval z) ≤ approximateThreshold left ambient) :
    approximateMargin right ambient ≤
      normSq ((RFAP.ConstructiveGCD.derivative p).eval z) := by
  let leftMajorant := denseEvalNormMajorant left ambient
  let rightMajorant := denseEvalNormMajorant right ambient
  let threshold := approximateThreshold left ambient
  let margin := approximateMargin right ambient
  have leftMajorantPositive : 0 < leftMajorant :=
    denseEvalNormMajorant_pos left ambient
  have rightMajorantPositive : 0 < rightMajorant :=
    denseEvalNormMajorant_pos right ambient
  let leftValue := left.eval z
  let rightValue := right.eval z
  let value := p.eval z
  let derivativeValue := (RFAP.ConstructiveGCD.derivative p).eval z
  let error := 1 - (leftValue * value + rightValue * derivativeValue)
  have leftBound : normSq leftValue ≤ leftMajorant :=
    normSq_eval_le_denseEvalNormMajorant left inside
  have rightBound : normSq rightValue ≤ rightMajorant :=
    normSq_eval_le_denseEvalNormMajorant right inside
  have errorBound : normSq error ≤ (1 / 16 : Coordinate) := by
    exact approximateIdentity inside
  by_cases marginBound : margin ≤ normSq derivativeValue
  · exact marginBound
  · have derivativeBound : normSq derivativeValue ≤ margin :=
      (lt_of_not_ge marginBound).le
    have leftProduct : normSq leftValue * normSq value ≤
        leftMajorant * threshold :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftBound small
        (normSq_nonneg value) leftMajorantPositive.le
    have rightProduct : normSq rightValue * normSq derivativeValue ≤
        rightMajorant * margin :=
      RFAP.ConstructiveFraction.mul_le_mul_direct rightBound derivativeBound
        (normSq_nonneg derivativeValue) rightMajorantPositive.le
    have leftScaled : leftMajorant * threshold ≤
        (1 / 16 : Coordinate) :=
      majorant_mul_sixteenth_inverse_le leftMajorantPositive
    have rightScaled : rightMajorant * margin ≤
        (1 / 16 : Coordinate) :=
      majorant_mul_sixteenth_inverse_le rightMajorantPositive
    have pairNorm := normSq_add_le_two
      (leftValue * value) (rightValue * derivativeValue)
    have pairBound :
        normSq (leftValue * value + rightValue * derivativeValue) ≤
          (1 / 4 : Coordinate) := by
      calc
        normSq (leftValue * value + rightValue * derivativeValue) ≤
            2 * (normSq (leftValue * value) +
              normSq (rightValue * derivativeValue)) := pairNorm
        _ = 2 * (normSq leftValue * normSq value +
              normSq rightValue * normSq derivativeValue) := by
          rw [normSq_mul, normSq_mul]
        _ ≤ 2 * ((1 / 16 : Coordinate) + 1 / 16) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.trans leftScaled)
              (rightProduct.trans rightScaled)) (by decide)
        _ = 1 / 4 := by decide
    have totalNorm := normSq_add_le_two
      (leftValue * value + rightValue * derivativeValue) error
    have identity :
        1 = (leftValue * value + rightValue * derivativeValue) + error := by
      dsimp only [error]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, one_re, one_im] <;>
        ring1
    have totalBound :
        normSq
            ((leftValue * value + rightValue * derivativeValue) + error) ≤
          (5 / 8 : Coordinate) := by
      calc
        normSq
            ((leftValue * value + rightValue * derivativeValue) + error) ≤
            2 *
            (normSq (leftValue * value + rightValue * derivativeValue) +
              normSq error) := totalNorm
        _ ≤ 2 * ((1 / 4 : Coordinate) + 1 / 16) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add pairBound errorBound) (by decide)
        _ = 5 / 8 := by decide
    have impossible : (1 : Coordinate) ≤ 5 / 8 := by
      calc
        (1 : Coordinate) =
            normSq
              ((leftValue * value + rightValue * derivativeValue) +
                error) := by
          rw [← identity, normSq_one]
        _ ≤ 5 / 8 := totalBound
    exact ((show ¬ ((1 : Coordinate) ≤ 5 / 8) by decide)
      impossible).elim

/-- A uniformly accurate displayed approximate Bézout identity separates
the derivative.  The error budget `1/16` and the two `1/16` product budgets
leave a strict rational gap after two applications of the Gaussian
sum-quadrance inequality. -/
def ofApproximateBezout
    (p left right : GaussianPolynomial) (ambient : Box)
    (approximateIdentity : ∀ {z : Gaussian}, ambient.Contains z →
      normSq
        (1 - (left.eval z * p.eval z + right.eval z *
          (RFAP.ConstructiveGCD.derivative p).eval z)) ≤
        (1 / 16 : Coordinate)) :
    Certificate p ambient where
  threshold := approximateThreshold left ambient
  threshold_pos := approximateThreshold_pos left ambient
  margin := approximateMargin right ambient
  margin_pos := approximateMargin_pos right ambient
  lower := approximateMargin_le p left right ambient approximateIdentity

/-- The ordinary exact squarefree Bézout certificate is the zero-error
special case.  The familiar `1/16` constants are retained here. -/
def ofSquarefree
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) : Certificate p ambient :=
  ofApproximateBezout p squarefree.left squarefree.right ambient (by
    intro z _inside
    rw [squarefree.identity z]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact (show (0 : Coordinate) ≤ 1 / 16 by decide))

end RFAP.DerivativeSeparation
