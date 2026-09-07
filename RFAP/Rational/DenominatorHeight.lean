import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.HeightApproximation
import RFAP.Rational.ResidualChordal

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace RFAP.RationalDenominatorHeight

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Fraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev SquarefreeCertificate := RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev LocalQuotientContext :=
  RFAP.RationalResidualChordal.LocalQuotientContext

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PolynomialBounds

/-- Necessary height bound for a nonzero quotient residual.  For a zero track
take `source = P`, `opposite = Q`; for a pole track take `source = Q`,
`opposite = P`, making this the corresponding reciprocal-residual bound. -/
theorem one_le_scaled_height_mul_quotientResidual
    {source opposite : GaussianPolynomial} {ambient : Box}
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (fraction : Fraction) (inside : state.box.Contains fraction.value)
    (sourceNonzero : source.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (RFAP.DenominatorHeight.coefficientScale source : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ source.natDegree *
          context.oppositeMajorant *
            RFAP.RationalResidualChordal.quotientResidualSq
              source opposite fraction.value := by
  have sourceLower :=
    RFAP.DenominatorHeight.one_le_scaled_height_mul_residual source
      (RFAP.GlobalWinding.isZero_false_of_natDegree_pos
        context.sourceDegreePositive)
      fraction sourceNonzero
  have sourceUpper :=
    context.sourceResidual_le_quotientResidualSq_mul_majorant
      refinesProtected inside
  have scalePositive : (0 : Coordinate) <
      (RFAP.DenominatorHeight.coefficientScale source : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (RFAP.DenominatorHeight.coefficientScale_pos source)
  have heightPositiveNat : 0 < fraction.height := by
    exact Nat.pow_pos fraction.denominatorPositive
  have heightPositive : (0 : Coordinate) < (fraction.height : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct heightPositiveNat
  have scaleNonnegative : (0 : Coordinate) ≤
      (RFAP.DenominatorHeight.coefficientScale source : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ source.natDegree :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        scalePositive.le 2)
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        heightPositive.le _)
  calc
    (1 : Coordinate) ≤
        (RFAP.DenominatorHeight.coefficientScale source : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ source.natDegree *
            normSq (source.eval fraction.value) := sourceLower
    _ ≤
        ((RFAP.DenominatorHeight.coefficientScale source : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ source.natDegree) *
            (RFAP.RationalResidualChordal.quotientResidualSq
              source opposite fraction.value * context.oppositeMajorant) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sourceUpper
        scaleNonnegative
    _ =
        (RFAP.DenominatorHeight.coefficientScale source : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ source.natDegree *
            context.oppositeMajorant *
              RFAP.RationalResidualChordal.quotientResidualSq
                source opposite fraction.value := by ring1

/-- A denominator-controlled source approximation together with the
corresponding protected quotient estimate. -/
structure Output
    {source opposite : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination : AxisEliminationCertificate source degreeBound)
    (epsilon : Coordinate) where
  polynomial : RFAP.HeightApproximation.Output degreeAtLeastTwo squarefree
    elimination context.protectedState.raw epsilon
  quotientResidual_le :
    RFAP.RationalResidualChordal.quotientResidualSq source opposite
        polynomial.fraction.value ≤
      (2 * denseLipschitzBound source ambient * epsilon ^ 2) /
        context.oppositeMargin

/-- Construct the height-controlled sample.  At a pole this is called with
the reduced denominator as `source`; the certified small quantity is then
`normSq(Q/P)`, not `normSq(P/Q)`. -/
def approximate
    {source opposite : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination : AxisEliminationCertificate source degreeBound)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    Output context degreeAtLeastTwo squarefree elimination epsilon := by
  let polynomial := RFAP.HeightApproximation.approximate degreeAtLeastTwo
    squarefree elimination context.protectedState.raw epsilonPositive
  let state := RFAP.HeightApproximation.stateOfOutput polynomial.extracted
  have refinesProtected : state.box.Refines context.protectedState.box := by
    exact polynomial.extracted.strictCurrent.refines
  have quotientBound := context.quotientResidualSq_le_diagonal
    refinesProtected polynomial.strictlyInside.contains
  have numeratorBound :
      4 * denseLipschitzBound source ambient * state.box.diagonalSq ≤
        2 * denseLipschitzBound source ambient * epsilon ^ 2 := by
    calc
      4 * denseLipschitzBound source ambient * state.box.diagonalSq ≤
          4 * denseLipschitzBound source ambient *
            ((1 / 2 : Coordinate) * epsilon ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          polynomial.extracted.diagonalSq_le_half
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (denseLipschitzBound_pos source ambient).le)
      _ = 2 * denseLipschitzBound source ambient * epsilon ^ 2 := by
        have fourHalf : (4 : Coordinate) * (1 / 2) = 2 := by decide
        calc
          4 * denseLipschitzBound source ambient *
              ((1 / 2 : Coordinate) * epsilon ^ 2) =
              ((4 : Coordinate) * (1 / 2)) *
                denseLipschitzBound source ambient * epsilon ^ 2 := by ring1
          _ = 2 * denseLipschitzBound source ambient * epsilon ^ 2 := by
            rw [fourHalf]
  have dividedBound :
      (4 * denseLipschitzBound source ambient * state.box.diagonalSq) /
          context.oppositeMargin ≤
        (2 * denseLipschitzBound source ambient * epsilon ^ 2) /
          context.oppositeMargin := by
    change
      (4 * denseLipschitzBound source ambient * state.box.diagonalSq) *
          context.oppositeMargin⁻¹ ≤
        (2 * denseLipschitzBound source ambient * epsilon ^ 2) *
          context.oppositeMargin⁻¹
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      numeratorBound
      (RFAP.ConstructiveFraction.inv_pos_direct
        context.oppositeMargin_pos).le
  exact
    { polynomial := polynomial
      quotientResidual_le := quotientBound.trans dividedBound }

/-- Positive quadratic coefficient in the protected quotient-residual bound. -/
def targetCoefficient
    {source opposite : GaussianPolynomial} {ambient : Box}
    (context : LocalQuotientContext source opposite ambient) : Coordinate :=
  (2 * denseLipschitzBound source ambient) / context.oppositeMargin

theorem targetCoefficient_pos
    {source opposite : GaussianPolynomial} {ambient : Box}
    (context : LocalQuotientContext source opposite ambient) :
    0 < targetCoefficient context := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (denseLipschitzBound_pos source ambient))
    context.oppositeMargin_pos

theorem targetCoefficient_mul_epsilon_sq
    {source opposite : GaussianPolynomial} {ambient : Box}
    (context : LocalQuotientContext source opposite ambient)
    (epsilon : Coordinate) :
    (2 * denseLipschitzBound source ambient * epsilon ^ 2) /
        context.oppositeMargin =
      targetCoefficient context * epsilon ^ 2 := by
  unfold targetCoefficient
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    (2 * denseLipschitzBound source ambient * epsilon ^ 2) *
        context.oppositeMargin⁻¹ =
        (2 * denseLipschitzBound source ambient) *
          (epsilon ^ 2 * context.oppositeMargin⁻¹) :=
      RFAP.ConstructiveFraction.mul_assoc _ _ _
    _ = (2 * denseLipschitzBound source ambient) *
          (context.oppositeMargin⁻¹ * epsilon ^ 2) := by
      exact congrArg
        (fun value => (2 * denseLipschitzBound source ambient) * value)
        (RFAP.ConstructiveFraction.mul_comm _ _)
    _ = (2 * denseLipschitzBound source ambient *
          context.oppositeMargin⁻¹) * epsilon ^ 2 :=
      (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm

/-- Execute protected quotient approximation with the square-root-scaled
request belonging to its checked quotient coefficient. -/
def approximateTarget
    {source opposite : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination : AxisEliminationCertificate source degreeBound)
    (target : Coordinate) :
    Output context degreeAtLeastTwo squarefree elimination
      (RFAP.HeightApproximation.targetEpsilon
        (targetCoefficient context) target) :=
  approximate context degreeAtLeastTwo squarefree elimination
    (RFAP.HeightApproximation.targetEpsilon_pos _ target)

theorem approximateTarget_quotientResidual_le
    {source opposite : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination : AxisEliminationCertificate source degreeBound)
    {target : Coordinate} (targetPositive : 0 < target) :
    RFAP.RationalResidualChordal.quotientResidualSq source opposite
        (approximateTarget context degreeAtLeastTwo squarefree elimination
          target).polynomial.fraction.value ≤ target := by
  have coefficientBound :=
    RFAP.HeightApproximation.coefficient_mul_targetEpsilon_sq_le
      (targetCoefficient_pos context) targetPositive
  have outputBound :=
    (approximateTarget context degreeAtLeastTwo squarefree elimination
      target).quotientResidual_le
  rw [targetCoefficient_mul_epsilon_sq] at outputBound
  exact outputBound.trans coefficientBound

end RFAP.RationalDenominatorHeight
