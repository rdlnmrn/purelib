import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ShrinkingTrack

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace RFAP.ResidualWinding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate

/-- Minimal protected parent needed by residual Newton localization.  The
parent winding count is intentionally absent: geometry, boundary clearance,
and refinement into the fixed ambient box are sufficient.  The squarefree
and elimination arguments supplied to the constructors carry the derivative,
Taylor, and safe-line data. -/
structure ProtectedAmbient (p : GaussianPolynomial) (ambient : Box) where
  box : Box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : RFAP.BoxClearance.BoundaryClearance p box

/-- Forget the winding count of an ordinary winding-one state. -/
def ProtectedAmbient.ofWindingOne
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) : ProtectedAmbient p ambient where
  box := state.box
  refinesAmbient := state.refinesAmbient
  proper := state.proper
  clearance := state.clearance

instance {p : GaussianPolynomial} {ambient : Box} :
    Coe (WindingOneState p ambient) (ProtectedAmbient p ambient) where
  coe := ProtectedAmbient.ofWindingOne

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.BoxClearance
open RFAP.LocalExtraction
open RFAP.NewtonBand
open RFAP.PolynomialBounds

/-- Positive square extending up and right from one displayed rational
sample.  Its fixed box anchor is definitionally that sample. -/
def anchoredSquare (point : Gaussian) (radius : Coordinate)
    (nonnegative : 0 ≤ radius) : Box where
  xLower := point.re
  xUpper := point.re + radius
  yLower := point.im
  yUpper := point.im + radius
  x_valid := le_add_of_nonneg_right nonnegative
  y_valid := le_add_of_nonneg_right nonnegative

@[simp] theorem anchoredSquare_anchor
    (point : Gaussian) (radius : Coordinate) (nonnegative : 0 ≤ radius) :
    (anchoredSquare point radius nonnegative).anchor = point := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> rfl

theorem anchoredSquare_proper
    (point : Gaussian) {radius : Coordinate} (positive : 0 < radius) :
    (anchoredSquare point radius positive.le).Proper := by
  constructor
  · calc
      point.re = 0 + point.re := by ring1
      _ < radius + point.re :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct positive point.re
      _ = point.re + radius := by ring1
  · calc
      point.im = 0 + point.im := by ring1
      _ < radius + point.im :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct positive point.im
      _ = point.im + radius := by ring1

@[simp] theorem anchoredSquare_diagonalSq
    (point : Gaussian) (radius : Coordinate) (nonnegative : 0 ≤ radius) :
    (anchoredSquare point radius nonnegative).diagonalSq = 2 * radius ^ 2 := by
  dsimp only [anchoredSquare, RFAP.Boxes.Box.diagonalSq,
    RFAP.Boxes.Box.widthX, RFAP.Boxes.Box.widthY]
  ring1

/-- Sharper Newton displacement bound using the actual displayed rational
residual, rather than the coarser whole-source variation budget. -/
theorem newton_displacementResidualMargin
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree) :
    normSq (newton.point - source.anchor) ≤
      normSq (p.eval source.anchor) /
        derivativeMargin squarefree ambient := by
  have derivativeNormPositive :
      0 < normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) :=
    normSq_pos newton.derivativeNonzero
  have marginPositive := derivativeMargin_pos squarefree ambient
  have inverseBound :
      (normSq
        ((RFAP.ConstructiveGCD.derivative p).eval source.anchor))⁻¹ ≤
      (derivativeMargin squarefree ambient)⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct marginPositive
      newton.derivativeLower
  rw [newton.point_eq,
    normSq_anchorNewtonCenter_sub_anchor newton.derivativeNonzero]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    inverseBound (normSq_nonneg (p.eval source.anchor))

/-- All finite inequalities needed to turn the rational anchor of `source`
into an eliminant-safe winding-four band strictly inside `current`. -/
structure Seed
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : ProtectedAmbient p ambient) where
  source : Box
  sourceRefines : source.Refines current.box
  residual : normSq (p.eval source.anchor) ≤
    anchorResidualBound p current.box source
  threshold : anchorResidualBound p current.box source ≤
    derivativeThreshold squarefree current.box
  radius : Coordinate
  radiusPositive : 0 < radius
  displacementBudget :
    normSq (p.eval source.anchor) /
        derivativeMargin squarefree current.box ≤ radius ^ 2
  taylorSmall :
    2 * (RFAP.NewtonExtraction.extractionBandTaylorCoefficient *
      denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        derivativeMargin squarefree current.box
  bandStrict :
    (selectedBand elimination (anchorNewtonCenter p source) radius
      radiusPositive).box.StrictInterior current.box

/-- Direct finite input for building a seed at a displayed rational point.
The four margin inequalities leave three radii for the selected Newton band;
the remaining hypotheses are coefficient-computed scalar budgets. -/
structure AnchoredInput
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient) where
  point : Gaussian
  radius : Coordinate
  radiusPositive : 0 < radius
  leftMargin : current.box.xLower + 3 * radius < point.re
  rightMargin : point.re + 3 * radius < current.box.xUpper
  bottomMargin : current.box.yLower + 3 * radius < point.im
  topMargin : point.im + 3 * radius < current.box.yUpper
  residual : normSq (p.eval point) ≤
    denseLipschitzBound p current.box * (2 * radius ^ 2)
  threshold : denseLipschitzBound p current.box * (2 * radius ^ 2) ≤
    derivativeThreshold squarefree current.box
  displacementBudget :
    normSq (p.eval point) /
        derivativeMargin squarefree current.box ≤ radius ^ 2
  taylorSmall :
    2 * (RFAP.NewtonExtraction.extractionBandTaylorCoefficient *
      denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        derivativeMargin squarefree current.box

namespace AnchoredInput

variable {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
variable {squarefree : SquarefreeCertificate p}
variable {current : ProtectedAmbient p ambient}

/-- The displayed point's anchored source square lies inside the current
winding box. -/
theorem sourceRefines
    (input : AnchoredInput squarefree current) :
    (anchoredSquare input.point input.radius input.radiusPositive.le).Refines
      current.box := by
  have radiusLeThree : input.radius ≤ 3 * input.radius := by
    have twiceNonnegative : 0 ≤ 2 * input.radius :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        input.radiusPositive.le
    calc
      input.radius = 0 + input.radius := by ring1
      _ ≤ 2 * input.radius + input.radius :=
        RFAP.ConstructiveFraction.add_le_add_right_direct twiceNonnegative
          input.radius
      _ = 3 * input.radius := by ring1
  have threeRadiusPositive : 0 < 3 * input.radius :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      input.radiusPositive
  have xLower : current.box.xLower ≤ input.point.re := by
    have beforeMargin : current.box.xLower <
        current.box.xLower + 3 * input.radius := by
      calc
        current.box.xLower = 0 + current.box.xLower := by ring1
        _ < 3 * input.radius + current.box.xLower :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct
            threeRadiusPositive current.box.xLower
        _ = current.box.xLower + 3 * input.radius := by ring1
    exact (beforeMargin.trans input.leftMargin).le
  have xUpper : input.point.re + input.radius ≤ current.box.xUpper := by
    exact (calc
        input.point.re + input.radius ≤
            input.point.re + 3 * input.radius := by
          rw [RFAP.ConstructiveFraction.add_comm input.point.re input.radius,
            RFAP.ConstructiveFraction.add_comm input.point.re
              (3 * input.radius)]
          exact RFAP.ConstructiveFraction.add_le_add_right_direct radiusLeThree
            input.point.re
        _ < current.box.xUpper := input.rightMargin).le
  have yLower : current.box.yLower ≤ input.point.im := by
    have beforeMargin : current.box.yLower <
        current.box.yLower + 3 * input.radius := by
      calc
        current.box.yLower = 0 + current.box.yLower := by ring1
        _ < 3 * input.radius + current.box.yLower :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct
            threeRadiusPositive current.box.yLower
        _ = current.box.yLower + 3 * input.radius := by ring1
    exact (beforeMargin.trans input.bottomMargin).le
  have yUpper : input.point.im + input.radius ≤ current.box.yUpper := by
    exact (calc
        input.point.im + input.radius ≤
            input.point.im + 3 * input.radius := by
          rw [RFAP.ConstructiveFraction.add_comm input.point.im input.radius,
            RFAP.ConstructiveFraction.add_comm input.point.im
              (3 * input.radius)]
          exact RFAP.ConstructiveFraction.add_le_add_right_direct radiusLeThree
            input.point.im
        _ < current.box.yUpper := input.topMargin).le
  exact
    ⟨xLower, xUpper, yLower, yUpper⟩

/-- Construct the complete residual seed from the anchored scalar input. -/
def seed
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    Seed squarefree elimination current := by
  let source := anchoredSquare input.point input.radius
    input.radiusPositive.le
  have sourceRefines : source.Refines current.box := by
    simpa only [source] using input.sourceRefines
  have sourceResidual : normSq (p.eval source.anchor) ≤
      anchorResidualBound p current.box source := by
    simpa only [source, anchoredSquare_anchor, anchorResidualBound,
      anchoredSquare_diagonalSq] using input.residual
  have sourceThreshold : anchorResidualBound p current.box source ≤
      derivativeThreshold squarefree current.box := by
    simpa only [source, anchorResidualBound, anchoredSquare_diagonalSq] using
      input.threshold
  have sourceDisplacementBudget :
      normSq (p.eval source.anchor) /
          derivativeMargin squarefree current.box ≤ input.radius ^ 2 := by
    simpa only [source, anchoredSquare_anchor] using
      input.displacementBudget
  let newton := computeNewtonCenterOfResidual p squarefree sourceRefines
    sourceResidual sourceThreshold
  have displacement :
      normSq (anchorNewtonCenter p source - source.anchor) ≤
        input.radius ^ 2 :=
    (newton_displacementResidualMargin newton).trans sourceDisplacementBudget
  have coordinateBounds :=
    RFAP.AffineWinding.coordinate_bounds_of_normSq_le
      input.radiusPositive.le displacement
  have centerRealLower : input.point.re - input.radius ≤
      (anchorNewtonCenter p source).re := by
    calc
      input.point.re - input.radius = -input.radius + input.point.re := by
        ring1
      _ ≤ (anchorNewtonCenter p source - source.anchor).re +
          input.point.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct coordinateBounds.1
          input.point.re
      _ = (anchorNewtonCenter p source).re := by
        simp only [source, anchoredSquare_anchor, sub_re]
        ring1
  have centerRealUpper : (anchorNewtonCenter p source).re ≤
      input.point.re + input.radius := by
    calc
      (anchorNewtonCenter p source).re =
          (anchorNewtonCenter p source - source.anchor).re +
            input.point.re := by
        simp only [source, anchoredSquare_anchor, sub_re]
        ring1
      _ ≤ input.radius + input.point.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.1 input.point.re
      _ = input.point.re + input.radius := by ring1
  have centerImagLower : input.point.im - input.radius ≤
      (anchorNewtonCenter p source).im := by
    calc
      input.point.im - input.radius = -input.radius + input.point.im := by
        ring1
      _ ≤ (anchorNewtonCenter p source - source.anchor).im +
          input.point.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.2.1 input.point.im
      _ = (anchorNewtonCenter p source).im := by
        simp only [source, anchoredSquare_anchor, sub_im]
        ring1
  have centerImagUpper : (anchorNewtonCenter p source).im ≤
      input.point.im + input.radius := by
    calc
      (anchorNewtonCenter p source).im =
          (anchorNewtonCenter p source - source.anchor).im +
            input.point.im := by
        simp only [source, anchoredSquare_anchor, sub_im]
        ring1
      _ ≤ input.radius + input.point.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.2.2 input.point.im
      _ = input.point.im + input.radius := by ring1
  let band := selectedBand elimination (anchorNewtonCenter p source)
    input.radius input.radiusPositive
  have leftPoint : current.box.xLower <
      input.point.re - 3 * input.radius := by
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
      (c := 3 * input.radius)
    calc
      current.box.xLower + 3 * input.radius < input.point.re :=
        input.leftMargin
      _ = (input.point.re - 3 * input.radius) + 3 * input.radius := by
        ring1
  have rightPoint : input.point.re + 3 * input.radius <
      current.box.xUpper := input.rightMargin
  have bottomPoint : current.box.yLower <
      input.point.im - 3 * input.radius := by
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
      (c := 3 * input.radius)
    calc
      current.box.yLower + 3 * input.radius < input.point.im :=
        input.bottomMargin
      _ = (input.point.im - 3 * input.radius) + 3 * input.radius := by
        ring1
  have topPoint : input.point.im + 3 * input.radius <
      current.box.yUpper := input.topMargin
  have bandStrict : band.box.StrictInterior current.box := by
    exact
      { left := by
          calc
            current.box.xLower < input.point.re - 3 * input.radius :=
              leftPoint
            _ = (input.point.re - input.radius) - 2 * input.radius := by
              ring1
            _ ≤ (anchorNewtonCenter p source).re - 2 * input.radius :=
              RFAP.ConstructiveFraction.sub_le_sub_right_direct centerRealLower _
            _ ≤ band.box.xLower := band.left_lower
        right := by
          calc
            band.box.xUpper ≤
                (anchorNewtonCenter p source).re + 2 * input.radius :=
              band.right_upper
            _ ≤ (input.point.re + input.radius) + 2 * input.radius :=
              RFAP.ConstructiveFraction.add_le_add_right_direct
                centerRealUpper _
            _ = input.point.re + 3 * input.radius := by ring1
            _ < current.box.xUpper := rightPoint
        bottom := by
          calc
            current.box.yLower < input.point.im - 3 * input.radius :=
              bottomPoint
            _ = (input.point.im - input.radius) - 2 * input.radius := by
              ring1
            _ ≤ (anchorNewtonCenter p source).im - 2 * input.radius :=
              RFAP.ConstructiveFraction.sub_le_sub_right_direct centerImagLower _
            _ ≤ band.box.yLower := band.bottom_lower
        top := by
          calc
            band.box.yUpper ≤
                (anchorNewtonCenter p source).im + 2 * input.radius :=
              band.top_upper
            _ ≤ (input.point.im + input.radius) + 2 * input.radius :=
              RFAP.ConstructiveFraction.add_le_add_right_direct
                centerImagUpper _
            _ = input.point.im + 3 * input.radius := by ring1
            _ < current.box.yUpper := topPoint }
  exact
    { source := source
      sourceRefines := sourceRefines
      residual := sourceResidual
      threshold := sourceThreshold
      radius := input.radius
      radiusPositive := input.radiusPositive
      displacementBudget := sourceDisplacementBudget
      taylorSmall := input.taylorSmall
      bandStrict := by simpa only [band] using bandStrict }

@[simp] theorem seed_source
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    (input.seed elimination).source =
      anchoredSquare input.point input.radius input.radiusPositive.le := rfl

@[simp] theorem seed_radius
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    (input.seed elimination).radius = input.radius := rfl

end AnchoredInput

/-! ## Direct restarts from an explicit derivative separation -/

/-- The finite data needed to restart on a predictable Newton-centered
square when the caller already has the derivative separation actually used
by the Newton argument.  Unlike `Seed`, this input does not pass through the
generic squarefree Bezout threshold or its point-dependent radius.  This is
useful for structured polynomial families whose derivative margin is known
uniformly from external finite geometry. -/
structure SeparatedRestartInput
    {p : GaussianPolynomial} {ambient : Box}
    (separation : RFAP.DerivativeSeparation.Certificate p ambient) where
  source : Box
  sourceRefines : source.Refines ambient
  residual : normSq (p.eval source.anchor) <=
    anchorResidualBound p ambient source
  threshold : normSq (p.eval source.anchor) <= separation.threshold
  radius : Coordinate
  radiusPositive : 0 < radius
  displacementBudget :
    normSq (p.eval source.anchor) / separation.margin <= radius ^ 2
  targetStrict :
    (RFAP.AffineWinding.centeredSquare
      (anchorNewtonCenter p source) radius radiusPositive.le).StrictInterior
        ambient
  taylorSmall :
    2 * (36 * denseTaylorRemainderBound p ambient * radius ^ 2) <=
      separation.margin

namespace SeparatedRestartInput

variable {p : GaussianPolynomial} {ambient : Box}
variable {separation : RFAP.DerivativeSeparation.Certificate p ambient}

/-- Build a direct separated restart from one rational anchor with two
radius margins on every side.  One radius pays for the Newton displacement
and the other for the centered target square. -/
def ofAnchored
    (point : Gaussian) (radius : Coordinate) (radiusPositive : 0 < radius)
    (leftMargin : ambient.xLower + 2 * radius < point.re)
    (rightMargin : point.re + 2 * radius < ambient.xUpper)
    (bottomMargin : ambient.yLower + 2 * radius < point.im)
    (topMargin : point.im + 2 * radius < ambient.yUpper)
    (residual : normSq (p.eval point) <=
      denseLipschitzBound p ambient * (2 * radius ^ 2))
    (threshold : normSq (p.eval point) <= separation.threshold)
    (displacementBudget : normSq (p.eval point) / separation.margin <=
      radius ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * radius ^ 2) <=
        separation.margin) :
    SeparatedRestartInput separation := by
  let source := anchoredSquare point radius radiusPositive.le
  have radiusLeTwo : radius <= 2 * radius := by
    calc
      radius = 0 + radius := by ring1
      _ <= radius + radius :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          radiusPositive.le radius
      _ = 2 * radius := by ring1
  have twiceRadiusPositive : 0 < 2 * radius :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) radiusPositive
  have sourceRefines : source.Refines ambient := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have beforeMargin : ambient.xLower < ambient.xLower + 2 * radius := by
        calc
          ambient.xLower = 0 + ambient.xLower := by ring1
          _ < 2 * radius + ambient.xLower :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct
              twiceRadiusPositive ambient.xLower
          _ = ambient.xLower + 2 * radius := by ring1
      exact (beforeMargin.trans leftMargin).le
    · change point.re + radius <= ambient.xUpper
      exact (calc
        point.re + radius <= point.re + 2 * radius := by
          rw [RFAP.ConstructiveFraction.add_comm point.re radius,
            RFAP.ConstructiveFraction.add_comm point.re (2 * radius)]
          exact RFAP.ConstructiveFraction.add_le_add_right_direct radiusLeTwo
            point.re
        _ < ambient.xUpper := rightMargin).le
    · have beforeMargin : ambient.yLower < ambient.yLower + 2 * radius := by
        calc
          ambient.yLower = 0 + ambient.yLower := by ring1
          _ < 2 * radius + ambient.yLower :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct
              twiceRadiusPositive ambient.yLower
          _ = ambient.yLower + 2 * radius := by ring1
      exact (beforeMargin.trans bottomMargin).le
    · change point.im + radius <= ambient.yUpper
      exact (calc
        point.im + radius <= point.im + 2 * radius := by
          rw [RFAP.ConstructiveFraction.add_comm point.im radius,
            RFAP.ConstructiveFraction.add_comm point.im (2 * radius)]
          exact RFAP.ConstructiveFraction.add_le_add_right_direct radiusLeTwo
            point.im
        _ < ambient.yUpper := topMargin).le
  have sourceResidual : normSq (p.eval source.anchor) <=
      anchorResidualBound p ambient source := by
    simpa only [source, anchoredSquare_anchor, anchorResidualBound,
      anchoredSquare_diagonalSq] using residual
  have sourceThreshold : normSq (p.eval source.anchor) <=
      separation.threshold := by
    simpa only [source, anchoredSquare_anchor] using threshold
  have sourceDisplacementBudget :
      normSq (p.eval source.anchor) / separation.margin <=
        radius ^ 2 := by
    simpa only [source, anchoredSquare_anchor] using displacementBudget
  let newton :=
    RFAP.LocalExtraction.computeNewtonCenterOfPointResidualSeparated p separation
      sourceRefines sourceResidual sourceThreshold
  have displacement :
      normSq (anchorNewtonCenter p source - source.anchor) <= radius ^ 2 := by
    have derivativeNormPositive :
        0 < normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) :=
      normSq_pos newton.derivativeNonzero
    have inverseBound :
        (normSq
          ((RFAP.ConstructiveGCD.derivative p).eval source.anchor))⁻¹ <=
            separation.margin⁻¹ :=
      RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
        separation.margin_pos newton.derivativeLower
    rw [RFAP.LocalExtraction.normSq_anchorNewtonCenter_sub_anchor
      newton.derivativeNonzero]
    calc
      normSq (p.eval source.anchor) *
            (normSq
              ((RFAP.ConstructiveGCD.derivative p).eval source.anchor))⁻¹ <=
          normSq (p.eval source.anchor) * separation.margin⁻¹ :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inverseBound
          (normSq_nonneg _)
      _ = normSq (p.eval source.anchor) / separation.margin := rfl
      _ <= radius ^ 2 := sourceDisplacementBudget
  have coordinateBounds :=
    RFAP.AffineWinding.coordinate_bounds_of_normSq_le radiusPositive.le
      displacement
  have centerRealLower : point.re - radius <=
      (anchorNewtonCenter p source).re := by
    calc
      point.re - radius = -radius + point.re := by ring1
      _ <= (anchorNewtonCenter p source - source.anchor).re + point.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct coordinateBounds.1
          point.re
      _ = (anchorNewtonCenter p source).re := by
        simp only [source, anchoredSquare_anchor, sub_re]
        ring1
  have centerRealUpper : (anchorNewtonCenter p source).re <=
      point.re + radius := by
    calc
      (anchorNewtonCenter p source).re =
          (anchorNewtonCenter p source - source.anchor).re + point.re := by
        simp only [source, anchoredSquare_anchor, sub_re]
        ring1
      _ <= radius + point.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.1 point.re
      _ = point.re + radius := by ring1
  have centerImagLower : point.im - radius <=
      (anchorNewtonCenter p source).im := by
    calc
      point.im - radius = -radius + point.im := by ring1
      _ <= (anchorNewtonCenter p source - source.anchor).im + point.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.2.1 point.im
      _ = (anchorNewtonCenter p source).im := by
        simp only [source, anchoredSquare_anchor, sub_im]
        ring1
  have centerImagUpper : (anchorNewtonCenter p source).im <=
      point.im + radius := by
    calc
      (anchorNewtonCenter p source).im =
          (anchorNewtonCenter p source - source.anchor).im + point.im := by
        simp only [source, anchoredSquare_anchor, sub_im]
        ring1
      _ <= radius + point.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          coordinateBounds.2.2.2 point.im
      _ = point.im + radius := by ring1
  have targetStrict :
      (RFAP.AffineWinding.centeredSquare
        (anchorNewtonCenter p source) radius radiusPositive.le).StrictInterior
          ambient := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ambient.xLower < (anchorNewtonCenter p source).re - radius
      exact (calc
        ambient.xLower < point.re - 2 * radius := by
          apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
            (c := 2 * radius)
          simpa only [show (point.re - 2 * radius) + 2 * radius = point.re by
            ring1] using leftMargin
        _ = (point.re - radius) - radius := by ring1
        _ <= (anchorNewtonCenter p source).re - radius :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct centerRealLower _)
    · change (anchorNewtonCenter p source).re + radius < ambient.xUpper
      exact (calc
        (anchorNewtonCenter p source).re + radius <=
            (point.re + radius) + radius :=
          RFAP.ConstructiveFraction.add_le_add_right_direct centerRealUpper _
        _ = point.re + 2 * radius := by ring1
        _ < ambient.xUpper := rightMargin)
    · change ambient.yLower < (anchorNewtonCenter p source).im - radius
      exact (calc
        ambient.yLower < point.im - 2 * radius := by
          apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
            (c := 2 * radius)
          simpa only [show (point.im - 2 * radius) + 2 * radius = point.im by
            ring1] using bottomMargin
        _ = (point.im - radius) - radius := by ring1
        _ <= (anchorNewtonCenter p source).im - radius :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct centerImagLower _)
    · change (anchorNewtonCenter p source).im + radius < ambient.yUpper
      exact (calc
        (anchorNewtonCenter p source).im + radius <=
            (point.im + radius) + radius :=
          RFAP.ConstructiveFraction.add_le_add_right_direct centerImagUpper _
        _ = point.im + 2 * radius := by ring1
        _ < ambient.yUpper := topMargin)
  exact
    { source := source
      sourceRefines := sourceRefines
      residual := sourceResidual
      threshold := sourceThreshold
      radius := radius
      radiusPositive := radiusPositive
      displacementBudget := sourceDisplacementBudget
      targetStrict := targetStrict
      taylorSmall := taylorSmall }

/-- The separated Newton point computed solely from the displayed source
box and the caller's explicit separation resource. -/
def newton (input : SeparatedRestartInput separation) :
    RFAP.LocalExtraction.SeparatedNewtonCenterCertificate
      p ambient input.source separation :=
  RFAP.LocalExtraction.computeNewtonCenterOfPointResidualSeparated p separation
    input.sourceRefines input.residual input.threshold

/-- The supplied displacement budget controls the computed Newton center. -/
theorem displacementSmall (input : SeparatedRestartInput separation) :
    normSq (anchorNewtonCenter p input.source - input.source.anchor) <=
      input.radius ^ 2 := by
  have derivativeNormPositive :
      0 < normSq
        ((RFAP.ConstructiveGCD.derivative p).eval input.source.anchor) :=
    normSq_pos input.newton.derivativeNonzero
  have inverseBound :
      (normSq
        ((RFAP.ConstructiveGCD.derivative p).eval input.source.anchor))⁻¹ <=
          separation.margin⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
      separation.margin_pos input.newton.derivativeLower
  rw [RFAP.LocalExtraction.normSq_anchorNewtonCenter_sub_anchor
    input.newton.derivativeNonzero]
  calc
    normSq (p.eval input.source.anchor) *
          (normSq
            ((RFAP.ConstructiveGCD.derivative p).eval
              input.source.anchor))⁻¹ <=
        normSq (p.eval input.source.anchor) * separation.margin⁻¹ :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inverseBound
        (normSq_nonneg _)
    _ = normSq (p.eval input.source.anchor) / separation.margin := rfl
    _ <= input.radius ^ 2 := input.displacementBudget

/-- The exact predictable target square of a direct separated restart. -/
def centeredBox (input : SeparatedRestartInput separation) : Box :=
  RFAP.AffineWinding.centeredSquare
    (anchorNewtonCenter p input.source) input.radius input.radiusPositive.le

theorem centeredBox_refines (input : SeparatedRestartInput separation) :
    input.centeredBox.Refines ambient :=
  input.targetStrict.refines

/-- The predictable restart square retains the strict margins supplied by
`ofAnchored`. -/
theorem centeredBox_strict (input : SeparatedRestartInput separation) :
    input.centeredBox.StrictInterior ambient :=
  input.targetStrict

@[simp] theorem centeredBox_diagonalSq
    (input : SeparatedRestartInput separation) :
    input.centeredBox.diagonalSq = 8 * input.radius ^ 2 :=
  RFAP.AffineWinding.centeredSquare_diagonalSq _ input.radiusPositive.le

/-- Restart directly on the predictable centered square, retaining an
explicit upper bound for the Newton linearization so that the resulting
boundary-clearance formula is known before any later owner is read. -/
def centeredStateWithMajorant
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : SeparatedRestartInput separation)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary input.centeredBox z ->
        normSq
          ((RFAP.NewtonWinding.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    WindingOneState p input.centeredBox := by
  let clearance :=
    RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper
  have windingFour :
      RFAP.Winding.quadrupledBoxWinding p input.centeredBox = 4 :=
    RFAP.NewtonWinding.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
  exact
    { box := input.centeredBox
      refinesAmbient := RFAP.Boxes.Box.refines_refl input.centeredBox
      proper := RFAP.AffineWinding.centeredSquare_proper _
        input.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

theorem centeredStateWithMajorant_clearance_bound
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : SeparatedRestartInput separation)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary input.centeredBox z ->
        normSq
          ((RFAP.NewtonWinding.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    (centeredStateWithMajorant degreeAtLeastTwo input
      linearizationMajorant linearizationMajorantPositive
      linearizationUpper).clearance.bound =
        RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
            input.radius ^ 2 /
          (4 * linearizationMajorant) := by
  unfold centeredStateWithMajorant
  exact
    RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant_bound
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper

/-- The ordinary finite shrinking program beginning at a direct separated
restart.  Squarefreeness and elimination are used only by the subsequent
shrinker, not to choose the restart radius. -/
def centeredTrackWithMajorant
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : SeparatedRestartInput separation)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary input.centeredBox z ->
        normSq
          ((RFAP.NewtonWinding.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    WindingOneTrack p input.centeredBox :=
  RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree elimination
    (centeredStateWithMajorant degreeAtLeastTwo input linearizationMajorant
      linearizationMajorantPositive linearizationUpper)

end SeparatedRestartInput

/-! ## Coefficient-computed anchored budgets -/

private def positiveMinimum (values : List Coordinate) : Coordinate :=
  values.foldr min 1

private theorem positiveMinimum_pos (values : List Coordinate)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact lt_min (positive head (by simp))
        (inductionHypothesis fun value member =>
          positive value (by simp [member]))

private theorem positiveMinimum_le_of_mem
    {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

private def anchoredTaylorCoefficient
    (p : GaussianPolynomial) (box : Box) : Coordinate :=
  2 * (RFAP.NewtonExtraction.extractionBandTaylorCoefficient *
    denseTaylorRemainderBound p box)

private theorem anchoredTaylorCoefficient_pos
    (p : GaussianPolynomial) (box : Box) :
    0 < anchoredTaylorCoefficient p box := by
  have twoPositive : (0 : Coordinate) < 2 := by decide
  have fourPositive : (0 : Coordinate) < 4 := by decide
  have ninePositive : (0 : Coordinate) < 9 := by decide
  have extractionPositive :
      0 < RFAP.NewtonExtraction.extractionBandTaylorCoefficient := by
    unfold RFAP.NewtonExtraction.extractionBandTaylorCoefficient
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct fourPositive ninePositive)
      ninePositive
  exact RFAP.ConstructiveFraction.mul_pos_direct twoPositive
    (RFAP.ConstructiveFraction.mul_pos_direct extractionPositive
      (denseTaylorRemainderBound_pos p box))

/-- Finite list of every positive scalar cap used for a rational point
strictly inside a winding box. -/
private def anchoredRadiusValues
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (cap : Coordinate) : List Coordinate :=
  [1,
    (point.re - current.box.xLower) / 6,
    (current.box.xUpper - point.re) / 6,
    (point.im - current.box.yLower) / 6,
    (current.box.yUpper - point.im) / 6,
    cap,
    derivativeThreshold squarefree current.box /
      (4 * denseLipschitzBound p current.box),
    derivativeMargin squarefree current.box /
      anchoredTaylorCoefficient p current.box]

/-- One positive rational radius below every geometric, Newton, Taylor, and
external cap for the displayed strict interior point. -/
def anchoredRadius
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (cap : Coordinate) : Coordinate :=
  positiveMinimum (anchoredRadiusValues squarefree current point cap)

theorem anchoredRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (strict : current.box.StrictContains point)
    {cap : Coordinate} (capPositive : 0 < cap) :
    0 < anchoredRadius squarefree current point cap := by
  apply positiveMinimum_pos
  intro value member
  simp [anchoredRadiusValues] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct strict.1) (by decide)
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct strict.2.1) (by decide)
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.1) (by decide)
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.2) (by decide)
  · exact capPositive
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (derivativeThreshold_pos squarefree current.box)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p current.box))
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (derivativeMargin_pos squarefree current.box)
      (anchoredTaylorCoefficient_pos p current.box)

/-- All scalar upper bounds exposed together for the later constructive
inequality proofs. -/
theorem anchoredRadius_bounds
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (cap : Coordinate) :
    let radius := anchoredRadius squarefree current point cap
    radius ≤ 1 ∧
      radius ≤ (point.re - current.box.xLower) / 6 ∧
      radius ≤ (current.box.xUpper - point.re) / 6 ∧
      radius ≤ (point.im - current.box.yLower) / 6 ∧
      radius ≤ (current.box.yUpper - point.im) / 6 ∧
      radius ≤ cap ∧
      radius ≤ derivativeThreshold squarefree current.box /
        (4 * denseLipschitzBound p current.box) ∧
      radius ≤ derivativeMargin squarefree current.box /
        anchoredTaylorCoefficient p current.box := by
  let values := anchoredRadiusValues squarefree current point cap
  have below (value : Coordinate) (member : value ∈ values) :
      positiveMinimum values ≤ value :=
    positiveMinimum_le_of_mem member
  exact
    ⟨below 1 (by simp [values, anchoredRadiusValues]),
      below ((point.re - current.box.xLower) / 6)
        (by simp [values, anchoredRadiusValues]),
      below ((current.box.xUpper - point.re) / 6)
        (by simp [values, anchoredRadiusValues]),
      below ((point.im - current.box.yLower) / 6)
        (by simp [values, anchoredRadiusValues]),
      below ((current.box.yUpper - point.im) / 6)
        (by simp [values, anchoredRadiusValues]),
      below cap (by simp [values, anchoredRadiusValues]),
      below (derivativeThreshold squarefree current.box /
          (4 * denseLipschitzBound p current.box))
        (by simp [values, anchoredRadiusValues]),
      below (derivativeMargin squarefree current.box /
          anchoredTaylorCoefficient p current.box)
        (by simp [values, anchoredRadiusValues])⟩

/-- Positive residual target simultaneously small enough for the anchored
source variation and the derivative-normalized Newton displacement. -/
def anchoredResidualTarget
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (cap : Coordinate) : Coordinate :=
  let radius := anchoredRadius squarefree current point cap
  min
    (denseLipschitzBound p current.box * (2 * radius ^ 2))
    (derivativeMargin squarefree current.box * radius ^ 2)

theorem anchoredResidualTarget_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (strict : current.box.StrictContains point)
    {cap : Coordinate} (capPositive : 0 < cap) :
    0 < anchoredResidualTarget squarefree current point cap := by
  let radius := anchoredRadius squarefree current point cap
  have radiusPositive : 0 < radius :=
    anchoredRadius_pos squarefree current point strict capPositive
  exact lt_min
    (RFAP.ConstructiveFraction.mul_pos_direct
      (denseLipschitzBound_pos p current.box)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2)))
    (RFAP.ConstructiveFraction.mul_pos_direct
      (derivativeMargin_pos squarefree current.box)
      (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2))

/-- The computed scalar radius satisfies all four margin inequalities and
both coefficient budgets, so an actual residual below the computed target
produces the complete anchored input. -/
def anchoredInputOfResidual
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (strict : current.box.StrictContains point)
    {cap : Coordinate} (capPositive : 0 < cap)
    (residual : normSq (p.eval point) <
      anchoredResidualTarget squarefree current point cap) :
    AnchoredInput squarefree current := by
  let radius := anchoredRadius squarefree current point cap
  have radiusPositive : 0 < radius :=
    anchoredRadius_pos squarefree current point strict capPositive
  have bounds := anchoredRadius_bounds squarefree current point cap
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct bounds.1
        radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have leftGapPositive : 0 < point.re - current.box.xLower :=
    RFAP.ConstructiveFraction.sub_pos_direct strict.1
  have rightGapPositive : 0 < current.box.xUpper - point.re :=
    RFAP.ConstructiveFraction.sub_pos_direct strict.2.1
  have bottomGapPositive : 0 < point.im - current.box.yLower :=
    RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.1
  have topGapPositive : 0 < current.box.yUpper - point.im :=
    RFAP.ConstructiveFraction.sub_pos_direct strict.2.2.2
  have sixPositive : (0 : Coordinate) < 6 := by decide
  have threePositive : (0 : Coordinate) < 3 := by decide
  have threeRadiusLtSix : 3 * radius < 6 * radius :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (by decide) radiusPositive
  have scaledGap {gap : Coordinate} (gapPositive : 0 < gap)
      (radiusLe : radius ≤ gap / 6) : 3 * radius < gap := by
    have radiusScaled : radius * 6 ≤ gap :=
      (RFAP.ConstructiveFraction.le_div_iff_pos sixPositive).1 radiusLe
    calc
      3 * radius < 6 * radius := threeRadiusLtSix
      _ = radius * 6 := by ring1
      _ ≤ gap := radiusScaled
  have leftThree := scaledGap leftGapPositive bounds.2.1
  have rightThree := scaledGap rightGapPositive bounds.2.2.1
  have bottomThree := scaledGap bottomGapPositive bounds.2.2.2.1
  have topThree := scaledGap topGapPositive bounds.2.2.2.2.1
  have leftMargin : current.box.xLower + 3 * radius < point.re := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct leftThree
        current.box.xLower
    calc
      current.box.xLower + 3 * radius =
          3 * radius + current.box.xLower := by ring1
      _ < (point.re - current.box.xLower) + current.box.xLower := shifted
      _ = point.re := by ring1
  have rightMargin : point.re + 3 * radius < current.box.xUpper := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct rightThree point.re
    calc
      point.re + 3 * radius = 3 * radius + point.re := by ring1
      _ < (current.box.xUpper - point.re) + point.re := shifted
      _ = current.box.xUpper := by ring1
  have bottomMargin : current.box.yLower + 3 * radius < point.im := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct bottomThree
        current.box.yLower
    calc
      current.box.yLower + 3 * radius =
          3 * radius + current.box.yLower := by ring1
      _ < (point.im - current.box.yLower) + current.box.yLower := shifted
      _ = point.im := by ring1
  have topMargin : point.im + 3 * radius < current.box.yUpper := by
    have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct topThree point.im
    calc
      point.im + 3 * radius = 3 * radius + point.im := by ring1
      _ < (current.box.yUpper - point.im) + point.im := shifted
      _ = current.box.yUpper := by ring1
  let lipschitz := denseLipschitzBound p current.box
  have lipschitzPositive : 0 < lipschitz :=
    denseLipschitzBound_pos p current.box
  have fourLipschitzPositive : 0 < 4 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have thresholdScaled : radius * (4 * lipschitz) ≤
      derivativeThreshold squarefree current.box :=
    (RFAP.ConstructiveFraction.le_div_iff_pos fourLipschitzPositive).1
      bounds.2.2.2.2.2.2.1
  have sourceThreshold : lipschitz * (2 * radius ^ 2) ≤
      derivativeThreshold squarefree current.box := by
    have twoLipschitzNonnegative : 0 ≤ 2 * lipschitz :=
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        lipschitzPositive).le
    calc
      lipschitz * (2 * radius ^ 2) =
          (2 * lipschitz) * radius ^ 2 := by ring1
      _ ≤ (2 * lipschitz) * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe twoLipschitzNonnegative
      _ ≤ (4 * lipschitz) * radius := by
        have coefficient : 2 * lipschitz ≤ 4 * lipschitz :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) lipschitzPositive.le
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          coefficient radiusPositive.le
      _ = radius * (4 * lipschitz) := by ring1
      _ ≤ derivativeThreshold squarefree current.box := thresholdScaled
  let taylorCoefficient := anchoredTaylorCoefficient p current.box
  have taylorPositive : 0 < taylorCoefficient :=
    anchoredTaylorCoefficient_pos p current.box
  have taylorScaled : radius * taylorCoefficient ≤
      derivativeMargin squarefree current.box :=
    (RFAP.ConstructiveFraction.le_div_iff_pos taylorPositive).1
      bounds.2.2.2.2.2.2.2
  have taylorSmall :
      2 * (RFAP.NewtonExtraction.extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p current.box * radius ^ 2) ≤
          derivativeMargin squarefree current.box := by
    calc
      2 * (RFAP.NewtonExtraction.extractionBandTaylorCoefficient *
          denseTaylorRemainderBound p current.box * radius ^ 2) =
          taylorCoefficient * radius ^ 2 := by
        dsimp only [taylorCoefficient, anchoredTaylorCoefficient]
        ring1
      _ ≤ taylorCoefficient * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe taylorPositive.le
      _ = radius * taylorCoefficient := by ring1
      _ ≤ derivativeMargin squarefree current.box := taylorScaled
  have residualSource : normSq (p.eval point) ≤
      lipschitz * (2 * radius ^ 2) :=
    residual.le.trans (min_le_left _ _)
  have residualDisplacement : normSq (p.eval point) /
      derivativeMargin squarefree current.box ≤ radius ^ 2 := by
    have residualMargin : normSq (p.eval point) ≤
        derivativeMargin squarefree current.box * radius ^ 2 :=
      residual.le.trans (min_le_right _ _)
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (derivativeMargin_pos squarefree current.box)).2
    calc
      normSq (p.eval point) ≤
          derivativeMargin squarefree current.box * radius ^ 2 :=
        residualMargin
      _ = radius ^ 2 * derivativeMargin squarefree current.box := by ring1
  exact
    { point := point
      radius := radius
      radiusPositive := radiusPositive
      leftMargin := leftMargin
      rightMargin := rightMargin
      bottomMargin := bottomMargin
      topMargin := topMargin
      residual := by simpa only [lipschitz] using residualSource
      threshold := by simpa only [lipschitz] using sourceThreshold
      displacementBudget := residualDisplacement
      taylorSmall := taylorSmall }

theorem anchoredRadius_le_cap
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (cap : Coordinate) :
    anchoredRadius squarefree current point cap ≤ cap :=
  (anchoredRadius_bounds squarefree current point cap).2.2.2.2.2.1

private theorem le_positiveMinimum
    {lower : Coordinate} (values : List Coordinate)
    (lowerOne : lower ≤ 1)
    (lowerValues : ∀ value ∈ values, lower ≤ value) :
    lower ≤ positiveMinimum values := by
  induction values with
  | nil => simpa only [positiveMinimum, List.foldr_nil] using lowerOne
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact le_min (lowerValues head (by simp))
        (inductionHypothesis fun value member =>
          lowerValues value (by simp [member]))

/-- If a requested cap is below the reference radius obtained with cap one,
then it is the exact selected anchored radius.  This lets an externally
computed dyadic scale reuse the existing Newton-band constructor without
duplicating any geometric or Taylor proof. -/
theorem anchoredRadius_eq_cap_of_le_reference
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) {cap : Coordinate}
    (capLeReference :
      cap ≤ anchoredRadius squarefree current point 1) :
    anchoredRadius squarefree current point cap = cap := by
  apply le_antisymm
  · exact anchoredRadius_le_cap squarefree current point cap
  · have bounds := anchoredRadius_bounds squarefree current point 1
    change cap ≤ positiveMinimum
      (anchoredRadiusValues squarefree current point cap)
    apply le_positiveMinimum
    · exact capLeReference.trans bounds.1
    · intro value member
      simp [anchoredRadiusValues] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact capLeReference.trans bounds.1
      · exact capLeReference.trans bounds.2.1
      · exact capLeReference.trans bounds.2.2.1
      · exact capLeReference.trans bounds.2.2.2.1
      · exact capLeReference.trans bounds.2.2.2.2.1
      · exact le_rfl
      · exact capLeReference.trans bounds.2.2.2.2.2.2.1
      · exact capLeReference.trans bounds.2.2.2.2.2.2.2

/-! ## Point-independent interior and Newton budgets -/

/-- Finite radius caps independent of the eventual displayed sample.  The
boundary-clearance strip supplies all four geometric margins at once. -/
private def uniformAnchoredRadiusValues
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (cap : Coordinate) : List Coordinate :=
  [1,
    current.clearance.residualInteriorRadius / 6,
    cap,
    derivativeThreshold squarefree current.box /
      (4 * denseLipschitzBound p current.box),
    derivativeMargin squarefree current.box /
      anchoredTaylorCoefficient p current.box]

/-- One positive radius valid for every sufficiently small-residual rational
point contained in the winding box. -/
def uniformAnchoredRadius
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (cap : Coordinate) : Coordinate :=
  positiveMinimum (uniformAnchoredRadiusValues squarefree current cap)

theorem uniformAnchoredRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    {cap : Coordinate} (capPositive : 0 < cap) :
    0 < uniformAnchoredRadius squarefree current cap := by
  apply positiveMinimum_pos
  intro value member
  simp [uniformAnchoredRadiusValues] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · decide
  · exact RFAP.ConstructiveFraction.div_pos_direct
      current.clearance.residualInteriorRadius_pos (by decide)
  · exact capPositive
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (derivativeThreshold_pos squarefree current.box)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p current.box))
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (derivativeMargin_pos squarefree current.box)
      (anchoredTaylorCoefficient_pos p current.box)

theorem uniformAnchoredRadius_bounds
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (cap : Coordinate) :
    let radius := uniformAnchoredRadius squarefree current cap
    radius ≤ 1 ∧
      radius ≤ current.clearance.residualInteriorRadius / 6 ∧
      radius ≤ cap ∧
      radius ≤ derivativeThreshold squarefree current.box /
        (4 * denseLipschitzBound p current.box) ∧
      radius ≤ derivativeMargin squarefree current.box /
        anchoredTaylorCoefficient p current.box := by
  let values := uniformAnchoredRadiusValues squarefree current cap
  have below (value : Coordinate) (member : value ∈ values) :
      positiveMinimum values ≤ value := positiveMinimum_le_of_mem member
  exact
    ⟨below 1 (by simp [values, uniformAnchoredRadiusValues]),
      below (current.clearance.residualInteriorRadius / 6)
        (by simp [values, uniformAnchoredRadiusValues]),
      below cap (by simp [values, uniformAnchoredRadiusValues]),
      below (derivativeThreshold squarefree current.box /
          (4 * denseLipschitzBound p current.box))
        (by simp [values, uniformAnchoredRadiusValues]),
      below (derivativeMargin squarefree current.box /
          anchoredTaylorCoefficient p current.box)
        (by simp [values, uniformAnchoredRadiusValues])⟩

/-- If an external cap is below the point-independent radius computed with
cap one, then that cap is exactly the uniform anchored radius.  This is the
uniform counterpart of `anchoredRadius_eq_cap_of_le_reference` and makes a
later localization radius predictable before its rational sample is read. -/
theorem uniformAnchoredRadius_eq_cap_of_le_reference
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient) {cap : Coordinate}
    (capLeReference :
      cap ≤ uniformAnchoredRadius squarefree current 1) :
    uniformAnchoredRadius squarefree current cap = cap := by
  apply le_antisymm
  · exact (uniformAnchoredRadius_bounds squarefree current cap).2.2.1
  · have bounds := uniformAnchoredRadius_bounds squarefree current 1
    change cap ≤ positiveMinimum
      (uniformAnchoredRadiusValues squarefree current cap)
    apply le_positiveMinimum
    · exact capLeReference.trans bounds.1
    · intro value member
      simp [uniformAnchoredRadiusValues] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact capLeReference.trans bounds.1
      · exact capLeReference.trans bounds.2.1
      · exact le_rfl
      · exact capLeReference.trans bounds.2.2.2.1
      · exact capLeReference.trans bounds.2.2.2.2

/-- Point-independent residual target: one quarter of the boundary clearance
ensures a uniform interior strip, while the other two terms are the ordinary
source-variation and Newton-displacement budgets at the uniform radius. -/
def uniformAnchoredResidualTarget
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (cap : Coordinate) : Coordinate :=
  let radius := uniformAnchoredRadius squarefree current cap
  min (current.clearance.bound / 4)
    (min
      (denseLipschitzBound p current.box * (2 * radius ^ 2))
      (derivativeMargin squarefree current.box * radius ^ 2))

theorem uniformAnchoredResidualTarget_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    {cap : Coordinate} (capPositive : 0 < cap) :
    0 < uniformAnchoredResidualTarget squarefree current cap := by
  let radius := uniformAnchoredRadius squarefree current cap
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      uniformAnchoredRadius_pos squarefree current capPositive
  exact lt_min
    (RFAP.ConstructiveFraction.div_pos_direct current.clearance.positive
      (by decide))
    (lt_min
      (RFAP.ConstructiveFraction.mul_pos_direct
        (denseLipschitzBound_pos p current.box)
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2)))
      (RFAP.ConstructiveFraction.mul_pos_direct
        (derivativeMargin_pos squarefree current.box)
        (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2)))

private theorem div_six_mono {left right : Coordinate}
    (order : left ≤ right) : left / 6 ≤ right / 6 := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct order
    (RFAP.ConstructiveFraction.inv_pos_direct
      (show (0 : Coordinate) < 6 by decide)).le

/-- The uniform radius is below the point-specific anchored radius for every
contained rational point meeting the clearance-quarter residual test. -/
theorem uniformAnchoredRadius_le_anchoredRadius
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (contains : current.box.Contains point)
    (cap : Coordinate)
    (residualSmall : normSq (p.eval point) < current.clearance.bound / 4) :
    uniformAnchoredRadius squarefree current cap ≤
      anchoredRadius squarefree current point cap := by
  let uniform := uniformAnchoredRadius squarefree current cap
  let interior := current.clearance.residualInteriorRadius
  have bounds := uniformAnchoredRadius_bounds squarefree current cap
  have margins := current.clearance.residualInteriorMargins contains
    residualSmall
  have leftGap : interior ≤ point.re - current.box.xLower := by
    calc
      interior = (current.box.xLower + interior) - current.box.xLower := by
        ring1
      _ ≤ point.re - current.box.xLower :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct margins.1.le current.box.xLower
  have rightGap : interior ≤ current.box.xUpper - point.re := by
    calc
      interior = (point.re + interior) - point.re := by ring1
      _ ≤ current.box.xUpper - point.re :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct margins.2.1.le point.re
  have bottomGap : interior ≤ point.im - current.box.yLower := by
    calc
      interior = (current.box.yLower + interior) - current.box.yLower := by
        ring1
      _ ≤ point.im - current.box.yLower :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct margins.2.2.1.le current.box.yLower
  have topGap : interior ≤ current.box.yUpper - point.im := by
    calc
      interior = (point.im + interior) - point.im := by ring1
      _ ≤ current.box.yUpper - point.im :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct margins.2.2.2.le point.im
  apply le_positiveMinimum (anchoredRadiusValues squarefree current point cap)
    bounds.1
  intro value member
  simp [anchoredRadiusValues] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bounds.1
  · exact bounds.2.1.trans (div_six_mono leftGap)
  · exact bounds.2.1.trans (div_six_mono rightGap)
  · exact bounds.2.1.trans (div_six_mono bottomGap)
  · exact bounds.2.1.trans (div_six_mono topGap)
  · exact bounds.2.2.1
  · exact bounds.2.2.2.1
  · exact bounds.2.2.2.2

/-- A cap below the point-independent reference radius is also the exact
point-specific radius at every contained sample satisfying the uniform
clearance-quarter test. -/
theorem anchoredRadius_eq_cap_of_le_uniformReference
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (contains : current.box.Contains point)
    {cap : Coordinate}
    (capLeReference :
      cap ≤ uniformAnchoredRadius squarefree current 1)
    (residualSmall :
      normSq (p.eval point) < current.clearance.bound / 4) :
    anchoredRadius squarefree current point cap = cap := by
  apply anchoredRadius_eq_cap_of_le_reference
  exact capLeReference.trans
    (uniformAnchoredRadius_le_anchoredRadius squarefree current point contains
      1 residualSmall)

/-- A point-independent residual request is sufficient for the existing
point-specific anchored Newton constructor.  The conclusion concerns only
the supplied rational point and does not assert that it is a root. -/
theorem uniform_residual_strict_and_anchored
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (contains : current.box.Contains point)
    {cap : Coordinate} (capPositive : 0 < cap)
    (residual : normSq (p.eval point) <
      uniformAnchoredResidualTarget squarefree current cap) :
    current.box.StrictContains point ∧
      normSq (p.eval point) <
        anchoredResidualTarget squarefree current point cap := by
  let uniform := uniformAnchoredRadius squarefree current cap
  let anchored := anchoredRadius squarefree current point cap
  have residualQuarter : normSq (p.eval point) <
      current.clearance.bound / 4 :=
    residual.trans_le (min_le_left _ _)
  have quarterLtBound : current.clearance.bound / 4 <
      current.clearance.bound := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      current.clearance.bound * (4 : Coordinate)⁻¹ <
          current.clearance.bound * 1 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          current.clearance.positive (by decide)
      _ = current.clearance.bound := by ring1
  have strict := current.clearance.strictContains_of_residual_lt contains
    (residualQuarter.trans quarterLtBound)
  have radiusOrder : uniform ≤ anchored := by
    simpa only [uniform, anchored] using
      uniformAnchoredRadius_le_anchoredRadius squarefree current point contains
        cap residualQuarter
  have radiusSquareOrder : uniform ^ 2 ≤ anchored ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (uniformAnchoredRadius_pos squarefree current capPositive).le radiusOrder 2
  have sourceOrder :
      denseLipschitzBound p current.box * (2 * uniform ^ 2) ≤
        denseLipschitzBound p current.box * (2 * anchored ^ 2) := by
    have doubled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusSquareOrder (show (0 : Coordinate) ≤ 2 by decide)
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct doubled
      (denseLipschitzBound_pos p current.box).le
  have displacementOrder :
      derivativeMargin squarefree current.box * uniform ^ 2 ≤
        derivativeMargin squarefree current.box * anchored ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusSquareOrder (derivativeMargin_pos squarefree current.box).le
  have residualUniform : normSq (p.eval point) <
      min
        (denseLipschitzBound p current.box * (2 * uniform ^ 2))
        (derivativeMargin squarefree current.box * uniform ^ 2) := by
    exact residual.trans_le (min_le_right _ _)
  have uniformLeAnchored :
      min
          (denseLipschitzBound p current.box * (2 * uniform ^ 2))
          (derivativeMargin squarefree current.box * uniform ^ 2) ≤
        min
          (denseLipschitzBound p current.box * (2 * anchored ^ 2))
          (derivativeMargin squarefree current.box * anchored ^ 2) :=
    min_le_min sourceOrder displacementOrder
  exact ⟨strict, by
    simpa only [anchoredResidualTarget, uniform, anchored] using
      residualUniform.trans_le uniformLeAnchored⟩

/-- Fully automatic residual seed once the displayed rational point is
strictly inside and its actual residual meets the computed target. -/
def seedOfResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (strict : current.box.StrictContains point)
    {cap : Coordinate} (capPositive : 0 < cap)
    (residual : normSq (p.eval point) <
      anchoredResidualTarget squarefree current point cap) :
    Seed squarefree elimination current :=
  (anchoredInputOfResidual squarefree current point strict capPositive
    residual).seed elimination

theorem seedOfResidual_radius_le_cap
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian) (strict : current.box.StrictContains point)
    {cap : Coordinate} (capPositive : 0 < cap)
    (residual : normSq (p.eval point) <
      anchoredResidualTarget squarefree current point cap) :
    (seedOfResidual squarefree elimination current point strict capPositive
      residual).radius ≤ cap := by
  exact anchoredRadius_le_cap squarefree current point cap

namespace Seed

variable {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
variable {squarefree : SquarefreeCertificate p}
variable {elimination : AxisEliminationCertificate p degreeBound}
variable {current : ProtectedAmbient p ambient}

/-- The Newton point is computed entirely from the displayed source anchor. -/
def newton (seed : Seed squarefree elimination current) :
    NewtonCenterCertificate p current.box seed.source squarefree :=
  computeNewtonCenterOfResidual p squarefree seed.sourceRefines seed.residual
    seed.threshold

/-- The four eliminant-safe rational coordinates around the computed Newton
point. -/
def band (seed : Seed squarefree elimination current) :
    NewtonBandBox (anchorNewtonCenter p seed.source) seed.radius :=
  selectedBand elimination (anchorNewtonCenter p seed.source) seed.radius
    seed.radiusPositive

theorem displacementSmall (seed : Seed squarefree elimination current) :
    normSq (anchorNewtonCenter p seed.source - seed.source.anchor) ≤
      seed.radius ^ 2 :=
  (newton_displacementResidualMargin seed.newton).trans seed.displacementBudget

theorem band_refines_current (seed : Seed squarefree elimination current) :
    seed.band.box.Refines current.box :=
  seed.bandStrict.refines

theorem band_refines_ambient (seed : Seed squarefree elimination current) :
    seed.band.box.Refines ambient :=
  seed.band_refines_current.trans current.refinesAmbient

/-! ## Predictable centered restarts -/

/-- The centered radius-`r` square contained in the eliminant-safe band of a
residual seed.  Unlike the selected band, all of its geometric data are exact
expressions in the seed radius. -/
def centeredBox (seed : Seed squarefree elimination current) : Box :=
  RFAP.AffineWinding.centeredSquare
    (anchorNewtonCenter p seed.source) seed.radius seed.radiusPositive.le

theorem centeredBox_refines_band
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.Refines seed.band.box := by
  exact ⟨seed.band.left_upper, seed.band.right_lower,
    seed.band.bottom_upper, seed.band.top_lower⟩

theorem centeredBox_refines_current
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.Refines current.box :=
  seed.centeredBox_refines_band.trans seed.band_refines_current

@[simp] theorem centeredBox_diagonalSq
    (seed : Seed squarefree elimination current) :
    seed.centeredBox.diagonalSq = 8 * seed.radius ^ 2 := by
  exact RFAP.AffineWinding.centeredSquare_diagonalSq _ seed.radiusPositive.le

/-- Re-read the seed's displayed source through any derivative-separation
certificate whose residual threshold admits that source. -/
def separatedNewton
    (seed : Seed squarefree elimination current)
    (separation : RFAP.DerivativeSeparation.Certificate p current.box)
    (sourceThreshold :
      RFAP.LocalExtraction.anchorResidualBound p current.box seed.source ≤
        separation.threshold) :
    RFAP.LocalExtraction.SeparatedNewtonCenterCertificate
      p current.box seed.source separation :=
  RFAP.LocalExtraction.computeNewtonCenterOfResidualSeparated p separation
    seed.sourceRefines seed.residual sourceThreshold

/-- Restart a residual seed on its exact centered square, using an explicit
derivative separation and any displayed upper bound for the Newton
linearization.  The square is used as its own finite ambient, so its boundary
clearance supplies all four ambient-line certificates without a global-line
choice. -/
def separatedCenteredStateWithMajorant
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (separation : RFAP.DerivativeSeparation.Certificate p current.box)
    (sourceThreshold :
      RFAP.LocalExtraction.anchorResidualBound p current.box seed.source ≤
        separation.threshold)
    (displacementSmall :
      normSq (anchorNewtonCenter p seed.source - seed.source.anchor) ≤
        seed.radius ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p current.box * seed.radius ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary seed.centeredBox z →
        normSq ((RFAP.NewtonWinding.newtonLinearization p seed.source).eval z) ≤
          linearizationMajorant) :
    WindingOneState p seed.centeredBox := by
  let newton := seed.separatedNewton separation sourceThreshold
  let clearance :=
    RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo newton seed.sourceRefines seed.radiusPositive
      seed.centeredBox_refines_current displacementSmall taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper
  have windingFour :
      RFAP.Winding.quadrupledBoxWinding p seed.centeredBox = 4 :=
    RFAP.NewtonWinding.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
      degreeAtLeastTwo newton seed.sourceRefines seed.radiusPositive
      seed.centeredBox_refines_current displacementSmall taylorSmall
  exact
    { box := seed.centeredBox
      refinesAmbient := RFAP.Boxes.Box.refines_refl seed.centeredBox
      proper := RFAP.AffineWinding.centeredSquare_proper _ seed.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

theorem separatedCenteredStateWithMajorant_clearance_bound
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (separation : RFAP.DerivativeSeparation.Certificate p current.box)
    (sourceThreshold :
      RFAP.LocalExtraction.anchorResidualBound p current.box seed.source ≤
        separation.threshold)
    (displacementSmall :
      normSq (anchorNewtonCenter p seed.source - seed.source.anchor) ≤
        seed.radius ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p current.box * seed.radius ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary seed.centeredBox z →
        normSq ((RFAP.NewtonWinding.newtonLinearization p seed.source).eval z) ≤
          linearizationMajorant) :
    (separatedCenteredStateWithMajorant degreeAtLeastTwo seed separation
      sourceThreshold displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper).clearance.bound =
        RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
            seed.radius ^ 2 /
          (4 * linearizationMajorant) := by
  unfold separatedCenteredStateWithMajorant
  exact
    RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant_bound
      degreeAtLeastTwo (seed.separatedNewton separation sourceThreshold)
      seed.sourceRefines seed.radiusPositive seed.centeredBox_refines_current
      displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper

/-- The centered restart retains the ordinary total finite shrinking
refiner, now beginning with a predictable box and clearance formula. -/
def separatedCenteredTrackWithMajorant
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (separation : RFAP.DerivativeSeparation.Certificate p current.box)
    (sourceThreshold :
      RFAP.LocalExtraction.anchorResidualBound p current.box seed.source ≤
        separation.threshold)
    (displacementSmall :
      normSq (anchorNewtonCenter p seed.source - seed.source.anchor) ≤
        seed.radius ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p current.box * seed.radius ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary seed.centeredBox z →
        normSq ((RFAP.NewtonWinding.newtonLinearization p seed.source).eval z) ≤
          linearizationMajorant) :
    WindingOneTrack p seed.centeredBox :=
  RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree elimination
    (separatedCenteredStateWithMajorant degreeAtLeastTwo seed separation
      sourceThreshold displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper)

/-- The rational residual seed produces an ordinary winding-one state, with
all boundary and ambient-line clearances needed by the standard refiner. -/
def state
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    WindingOneState p ambient := by
  let center := anchorNewtonCenter p seed.source
  let band := seed.band
  have bandRefinesCurrent : band.box.Refines current.box :=
    seed.band_refines_current
  let leftLine := selectedBandLeftClearance elimination current.box center
    seed.radiusPositive
  let rightLine := selectedBandRightClearance elimination current.box center
    seed.radiusPositive
  let bottomLine := selectedBandBottomClearance elimination current.box center
    seed.radiusPositive
  let topLine := selectedBandTopClearance elimination current.box center
    seed.radiusPositive
  let ambientLeftLine := selectedBandLeftClearance elimination ambient center
    seed.radiusPositive
  let ambientRightLine := selectedBandRightClearance elimination ambient center
    seed.radiusPositive
  let ambientBottomLine := selectedBandBottomClearance elimination ambient
    center seed.radiusPositive
  let ambientTopLine := selectedBandTopClearance elimination ambient center
    seed.radiusPositive
  let clearance : RFAP.BoxClearance.BoundaryClearance p band.box :=
    boundaryOfLines
    (VerticalLineClearance.restrict leftLine bandRefinesCurrent)
    (VerticalLineClearance.restrict rightLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict bottomLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict topLine bandRefinesCurrent)
  have windingFour :
      RFAP.Winding.quadrupledBoxWinding p band.box = 4 :=
    quadrupledBoxWinding_eq_four_of_newtonBand degreeAtLeastTwo seed.newton
      seed.sourceRefines seed.radiusPositive band bandRefinesCurrent
      seed.displacementSmall seed.taylorSmall
  exact
    { box := band.box
      refinesAmbient := bandRefinesCurrent.trans current.refinesAmbient
      proper := band.proper seed.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := ambientLeftLine
      ambientRightClearance := ambientRightLine
      ambientBottomClearance := ambientBottomLine
      ambientTopClearance := ambientTopLine }

theorem state_strict_current
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    (seed.state degreeAtLeastTwo).box.StrictInterior current.box := by
  change (selectedBand elimination (anchorNewtonCenter p seed.source)
    seed.radius seed.radiusPositive).box.StrictInterior current.box
  exact seed.bandStrict

/-- The standard finite refiner turns the residual-built state into a total
shrinking track. -/
def track
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    WindingOneTrack p ambient :=
  RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree
    elimination (seed.state degreeAtLeastTwo)

/-! ## Location of the displayed rational anchor -/

theorem center_sub_anchor_coordinate_bounds
    (seed : Seed squarefree elimination current) :
    -seed.radius ≤
        (anchorNewtonCenter p seed.source - seed.source.anchor).re ∧
      (anchorNewtonCenter p seed.source - seed.source.anchor).re ≤
        seed.radius ∧
      -seed.radius ≤
        (anchorNewtonCenter p seed.source - seed.source.anchor).im ∧
      (anchorNewtonCenter p seed.source - seed.source.anchor).im ≤
        seed.radius :=
  RFAP.AffineWinding.coordinate_bounds_of_normSq_le
    seed.radiusPositive.le seed.displacementSmall

/-- Every side of the selected band stays within three radii of the original
displayed rational sample. -/
theorem anchor_band_coordinate_bounds
    (seed : Seed squarefree elimination current) :
    seed.source.anchor.re - 3 * seed.radius ≤ seed.band.box.xLower ∧
      seed.band.box.xUpper ≤ seed.source.anchor.re + 3 * seed.radius ∧
      seed.source.anchor.im - 3 * seed.radius ≤ seed.band.box.yLower ∧
      seed.band.box.yUpper ≤ seed.source.anchor.im + 3 * seed.radius := by
  have centerBounds := seed.center_sub_anchor_coordinate_bounds
  have centerRealLower : seed.source.anchor.re - seed.radius ≤
      (anchorNewtonCenter p seed.source).re := by
    calc
      seed.source.anchor.re - seed.radius =
          -seed.radius + seed.source.anchor.re := by ring1
      _ ≤ (anchorNewtonCenter p seed.source - seed.source.anchor).re +
          seed.source.anchor.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct centerBounds.1
          seed.source.anchor.re
      _ = (anchorNewtonCenter p seed.source).re := by
        simp only [sub_re]
        ring1
  have centerRealUpper : (anchorNewtonCenter p seed.source).re ≤
      seed.source.anchor.re + seed.radius := by
    calc
      (anchorNewtonCenter p seed.source).re =
          (anchorNewtonCenter p seed.source - seed.source.anchor).re +
            seed.source.anchor.re := by
        simp only [sub_re]
        ring1
      _ ≤ seed.radius + seed.source.anchor.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct centerBounds.2.1
          seed.source.anchor.re
      _ = seed.source.anchor.re + seed.radius := by ring1
  have centerImagLower : seed.source.anchor.im - seed.radius ≤
      (anchorNewtonCenter p seed.source).im := by
    calc
      seed.source.anchor.im - seed.radius =
          -seed.radius + seed.source.anchor.im := by ring1
      _ ≤ (anchorNewtonCenter p seed.source - seed.source.anchor).im +
          seed.source.anchor.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct centerBounds.2.2.1
          seed.source.anchor.im
      _ = (anchorNewtonCenter p seed.source).im := by
        simp only [sub_im]
        ring1
  have centerImagUpper : (anchorNewtonCenter p seed.source).im ≤
      seed.source.anchor.im + seed.radius := by
    calc
      (anchorNewtonCenter p seed.source).im =
          (anchorNewtonCenter p seed.source - seed.source.anchor).im +
            seed.source.anchor.im := by
        simp only [sub_im]
        ring1
      _ ≤ seed.radius + seed.source.anchor.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct centerBounds.2.2.2
          seed.source.anchor.im
      _ = seed.source.anchor.im + seed.radius := by ring1
  exact
    ⟨(by
        calc
          seed.source.anchor.re - 3 * seed.radius =
              (seed.source.anchor.re - seed.radius) - 2 * seed.radius := by
            ring1
          _ ≤ (anchorNewtonCenter p seed.source).re - 2 * seed.radius :=
            RFAP.ConstructiveFraction.sub_le_sub_right_direct centerRealLower _
          _ ≤ seed.band.box.xLower := seed.band.left_lower),
      (by
        calc
          seed.band.box.xUpper ≤
              (anchorNewtonCenter p seed.source).re + 2 * seed.radius :=
            seed.band.right_upper
          _ ≤ (seed.source.anchor.re + seed.radius) + 2 * seed.radius :=
            RFAP.ConstructiveFraction.add_le_add_right_direct centerRealUpper _
          _ = seed.source.anchor.re + 3 * seed.radius := by ring1),
      (by
        calc
          seed.source.anchor.im - 3 * seed.radius =
              (seed.source.anchor.im - seed.radius) - 2 * seed.radius := by
            ring1
          _ ≤ (anchorNewtonCenter p seed.source).im - 2 * seed.radius :=
            RFAP.ConstructiveFraction.sub_le_sub_right_direct centerImagLower _
          _ ≤ seed.band.box.yLower := seed.band.bottom_lower),
      (by
        calc
          seed.band.box.yUpper ≤
              (anchorNewtonCenter p seed.source).im + 2 * seed.radius :=
            seed.band.top_upper
          _ ≤ (seed.source.anchor.im + seed.radius) + 2 * seed.radius :=
            RFAP.ConstructiveFraction.add_le_add_right_direct centerImagUpper _
          _ = seed.source.anchor.im + 3 * seed.radius := by ring1)⟩

end Seed

end RFAP.ResidualWinding
