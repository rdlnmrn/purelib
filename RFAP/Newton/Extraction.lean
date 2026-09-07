import mathlib.Tactic.QuotientFreeRing
import RFAP.Newton.Raw
import RFAP.Newton.Winding
import RFAP.Geometry.ProtectedBoundary

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace RFAP.NewtonExtraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev RawWindingState := RFAP.RawSubdivision.RawWindingState
abbrev NewtonCenterCertificate :=
  RFAP.LocalExtraction.NewtonCenterCertificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds
open RFAP.LocalExtraction
open RFAP.RawSubdivision
open RFAP.AffineWinding
open RFAP.NewtonWinding
open RFAP.ProtectedBoundary

/-- Factored coefficient in the Taylor smallness request. -/
def extractionTaylorScale : Coordinate := (8 : Coordinate) * 9 * 9

/-- The unfactored Taylor coefficient used by a radius-two Newton band. -/
def extractionBandTaylorCoefficient : Coordinate := (4 : Coordinate) * 9 * 9

private theorem extractionTaylorScale_pos : 0 < extractionTaylorScale := by
  unfold extractionTaylorScale
  have eightPositive := RFAP.ConstructiveFraction.natCast_pos_direct
    (n := 8) (by decide)
  have ninePositive := RFAP.ConstructiveFraction.natCast_pos_direct
    (n := 9) (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct eightPositive ninePositive)
    ninePositive

/-- Radius below the protected strip, the unit scale, and the finite Taylor
dominance scale. -/
def baseExtractionRadius
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient) : Coordinate :=
  min ((1 / 2 : Coordinate) *
      protectedBoundaryRadius p ambient clearance)
    (min 1 (derivativeMargin squarefree ambient /
      (extractionTaylorScale * denseTaylorRemainderBound p ambient)))

theorem baseExtractionRadius_pos
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) :
    0 < baseExtractionRadius squarefree ambient clearance := by
  have onePositive : (0 : Coordinate) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
  have denominatorPositive := RFAP.ConstructiveFraction.mul_pos_direct
    extractionTaylorScale_pos
    (denseTaylorRemainderBound_pos p ambient)
  exact lt_min
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (protectedBoundaryRadius_pos p clearance proper))
    (lt_min onePositive
      (RFAP.ConstructiveFraction.div_pos_direct
        (derivativeMargin_pos squarefree ambient) denominatorPositive))

/-- The requested radius also enforces the final diagonal request. -/
def extractionRadius
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) : Coordinate :=
  min (baseExtractionRadius squarefree ambient clearance)
    ((1 / 8 : Coordinate) * epsilon)

theorem extractionRadius_pos
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    0 < extractionRadius squarefree ambient clearance epsilon := by
  exact lt_min (baseExtractionRadius_pos squarefree clearance proper)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) epsilonPositive)

theorem extractionRadius_le_protected
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    extractionRadius squarefree ambient clearance epsilon ≤
      protectedBoundaryRadius p ambient clearance :=
  have halfBound : extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 2 : Coordinate) *
        protectedBoundaryRadius p ambient clearance :=
    (min_le_left _ _).trans (min_le_left _ _)
  calc
    extractionRadius squarefree ambient clearance epsilon ≤
        (1 / 2 : Coordinate) *
          protectedBoundaryRadius p ambient clearance := halfBound
    _ ≤ 1 * protectedBoundaryRadius p ambient clearance :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Coordinate) ≤ 1 by decide)
        (protectedBoundaryRadius_nonneg p ambient clearance)
    _ = protectedBoundaryRadius p ambient clearance := by
      exact one_mul _

theorem extractionRadius_twice_le_protected
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    2 * extractionRadius squarefree ambient clearance epsilon ≤
      protectedBoundaryRadius p ambient clearance := by
  have halfBound : extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 2 : Coordinate) *
        protectedBoundaryRadius p ambient clearance :=
    (min_le_left _ _).trans (min_le_left _ _)
  have twoNonnegative : (0 : Coordinate) ≤ 2 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 2) (by decide)).le
  calc
    2 * extractionRadius squarefree ambient clearance epsilon ≤
        2 * ((1 / 2 : Coordinate) *
          protectedBoundaryRadius p ambient clearance) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct halfBound
        twoNonnegative
    _ = protectedBoundaryRadius p ambient clearance := by
      have twoHalf : (2 : Coordinate) * (1 / 2) = 1 := by decide
      calc
        2 * ((1 / 2 : Coordinate) *
            protectedBoundaryRadius p ambient clearance) =
            (2 * (1 / 2 : Coordinate)) *
              protectedBoundaryRadius p ambient clearance :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
        _ = 1 * protectedBoundaryRadius p ambient clearance := by
          rw [twoHalf]
        _ = protectedBoundaryRadius p ambient clearance := one_mul _

theorem extractionRadius_le_one
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    extractionRadius squarefree ambient clearance epsilon ≤ 1 :=
  (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem extractionRadius_le_eighth
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 8 : Coordinate) * epsilon :=
  min_le_right _ _

theorem extractionRadius_taylor
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    let r := extractionRadius squarefree ambient clearance epsilon
    2 * (extractionBandTaylorCoefficient *
      denseTaylorRemainderBound p ambient * r ^ 2) ≤
      derivativeMargin squarefree ambient := by
  let r := extractionRadius squarefree ambient clearance epsilon
  let eta := derivativeMargin squarefree ambient
  let taylor := denseTaylorRemainderBound p ambient
  have radiusPositive : 0 < r :=
    extractionRadius_pos squarefree clearance proper epsilonPositive
  have radiusLeOne : r ≤ 1 :=
    extractionRadius_le_one squarefree ambient clearance epsilon
  have radiusRatio : r ≤ eta / (extractionTaylorScale * taylor) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have denominatorPositive : 0 < extractionTaylorScale * taylor :=
    RFAP.ConstructiveFraction.mul_pos_direct extractionTaylorScale_pos
      (denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (extractionTaylorScale * taylor) ≤ eta :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = r := by ring1
  have scaledSquare : extractionTaylorScale * taylor * r ^ 2 ≤
      extractionTaylorScale * taylor * r :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLeRadius
      denominatorPositive.le
  calc
    2 * (extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p ambient * r ^ 2) =
        extractionTaylorScale * taylor * r ^ 2 := by
      dsimp only [extractionBandTaylorCoefficient, extractionTaylorScale,
        taylor]
      ring1
    _ ≤ extractionTaylorScale * taylor * r := scaledSquare
    _ = r * (extractionTaylorScale * taylor) := by ring1
    _ ≤ eta := ratioScaled

/-- Squared-diagonal threshold sufficient for the protected strip, derivative
separation, and Newton displacement. -/
def sourceDiagonalThreshold
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) : Coordinate :=
  let rho := protectedBoundaryRadius p ambient clearance
  let r := extractionRadius squarefree ambient clearance epsilon
  let lipschitz := denseLipschitzBound p ambient
  min (rho ^ 2)
    (min (derivativeThreshold squarefree ambient / lipschitz)
      (derivativeMargin squarefree ambient * r ^ 2 / lipschitz))

theorem sourceDiagonalThreshold_pos
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    0 < sourceDiagonalThreshold squarefree ambient clearance epsilon := by
  have rhoPositive := protectedBoundaryRadius_pos p clearance proper
  have radiusPositive := extractionRadius_pos squarefree clearance proper
    epsilonPositive
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  exact lt_min
    (RFAP.ConstructiveFraction.pow_pos_direct rhoPositive 2)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct
        (derivativeThreshold_pos squarefree ambient) lipschitzPositive)
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.mul_pos_direct
          (derivativeMargin_pos squarefree ambient)
          (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2))
        lipschitzPositive))

theorem sourceDiagonalThreshold_le_protected
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      protectedBoundaryRadius p ambient clearance ^ 2 :=
  min_le_left _ _

theorem sourceDiagonalThreshold_le_derivative
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      derivativeThreshold squarefree ambient /
        denseLipschitzBound p ambient :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem sourceDiagonalThreshold_le_displacement
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      derivativeMargin squarefree ambient *
          extractionRadius squarefree ambient clearance epsilon ^ 2 /
        denseLipschitzBound p ambient :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- A center within squared distance `r²` of the source anchor produces a
strictly interior radius-`r` square whenever the source avoids the four
`4ρ` strips and `r ≤ ρ`. -/
theorem centeredSquare_strictInterior
    {outer source : Box} {center : Gaussian} {r rho : Coordinate}
    (radiusPositive : 0 < r) (radiusLeProtected : r ≤ rho)
    (stripBounds :
      outer.xLower + 4 * rho < source.xLower ∧
        source.xUpper < outer.xUpper - 4 * rho ∧
        outer.yLower + 4 * rho < source.yLower ∧
        source.yUpper < outer.yUpper - 4 * rho)
    (near : normSq (center - source.anchor) ≤ r ^ 2) :
    (centeredSquare center r radiusPositive.le).StrictInterior outer := by
  have coordinateBounds := coordinate_bounds_of_normSq_le
    radiusPositive.le near
  have realLower : -r ≤ center.re - source.xLower := by
    exact coordinateBounds.1
  have realUpper : center.re - source.xLower ≤ r := by
    exact coordinateBounds.2.1
  have imaginaryLower : -r ≤ center.im - source.yLower := by
    exact coordinateBounds.2.2.1
  have imaginaryUpper : center.im - source.yLower ≤ r := by
    exact coordinateBounds.2.2.2
  have centerRealLower : source.xLower - r ≤ center.re := by
    calc
      source.xLower - r = -r + source.xLower := by ring1
      _ ≤ (center.re - source.xLower) + source.xLower :=
        add_le_add_left realLower source.xLower
      _ = center.re := by ring1
  have centerRealUpper : center.re ≤ source.xLower + r := by
    calc
      center.re = (center.re - source.xLower) + source.xLower := by ring1
      _ ≤ r + source.xLower := add_le_add_left realUpper source.xLower
      _ = source.xLower + r := by ring1
  have centerImaginaryLower : source.yLower - r ≤ center.im := by
    calc
      source.yLower - r = -r + source.yLower := by ring1
      _ ≤ (center.im - source.yLower) + source.yLower :=
        add_le_add_left imaginaryLower source.yLower
      _ = center.im := by ring1
  have centerImaginaryUpper : center.im ≤ source.yLower + r := by
    calc
      center.im = (center.im - source.yLower) + source.yLower := by ring1
      _ ≤ r + source.yLower :=
        add_le_add_left imaginaryUpper source.yLower
      _ = source.yLower + r := by ring1
  have twoRadiusLeFourProtected : 2 * r ≤ 4 * rho := by
    calc
      2 * r ≤ 2 * rho :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusLeProtected
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 2) (by decide)).le
      _ ≤ 4 * rho :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (RFAP.ConstructiveFraction.natCast_le_direct
            (m := 2) (n := 4) (by decide))
          (radiusPositive.le.trans radiusLeProtected)
  have leftGap : outer.xLower + 2 * r < source.xLower :=
    (add_le_add_right twoRadiusLeFourProtected outer.xLower).trans_lt
      stripBounds.1
  have bottomGap : outer.yLower + 2 * r < source.yLower :=
    (add_le_add_right twoRadiusLeFourProtected outer.yLower).trans_lt
      stripBounds.2.2.1
  have rightGap : source.xUpper + 2 * r < outer.xUpper := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      stripBounds.2.1 (4 * rho)
    have fullGap : source.xUpper + 4 * rho < outer.xUpper := by
      calc
        source.xUpper + 4 * rho <
            (outer.xUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.xUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.xUpper).trans_lt
      fullGap
  have topGap : source.yUpper + 2 * r < outer.yUpper := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      stripBounds.2.2.2 (4 * rho)
    have fullGap : source.yUpper + 4 * rho < outer.yUpper := by
      calc
        source.yUpper + 4 * rho <
            (outer.yUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.yUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.yUpper).trans_lt
      fullGap
  constructor
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      leftGap (-2 * r)
    calc
      outer.xLower = (outer.xLower + 2 * r) + (-2 * r) := by ring1
      _ < source.xLower + (-2 * r) := shifted
      _ = (source.xLower - r) - r := by ring1
      _ ≤ center.re - r := add_le_add_left centerRealLower (-r)
  · calc
      center.re + r ≤ source.xLower + 2 * r := by
        have shifted := add_le_add_left centerRealUpper r
        calc
          center.re + r ≤ (source.xLower + r) + r := shifted
          _ = source.xLower + 2 * r := by ring1
      _ ≤ source.xUpper + 2 * r :=
        add_le_add_left source.x_valid (2 * r)
      _ < outer.xUpper := rightGap
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      bottomGap (-2 * r)
    calc
      outer.yLower = (outer.yLower + 2 * r) + (-2 * r) := by ring1
      _ < source.yLower + (-2 * r) := shifted
      _ = (source.yLower - r) - r := by ring1
      _ ≤ center.im - r := add_le_add_left centerImaginaryLower (-r)
  · calc
      center.im + r ≤ source.yLower + 2 * r := by
        have shifted := add_le_add_left centerImaginaryUpper r
        calc
          center.im + r ≤ (source.yLower + r) + r := shifted
          _ = source.yLower + 2 * r := by ring1
      _ ≤ source.yUpper + 2 * r :=
        add_le_add_left source.y_valid (2 * r)
      _ < outer.yUpper := topGap

/-! ## Executable source selection and winding-one extraction -/

/-- The raw-subdivision phase, kept as a small proof-bearing finite output. -/
structure SourceOutput
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : RawWindingState p ambient) (epsilon : Coordinate) where
  source : RawWindingState p current.box
  diagonalSq_le : source.box.diagonalSq ≤
    sourceDiagonalThreshold squarefree current.box current.clearance epsilon

/-- Refine the current nonzero-winding box to all coefficient-computed source
thresholds in one finite subdivision request. -/
def selectSource
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    SourceOutput squarefree current epsilon := by
  let initialState : RawWindingState p current.box :=
    { box := current.box
      refinesAmbient := RFAP.Boxes.Box.refines_refl current.box
      proper := current.proper
      clearance := current.clearance
      rawWinding_ne := current.rawWinding_ne }
  let threshold := sourceDiagonalThreshold squarefree current.box
    current.clearance epsilon
  have thresholdPositive : 0 < threshold :=
    sourceDiagonalThreshold_pos squarefree current.clearance current.proper
      epsilonPositive
  let source := refineTo elimination initialState threshold
  exact
    { source := source
      diagonalSq_le := refineTo_diagonalSq_le elimination initialState
        thresholdPositive }

/-- Complete local output: a strictly nested clear box with raw winding four
and the requested squared-diagonal accuracy. -/
structure Output
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : RawWindingState p ambient) (epsilon : Coordinate) where
  source : RawWindingState p current.box
  radius : Coordinate
  radiusPositive : 0 < radius
  newton : NewtonCenterCertificate p current.box source.box squarefree
  displacementSmall : normSq
    (anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  stripBounds :
    current.box.xLower + 4 *
        protectedBoundaryRadius p current.box current.clearance <
          source.box.xLower ∧
      source.box.xUpper < current.box.xUpper - 4 *
        protectedBoundaryRadius p current.box current.clearance ∧
      current.box.yLower + 4 *
        protectedBoundaryRadius p current.box current.clearance <
          source.box.yLower ∧
      source.box.yUpper < current.box.yUpper - 4 *
        protectedBoundaryRadius p current.box current.clearance
  bandTaylorSmall :
    2 * (extractionBandTaylorCoefficient *
      denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        derivativeMargin squarefree current.box
  box : Box
  box_eq : box = centeredSquare
    (anchorNewtonCenter p source.box) radius radiusPositive.le
  strictCurrent : box.StrictInterior current.box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  rawWindingFour : RFAP.Winding.quadrupledBoxWinding p box = 4
  diagonalSq_le : box.diagonalSq ≤ epsilon ^ 2

/-- The complete finite local extraction.  Its only search is the bounded
safe-cut iteration in `selectSource`; the Newton center and target square are
then exact constructive-rational expressions. -/
def extract
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) : Output squarefree current epsilon := by
  let sourceData := selectSource squarefree elimination current epsilonPositive
  let source := sourceData.source
  let r := extractionRadius squarefree current.box current.clearance epsilon
  let rho := protectedBoundaryRadius p current.box current.clearance
  let lipschitz := denseLipschitzBound p current.box
  let eta := derivativeMargin squarefree current.box
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    extractionRadius_pos squarefree current.clearance current.proper
      epsilonPositive
  have rhoPositive : 0 < rho :=
    protectedBoundaryRadius_pos p current.clearance current.proper
  have lipschitzPositive : 0 < lipschitz :=
    denseLipschitzBound_pos p current.box
  have etaPositive : 0 < eta := derivativeMargin_pos squarefree current.box
  have sourceDiagonal := sourceData.diagonalSq_le
  have sourceProtected : source.box.diagonalSq ≤ rho ^ 2 :=
    sourceDiagonal.trans
      (sourceDiagonalThreshold_le_protected squarefree current.box
        current.clearance epsilon)
  have sourceDerivative : anchorResidualBound p current.box source.box ≤
      derivativeThreshold squarefree current.box := by
    have thresholdBound := sourceDiagonalThreshold_le_derivative squarefree
      current.box current.clearance epsilon
    have scaledThreshold :
        sourceDiagonalThreshold squarefree current.box current.clearance epsilon *
            lipschitz ≤ derivativeThreshold squarefree current.box :=
      (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz *
          sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon * lipschitz := by ring1
      _ ≤ derivativeThreshold squarefree current.box := scaledThreshold
  let newton := computeNewtonCenterOfRawWinding p degreePositive squarefree
    source.refinesAmbient source.proper source.rawWinding_ne sourceDerivative
  have residualDisplacement : anchorResidualBound p current.box source.box ≤
      eta * r ^ 2 := by
    have thresholdBound := sourceDiagonalThreshold_le_displacement squarefree
      current.box current.clearance epsilon
    have scaledThreshold :
        sourceDiagonalThreshold squarefree current.box current.clearance epsilon *
            lipschitz ≤ eta * r ^ 2 :=
      (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz *
          sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon * lipschitz := by ring1
      _ ≤ eta * r ^ 2 := scaledThreshold
  have displacementSmall :
      normSq (anchorNewtonCenter p source.box - source.box.anchor) ≤ r ^ 2 := by
    calc
      normSq (anchorNewtonCenter p source.box - source.box.anchor) ≤
          anchorResidualBound p current.box source.box / eta :=
        newton.displacementMargin
      _ ≤ r ^ 2 :=
        (RFAP.ConstructiveFraction.div_le_iff_pos etaPositive).mpr (by
          calc
            anchorResidualBound p current.box source.box ≤ eta * r ^ 2 :=
              residualDisplacement
            _ = r ^ 2 * eta := by ring1)
  have stripBounds := strictly_inside_protectedBoundary
    (p := p) degreePositive current.clearance current.proper source.proper
      source.refinesAmbient source.rawWinding_ne sourceProtected
  have radiusLeRho : r ≤ rho :=
    extractionRadius_le_protected squarefree current.box current.clearance
      epsilon
  let target := centeredSquare (anchorNewtonCenter p source.box) r
    radiusPositive.le
  have targetStrict : target.StrictInterior current.box :=
    centeredSquare_strictInterior radiusPositive radiusLeRho stripBounds
      displacementSmall
  have targetRefinesCurrent : target.Refines current.box :=
    targetStrict.refines
  have targetRefinesAmbient : target.Refines ambient :=
    targetRefinesCurrent.trans current.refinesAmbient
  have bandTaylorSmall :
      2 * (extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p current.box * r ^ 2) ≤
        derivativeMargin squarefree current.box :=
    extractionRadius_taylor squarefree current.clearance current.proper
      epsilonPositive
  have taylorSmall :
      2 * (36 * denseTaylorRemainderBound p current.box * r ^ 2) ≤
        derivativeMargin squarefree current.box := by
    have remainderNonnegative :
        0 ≤ denseTaylorRemainderBound p current.box * r ^ 2 :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (denseTaylorRemainderBound_pos p current.box).le
        (RFAP.ConstructiveFraction.sq_nonneg_direct r)
    have smallBlockNonnegative :
        0 ≤ ((4 : Coordinate) * 9) *
          (denseTaylorRemainderBound p current.box * r ^ 2) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_pos_direct
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 4) (by decide))
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 9) (by decide))).le
        remainderNonnegative
    have smallBlockLe :
        ((4 : Coordinate) * 9) *
            (denseTaylorRemainderBound p current.box * r ^ 2) ≤
          9 * (((4 : Coordinate) * 9) *
            (denseTaylorRemainderBound p current.box * r ^ 2)) := by
      calc
        ((4 : Coordinate) * 9) *
            (denseTaylorRemainderBound p current.box * r ^ 2) =
            1 * (((4 : Coordinate) * 9) *
              (denseTaylorRemainderBound p current.box * r ^ 2)) := by ring1
        _ ≤ 9 * (((4 : Coordinate) * 9) *
              (denseTaylorRemainderBound p current.box * r ^ 2)) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (RFAP.ConstructiveFraction.natCast_le_direct
              (m := 1) (n := 9) (by decide)) smallBlockNonnegative
    have twoNonnegative : (0 : Coordinate) ≤ 2 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 2) (by decide)).le
    calc
      2 * (36 * denseTaylorRemainderBound p current.box * r ^ 2) =
          2 * (((4 : Coordinate) * 9) *
            (denseTaylorRemainderBound p current.box * r ^ 2)) := by ring1
      _ ≤ 2 * (9 * (((4 : Coordinate) * 9) *
            (denseTaylorRemainderBound p current.box * r ^ 2))) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          smallBlockLe twoNonnegative
      _ = 2 * (extractionBandTaylorCoefficient *
            denseTaylorRemainderBound p current.box * r ^ 2) := by
        unfold extractionBandTaylorCoefficient
        ring1
      _ ≤ derivativeMargin squarefree current.box := bandTaylorSmall
  have windingFour : RFAP.Winding.quadrupledBoxWinding p target = 4 :=
    quadrupledBoxWinding_eq_four_of_newtonSquare degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have targetClearance : BoundaryClearance p target :=
    newtonSquareBoundaryClearance degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have radiusEighth : r ≤ (1 / 8 : Coordinate) * epsilon :=
    extractionRadius_le_eighth squarefree current.box current.clearance epsilon
  have squareBound : r ^ 2 ≤ ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le radiusEighth 2
  have epsilonSquareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct epsilon
  have eighthSquare : (1 / 8 : Coordinate) * epsilon ^ 2 ≤ epsilon ^ 2 := by
    calc
      (1 / 8 : Coordinate) * epsilon ^ 2 ≤ 1 * epsilon ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) epsilonSquareNonnegative
      _ = epsilon ^ 2 := by ring1
  have targetDiagonal : target.diagonalSq ≤ epsilon ^ 2 := by
    have coefficientIdentity :
        (8 : Coordinate) * (1 / 8) ^ 2 = 1 / 8 := by decide
    calc
      target.diagonalSq = 8 * r ^ 2 :=
        centeredSquare_diagonalSq (anchorNewtonCenter p source.box)
          radiusPositive.le
      _ ≤ 8 * ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareBound
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 8) (by decide)).le
      _ = (8 * (1 / 8 : Coordinate) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 8 : Coordinate) * epsilon ^ 2 := by
        rw [coefficientIdentity]
      _ ≤ epsilon ^ 2 := eighthSquare
  exact
    { source := source
      radius := r
      radiusPositive := radiusPositive
      newton := newton
      displacementSmall := displacementSmall
      stripBounds := stripBounds
      bandTaylorSmall := bandTaylorSmall
      box := target
      box_eq := rfl
      strictCurrent := targetStrict
      refinesAmbient := targetRefinesAmbient
      proper := centeredSquare_proper (anchorNewtonCenter p source.box)
        radiusPositive
      clearance := targetClearance
      rawWindingFour := windingFour
      diagonalSq_le := targetDiagonal }

/-! ## Extraction from an explicit derivative-separation resource -/

abbrev DerivativeSeparation (p : GaussianPolynomial) (ambient : Box) :=
  RFAP.DerivativeSeparation.Certificate p ambient
abbrev SeparatedNewtonCenterCertificate :=
  RFAP.LocalExtraction.SeparatedNewtonCenterCertificate

/-- Radius chosen from the protected boundary, the unit scale, and the
Taylor scale attached to an explicit derivative margin. -/
def separatedBaseExtractionRadius
    {p : GaussianPolynomial} (separation : DerivativeSeparation p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient) : Coordinate :=
  min ((1 / 2 : Coordinate) *
      protectedBoundaryRadius p ambient clearance)
    (min 1 (separation.margin /
      (72 * denseTaylorRemainderBound p ambient)))

theorem separatedBaseExtractionRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper) :
    0 < separatedBaseExtractionRadius separation ambient clearance := by
  have denominatorPositive :
      0 < (72 : Coordinate) * denseTaylorRemainderBound p ambient :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (denseTaylorRemainderBound_pos p ambient)
  exact lt_min
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (protectedBoundaryRadius_pos p clearance proper))
    (lt_min (by decide)
      (RFAP.ConstructiveFraction.div_pos_direct
        separation.margin_pos denominatorPositive))

/-- The final radius also meets the caller's displayed accuracy request. -/
def separatedExtractionRadius
    {p : GaussianPolynomial} (separation : DerivativeSeparation p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) : Coordinate :=
  min (separatedBaseExtractionRadius separation ambient clearance)
    ((1 / 8 : Coordinate) * epsilon)

theorem separatedExtractionRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < separatedExtractionRadius separation ambient clearance epsilon :=
  lt_min (separatedBaseExtractionRadius_pos separation clearance proper)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) epsilonPositive)

theorem separatedExtractionRadius_le_protected
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedExtractionRadius separation ambient clearance epsilon ≤
      protectedBoundaryRadius p ambient clearance := by
  have halfBound :
      separatedExtractionRadius separation ambient clearance epsilon ≤
        (1 / 2 : Coordinate) *
          protectedBoundaryRadius p ambient clearance :=
    (min_le_left _ _).trans (min_le_left _ _)
  calc
    separatedExtractionRadius separation ambient clearance epsilon ≤
        (1 / 2 : Coordinate) *
          protectedBoundaryRadius p ambient clearance := halfBound
    _ ≤ 1 * protectedBoundaryRadius p ambient clearance :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Coordinate) ≤ 1 by decide)
        (protectedBoundaryRadius_nonneg p ambient clearance)
    _ = protectedBoundaryRadius p ambient clearance := one_mul _

theorem separatedExtractionRadius_le_one
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedExtractionRadius separation ambient clearance epsilon ≤ 1 :=
  (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem separatedExtractionRadius_le_eighth
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedExtractionRadius separation ambient clearance epsilon ≤
      (1 / 8 : Coordinate) * epsilon :=
  min_le_right _ _

theorem separatedExtractionRadius_taylor
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    let r := separatedExtractionRadius separation ambient clearance epsilon
    2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
      separation.margin := by
  let r := separatedExtractionRadius separation ambient clearance epsilon
  let taylor := denseTaylorRemainderBound p ambient
  have radiusPositive : 0 < r :=
    separatedExtractionRadius_pos separation clearance proper epsilonPositive
  have radiusLeOne : r ≤ 1 :=
    separatedExtractionRadius_le_one separation clearance epsilon
  have radiusRatio : r ≤ separation.margin / (72 * taylor) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have denominatorPositive : 0 < (72 : Coordinate) * taylor :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (72 * taylor) ≤ separation.margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = r := one_mul _
  calc
    2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) =
        (72 * taylor) * r ^ 2 := by
      dsimp only [taylor]
      ring1
    _ ≤ (72 * taylor) * r :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        squareLeRadius denominatorPositive.le
    _ = r * (72 * taylor) := by ring1
    _ ≤ separation.margin := ratioScaled

/-- Source subdivision threshold for an explicit derivative separation. -/
def separatedSourceDiagonalThreshold
    {p : GaussianPolynomial} (separation : DerivativeSeparation p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Coordinate) : Coordinate :=
  let rho := protectedBoundaryRadius p ambient clearance
  let r := separatedExtractionRadius separation ambient clearance epsilon
  let lipschitz := denseLipschitzBound p ambient
  min (rho ^ 2)
    (min (separation.threshold / lipschitz)
      (separation.margin * r ^ 2 / lipschitz))

theorem separatedSourceDiagonalThreshold_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < separatedSourceDiagonalThreshold separation ambient clearance epsilon :=
  lt_min
    (RFAP.ConstructiveFraction.pow_pos_direct
      (protectedBoundaryRadius_pos p clearance proper) 2)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct separation.threshold_pos
        (denseLipschitzBound_pos p ambient))
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.mul_pos_direct separation.margin_pos
          (RFAP.ConstructiveFraction.pow_pos_direct
            (separatedExtractionRadius_pos separation clearance proper
              epsilonPositive) 2))
        (denseLipschitzBound_pos p ambient)))

theorem separatedSourceDiagonalThreshold_le_protected
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      protectedBoundaryRadius p ambient clearance ^ 2 :=
  min_le_left _ _

theorem separatedSourceDiagonalThreshold_le_derivative
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      separation.threshold / denseLipschitzBound p ambient :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem separatedSourceDiagonalThreshold_le_displacement
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Coordinate) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      separation.margin *
          separatedExtractionRadius separation ambient clearance epsilon ^ 2 /
        denseLipschitzBound p ambient :=
  (min_le_right _ _).trans (min_le_right _ _)

structure SeparatedSourceOutput
    {p : GaussianPolynomial} {ambient : Box}
    (current : RawWindingState p ambient)
    (separation : DerivativeSeparation p current.box)
    (epsilon : Coordinate) where
  source : RawWindingState p current.box
  diagonalSq_le : source.box.diagonalSq ≤
    separatedSourceDiagonalThreshold separation current.box
      current.clearance epsilon

def selectSeparatedSource
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (separation : DerivativeSeparation p current.box)
    (elimination : AxisEliminationCertificate p degreeBound)
    (epsilonPositive : 0 < epsilon) :
    SeparatedSourceOutput current separation epsilon := by
  let initialState : RawWindingState p current.box :=
    { box := current.box
      refinesAmbient := RFAP.Boxes.Box.refines_refl current.box
      proper := current.proper
      clearance := current.clearance
      rawWinding_ne := current.rawWinding_ne }
  let threshold := separatedSourceDiagonalThreshold separation current.box
    current.clearance epsilon
  have thresholdPositive : 0 < threshold :=
    separatedSourceDiagonalThreshold_pos separation current.clearance
      current.proper epsilonPositive
  let source := refineTo elimination initialState threshold
  exact
    { source := source
      diagonalSq_le := refineTo_diagonalSq_le elimination initialState
        thresholdPositive }

/-- Strictly nested Newton-square output obtained without a global
squarefree certificate for the displayed polynomial. -/
structure SeparatedOutput
    {p : GaussianPolynomial} {ambient : Box}
    (current : RawWindingState p ambient)
    (separation : DerivativeSeparation p current.box)
    (epsilon : Coordinate) where
  source : RawWindingState p current.box
  radius : Coordinate
  radius_eq : radius = separatedExtractionRadius separation current.box
    current.clearance epsilon
  radiusPositive : 0 < radius
  newton : SeparatedNewtonCenterCertificate
    p current.box source.box separation
  displacementSmall : normSq
    (anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  taylorSmall :
    2 * (36 * denseTaylorRemainderBound p current.box * radius ^ 2) ≤
      separation.margin
  box : Box
  box_eq : box = centeredSquare
    (anchorNewtonCenter p source.box) radius radiusPositive.le
  strictCurrent : box.StrictInterior current.box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  clearance_bound : clearance.bound =
    RFAP.NewtonWinding.separatedNewtonDominanceMargin separation radius ^ 2 /
      (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
        p current.box radius)
  rawWindingFour : RFAP.Winding.quadrupledBoxWinding p box = 4
  diagonalSq_le : box.diagonalSq ≤ epsilon ^ 2

/-- Complete finite local extraction driven by explicit derivative
separation. -/
def extractSeparated
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (separation : DerivativeSeparation p current.box)
    (elimination : AxisEliminationCertificate p degreeBound)
    (epsilonPositive : 0 < epsilon) :
    SeparatedOutput current separation epsilon := by
  let sourceData := selectSeparatedSource current separation elimination
    epsilonPositive
  let source := sourceData.source
  let r := separatedExtractionRadius separation current.box
    current.clearance epsilon
  let rho := protectedBoundaryRadius p current.box current.clearance
  let lipschitz := denseLipschitzBound p current.box
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    separatedExtractionRadius_pos separation current.clearance current.proper
      epsilonPositive
  have lipschitzPositive : 0 < lipschitz :=
    denseLipschitzBound_pos p current.box
  have sourceDiagonal := sourceData.diagonalSq_le
  have sourceProtected : source.box.diagonalSq ≤ rho ^ 2 :=
    sourceDiagonal.trans
      (separatedSourceDiagonalThreshold_le_protected separation
        current.clearance epsilon)
  have sourceDerivative : anchorResidualBound p current.box source.box ≤
      separation.threshold := by
    have thresholdBound := separatedSourceDiagonalThreshold_le_derivative
      separation current.clearance epsilon
    have scaledThreshold :
        separatedSourceDiagonalThreshold separation current.box
            current.clearance epsilon * lipschitz ≤ separation.threshold :=
      (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz * separatedSourceDiagonalThreshold separation
          current.box current.clearance epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = separatedSourceDiagonalThreshold separation current.box
          current.clearance epsilon * lipschitz := by ring1
      _ ≤ separation.threshold := scaledThreshold
  let newton := computeNewtonCenterOfRawWindingSeparated p degreePositive
    separation source.refinesAmbient source.proper source.rawWinding_ne
      sourceDerivative
  have residualDisplacement :
      anchorResidualBound p current.box source.box ≤
        separation.margin * r ^ 2 := by
    have thresholdBound := separatedSourceDiagonalThreshold_le_displacement
      separation current.clearance epsilon
    have scaledThreshold :
        separatedSourceDiagonalThreshold separation current.box
            current.clearance epsilon * lipschitz ≤
          separation.margin * r ^ 2 :=
      (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz * separatedSourceDiagonalThreshold separation
          current.box current.clearance epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = separatedSourceDiagonalThreshold separation current.box
          current.clearance epsilon * lipschitz := by ring1
      _ ≤ separation.margin * r ^ 2 := scaledThreshold
  have displacementSmall :
      normSq (anchorNewtonCenter p source.box - source.box.anchor) ≤ r ^ 2 := by
    calc
      normSq (anchorNewtonCenter p source.box - source.box.anchor) ≤
          anchorResidualBound p current.box source.box / separation.margin :=
        newton.displacementMargin
      _ ≤ r ^ 2 :=
        (RFAP.ConstructiveFraction.div_le_iff_pos separation.margin_pos).mpr
          (by
            calc
              anchorResidualBound p current.box source.box ≤
                  separation.margin * r ^ 2 := residualDisplacement
              _ = r ^ 2 * separation.margin := by ring1)
  have stripBounds := strictly_inside_protectedBoundary
    (p := p) degreePositive current.clearance current.proper source.proper
      source.refinesAmbient source.rawWinding_ne sourceProtected
  have radiusLeRho : r ≤ rho :=
    separatedExtractionRadius_le_protected separation current.clearance epsilon
  let target := centeredSquare (anchorNewtonCenter p source.box) r
    radiusPositive.le
  have targetStrict : target.StrictInterior current.box :=
    centeredSquare_strictInterior radiusPositive radiusLeRho stripBounds
      displacementSmall
  have targetRefinesCurrent : target.Refines current.box :=
    targetStrict.refines
  have targetRefinesAmbient : target.Refines ambient :=
    targetRefinesCurrent.trans current.refinesAmbient
  have taylorSmall :
      2 * (36 * denseTaylorRemainderBound p current.box * r ^ 2) ≤
        separation.margin :=
    separatedExtractionRadius_taylor separation current.clearance
      current.proper epsilonPositive
  have windingFour : RFAP.Winding.quadrupledBoxWinding p target = 4 :=
    quadrupledBoxWinding_eq_four_of_separatedNewtonSquare degreeAtLeastTwo
      newton source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  let targetClearance : BoundaryClearance p target :=
    separatedNewtonSquareBoundaryClearance degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have targetClearanceBound : targetClearance.bound =
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
          p current.box r) := rfl
  have radiusEighth : r ≤ (1 / 8 : Coordinate) * epsilon :=
    separatedExtractionRadius_le_eighth separation current.clearance epsilon
  have squareBound : r ^ 2 ≤ ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le radiusEighth 2
  have epsilonSquareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct epsilon
  have targetDiagonal : target.diagonalSq ≤ epsilon ^ 2 := by
    have coefficientIdentity :
        (8 : Coordinate) * (1 / 8) ^ 2 = 1 / 8 := by decide
    calc
      target.diagonalSq = 8 * r ^ 2 :=
        centeredSquare_diagonalSq (anchorNewtonCenter p source.box)
          radiusPositive.le
      _ ≤ 8 * ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareBound
          (by decide)
      _ = (8 * (1 / 8 : Coordinate) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 8 : Coordinate) * epsilon ^ 2 := by rw [coefficientIdentity]
      _ ≤ 1 * epsilon ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 / 8 : Coordinate) ≤ 1 by decide)
          epsilonSquareNonnegative
      _ = epsilon ^ 2 := one_mul _
  exact
    { source := source
      radius := r
      radius_eq := rfl
      radiusPositive := radiusPositive
      newton := newton
      displacementSmall := displacementSmall
      taylorSmall := taylorSmall
      box := target
      box_eq := rfl
      strictCurrent := targetStrict
      refinesAmbient := targetRefinesAmbient
      proper := centeredSquare_proper (anchorNewtonCenter p source.box)
        radiusPositive
      clearance := targetClearance
      clearance_bound := targetClearanceBound
      rawWindingFour := windingFour
      diagonalSq_le := targetDiagonal }

/-! ## A-priori majorants for progressive-coefficient continuation -/

/-- Finite upper bounds sufficient to run the Newton construction with a
radius and final clearance that can be bounded before the displayed
polynomial is revealed. -/
structure ExtractionMajorants (p : GaussianPolynomial) (ambient : Box) where
  lipschitz : Coordinate
  lipschitz_pos : 0 < lipschitz
  lipschitz_upper : denseLipschitzBound p ambient ≤ lipschitz
  taylor : Coordinate
  taylor_pos : 0 < taylor
  taylor_upper : denseTaylorRemainderBound p ambient ≤ taylor
  derivative : Coordinate
  derivative_pos : 0 < derivative
  derivative_upper : ∀ {z : Gaussian}, ambient.Contains z →
    normSq ((RFAP.ConstructiveGCD.derivative p).eval z) ≤ derivative

/-- The coefficient-computed bounds of one displayed polynomial, packaged as
the canonical majorants for quantitative extraction.  This constructor is
useful when no coefficient channel has to be anticipated: all three bounds
are exact finite scans of the current polynomial and box. -/
def exactExtractionMajorants (p : GaussianPolynomial) (ambient : Box) :
    ExtractionMajorants p ambient where
  lipschitz := denseLipschitzBound p ambient
  lipschitz_pos := denseLipschitzBound_pos p ambient
  lipschitz_upper := le_rfl
  taylor := denseTaylorRemainderBound p ambient
  taylor_pos := denseTaylorRemainderBound_pos p ambient
  taylor_upper := le_rfl
  derivative := denseEvalNormMajorant
    (RFAP.ConstructiveGCD.derivative p) ambient
  derivative_pos := denseEvalNormMajorant_pos
    (RFAP.ConstructiveGCD.derivative p) ambient
  derivative_upper := by
    intro z inside
    exact normSq_eval_le_denseEvalNormMajorant
      (RFAP.ConstructiveGCD.derivative p) inside

/-- Polynomial-independent protected radius computed from the five rational
quantities which are known before a later coefficient reading is revealed. -/
def predictedProtectedRadiusData
    (ambient : Box) (clearanceBound lipschitz : Coordinate) : Coordinate :=
  min (1 / protectedBoundaryScale)
    (min (clearanceBound / (2 * lipschitz))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

/-- Polynomial-independent extraction radius.  This is the numerical content
of `majorizedExtractionRadius`, separated from its proof-carrying resources. -/
def predictedExtractionRadiusData
    (ambient : Box) (margin clearanceBound lipschitz taylor epsilon :
      Coordinate) : Coordinate :=
  min
    (min ((1 / 2 : Coordinate) *
        predictedProtectedRadiusData ambient clearanceBound lipschitz)
      (min 1 (margin / (72 * taylor))))
    ((1 / 8 : Coordinate) * epsilon)

/-- Positive boundary-clearance lower bound computable solely from displayed
rational input data, before the polynomial carrying those bounds is read. -/
def predictedExtractionClearanceData
    (ambient : Box)
    (margin clearanceBound lipschitz taylor derivative epsilon : Coordinate) :
    Coordinate :=
  let radius := predictedExtractionRadiusData ambient margin clearanceBound
    lipschitz taylor epsilon
  let dominance := margin * radius ^ 2 / 2
  dominance ^ 2 / (8 * derivative)

theorem predictedProtectedRadiusData_pos
    {ambient : Box} {clearanceBound lipschitz : Coordinate}
    (proper : ambient.Proper) (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) :
    0 < predictedProtectedRadiusData ambient clearanceBound lipschitz := by
  have scalePositive : 0 < protectedBoundaryScale := by
    unfold protectedBoundaryScale
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide))
      (by decide)
  exact lt_min
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) scalePositive)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct clearancePositive
        (RFAP.ConstructiveFraction.mul_pos_direct
          (by decide) lipschitzPositive))
      (lt_min
        (RFAP.ConstructiveFraction.div_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct proper.1) (by decide))
        (RFAP.ConstructiveFraction.div_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct proper.2) (by decide))))

theorem predictedExtractionRadiusData_pos
    {ambient : Box} {margin clearanceBound lipschitz taylor epsilon :
      Coordinate}
    (proper : ambient.Proper) (marginPositive : 0 < margin)
    (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) (taylorPositive : 0 < taylor)
    (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionRadiusData ambient margin clearanceBound
      lipschitz taylor epsilon := by
  exact lt_min
    (lt_min
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (predictedProtectedRadiusData_pos proper clearancePositive
          lipschitzPositive))
      (lt_min (by decide)
        (RFAP.ConstructiveFraction.div_pos_direct marginPositive
          (RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 72) (by decide)) taylorPositive))))
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) epsilonPositive)

theorem predictedExtractionClearanceData_pos
    {ambient : Box}
    {margin clearanceBound lipschitz taylor derivative epsilon : Coordinate}
    (proper : ambient.Proper) (marginPositive : 0 < margin)
    (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) (taylorPositive : 0 < taylor)
    (derivativePositive : 0 < derivative) (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionClearanceData ambient margin clearanceBound
      lipschitz taylor derivative epsilon := by
  have radiusPositive := predictedExtractionRadiusData_pos proper
    marginPositive clearancePositive lipschitzPositive taylorPositive
    epsilonPositive
  have dominancePositive : 0 < margin *
      predictedExtractionRadiusData ambient margin clearanceBound lipschitz
        taylor epsilon ^ 2 / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct marginPositive
        (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2))
      (by decide)
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct dominancePositive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      derivativePositive)

/-- Protected-boundary radius with the admitted Lipschitz majorant in place
of the newly revealed polynomial's exact scan. -/
def majorizedProtectedRadius
    {p : GaussianPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) : Coordinate :=
  min (1 / protectedBoundaryScale)
    (min (clearance.bound / (2 * majorants.lipschitz))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

@[simp] theorem majorizedProtectedRadius_eq_data
    {p : GaussianPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) :
    majorizedProtectedRadius clearance majorants =
      predictedProtectedRadiusData ambient clearance.bound
        majorants.lipschitz := rfl

theorem majorizedProtectedRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) (proper : ambient.Proper) :
    0 < majorizedProtectedRadius clearance majorants := by
  have scalePositive : 0 < protectedBoundaryScale := by
    unfold protectedBoundaryScale
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide))
      (by decide)
  exact lt_min
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) scalePositive)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct clearance.positive
        (RFAP.ConstructiveFraction.mul_pos_direct
          (by decide) majorants.lipschitz_pos))
      (lt_min
        (RFAP.ConstructiveFraction.div_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct proper.1) (by decide))
        (RFAP.ConstructiveFraction.div_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct proper.2) (by decide))))

theorem majorizedProtectedRadius_le
    {p : GaussianPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) :
    majorizedProtectedRadius clearance majorants ≤
      protectedBoundaryRadius p ambient clearance := by
  unfold majorizedProtectedRadius protectedBoundaryRadius
  apply min_le_min le_rfl
  apply min_le_min
  · have actualDenominatorPositive :
        0 < (2 : Coordinate) * denseLipschitzBound p ambient :=
      RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p ambient)
    have denominatorOrder :
        2 * denseLipschitzBound p ambient ≤ 2 * majorants.lipschitz :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        majorants.lipschitz_upper (by decide)
    exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      clearance.positive.le actualDenominatorPositive denominatorOrder
  · exact min_le_min le_rfl le_rfl

/-- Radius which is guaranteed to lie below the actual extraction radius of
every polynomial satisfying `majorants`. -/
def majorizedExtractionRadius
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient)
    (epsilon : Coordinate) : Coordinate :=
  min
    (min ((1 / 2 : Coordinate) *
        majorizedProtectedRadius clearance majorants)
      (min 1 (separation.margin / (72 * majorants.taylor))))
    ((1 / 8 : Coordinate) * epsilon)

@[simp] theorem majorizedExtractionRadius_eq_data
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) (epsilon : Coordinate) :
    majorizedExtractionRadius separation clearance majorants epsilon =
      predictedExtractionRadiusData ambient separation.margin clearance.bound
        majorants.lipschitz majorants.taylor epsilon := rfl

theorem majorizedExtractionRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) (proper : ambient.Proper)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < majorizedExtractionRadius separation clearance majorants epsilon := by
  exact lt_min
    (lt_min
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (majorizedProtectedRadius_pos clearance majorants proper))
      (lt_min (by decide)
        (RFAP.ConstructiveFraction.div_pos_direct separation.margin_pos
          (RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 72) (by decide)) majorants.taylor_pos))))
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) epsilonPositive)

theorem majorizedExtractionRadius_le
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient)
    (epsilon : Coordinate) :
    majorizedExtractionRadius separation clearance majorants epsilon ≤
      separatedExtractionRadius separation ambient clearance epsilon := by
  unfold majorizedExtractionRadius separatedExtractionRadius
  apply min_le_min
  · unfold separatedBaseExtractionRadius
    apply min_le_min
    · exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (majorizedProtectedRadius_le clearance majorants) (by decide)
    · apply min_le_min le_rfl
      have actualDenominatorPositive :
          0 < (72 : Coordinate) * denseTaylorRemainderBound p ambient :=
        RFAP.ConstructiveFraction.mul_pos_direct
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 72) (by decide))
          (denseTaylorRemainderBound_pos p ambient)
      have denominatorOrder :
          72 * denseTaylorRemainderBound p ambient ≤
            72 * majorants.taylor :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          majorants.taylor_upper
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 72) (by decide)).le
      exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        separation.margin_pos.le actualDenominatorPositive denominatorOrder
  · exact le_rfl

def majorizedLinearizationMajorant
    {p : GaussianPolynomial} {ambient : Box}
    (majorants : ExtractionMajorants p ambient) : Coordinate :=
  2 * majorants.derivative

theorem majorizedLinearizationMajorant_pos
    {p : GaussianPolynomial} {ambient : Box}
    (majorants : ExtractionMajorants p ambient) :
    0 < majorizedLinearizationMajorant majorants :=
  RFAP.ConstructiveFraction.mul_pos_direct
    (by decide) majorants.derivative_pos

/-- Predicted positive clearance bound available before the admitted
polynomial is read. -/
def predictedExtractionClearance
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient)
    (epsilon : Coordinate) : Coordinate :=
  let radius := majorizedExtractionRadius separation clearance majorants epsilon
  let margin := separation.margin * radius ^ 2 / 2
  margin ^ 2 / (8 * majorants.derivative)

@[simp] theorem predictedExtractionClearance_eq_data
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) (epsilon : Coordinate) :
    predictedExtractionClearance separation clearance majorants epsilon =
      predictedExtractionClearanceData ambient separation.margin
        clearance.bound majorants.lipschitz majorants.taylor
        majorants.derivative epsilon := rfl

theorem predictedExtractionClearance_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : ExtractionMajorants p ambient) (proper : ambient.Proper)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionClearance separation clearance majorants epsilon := by
  have radiusPositive := majorizedExtractionRadius_pos separation clearance
    majorants proper epsilonPositive
  have marginPositive : 0 < separation.margin *
      majorizedExtractionRadius separation clearance majorants epsilon ^ 2 / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct separation.margin_pos
        (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2))
      (by decide)
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct
      (by decide) majorants.derivative_pos)

/-- The extraction result equipped with the a-priori clearance certificate
used by progressive continuation. -/
structure MajorizedSeparatedOutput
    {p : GaussianPolynomial} {ambient : Box}
    (current : RawWindingState p ambient)
    (separation : DerivativeSeparation p current.box)
    (majorants : ExtractionMajorants p current.box)
    (epsilon : Coordinate) where
  core : SeparatedOutput current separation epsilon
  clearance : BoundaryClearance p core.box
  clearance_bound : clearance.bound =
    RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
        core.radius ^ 2 /
      (8 * majorants.derivative)
  predicted_clearance_le :
    predictedExtractionClearance separation current.clearance majorants epsilon ≤
      clearance.bound

/-- Run separated extraction and replace its boundary clearance with the
explicit majorant-based certificate. -/
def extractSeparatedMajorized
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (current : RawWindingState p ambient)
    (separation : DerivativeSeparation p current.box)
    (majorants : ExtractionMajorants p current.box)
    (elimination : AxisEliminationCertificate p degreeBound)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    MajorizedSeparatedOutput current separation majorants epsilon := by
  let core := extractSeparated degreeAtLeastTwo current separation elimination
    epsilonPositive
  have radiusLeOne : core.radius ≤ 1 := by
    rw [core.radius_eq]
    exact separatedExtractionRadius_le_one separation current.clearance epsilon
  have radiusSquareLeOne : core.radius ^ 2 ≤ 1 := by
    calc
      core.radius ^ 2 ≤ (1 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct core.radiusPositive.le
          radiusLeOne 2
      _ = 1 := by decide
  have centeredRefines :
      (centeredSquare (anchorNewtonCenter p core.source.box) core.radius
        core.radiusPositive.le).Refines current.box := by
    rw [← core.box_eq]
    exact core.strictCurrent.refines
  have linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary
        (centeredSquare (anchorNewtonCenter p core.source.box) core.radius
          core.radiusPositive.le) z →
      normSq ((RFAP.NewtonWinding.newtonLinearization p core.source.box).eval z) ≤
        majorizedLinearizationMajorant majorants := by
    intro z boundary
    have sourceAnchorInside : current.box.Contains core.source.box.anchor :=
      core.source.refinesAmbient.contains core.source.box.contains_anchor
    have derivativeBound := majorants.derivative_upper sourceAnchorInside
    have radial := centeredSquare_normSq_sub_center_le
      (anchorNewtonCenter p core.source.box) core.radiusPositive.le boundary.1
    rw [RFAP.NewtonWinding.newtonLinearization,
      RFAP.AffineWinding.affineCoordinate_eval, normSq_mul]
    calc
      normSq ((RFAP.ConstructiveGCD.derivative p).eval core.source.box.anchor) *
          normSq (z - anchorNewtonCenter p core.source.box) ≤
        majorants.derivative * (2 * core.radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct derivativeBound radial
          (normSq_nonneg (z - anchorNewtonCenter p core.source.box))
          majorants.derivative_pos.le
      _ ≤ majorants.derivative * 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            radiusSquareLeOne (by decide)) majorants.derivative_pos.le
      _ = majorizedLinearizationMajorant majorants := by
        unfold majorizedLinearizationMajorant
        ring1
  let centeredClearance :=
    RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo core.newton core.source.refinesAmbient
      core.radiusPositive centeredRefines core.displacementSmall
      core.taylorSmall (majorizedLinearizationMajorant majorants)
      (majorizedLinearizationMajorant_pos majorants) linearizationUpper
  let clearance : BoundaryClearance p core.box := by
    rw [core.box_eq]
    exact centeredClearance
  have clearanceBound : clearance.bound =
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
          core.radius ^ 2 /
        (8 * majorants.derivative) := by
    change centeredClearance.bound = _
    rw [RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearanceWithMajorant_bound]
    have denominatorIdentity :
        (4 : Coordinate) * majorizedLinearizationMajorant majorants =
          8 * majorants.derivative := by
      unfold majorizedLinearizationMajorant
      ring1
    rw [denominatorIdentity]
  let predictedRadius := majorizedExtractionRadius separation current.clearance
    majorants epsilon
  have predictedRadiusPositive : 0 < predictedRadius :=
    majorizedExtractionRadius_pos separation current.clearance majorants
      current.proper epsilonPositive
  have predictedRadiusLe : predictedRadius ≤ core.radius := by
    rw [core.radius_eq]
    exact majorizedExtractionRadius_le separation current.clearance
      majorants epsilon
  have predictedSquareLe : predictedRadius ^ 2 ≤ core.radius ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct predictedRadiusPositive.le
      predictedRadiusLe 2
  let actualBase :=
    36 * denseTaylorRemainderBound p current.box * core.radius ^ 2
  have errorHalf : RFAP.NewtonWinding.newtonErrorBudget p current.box
      core.radius ≤ separation.margin * core.radius ^ 2 / 2 := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos
      (show (0 : Coordinate) < 2 by decide)).mpr
    have scaledTaylor :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        core.taylorSmall
        (RFAP.ConstructiveFraction.sq_nonneg_direct core.radius)
    calc
      RFAP.NewtonWinding.newtonErrorBudget p current.box core.radius * 2 =
          (2 * actualBase) * core.radius ^ 2 := by
        unfold RFAP.NewtonWinding.newtonErrorBudget
        dsimp only [actualBase]
        ring1
      _ ≤ separation.margin * core.radius ^ 2 := scaledTaylor
  have halfMarginLe : separation.margin * core.radius ^ 2 / 2 ≤
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
        core.radius := by
    unfold RFAP.NewtonWinding.separatedNewtonDominanceMargin
    apply (le_sub_iff_add_le).mpr
    have halfIdentity : separation.margin * core.radius ^ 2 / 2 +
        separation.margin * core.radius ^ 2 / 2 =
          separation.margin * core.radius ^ 2 := by
      apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
        (show (2 : Coordinate) ≠ 0 by decide)
      have cancel : (separation.margin * core.radius ^ 2 / 2) * 2 =
          separation.margin * core.radius ^ 2 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)
      rw [_root_.add_mul, cancel]
      exact (_root_.mul_two _).symm
    calc
      separation.margin * core.radius ^ 2 / 2 +
          RFAP.NewtonWinding.newtonErrorBudget p current.box core.radius ≤
          separation.margin * core.radius ^ 2 / 2 +
          separation.margin * core.radius ^ 2 / 2 :=
        RFAP.ConstructiveFraction.add_le_add_direct le_rfl errorHalf
      _ = separation.margin * core.radius ^ 2 := halfIdentity
  have predictedMarginLe : separation.margin * predictedRadius ^ 2 / 2 ≤
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
        core.radius := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      predictedSquareLe separation.margin_pos.le
    have divided : separation.margin * predictedRadius ^ 2 / 2 ≤
        separation.margin * core.radius ^ 2 / 2 := by
      change (separation.margin * predictedRadius ^ 2) *
          (2 : Coordinate)⁻¹ ≤
        (separation.margin * core.radius ^ 2) * (2 : Coordinate)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scaled
        (RFAP.ConstructiveFraction.inv_pos_direct
          (show (0 : Coordinate) < 2 by decide)).le
    exact divided.trans halfMarginLe
  have actualMarginPositive :=
    RFAP.NewtonWinding.separatedNewtonDominanceMargin_pos separation
      core.radiusPositive core.taylorSmall
  have marginSquareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct separation.margin_pos
        (RFAP.ConstructiveFraction.pow_pos_direct predictedRadiusPositive 2))
      (by decide)).le predictedMarginLe 2
  have denominatorPositive : 0 < (8 : Coordinate) * majorants.derivative :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      majorants.derivative_pos
  have predictedClearanceLe :
      predictedExtractionClearance separation current.clearance majorants
          epsilon ≤ clearance.bound := by
    rw [clearanceBound]
    unfold predictedExtractionClearance
    change _ * ((8 : Coordinate) * majorants.derivative)⁻¹ ≤
      _ * ((8 : Coordinate) * majorants.derivative)⁻¹
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      marginSquareLe
      (RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive).le
  exact
    { core := core
      clearance := clearance
      clearance_bound := clearanceBound
      predicted_clearance_le := predictedClearanceLe }

end RFAP.NewtonExtraction
