import FTA.CCLBranchEventOwner
import FTA.CentralBandGrid
import FTA.ConstructiveTrack
import FTA.RawLocalExtraction

/-!
# Winding extraction from a classified CCL event

A selected algebraic branch event supplies rational path points with an
arbitrarily small polynomial residual.  Boundary clearance keeps a suitably
chosen point a fixed rational distance inside the current winding box.  This
module packages that point in a small centered source square and applies the
ordinary Newton-band construction without assuming that the source square
already has nonzero winding.
-/

namespace FTA
namespace CCLEventExtraction

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLClearanceExclusion
open FTA.CentralBandGrid
open FTA.ComputablePolynomial
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.RawLocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

/-- Rational square of half-width `radius` centered at `point`. -/
def centeredSourceSquare (point : QI) (radius : ℚ)
    (radiusNonnegative : 0 ≤ radius) : RatBox where
  xLower := point.re - radius
  xUpper := point.re + radius
  yLower := point.im - radius
  yUpper := point.im + radius
  x_valid := by linarith
  y_valid := by linarith

@[simp] theorem centeredSourceSquare_center
    (point : QI) (radius : ℚ) (radiusNonnegative : 0 ≤ radius) :
    (centeredSourceSquare point radius radiusNonnegative).center = point := by
  ext <;> simp [centeredSourceSquare, RatBox.center]

theorem centeredSourceSquare_proper
    (point : QI) {radius : ℚ} (radiusPositive : 0 < radius) :
    (centeredSourceSquare point radius radiusPositive.le).Proper := by
  constructor <;> dsimp only [centeredSourceSquare] <;> linarith

/-- Lower an existing boundary-clearance constant to any requested positive
cap.  The geometric box and its boundary proof are unchanged. -/
def shrinkBoundaryClearance
    {p : GaussianPolynomial} {box : RatBox}
    (clearance : BoxBoundaryClearanceCertificate p box)
    (cap : ℚ) (capPositive : 0 < cap) :
    BoxBoundaryClearanceCertificate p box where
  bound := min clearance.bound cap
  positive := lt_min clearance.positive capPositive
  lower := by
    intro point boundary
    exact (min_le_left _ _).trans (clearance.lower point boundary)

theorem shrinkBoundaryClearance_bound_le_cap
    {p : GaussianPolynomial} {box : RatBox}
    (clearance : BoxBoundaryClearanceCertificate p box)
    (cap : ℚ) (capPositive : 0 < cap) :
    (shrinkBoundaryClearance clearance cap capPositive).bound ≤ cap :=
  min_le_right _ _

@[simp] theorem centeredSourceSquare_diagonalSq
    (point : QI) (radius : ℚ) (radiusNonnegative : 0 ≤ radius) :
    (centeredSourceSquare point radius radiusNonnegative).diagonalSq =
      8 * radius ^ 2 := by
  dsimp only [centeredSourceSquare, RatBox.diagonalSq]
  ring

/-- Newton-band radius capped by both the uniform event-interior scale and
the Taylor-dominance scale. -/
def eventBandRadius
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  min (boundaryInteriorRadius p box clearance / 2)
    (min 1 (LocalExtraction.derivativeMargin squarefree box /
      (600 * denseTaylorRemainderBound p box)))

theorem eventBandRadius_pos
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < eventBandRadius squarefree clearance := by
  exact lt_min
    (div_pos (boundaryInteriorRadius_pos p box clearance) (by norm_num))
    (lt_min zero_lt_one
      (div_pos (LocalExtraction.derivativeMargin_pos squarefree box)
        (mul_pos (by norm_num) (denseTaylorRemainderBound_pos p box))))

theorem eventBandRadius_le_half_interior
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    eventBandRadius squarefree clearance ≤
      boundaryInteriorRadius p box clearance / 2 :=
  min_le_left _ _

/-- A sufficiently small clearance constant makes the extracted event band
no wider than an arbitrary positive rational target. -/
theorem eventBandRadius_le_of_clearance_bound
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {target : ℚ} (boundLe : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient box) * target) :
    eventBandRadius squarefree clearance ≤ target := by
  let L := denseLipschitzBound p (nearbyAmbient box)
  have LPositive : 0 < L := denseLipschitzBound_pos p (nearbyAmbient box)
  have bandLe := eventBandRadius_le_half_interior squarefree clearance
  have interiorLe : boundaryInteriorRadius p box clearance ≤
      clearance.bound / (256 * L) := min_le_right _ _
  have scaled : clearance.bound / (512 * L) ≤ target := by
    apply (div_le_iff₀ (mul_pos (by norm_num) LPositive)).2
    dsimp only [L] at boundLe ⊢
    nlinarith
  dsimp only [L] at interiorLe scaled ⊢
  calc
    eventBandRadius squarefree clearance ≤
        boundaryInteriorRadius p box clearance / 2 := bandLe
    _ ≤ (clearance.bound / (256 * denseLipschitzBound p
          (nearbyAmbient box))) / 2 := by gcongr
    _ = clearance.bound /
        (512 * denseLipschitzBound p (nearbyAmbient box)) := by ring
    _ ≤ target := scaled

theorem eventBandRadius_taylor
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    300 * denseTaylorRemainderBound p box *
        eventBandRadius squarefree clearance ^ 2 <
      LocalExtraction.derivativeMargin squarefree box := by
  let radius := eventBandRadius squarefree clearance
  let eta := LocalExtraction.derivativeMargin squarefree box
  let remainder := denseTaylorRemainderBound p box
  have radiusPositive : 0 < radius := eventBandRadius_pos squarefree clearance
  have radiusLeOne : radius ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have radiusLeRatio : radius ≤ eta / (600 * remainder) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have remainderPositive : 0 < remainder :=
    denseTaylorRemainderBound_pos p box
  have scaled : 600 * remainder * radius ≤ eta := by
    have := (le_div_iff₀ (mul_pos (by norm_num) remainderPositive)).mp
      radiusLeRatio
    nlinarith
  have squareLe : radius ^ 2 ≤ radius := by nlinarith
  dsimp only [radius, eta, remainder] at scaled squareLe ⊢
  nlinarith

/-- Squared-diagonal target ensuring the derivative threshold and the
Newton-displacement inequality for the fixed event band radius. -/
def eventSourceDiagonalThreshold
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  let radius := eventBandRadius squarefree clearance
  let L := denseLipschitzBound p box
  min (LocalExtraction.derivativeThreshold squarefree box / L)
    (LocalExtraction.derivativeMargin squarefree box * radius ^ 2 / (32 * L))

theorem eventSourceDiagonalThreshold_pos
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < eventSourceDiagonalThreshold squarefree clearance := by
  have radiusPositive := eventBandRadius_pos squarefree clearance
  have LPositive := denseLipschitzBound_pos p box
  exact lt_min
    (div_pos (LocalExtraction.derivativeThreshold_pos squarefree box) LPositive)
    (div_pos
      (mul_pos (LocalExtraction.derivativeMargin_pos squarefree box)
        (sq_pos_of_pos radiusPositive))
      (mul_pos (by norm_num) LPositive))

/-- Positive half-width of the source square.  The extra caps make it fit
well inside the event margin and avoid a square-root operation. -/
def eventSourceRadius
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  min (eventBandRadius squarefree clearance / 4)
    (min 1 (eventSourceDiagonalThreshold squarefree clearance / 16))

theorem eventSourceRadius_pos
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < eventSourceRadius squarefree clearance := by
  exact lt_min
    (div_pos (eventBandRadius_pos squarefree clearance) (by norm_num))
    (lt_min zero_lt_one
      (div_pos (eventSourceDiagonalThreshold_pos squarefree clearance)
        (by norm_num)))

theorem eventSourceRadius_le_band_quarter
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    eventSourceRadius squarefree clearance ≤
      eventBandRadius squarefree clearance / 4 :=
  min_le_left _ _

theorem eventSource_diagonal_le_threshold
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) (point : QI) :
    (centeredSourceSquare point (eventSourceRadius squarefree clearance)
      (eventSourceRadius_pos squarefree clearance).le).diagonalSq ≤
        eventSourceDiagonalThreshold squarefree clearance := by
  let sourceRadius := eventSourceRadius squarefree clearance
  let threshold := eventSourceDiagonalThreshold squarefree clearance
  have sourcePositive : 0 < sourceRadius :=
    eventSourceRadius_pos squarefree clearance
  have sourceLeOne : sourceRadius ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have sourceLeThreshold : sourceRadius ≤ threshold / 16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have squareLe : sourceRadius ^ 2 ≤ sourceRadius := by nlinarith
  rw [centeredSourceSquare_diagonalSq]
  dsimp only [sourceRadius, threshold] at *
  nlinarith

/-- Residual request for the event approximation.  The first cap supplies
boundary-interior geometry; the second is exactly the centered source
square's Lipschitz residual allowance. -/
def eventSourceResidualThreshold
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  min (clearance.bound / 16)
    (denseLipschitzBound p box *
      (8 * eventSourceRadius squarefree clearance ^ 2))

theorem eventSourceResidualThreshold_pos
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < eventSourceResidualThreshold squarefree clearance := by
  exact lt_min (div_pos clearance.positive (by norm_num))
    (mul_pos (denseLipschitzBound_pos p box)
      (mul_pos (by norm_num)
        (sq_pos_of_pos (eventSourceRadius_pos squarefree clearance))))

theorem eventSourceResidualThreshold_le_clearance
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    eventSourceResidualThreshold squarefree clearance ≤
      clearance.bound / 16 :=
  min_le_left _ _

theorem eventSourceResidualThreshold_le_sourceBound
    {p : GaussianPolynomial} {box : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    eventSourceResidualThreshold squarefree clearance ≤
      denseLipschitzBound p box *
        (8 * eventSourceRadius squarefree clearance ^ 2) :=
  min_le_right _ _

/-- The single common event-parameter width used by the direct source
construction. -/
def eventSourceApproximationWidth
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  cell.controlledApproximationWidth clearance
    (eventSourceResidualThreshold squarefree clearance)

theorem eventSourceApproximationWidth_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < eventSourceApproximationWidth cell squarefree clearance :=
  cell.controlledApproximationWidth_pos clearance
    (eventSourceResidualThreshold_pos squarefree clearance)

/-- Rational affine path point at the common narrowed event endpoint. -/
def eventSourcePoint
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : QI :=
  path.value
    (cell.clearedApproximation
      (eventSourceApproximationWidth cell squarefree clearance)
      (eventSourceApproximationWidth_pos cell squarefree clearance)).refined.interval.lower

theorem eventSourcePoint_pathDenominator_ne
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    path.denominator.eval (PathPolynomial.ofRat
      (cell.clearedApproximation
        (eventSourceApproximationWidth cell squarefree clearance)
        (eventSourceApproximationWidth_pos cell squarefree clearance)).refined.interval.lower) ≠
      0 := by
  let approximation := cell.clearedApproximation
    (eventSourceApproximationWidth cell squarefree clearance)
    (eventSourceApproximationWidth_pos cell squarefree clearance)
  apply cell.path_denominator_ne_on_cell
  · exact approximation.refines.1
  · exact approximation.refined.proper.le.trans approximation.refines.2

/-- Centered rational source square around the controlled event point. -/
def eventSourceBox
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : RatBox :=
  centeredSourceSquare (eventSourcePoint cell squarefree clearance)
    (eventSourceRadius squarefree clearance)
    (eventSourceRadius_pos squarefree clearance).le

@[simp] theorem eventSourceBox_center
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    (eventSourceBox cell squarefree clearance).center =
      eventSourcePoint cell squarefree clearance := by
  simp [eventSourceBox]

theorem eventSourcePoint_residual
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    normSq (p.eval (eventSourcePoint cell squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := by
  exact cell.controlledApproximation_residual_le clearance
    (eventSourceResidualThreshold_pos squarefree clearance)

theorem eventSourcePoint_deepInside
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    let point := eventSourcePoint cell squarefree clearance
    let radius := boundaryInteriorRadius p box clearance
    box.xLower + 4 * radius < point.re ∧
      point.re < box.xUpper - 4 * radius ∧
      box.yLower + 4 * radius < point.im ∧
      point.im < box.yUpper - 4 * radius := by
  exact cell.controlledApproximation_deepInside clearance
    (eventSourceResidualThreshold_pos squarefree clearance)
    (eventSourceResidualThreshold_le_clearance squarefree clearance)

theorem eventSourceBox_proper
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    (eventSourceBox cell squarefree clearance).Proper :=
  centeredSourceSquare_proper _ (eventSourceRadius_pos squarefree clearance)

theorem eventSourceBox_refines
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    (eventSourceBox cell squarefree clearance).Refines box := by
  let point := eventSourcePoint cell squarefree clearance
  let sourceRadius := eventSourceRadius squarefree clearance
  let bandRadius := eventBandRadius squarefree clearance
  let interiorRadius := boundaryInteriorRadius p box clearance
  have deep := eventSourcePoint_deepInside cell squarefree clearance
  have sourceLeBand : sourceRadius ≤ bandRadius / 4 :=
    eventSourceRadius_le_band_quarter squarefree clearance
  have bandLeInterior : bandRadius ≤ interiorRadius / 2 :=
    eventBandRadius_le_half_interior squarefree clearance
  have interiorPositive : 0 < interiorRadius :=
    boundaryInteriorRadius_pos p box clearance
  have sourceLeInterior : sourceRadius ≤ interiorRadius := by
    calc
      sourceRadius ≤ bandRadius / 4 := sourceLeBand
      _ ≤ interiorRadius / 8 := by linarith
      _ ≤ interiorRadius := by linarith
  change box.xLower + 4 * interiorRadius < point.re ∧
    point.re < box.xUpper - 4 * interiorRadius ∧
    box.yLower + 4 * interiorRadius < point.im ∧
    point.im < box.yUpper - 4 * interiorRadius at deep
  rcases deep with ⟨left, right, bottom, top⟩
  change box.xLower ≤ point.re - sourceRadius ∧
    point.re + sourceRadius ≤ box.xUpper ∧
    box.yLower ≤ point.im - sourceRadius ∧
    point.im + sourceRadius ≤ box.yUpper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem eventSourceBox_centerResidual
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    normSq (p.eval (eventSourceBox cell squarefree clearance).center) ≤
      centerResidualBound p box
        (eventSourceBox cell squarefree clearance) := by
  let sourceRadius := eventSourceRadius squarefree clearance
  have residual := eventSourcePoint_residual cell squarefree clearance
  have thresholdLe :=
    eventSourceResidualThreshold_le_sourceBound squarefree clearance
  rw [eventSourceBox_center]
  rw [centerResidualBound, eventSourceBox, centeredSourceSquare_diagonalSq]
  exact residual.trans thresholdLe

theorem eventSourceBox_centerResidual_le_derivativeThreshold
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    centerResidualBound p box (eventSourceBox cell squarefree clearance) ≤
      LocalExtraction.derivativeThreshold squarefree box := by
  let threshold := eventSourceDiagonalThreshold squarefree clearance
  let L := denseLipschitzBound p box
  have diagonalLe := eventSource_diagonal_le_threshold
    squarefree clearance (eventSourcePoint cell squarefree clearance)
  have thresholdLe : threshold ≤
      LocalExtraction.derivativeThreshold squarefree box / L :=
    min_le_left _ _
  have LPositive : 0 < L := denseLipschitzBound_pos p box
  have scaled : L * threshold ≤
      LocalExtraction.derivativeThreshold squarefree box := by
    have := (le_div_iff₀ LPositive).mp thresholdLe
    nlinarith
  calc
    centerResidualBound p box (eventSourceBox cell squarefree clearance) =
        L * (eventSourceBox cell squarefree clearance).diagonalSq := rfl
    _ ≤ L * threshold :=
      mul_le_mul_of_nonneg_left diagonalLe LPositive.le
    _ ≤ LocalExtraction.derivativeThreshold squarefree box := scaled

theorem eventSourceBox_newtonDisplacementBudget
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    centerResidualBound p box (eventSourceBox cell squarefree clearance) /
        LocalExtraction.derivativeMargin squarefree box <
      eventBandRadius squarefree clearance ^ 2 / 16 := by
  let source := eventSourceBox cell squarefree clearance
  let threshold := eventSourceDiagonalThreshold squarefree clearance
  let radius := eventBandRadius squarefree clearance
  let L := denseLipschitzBound p box
  let eta := LocalExtraction.derivativeMargin squarefree box
  have diagonalLe := eventSource_diagonal_le_threshold
    squarefree clearance (eventSourcePoint cell squarefree clearance)
  have thresholdLe : threshold ≤ eta * radius ^ 2 / (32 * L) :=
    min_le_right _ _
  have LPositive : 0 < L := denseLipschitzBound_pos p box
  have etaPositive : 0 < eta :=
    LocalExtraction.derivativeMargin_pos squarefree box
  have radiusPositive : 0 < radius := eventBandRadius_pos squarefree clearance
  have residualLe : centerResidualBound p box source ≤
      eta * radius ^ 2 / 32 := by
    calc
      centerResidualBound p box source = L * source.diagonalSq := rfl
      _ ≤ L * threshold :=
        mul_le_mul_of_nonneg_left diagonalLe LPositive.le
      _ ≤ L * (eta * radius ^ 2 / (32 * L)) :=
        mul_le_mul_of_nonneg_left thresholdLe LPositive.le
      _ = eta * radius ^ 2 / 32 := by
        field_simp [ne_of_gt LPositive]
  have divided : centerResidualBound p box source / eta ≤
      radius ^ 2 / 32 := by
    apply (div_le_iff₀ etaPositive).2
    calc
      centerResidualBound p box source ≤ eta * radius ^ 2 / 32 := residualLe
      _ = radius ^ 2 / 32 * eta := by ring
  dsimp only [source, threshold, radius, L, eta] at divided ⊢
  nlinarith [sq_pos_of_pos radiusPositive]

/-- Newton certificate seeded directly by the event approximation's explicit
residual, with no winding premise on the centered source square. -/
def eventNewtonCenter
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    NewtonCenterCertificate p box (eventSourceBox cell squarefree clearance)
      squarefree :=
  computeNewtonCenterOfResidual p squarefree
    (eventSourceBox_refines cell squarefree clearance)
    (eventSourceBox_centerResidual cell squarefree clearance)
    (eventSourceBox_centerResidual_le_derivativeThreshold
      cell squarefree clearance)

/-- The outer safe-band square around the computed Newton center remains in
the retained event box. -/
theorem eventNewtonBandSquareInside
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    BandSquareInside box
      (rationalNewtonCenter p (eventSourceBox cell squarefree clearance))
      (eventBandRadius squarefree clearance) := by
  let source := eventSourceBox cell squarefree clearance
  let point := eventSourcePoint cell squarefree clearance
  let newtonPoint := rationalNewtonCenter p source
  let radius := eventBandRadius squarefree clearance
  let interiorRadius := boundaryInteriorRadius p box clearance
  have radiusPositive : 0 < radius := eventBandRadius_pos squarefree clearance
  have radiusLeInterior : radius ≤ interiorRadius / 2 :=
    eventBandRadius_le_half_interior squarefree clearance
  have deep := eventSourcePoint_deepInside cell squarefree clearance
  change box.xLower + 4 * interiorRadius < point.re ∧
    point.re < box.xUpper - 4 * interiorRadius ∧
    box.yLower + 4 * interiorRadius < point.im ∧
    point.im < box.yUpper - 4 * interiorRadius at deep
  rcases deep with ⟨left, right, bottom, top⟩
  have displacement : normSq (newtonPoint - point) < radius ^ 2 / 16 := by
    have certified := (eventNewtonCenter cell squarefree clearance).displacement
    have budget := eventSourceBox_newtonDisplacementBudget
      cell squarefree clearance
    rw [(eventNewtonCenter cell squarefree clearance).point_eq] at certified
    have near := certified.trans_lt budget
    simpa only [source, point, newtonPoint, eventSourceBox_center] using near
  have coordinateDisplacement :
      -radius / 4 < newtonPoint.re - point.re ∧
        newtonPoint.re - point.re < radius / 4 ∧
        -radius / 4 < newtonPoint.im - point.im ∧
        newtonPoint.im - point.im < radius / 4 := by
    apply coordinate_bounds_of_sq_add_sq_lt radiusPositive
    simpa only [normSq, sub_re, sub_im] using displacement
  rcases coordinateDisplacement with ⟨xLower, xUpper, yLower, yUpper⟩
  constructor <;> linarith

/-- Four finite safe-axis searches now produce a genuine winding-one band
from the classified event approximation. -/
def extractEventBand
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    SafeNewtonBandOutput p box (eventSourceBox cell squarefree clearance) D
      (eventBandRadius squarefree clearance) :=
  selectSafeNewtonBand squarefree
    (eventNewtonCenter cell squarefree clearance)
    (eventSourceBox_refines cell squarefree clearance) elimination
    (eventBandRadius_pos squarefree clearance)
    (eventNewtonBandSquareInside cell squarefree clearance)
    (eventSourceBox_newtonDisplacementBudget cell squarefree clearance)
    (eventBandRadius_taylor squarefree clearance)

theorem extractedEventBand_strictInterior
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior
      (extractEventBand cell squarefree clearance elimination).band.box box := by
  let extracted := extractEventBand cell squarefree clearance elimination
  let center := rationalNewtonCenter p (eventSourceBox cell squarefree clearance)
  let radius := eventBandRadius squarefree clearance
  have inside := eventNewtonBandSquareInside cell squarefree clearance
  have leftSpec := leftCoordinate_spec extracted.elimination center
    extracted.radius_positive
  have rightSpec := rightCoordinate_spec extracted.elimination center
    extracted.radius_positive
  have bottomSpec := bottomCoordinate_spec extracted.elimination center
    extracted.radius_positive
  have topSpec := topCoordinate_spec extracted.elimination center
    extracted.radius_positive
  have leftStrict : center.re - 2 * radius < extracted.band.box.xLower := by
    simpa [extracted, SafeNewtonBandOutput.band, center, radius, selectedBand] using
      leftSpec.2.1
  have rightStrict : extracted.band.box.xUpper < center.re + 2 * radius := by
    simpa [extracted, SafeNewtonBandOutput.band, center, radius, selectedBand] using
      rightSpec.2.2
  have bottomStrict : center.im - 2 * radius < extracted.band.box.yLower := by
    simpa [extracted, SafeNewtonBandOutput.band, center, radius, selectedBand] using
      bottomSpec.2.1
  have topStrict : extracted.band.box.yUpper < center.im + 2 * radius := by
    simpa [extracted, SafeNewtonBandOutput.band, center, radius, selectedBand] using
      topSpec.2.2
  exact
    { left := inside.left.trans_lt leftStrict
      right := rightStrict.trans_le inside.right
      bottom := inside.bottom.trans_lt bottomStrict
      top := topStrict.trans_le inside.top }

/-- The rational classified-event point lies strictly inside the extracted
winding-one band. -/
theorem eventSourcePoint_strictContains_extractedBand
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (extractEventBand cell squarefree clearance elimination).band.box.StrictContains
      (eventSourcePoint cell squarefree clearance) := by
  let source := eventSourceBox cell squarefree clearance
  let point := eventSourcePoint cell squarefree clearance
  let newtonPoint := rationalNewtonCenter p source
  let radius := eventBandRadius squarefree clearance
  let extracted := extractEventBand cell squarefree clearance elimination
  let band := extracted.band
  have radiusPositive : 0 < radius := eventBandRadius_pos squarefree clearance
  have certified := (eventNewtonCenter cell squarefree clearance).displacement
  rw [(eventNewtonCenter cell squarefree clearance).point_eq] at certified
  have displacement : normSq (newtonPoint - point) < radius ^ 2 / 16 := by
    have near := certified.trans_lt
      (eventSourceBox_newtonDisplacementBudget cell squarefree clearance)
    simpa only [source, point, newtonPoint, radius, eventSourceBox_center] using near
  have coordinateDisplacement :=
    coordinate_bounds_of_sq_add_sq_lt radiusPositive (by
      simpa only [normSq, sub_re, sub_im] using displacement)
  rcases coordinateDisplacement with ⟨xLower, xUpper, yLower, yUpper⟩
  have leftBand := band.left_upper
  have rightBand := band.right_lower
  have bottomBand := band.bottom_upper
  have topBand := band.top_lower
  change band.box.xLower < point.re ∧ point.re < band.box.xUpper ∧
    band.box.yLower < point.im ∧ point.im < band.box.yUpper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Package the extracted event band as an ordinary winding-one state in any
larger ambient box containing the retained event box. -/
def eventWindingOneState
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneState p ambient := by
  let extracted := extractEventBand cell squarefree clearance elimination
  exact
    { box := extracted.band.box
      refinesAmbient := extracted.refines.trans boxRefines
      proper := extracted.band.proper extracted.radius_positive
      rawWindingFour := extracted.raw_winding_four
      clearance := extracted.boundaryClearance
      ambientLeftClearance := extracted.leftLineClearanceIn ambient
      ambientRightClearance := extracted.rightLineClearanceIn ambient
      ambientBottomClearance := extracted.bottomLineClearanceIn ambient
      ambientTopClearance := extracted.topLineClearanceIn ambient }

theorem eventWindingOneState_strictInterior
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior
      (eventWindingOneState boxRefines cell squarefree clearance elimination).box
      box := by
  change StrictInterior
    (extractEventBand cell squarefree clearance elimination).band.box box
  exact extractedEventBand_strictInterior cell squarefree clearance elimination

theorem eventWindingOneState_widthX_le
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (eventWindingOneState boxRefines cell squarefree clearance elimination).box.xUpper -
        (eventWindingOneState boxRefines cell squarefree clearance elimination).box.xLower ≤
      4 * eventBandRadius squarefree clearance := by
  let band := (extractEventBand cell squarefree clearance elimination).band
  change band.box.xUpper - band.box.xLower ≤
    4 * eventBandRadius squarefree clearance
  linarith [band.left_lower, band.right_upper]

theorem eventWindingOneState_widthY_le
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (eventWindingOneState boxRefines cell squarefree clearance elimination).box.yUpper -
        (eventWindingOneState boxRefines cell squarefree clearance elimination).box.yLower ≤
      4 * eventBandRadius squarefree clearance := by
  let band := (extractEventBand cell squarefree clearance elimination).band
  change band.box.yUpper - band.box.yLower ≤
    4 * eventBandRadius squarefree clearance
  linarith [band.bottom_lower, band.top_upper]

theorem eventWindingOneState_contains_sourcePoint
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (eventWindingOneState boxRefines cell squarefree clearance elimination).box.Contains
      (eventSourcePoint cell squarefree clearance) :=
  (eventSourcePoint_strictContains_extractedBand
    cell squarefree clearance elimination).contains

/-- Concrete refinement track seeded by the newly extracted event state. -/
def eventWindingOneTrack
    {p : GaussianPolynomial} {path : ProjectivePath.Path}
    {ambient box : RatBox} (boxRefines : box.Refines ambient)
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneTrack p ambient :=
  FTA.ConstructiveTrack.ofInitial squarefree elimination
    (eventWindingOneState boxRefines cell squarefree clearance elimination)

end CCLEventExtraction
end FTA
