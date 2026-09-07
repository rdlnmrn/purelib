import mathlib.Tactic.QuotientFreeRing
import RFAP.Newton.Extraction

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

namespace RFAP.NewtonBand

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev VerticalLineClearance :=
  RFAP.BoxClearance.VerticalLineClearance
abbrev HorizontalLineClearance :=
  RFAP.BoxClearance.HorizontalLineClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev RawWindingState := RFAP.RawSubdivision.RawWindingState

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PolynomialBounds
open RFAP.SafeCandidates
open RFAP.AxisSafeCuts
open RFAP.BoxClearance
open RFAP.GlobalWinding
open RFAP.Winding
open RFAP.WindingHomotopy
open RFAP.AffineWinding
open RFAP.LocalExtraction
open RFAP.NewtonWinding
open RFAP.NewtonExtraction
open RFAP.ProtectedBoundary

private theorem radius_lt_twice {r : Coordinate} (positive : 0 < r) :
    r < 2 * r := by
  calc
    r = 0 + r := by ring1
    _ < r + r :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct positive r
    _ = 2 * r := by ring1

private theorem sub_twice_lt_sub {c r : Coordinate} (positive : 0 < r) :
    c - 2 * r < c - r := by
  have negative := RFAP.ConstructiveFraction.neg_lt_neg_direct
    (radius_lt_twice positive)
  calc
    c - 2 * r = -(2 * r) + c := by ring1
    _ < -r + c :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct negative c
    _ = c - r := by ring1

private theorem add_lt_add_twice {c r : Coordinate} (positive : 0 < r) :
    c + r < c + 2 * r := by
  have enlarged := RFAP.ConstructiveFraction.add_lt_add_right_direct
    (radius_lt_twice positive) c
  simpa only [RFAP.ConstructiveFraction.add_comm] using enlarged

private theorem sub_lt_center {c r : Coordinate} (positive : 0 < r) :
    c - r < c := by
  have negative : -r < 0 := neg_neg_of_pos positive
  calc
    c - r = -r + c := by ring1
    _ < 0 + c :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct negative c
    _ = c := by ring1

private theorem center_lt_add {c r : Coordinate} (positive : 0 < r) :
    c < c + r := by
  have enlarged := RFAP.ConstructiveFraction.add_lt_add_right_direct positive c
  calc
    c = 0 + c := by ring1
    _ < r + c := enlarged
    _ = c + r := by ring1

/-- A rectangle whose four sides lie in the annular axis bands from distance
`r` through distance `2r` around `center`. -/
structure NewtonBandBox (center : Gaussian) (r : Coordinate) where
  box : Box
  left_lower : center.re - 2 * r ≤ box.xLower
  left_upper : box.xLower ≤ center.re - r
  right_lower : center.re + r ≤ box.xUpper
  right_upper : box.xUpper ≤ center.re + 2 * r
  bottom_lower : center.im - 2 * r ≤ box.yLower
  bottom_upper : box.yLower ≤ center.im - r
  top_lower : center.im + r ≤ box.yUpper
  top_upper : box.yUpper ≤ center.im + 2 * r

theorem NewtonBandBox.center_strictly_inside
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    (positive : 0 < r) :
    band.box.xLower < center.re ∧ center.re < band.box.xUpper ∧
      band.box.yLower < center.im ∧ center.im < band.box.yUpper :=
  ⟨band.left_upper.trans_lt (sub_lt_center positive),
    (center_lt_add positive).trans_le band.right_lower,
    band.bottom_upper.trans_lt (sub_lt_center positive),
    (center_lt_add positive).trans_le band.top_lower⟩

theorem NewtonBandBox.proper
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    (positive : 0 < r) : band.box.Proper := by
  have inside := band.center_strictly_inside positive
  exact ⟨inside.1.trans inside.2.1, inside.2.2.1.trans inside.2.2.2⟩

theorem NewtonBandBox.refines_outerSquare
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    (nonnegative : 0 ≤ r) :
    band.box.Refines
      (centeredSquare center (2 * r)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          nonnegative)) :=
  ⟨band.left_lower, band.right_upper,
    band.bottom_lower, band.top_upper⟩

/-- Both side lengths are at most `4r`. -/
theorem NewtonBandBox.diagonalSq_le
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    (positive : 0 < r) : band.box.diagonalSq ≤ 32 * r ^ 2 := by
  have widthXBound : band.box.widthX ≤ 4 * r := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_direct band.right_upper band.left_lower
    calc
      band.box.widthX = band.box.xUpper - band.box.xLower := rfl
      _ ≤ (center.re + 2 * r) - (center.re - 2 * r) := shifted
      _ = 4 * r := by ring1
  have widthYBound : band.box.widthY ≤ 4 * r := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_direct band.top_upper band.bottom_lower
    calc
      band.box.widthY = band.box.yUpper - band.box.yLower := rfl
      _ ≤ (center.im + 2 * r) - (center.im - 2 * r) := shifted
      _ = 4 * r := by ring1
  have fourRadiusNonnegative : 0 ≤ 4 * r :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le
  have widthXSquared := RFAP.ConstructiveFraction.pow_le_pow_direct
    band.box.widthX_nonneg widthXBound 2
  have widthYSquared := RFAP.ConstructiveFraction.pow_le_pow_direct
    band.box.widthY_nonneg widthYBound 2
  calc
    band.box.diagonalSq = band.box.widthX ^ 2 + band.box.widthY ^ 2 := rfl
    _ ≤ (4 * r) ^ 2 + (4 * r) ^ 2 :=
      add_le_add widthXSquared widthYSquared
    _ = 32 * r ^ 2 := by ring1

/-- The widest rectangle allowed by the Newton-band side constraints. -/
def widestNewtonBand (center : Gaussian) (r : Coordinate) (positive : 0 < r) :
    NewtonBandBox center r :=
  { box := centeredSquare center (2 * r)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le)
    left_lower := le_rfl
    left_upper := (sub_twice_lt_sub positive).le
    right_lower := (add_lt_add_twice positive).le
    right_upper := le_rfl
    bottom_lower := le_rfl
    bottom_upper := (sub_twice_lt_sub positive).le
    top_lower := (add_lt_add_twice positive).le
    top_upper := le_rfl }

/-- The coefficient `32` in `NewtonBandBox.diagonalSq_le` is attained by the
widest admissible band. -/
theorem widestNewtonBand_diagonalSq
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) :
    (widestNewtonBand center r positive).box.diagonalSq = 32 * r ^ 2 := by
  change
    (centeredSquare center (2 * r)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        positive.le)).diagonalSq = 32 * r ^ 2
  rw [centeredSquare_diagonalSq]
  ring1

/-- Accordingly the half-square coefficient exposed by extraction is exact
for the band geometry when the request is `8r`. -/
theorem widestNewtonBand_diagonalSq_eq_half_request
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) :
    (widestNewtonBand center r positive).box.diagonalSq =
      (1 / 2 : Coordinate) * (8 * r) ^ 2 := by
  rw [widestNewtonBand_diagonalSq]
  have coefficientIdentity : (1 / 2 : Coordinate) * 8 ^ 2 = 32 := by decide
  calc
    32 * r ^ 2 = ((1 / 2 : Coordinate) * 8 ^ 2) * r ^ 2 := by
      rw [coefficientIdentity]
    _ = (1 / 2 : Coordinate) * (8 * r) ^ 2 := by ring1

/-- Every point of the selected band is within squared distance `8r²` of its
center. -/
theorem NewtonBandBox.radial_upper
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    {z : Gaussian} (inside : band.box.Contains z) :
    normSq (z - center) ≤ 8 * r ^ 2 := by
  have realLower : -(2 * r) ≤ z.re - center.re := by
    calc
      -(2 * r) = center.re - 2 * r - center.re := by ring1
      _ ≤ z.re - center.re := RFAP.ConstructiveFraction.sub_le_sub_right_direct
        (band.left_lower.trans inside.1) center.re
  have realUpper : z.re - center.re ≤ 2 * r := by
    calc
      z.re - center.re ≤ center.re + 2 * r - center.re :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct (inside.2.1.trans band.right_upper) center.re
      _ = 2 * r := by ring1
  have imaginaryLower : -(2 * r) ≤ z.im - center.im := by
    calc
      -(2 * r) = center.im - 2 * r - center.im := by ring1
      _ ≤ z.im - center.im := RFAP.ConstructiveFraction.sub_le_sub_right_direct
        (band.bottom_lower.trans inside.2.2.1) center.im
  have imaginaryUpper : z.im - center.im ≤ 2 * r := by
    calc
      z.im - center.im ≤ center.im + 2 * r - center.im :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct (inside.2.2.2.trans band.top_upper) center.im
      _ = 2 * r := by ring1
  have realSquare := RFAP.Boxes.Box.sq_le_endpoint_max
    realLower realUpper
  have imaginarySquare := RFAP.Boxes.Box.sq_le_endpoint_max
    imaginaryLower imaginaryUpper
  have endpointSquare : (-(2 * r)) ^ 2 = (2 * r) ^ 2 := by ring1
  rw [endpointSquare, max_self] at realSquare imaginarySquare
  calc
    normSq (z - center) =
        (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 := rfl
    _ ≤ (2 * r) ^ 2 + (2 * r) ^ 2 :=
      add_le_add realSquare imaginarySquare
    _ = 8 * r ^ 2 := by ring1

/-- Every boundary point is at squared distance at least `r²` from the
center. -/
theorem NewtonBandBox.radial_lower
    {center : Gaussian} {r : Coordinate} (band : NewtonBandBox center r)
    (nonnegative : 0 ≤ r) {z : Gaussian}
    (boundary : OnBoxBoundary band.box z) :
    r ^ 2 ≤ normSq (z - center) := by
  rcases boundary.2 with onLeft | onRight | onBottom | onTop
  · have distance : r ≤ center.re - z.re := by
      calc
        r = center.re - (center.re - r) := by ring1
        _ ≤ center.re - band.box.xLower :=
          RFAP.ConstructiveFraction.sub_le_sub_left_direct band.left_upper center.re
        _ = center.re - z.re := by rw [onLeft]
    have square := RFAP.ConstructiveFraction.pow_le_pow_direct
      nonnegative distance 2
    calc
      r ^ 2 ≤ (center.re - z.re) ^ 2 := square
      _ = (z.re - center.re) ^ 2 := by ring1
      _ ≤ (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  · have distance : r ≤ z.re - center.re := by
      calc
        r = center.re + r - center.re := by ring1
        _ ≤ band.box.xUpper - center.re :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct band.right_lower center.re
        _ = z.re - center.re := by rw [onRight]
    have square := RFAP.ConstructiveFraction.pow_le_pow_direct
      nonnegative distance 2
    exact square.trans (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))
  · have distance : r ≤ center.im - z.im := by
      calc
        r = center.im - (center.im - r) := by ring1
        _ ≤ center.im - band.box.yLower :=
          RFAP.ConstructiveFraction.sub_le_sub_left_direct band.bottom_upper center.im
        _ = center.im - z.im := by rw [onBottom]
    have square := RFAP.ConstructiveFraction.pow_le_pow_direct
      nonnegative distance 2
    calc
      r ^ 2 ≤ (center.im - z.im) ^ 2 := square
      _ = (z.im - center.im) ^ 2 := by ring1
      _ ≤ (z.re - center.re) ^ 2 + (z.im - center.im) ^ 2 :=
        le_add_of_nonneg_left
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  · have distance : r ≤ z.im - center.im := by
      calc
        r = center.im + r - center.im := by ring1
        _ ≤ band.box.yUpper - center.im :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct band.top_lower center.im
        _ = z.im - center.im := by rw [onTop]
    have square := RFAP.ConstructiveFraction.pow_le_pow_direct
      nonnegative distance 2
    exact square.trans (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))

def leftCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) : Coordinate :=
  centralSearchValue elimination.vertical degreeBound
    (a := center.re - 2 * r) (b := center.re - r)
    (sub_twice_lt_sub (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

def rightCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) : Coordinate :=
  centralSearchValue elimination.vertical degreeBound
    (a := center.re + r) (b := center.re + 2 * r)
    (add_lt_add_twice (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

def bottomCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) : Coordinate :=
  centralSearchValue elimination.horizontal degreeBound
    (a := center.im - 2 * r) (b := center.im - r)
    (sub_twice_lt_sub (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

def topCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) : Coordinate :=
  centralSearchValue elimination.horizontal degreeBound
    (a := center.im + r) (b := center.im + 2 * r)
    (add_lt_add_twice (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

theorem leftCoordinate_spec {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.vertical.eval
        (leftCoordinate elimination center r positive) ≠ 0 ∧
      center.re - 2 * r < leftCoordinate elimination center r positive ∧
      leftCoordinate elimination center r positive < center.re - r := by
  exact centralSearchValue_spec elimination.vertical degreeBound
    (a := center.re - 2 * r) (b := center.re - r)
    (sub_twice_lt_sub (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

theorem rightCoordinate_spec {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.vertical.eval
        (rightCoordinate elimination center r positive) ≠ 0 ∧
      center.re + r < rightCoordinate elimination center r positive ∧
      rightCoordinate elimination center r positive < center.re + 2 * r := by
  exact centralSearchValue_spec elimination.vertical degreeBound
    (a := center.re + r) (b := center.re + 2 * r)
    (add_lt_add_twice (c := center.re) positive) elimination.vertical_nonzero
    elimination.vertical_degree

theorem bottomCoordinate_spec {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.horizontal.eval
        (bottomCoordinate elimination center r positive) ≠ 0 ∧
      center.im - 2 * r < bottomCoordinate elimination center r positive ∧
      bottomCoordinate elimination center r positive < center.im - r := by
  exact centralSearchValue_spec elimination.horizontal degreeBound
    (a := center.im - 2 * r) (b := center.im - r)
    (sub_twice_lt_sub (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

theorem topCoordinate_spec {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.horizontal.eval
        (topCoordinate elimination center r positive) ≠ 0 ∧
      center.im + r < topCoordinate elimination center r positive ∧
      topCoordinate elimination center r positive < center.im + 2 * r := by
  exact centralSearchValue_spec elimination.horizontal degreeBound
    (a := center.im + r) (b := center.im + 2 * r)
    (add_lt_add_twice (c := center.im) positive)
    elimination.horizontal_nonzero
    elimination.horizontal_degree

/-- Execute all four bounded safe-coordinate searches. -/
def selectedBand {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) (r : Coordinate) (positive : 0 < r) :
    NewtonBandBox center r := by
  have left := leftCoordinate_spec elimination center positive
  have right := rightCoordinate_spec elimination center positive
  have bottom := bottomCoordinate_spec elimination center positive
  have top := topCoordinate_spec elimination center positive
  exact
    { box :=
        { xLower := leftCoordinate elimination center r positive
          xUpper := rightCoordinate elimination center r positive
          yLower := bottomCoordinate elimination center r positive
          yUpper := topCoordinate elimination center r positive
          x_valid := (left.2.2.trans
            ((sub_lt_center positive).trans
              ((center_lt_add positive).trans right.2.1))).le
          y_valid := (bottom.2.2.trans
            ((sub_lt_center positive).trans
              ((center_lt_add positive).trans top.2.1))).le }
      left_lower := left.2.1.le
      left_upper := left.2.2.le
      right_lower := right.2.1.le
      right_upper := right.2.2.le
      bottom_lower := bottom.2.1.le
      bottom_upper := bottom.2.2.le
      top_lower := top.2.1.le
      top_upper := top.2.2.le }

theorem selectedBand_left_nonzero
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.vertical.eval
      (selectedBand elimination center r positive).box.xLower ≠ 0 := by
  simpa only [selectedBand] using
    (leftCoordinate_spec elimination center positive).1

theorem selectedBand_right_nonzero
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.vertical.eval
      (selectedBand elimination center r positive).box.xUpper ≠ 0 := by
  simpa only [selectedBand] using
    (rightCoordinate_spec elimination center positive).1

theorem selectedBand_bottom_nonzero
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.horizontal.eval
      (selectedBand elimination center r positive).box.yLower ≠ 0 := by
  simpa only [selectedBand] using
    (bottomCoordinate_spec elimination center positive).1

theorem selectedBand_top_nonzero
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (center : Gaussian) {r : Coordinate} (positive : 0 < r) :
    elimination.horizontal.eval
      (selectedBand elimination center r positive).box.yUpper ≠ 0 := by
  simpa only [selectedBand] using
    (topCoordinate_spec elimination center positive).1

def selectedBandLeftClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian) {r : Coordinate}
    (positive : 0 < r) : VerticalLineClearance p ambient
      (selectedBand elimination center r positive).box.xLower := by
  apply verticalOfCoprime p ambient
  simpa only [verticalPathReal, verticalPathImag] using
    elimination.vertical_coprime _
      (selectedBand_left_nonzero elimination center positive)

def selectedBandRightClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian) {r : Coordinate}
    (positive : 0 < r) : VerticalLineClearance p ambient
      (selectedBand elimination center r positive).box.xUpper := by
  apply verticalOfCoprime p ambient
  simpa only [verticalPathReal, verticalPathImag] using
    elimination.vertical_coprime _
      (selectedBand_right_nonzero elimination center positive)

def selectedBandBottomClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian) {r : Coordinate}
    (positive : 0 < r) : HorizontalLineClearance p ambient
      (selectedBand elimination center r positive).box.yLower := by
  apply horizontalOfCoprime p ambient
  simpa only [horizontalPathReal, horizontalPathImag] using
    elimination.horizontal_coprime _
      (selectedBand_bottom_nonzero elimination center positive)

def selectedBandTopClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (ambient : Box) (center : Gaussian) {r : Coordinate}
    (positive : 0 < r) : HorizontalLineClearance p ambient
      (selectedBand elimination center r positive).box.yUpper := by
  apply horizontalOfCoprime p ambient
  simpa only [horizontalPathReal, horizontalPathImag] using
    elimination.horizontal_coprime _
      (selectedBand_top_nonzero elimination center positive)

private theorem extractionBandTaylorCoefficient_pos :
    0 < extractionBandTaylorCoefficient := by
  unfold extractionBandTaylorCoefficient
  have fourPositive : (0 : Coordinate) < 4 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide)
  have ninePositive : (0 : Coordinate) < 9 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 9) (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct fourPositive ninePositive)
    ninePositive

/-- A band point and an `r²` Newton displacement are together within
`18r²` of the source anchor. -/
theorem NewtonBandBox.normSq_sub_anchor_le
    {p : GaussianPolynomial} {source : Box} {r : Coordinate}
    (band : NewtonBandBox (anchorNewtonCenter p source) r)
    (displacementSmall : normSq
      (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian} (inside : band.box.Contains z) :
    normSq (z - source.anchor) ≤ 18 * r ^ 2 := by
  have radial := band.radial_upper inside
  have decomposition : z - source.anchor =
      (z - anchorNewtonCenter p source) +
        (anchorNewtonCenter p source - source.anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring1
  rw [decomposition]
  have sumBound := normSq_add_le_two
    (z - anchorNewtonCenter p source)
    (anchorNewtonCenter p source - source.anchor)
  calc
    normSq ((z - anchorNewtonCenter p source) +
        (anchorNewtonCenter p source - source.anchor)) ≤
        2 * (normSq (z - anchorNewtonCenter p source) +
          normSq (anchorNewtonCenter p source - source.anchor)) := sumBound
    _ ≤ 2 * (8 * r ^ 2 + r ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add radial displacementSmall) (by decide)
    _ = 18 * r ^ 2 := by ring1

/-- Coarse finite Taylor budget on a radius-two Newton band. -/
def bandErrorBudget (p : GaussianPolynomial) (ambient : Box)
    (r : Coordinate) : Coordinate :=
  extractionBandTaylorCoefficient * denseTaylorRemainderBound p ambient *
    (r ^ 2) ^ 2

theorem newtonError_le_bandBudget
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : RFAP.LocalExtraction.NewtonCenterCertificate
      p ambient source squarefree)
    (sourceRefines : source.Refines ambient) {r : Coordinate}
    (band : NewtonBandBox (anchorNewtonCenter p source) r)
    (targetRefines : band.box.Refines ambient)
    (displacementSmall : normSq
      (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian} (boundary : OnBoxBoundary band.box z) :
    normSq ((newtonError p source).eval z) ≤
      bandErrorBudget p ambient r := by
  have insideAmbient := targetRefines.contains boundary.1
  have distance := band.normSq_sub_anchor_le displacementSmall boundary.1
  have distanceSquared : normSq (z - source.anchor) ^ 2 ≤
      (18 * r ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (normSq_nonneg (z - source.anchor)) distance 2
  have rawError := normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    normSq ((newtonError p source).eval z) ≤
        denseTaylorRemainderBound p ambient *
          normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ denseTaylorRemainderBound p ambient * (18 * r ^ 2) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        distanceSquared (denseTaylorRemainderBound_pos p ambient).le
    _ = bandErrorBudget p ambient r := by
      unfold bandErrorBudget extractionBandTaylorCoefficient
      ring1

theorem newtonLinearization_band_boundary_lower
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : RFAP.LocalExtraction.NewtonCenterCertificate
      p ambient source squarefree)
    {r : Coordinate}
    (band : NewtonBandBox (anchorNewtonCenter p source) r)
    (radiusNonnegative : 0 ≤ r) {z : Gaussian}
    (boundary : OnBoxBoundary band.box z) :
    derivativeMargin squarefree ambient * r ^ 2 ≤
      normSq ((newtonLinearization p source).eval z) := by
  have radial := band.radial_lower radiusNonnegative boundary
  have productLower := RFAP.ConstructiveFraction.mul_le_mul_direct
    newton.derivativeLower radial
    (RFAP.ConstructiveFraction.sq_nonneg_direct r)
    (normSq_nonneg
      ((RFAP.ConstructiveGCD.derivative p).eval source.anchor))
  calc
    derivativeMargin squarefree ambient * r ^ 2 ≤
        normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) *
          normSq (z - anchorNewtonCenter p source) := productLower
    _ = normSq ((newtonLinearization p source).eval z) := by
      rw [newtonLinearization, affineCoordinate_eval, normSq_mul]

/-- Positive norm gap left after the complete band Taylor budget. -/
def bandDominanceMargin {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box)
    (r : Coordinate) : Coordinate :=
  derivativeMargin squarefree ambient * r ^ 2 -
    bandErrorBudget p ambient r

theorem bandDominanceMargin_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p) {r : Coordinate}
    (positive : 0 < r)
    (taylorSmall :
      2 * (extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p ambient * r ^ 2) ≤
          derivativeMargin squarefree ambient) :
    0 < bandDominanceMargin squarefree ambient r := by
  let base := extractionBandTaylorCoefficient *
    denseTaylorRemainderBound p ambient * r ^ 2
  have radiusSquarePositive :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  have basePositive : 0 < base :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct
        extractionBandTaylorCoefficient_pos
        (denseTaylorRemainderBound_pos p ambient))
      radiusSquarePositive
  have baseStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have baseBelowMargin : base < derivativeMargin squarefree ambient :=
    baseStrict.trans_le taylorSmall
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    baseBelowMargin radiusSquarePositive
  apply RFAP.ConstructiveFraction.sub_pos_direct
  change bandErrorBudget p ambient r <
    derivativeMargin squarefree ambient * r ^ 2
  calc
    bandErrorBudget p ambient r = base * r ^ 2 := by
      dsimp only [bandErrorBudget, base]
      ring1
    _ < derivativeMargin squarefree ambient * r ^ 2 := scaled

private theorem gap_le_gap
    {eta budget error linear : Coordinate}
    (errorBound : error ≤ budget) (linearBound : eta ≤ linear) :
    eta - budget ≤ linear - error := by
  apply (le_sub_iff_add_le).mpr
  calc
    eta - budget + error ≤ eta - budget + budget :=
      add_le_add_right errorBound _
    _ = eta := by ring1
    _ ≤ linear := linearBound

/-- Finite Taylor dominance on every side of a selected Newton band. -/
def newtonBandBoundaryNormDominance
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : RFAP.LocalExtraction.NewtonCenterCertificate
      p ambient source squarefree)
    (sourceRefines : source.Refines ambient) {r : Coordinate}
    (positive : 0 < r)
    (band : NewtonBandBox (anchorNewtonCenter p source) r)
    (targetRefines : band.box.Refines ambient)
    (displacementSmall : normSq
      (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p ambient * r ^ 2) ≤
          derivativeMargin squarefree ambient) :
    BoundaryNormDominance
      (newtonLinearization p source) (newtonError p source) band.box where
  margin := bandDominanceMargin squarefree ambient r
  positive := bandDominanceMargin_pos squarefree positive taylorSmall
  lower := by
    intro z boundary
    exact gap_le_gap
      (newtonError_le_bandBudget newton sourceRefines band targetRefines
        displacementSmall boundary)
      (newtonLinearization_band_boundary_lower newton band positive.le
        boundary)

/-- The eliminant-safe Newton band has raw winding four. -/
theorem quadrupledBoxWinding_eq_four_of_newtonBand
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : RFAP.LocalExtraction.NewtonCenterCertificate
      p ambient source squarefree)
    (sourceRefines : source.Refines ambient) {r : Coordinate}
    (positive : 0 < r)
    (band : NewtonBandBox (anchorNewtonCenter p source) r)
    (targetRefines : band.box.Refines ambient)
    (displacementSmall : normSq
      (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (extractionBandTaylorCoefficient *
        denseTaylorRemainderBound p ambient * r ^ 2) ≤
          derivativeMargin squarefree ambient) :
    quadrupledBoxWinding p band.box = 4 := by
  have centerInside := band.center_strictly_inside positive
  have proper := band.proper positive
  let affineClearance : BoundaryClearance
      (newtonLinearization p source) band.box := by
    simpa only [newtonLinearization] using
      affineCoordinate_boundaryClearanceBox newton.derivativeNonzero
        (anchorNewtonCenter p source) centerInside.1 centerInside.2.1
        centerInside.2.2.1 centerInside.2.2.2
  let dominance := newtonBandBoundaryNormDominance newton sourceRefines
    positive band targetRefines displacementSmall taylorSmall
  have transfer := quadrupledBoxWinding_add_of_boundaryNormDominance
    (newtonLinearization p source) (newtonError p source) band.box proper
    affineClearance dominance
  have sumIdentity := newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at transfer
  calc
    quadrupledBoxWinding p band.box =
        quadrupledBoxWinding p.normalize band.box :=
      (quadrupledBoxWinding_normalize p band.box).symm
    _ = quadrupledBoxWinding (newtonLinearization p source) band.box :=
      transfer
    _ = 4 := by
      simpa only [newtonLinearization] using
        quadrupledBoxWinding_affineCoordinate newton.derivativeNonzero
          (anchorNewtonCenter p source) centerInside.1 centerInside.2.1
          centerInside.2.2.1 centerInside.2.2.2

/-! ## Complete executable safe-band extraction -/

/-- A strictly nested winding-four band together with four full-line
clearances in both the current and fixed ambient boxes. -/
structure Output
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : RawWindingState p ambient) (epsilon : Coordinate) where
  source : RawWindingState p current.box
  radius : Coordinate
  radiusPositive : 0 < radius
  band : NewtonBandBox (anchorNewtonCenter p source.box) radius
  newton : RFAP.LocalExtraction.NewtonCenterCertificate
    p current.box source.box squarefree
  displacementSmall : normSq
    (anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  strictCurrent : band.box.StrictInterior current.box
  refinesAmbient : band.box.Refines ambient
  proper : band.box.Proper
  leftLineClearance : VerticalLineClearance p current.box band.box.xLower
  rightLineClearance : VerticalLineClearance p current.box band.box.xUpper
  bottomLineClearance : HorizontalLineClearance p current.box band.box.yLower
  topLineClearance : HorizontalLineClearance p current.box band.box.yUpper
  ambientLeftClearance : VerticalLineClearance p ambient band.box.xLower
  ambientRightClearance : VerticalLineClearance p ambient band.box.xUpper
  ambientBottomClearance : HorizontalLineClearance p ambient band.box.yLower
  ambientTopClearance : HorizontalLineClearance p ambient band.box.yUpper
  clearance : BoundaryClearance p band.box
  rawWindingFour : quadrupledBoxWinding p band.box = 4
  diagonalSq_le_half :
    band.box.diagonalSq ≤ (1 / 2 : Coordinate) * epsilon ^ 2
  diagonalSq_le : band.box.diagonalSq ≤ epsilon ^ 2

def Output.box
    {p : GaussianPolynomial} {ambient : Box}
    {squarefree : SquarefreeCertificate p}
    {current : RawWindingState p ambient} {epsilon : Coordinate}
    (output : Output squarefree current epsilon) : Box :=
  output.band.box

/-- Run source refinement, Newton computation, and four bounded eliminant
searches to obtain a globally partition-safe winding-four box. -/
def extract
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) : Output squarefree current epsilon := by
  let core := RFAP.NewtonExtraction.extract degreeAtLeastTwo
    squarefree elimination current epsilonPositive
  let source := core.source
  let r := extractionRadius squarefree current.box current.clearance epsilon
  let center := anchorNewtonCenter p source.box
  have radiusPositive : 0 < r :=
    extractionRadius_pos squarefree current.clearance current.proper
      epsilonPositive
  let band := selectedBand elimination center r radiusPositive
  have twoPositive : (0 : Coordinate) < 2 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 2) (by decide)
  have twiceRadiusPositive : 0 < 2 * r :=
    RFAP.ConstructiveFraction.mul_pos_direct twoPositive radiusPositive
  have twiceRadiusNonnegative : 0 ≤ 2 * r := twiceRadiusPositive.le
  have twiceRadiusLeProtected :
      2 * r ≤ protectedBoundaryRadius p current.box current.clearance :=
    extractionRadius_twice_le_protected squarefree current.box
      current.clearance epsilon
  have radiusLeTwice : r ≤ 2 * r := (radius_lt_twice radiusPositive).le
  have radiusSquareLeTwice : r ^ 2 ≤ (2 * r) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radiusLeTwice 2
  have displacementForOuter :
      normSq (center - source.box.anchor) ≤ (2 * r) ^ 2 :=
    core.displacementSmall.trans radiusSquareLeTwice
  let outerSquare := centeredSquare center (2 * r) twiceRadiusNonnegative
  have outerStrict : outerSquare.StrictInterior current.box :=
    centeredSquare_strictInterior twiceRadiusPositive
      twiceRadiusLeProtected core.stripBounds displacementForOuter
  have bandRefinesOuter : band.box.Refines outerSquare := by
    exact band.refines_outerSquare radiusPositive.le
  have bandStrict : band.box.StrictInterior current.box :=
    outerStrict.of_refines bandRefinesOuter
  have bandRefinesCurrent : band.box.Refines current.box := bandStrict.refines
  have bandRefinesAmbient : band.box.Refines ambient :=
    bandRefinesCurrent.trans current.refinesAmbient
  have bandProper : band.box.Proper := band.proper radiusPositive
  let leftLine := selectedBandLeftClearance elimination current.box center
    radiusPositive
  let rightLine := selectedBandRightClearance elimination current.box center
    radiusPositive
  let bottomLine := selectedBandBottomClearance elimination current.box center
    radiusPositive
  let topLine := selectedBandTopClearance elimination current.box center
    radiusPositive
  let ambientLeftLine := selectedBandLeftClearance elimination ambient center
    radiusPositive
  let ambientRightLine := selectedBandRightClearance elimination ambient center
    radiusPositive
  let ambientBottomLine := selectedBandBottomClearance elimination ambient center
    radiusPositive
  let ambientTopLine := selectedBandTopClearance elimination ambient center
    radiusPositive
  let bandClearance : BoundaryClearance p band.box := boundaryOfLines
    (VerticalLineClearance.restrict leftLine bandRefinesCurrent)
    (VerticalLineClearance.restrict rightLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict bottomLine bandRefinesCurrent)
    (HorizontalLineClearance.restrict topLine bandRefinesCurrent)
  have windingFour : quadrupledBoxWinding p band.box = 4 :=
    quadrupledBoxWinding_eq_four_of_newtonBand degreeAtLeastTwo core.newton
      source.refinesAmbient radiusPositive band bandRefinesCurrent
      core.displacementSmall core.bandTaylorSmall
  have radiusEighth : r ≤ (1 / 8 : Coordinate) * epsilon :=
    extractionRadius_le_eighth squarefree current.box current.clearance epsilon
  have radiusSquare : r ^ 2 ≤ ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radiusEighth 2
  have thirtyTwoNonnegative : (0 : Coordinate) ≤ 32 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 32) (by decide)).le
  have epsilonSquareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct epsilon
  have halfSquare : (1 / 2 : Coordinate) * epsilon ^ 2 ≤ epsilon ^ 2 := by
    calc
      (1 / 2 : Coordinate) * epsilon ^ 2 ≤ 1 * epsilon ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 / 2 : Coordinate) ≤ 1 by decide)
          epsilonSquareNonnegative
      _ = epsilon ^ 2 := by ring1
  have diagonalHalf :
      band.box.diagonalSq ≤ (1 / 2 : Coordinate) * epsilon ^ 2 := by
    have coefficientIdentity :
        (32 : Coordinate) * (1 / 8) ^ 2 = 1 / 2 := by
      have eightNonzero : (8 : Coordinate) ≠ 0 :=
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 8) (by decide)).ne'
      have twoNonzero : (2 : Coordinate) ≠ 0 :=
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 2) (by decide)).ne'
      have eighthCancel : (1 / 8 : Coordinate) * 8 = 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 8 eightNonzero
      have halfCancel : (1 / 2 : Coordinate) * 2 = 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 2 twoNonzero
      apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne twoNonzero
      calc
        ((32 : Coordinate) * (1 / 8) ^ 2) * 2 =
            ((1 / 8 : Coordinate) * 8) * ((1 / 8) * 8) := by ring1
        _ = 1 := by rw [eighthCancel]; ring1
        _ = (1 / 2 : Coordinate) * 2 := halfCancel.symm
    calc
      band.box.diagonalSq ≤ 32 * r ^ 2 := band.diagonalSq_le radiusPositive
      _ ≤ 32 * ((1 / 8 : Coordinate) * epsilon) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusSquare thirtyTwoNonnegative
      _ = (32 * (1 / 8 : Coordinate) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 2 : Coordinate) * epsilon ^ 2 := by
        rw [coefficientIdentity]
  have diagonal : band.box.diagonalSq ≤ epsilon ^ 2 :=
    diagonalHalf.trans halfSquare
  exact
    { source := source
      radius := r
      radiusPositive := radiusPositive
      band := band
      newton := core.newton
      displacementSmall := core.displacementSmall
      strictCurrent := bandStrict
      refinesAmbient := bandRefinesAmbient
      proper := bandProper
      leftLineClearance := leftLine
      rightLineClearance := rightLine
      bottomLineClearance := bottomLine
      topLineClearance := topLine
      ambientLeftClearance := ambientLeftLine
      ambientRightClearance := ambientRightLine
      ambientBottomClearance := ambientBottomLine
      ambientTopClearance := ambientTopLine
      clearance := bandClearance
      rawWindingFour := windingFour
      diagonalSq_le_half := diagonalHalf
      diagonalSq_le := diagonal }

end RFAP.NewtonBand
