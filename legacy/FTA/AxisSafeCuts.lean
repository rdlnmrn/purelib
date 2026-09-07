import FTA.LocalExtraction
import FTA.BoxClearance
import FTA.PathClearance
import FTA.SafeCuts

/-!
# Resultant-certified safe Newton-band cuts

This module connects the bounded central-third search to the four rational
axis-parallel cuts used at the end of local extraction.  The elimination
certificate records exactly the output that the subsequent Sylvester
resultant construction must supply: two nonzero bounded-degree polynomials
and dense Bezout certificates for every specialization at which the relevant
eliminant is nonzero.

Given that finite certificate, all four searches below are total executable
computations.  Their selected coordinates lie in the prescribed Newton
bands, carry positive full-line clearance certificates inside the ambient
box, and bound a central rectangle of winding one.
-/

namespace FTA.AxisSafeCuts

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.BoxClearance
open ComputablePolynomial.DensePolynomial
open FTA.DenseSquarefree
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.PathClearance
open FTA.PathPolynomial
open FTA.SafeCandidates
open FTA.SafeCuts
open FTA.SturmTransducer
open FTA.Winding

abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ

/-- Dense real coordinate polynomial on the full vertical line `x + it`. -/
def verticalPathReal (p : GaussianPolynomial) (x : ℚ) : RatPolynomial :=
  pathReal p (verticalBase x) verticalDirection

/-- Dense imaginary coordinate polynomial on the full vertical line. -/
def verticalPathImag (p : GaussianPolynomial) (x : ℚ) : RatPolynomial :=
  pathImag p (verticalBase x) verticalDirection

/-- Dense real coordinate polynomial on the full horizontal line `t + iy`. -/
def horizontalPathReal (p : GaussianPolynomial) (y : ℚ) : RatPolynomial :=
  pathReal p (horizontalBase y) horizontalDirection

/-- Dense imaginary coordinate polynomial on the full horizontal line. -/
def horizontalPathImag (p : GaussianPolynomial) (y : ℚ) : RatPolynomial :=
  pathImag p (horizontalBase y) horizontalDirection

/-- Finite elimination data needed by the safe-axis search.  The two dense
polynomials are the eventual `Y`- and `X`-Sylvester resultants respectively;
the specialization fields expose their Bezout consequence in the executable
dense representation used by path clearance. -/
structure AxisEliminationCertificate (p : GaussianPolynomial) (D : ℕ) where
  vertical : RatPolynomial
  horizontal : RatPolynomial
  vertical_nonzero : vertical.toPolynomial ≠ 0
  horizontal_nonzero : horizontal.toPolynomial ≠ 0
  vertical_degree : vertical.toPolynomial.natDegree ≤ D
  horizontal_degree : horizontal.toPolynomial.natDegree ≤ D
  vertical_coprime : ∀ x : ℚ, vertical.eval x ≠ 0 →
    CoprimeCertificate (verticalPathReal p x) (verticalPathImag p x)
  horizontal_coprime : ∀ y : ℚ, horizontal.eval y ≠ 0 →
    CoprimeCertificate (horizontalPathReal p y) (horizontalPathImag p y)

/-- Total bounded search for a safe vertical coordinate in an arbitrary
nondegenerate rational interval. -/
def verticalSafeCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) : ℚ :=
  centralSearchValue certificate.vertical D hab
    certificate.vertical_nonzero certificate.vertical_degree

theorem verticalSafeCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) :
    certificate.vertical.eval (verticalSafeCoordinate certificate hab) ≠ 0 ∧
      a < verticalSafeCoordinate certificate hab ∧
      verticalSafeCoordinate certificate hab < b := by
  rcases centralSearchValue_spec certificate.vertical D hab
      certificate.vertical_nonzero certificate.vertical_degree with
    ⟨hne, hleft, hright⟩
  exact ⟨hne, (centralLeft_inside hab).trans hleft,
    hright.trans (centralRight_inside hab)⟩

/-- Total bounded search for a safe horizontal coordinate. -/
def horizontalSafeCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) : ℚ :=
  centralSearchValue certificate.horizontal D hab
    certificate.horizontal_nonzero certificate.horizontal_degree

theorem horizontalSafeCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) :
    certificate.horizontal.eval (horizontalSafeCoordinate certificate hab) ≠ 0 ∧
      a < horizontalSafeCoordinate certificate hab ∧
      horizontalSafeCoordinate certificate hab < b := by
  rcases centralSearchValue_spec certificate.horizontal D hab
      certificate.horizontal_nonzero certificate.horizontal_degree with
    ⟨hne, hleft, hright⟩
  exact ⟨hne, (centralLeft_inside hab).trans hleft,
    hright.trans (centralRight_inside hab)⟩

theorem verticalSafeCoordinate_contraction
    {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) :
    verticalSafeCoordinate certificate hab - a < (2 / 3 : ℚ) * (b - a) ∧
      b - verticalSafeCoordinate certificate hab < (2 / 3 : ℚ) * (b - a) := by
  have h := centralSearchValue_spec certificate.vertical D hab
    certificate.vertical_nonzero certificate.vertical_degree
  dsimp [centralLeft, centralRight] at h
  dsimp only [verticalSafeCoordinate]
  exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩

theorem horizontalSafeCoordinate_contraction
    {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {a b : ℚ}
    (hab : a < b) :
    horizontalSafeCoordinate certificate hab - a < (2 / 3 : ℚ) * (b - a) ∧
      b - horizontalSafeCoordinate certificate hab < (2 / 3 : ℚ) * (b - a) := by
  have h := centralSearchValue_spec certificate.horizontal D hab
    certificate.horizontal_nonzero certificate.horizontal_degree
  dsimp [centralLeft, centralRight] at h
  dsimp only [horizontalSafeCoordinate]
  exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩

def leftCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) (r : ℚ)
    (hr : 0 < r) : ℚ :=
  verticalSafeCoordinate certificate (by linarith : center.re - 2 * r < center.re - r)

def rightCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) (r : ℚ)
    (hr : 0 < r) : ℚ :=
  verticalSafeCoordinate certificate (by linarith : center.re + r < center.re + 2 * r)

def bottomCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) (r : ℚ)
    (hr : 0 < r) : ℚ :=
  horizontalSafeCoordinate certificate (by linarith : center.im - 2 * r < center.im - r)

def topCoordinate {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) (r : ℚ)
    (hr : 0 < r) : ℚ :=
  horizontalSafeCoordinate certificate (by linarith : center.im + r < center.im + 2 * r)

theorem leftCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.vertical.eval (leftCoordinate certificate center r hr) ≠ 0 ∧
      center.re - 2 * r < leftCoordinate certificate center r hr ∧
      leftCoordinate certificate center r hr < center.re - r := by
  unfold leftCoordinate
  exact verticalSafeCoordinate_spec certificate (by linarith)

theorem rightCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.vertical.eval (rightCoordinate certificate center r hr) ≠ 0 ∧
      center.re + r < rightCoordinate certificate center r hr ∧
      rightCoordinate certificate center r hr < center.re + 2 * r := by
  unfold rightCoordinate
  exact verticalSafeCoordinate_spec certificate (by linarith)

theorem bottomCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.horizontal.eval (bottomCoordinate certificate center r hr) ≠ 0 ∧
      center.im - 2 * r < bottomCoordinate certificate center r hr ∧
      bottomCoordinate certificate center r hr < center.im - r := by
  unfold bottomCoordinate
  exact horizontalSafeCoordinate_spec certificate (by linarith)

theorem topCoordinate_spec {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.horizontal.eval (topCoordinate certificate center r hr) ≠ 0 ∧
      center.im + r < topCoordinate certificate center r hr ∧
      topCoordinate certificate center r hr < center.im + 2 * r := by
  unfold topCoordinate
  exact horizontalSafeCoordinate_spec certificate (by linarith)

/-- The rational central rectangle computed by the four bounded searches. -/
def selectedBand {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) (r : ℚ)
    (hr : 0 < r) : NewtonBandBox center r := by
  have hleft := leftCoordinate_spec certificate center hr
  have hright := rightCoordinate_spec certificate center hr
  have hbottom := bottomCoordinate_spec certificate center hr
  have htop := topCoordinate_spec certificate center hr
  exact
    { box :=
        { xLower := leftCoordinate certificate center r hr
          xUpper := rightCoordinate certificate center r hr
          yLower := bottomCoordinate certificate center r hr
          yUpper := topCoordinate certificate center r hr
          x_valid := by linarith [hleft.2.2, hright.2.1]
          y_valid := by linarith [hbottom.2.2, htop.2.1] }
      left_lower := hleft.2.1.le
      left_upper := hleft.2.2.le
      right_lower := hright.2.1.le
      right_upper := hright.2.2.le
      bottom_lower := hbottom.2.1.le
      bottom_upper := hbottom.2.2.le
      top_lower := htop.2.1.le
      top_upper := htop.2.2.le }

/-- The outer `2r` square around the Newton center lies in the ambient box. -/
structure BandSquareInside (ambient : CCL.RatBox) (center : QI) (r : ℚ) : Prop where
  left : ambient.xLower ≤ center.re - 2 * r
  right : center.re + 2 * r ≤ ambient.xUpper
  bottom : ambient.yLower ≤ center.im - 2 * r
  top : center.im + 2 * r ≤ ambient.yUpper

theorem selectedBand_refines {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) {ambient : CCL.RatBox}
    (center : QI) {r : ℚ} (hr : 0 < r)
    (inside : BandSquareInside ambient center r) :
    (selectedBand certificate center r hr).box.Refines ambient := by
  let band := selectedBand certificate center r hr
  exact ⟨inside.left.trans band.left_lower,
    band.right_upper.trans inside.right,
    inside.bottom.trans band.bottom_lower,
    band.top_upper.trans inside.top⟩

def verticalInterval (ambient : CCL.RatBox) : RationalInterval :=
  ⟨ambient.yLower, ambient.yUpper⟩

def horizontalInterval (ambient : CCL.RatBox) : RationalInterval :=
  ⟨ambient.xLower, ambient.xUpper⟩

theorem selectedBand_left_nonzero {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.vertical.eval
      (selectedBand certificate center r hr).box.xLower ≠ 0 := by
  simpa [selectedBand] using (leftCoordinate_spec certificate center hr).1

theorem selectedBand_right_nonzero {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.vertical.eval
      (selectedBand certificate center r hr).box.xUpper ≠ 0 := by
  simpa [selectedBand] using (rightCoordinate_spec certificate center hr).1

theorem selectedBand_bottom_nonzero {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.horizontal.eval
      (selectedBand certificate center r hr).box.yLower ≠ 0 := by
  simpa [selectedBand] using (bottomCoordinate_spec certificate center hr).1

theorem selectedBand_top_nonzero {p : GaussianPolynomial} {D : ℕ}
    (certificate : AxisEliminationCertificate p D) (center : QI) {r : ℚ}
    (hr : 0 < r) :
    certificate.horizontal.eval
      (selectedBand certificate center r hr).box.yUpper ≠ 0 := by
  simpa [selectedBand] using (topCoordinate_spec certificate center hr).1

/-- Proof-bearing result of all four safe-line searches.  The selected band
and all four Bezout/clearance certificates are computed projections of the
stored finite elimination certificate. -/
structure SafeNewtonBandOutput (p : GaussianPolynomial)
    (ambient source : CCL.RatBox) (D : ℕ) (r : ℚ) where
  radius_positive : 0 < r
  elimination : AxisEliminationCertificate p D
  refines :
    (selectedBand elimination (rationalNewtonCenter p source) r
      radius_positive).box.Refines ambient
  raw_winding_four : quadrupledBoxWinding p
    (selectedBand elimination (rationalNewtonCenter p source) r
      radius_positive).box = 4

def SafeNewtonBandOutput.band {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  selectedBand output.elimination (rationalNewtonCenter p source) r
    output.radius_positive

theorem SafeNewtonBandOutput.winding_one {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    boxWinding p output.band.box = 1 := by
  have hraw : quadrupledBoxWinding p output.band.box = 4 := by
    simpa only [SafeNewtonBandOutput.band] using output.raw_winding_four
  rw [boxWinding, hraw]
  norm_num

def SafeNewtonBandOutput.leftCoprime {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  output.elimination.vertical_coprime output.band.box.xLower
    (selectedBand_left_nonzero output.elimination
      (rationalNewtonCenter p source) output.radius_positive)

def SafeNewtonBandOutput.rightCoprime {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  output.elimination.vertical_coprime output.band.box.xUpper
    (selectedBand_right_nonzero output.elimination
      (rationalNewtonCenter p source) output.radius_positive)

def SafeNewtonBandOutput.bottomCoprime {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  output.elimination.horizontal_coprime output.band.box.yLower
    (selectedBand_bottom_nonzero output.elimination
      (rationalNewtonCenter p source) output.radius_positive)

def SafeNewtonBandOutput.topCoprime {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  output.elimination.horizontal_coprime output.band.box.yUpper
    (selectedBand_top_nonzero output.elimination
      (rationalNewtonCenter p source) output.radius_positive)

def SafeNewtonBandOutput.leftClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  certificateOfCoprime output.leftCoprime (verticalInterval ambient)

def SafeNewtonBandOutput.rightClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  certificateOfCoprime output.rightCoprime (verticalInterval ambient)

def SafeNewtonBandOutput.bottomClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  certificateOfCoprime output.bottomCoprime (horizontalInterval ambient)

def SafeNewtonBandOutput.topClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :=
  certificateOfCoprime output.topCoprime (horizontalInterval ambient)

def SafeNewtonBandOutput.leftLineClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    VerticalLineClearance p ambient output.band.box.xLower :=
  verticalOfPathCertificate p ambient output.band.box.xLower
    output.leftClearance

def SafeNewtonBandOutput.rightLineClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    VerticalLineClearance p ambient output.band.box.xUpper :=
  verticalOfPathCertificate p ambient output.band.box.xUpper
    output.rightClearance

def SafeNewtonBandOutput.bottomLineClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    HorizontalLineClearance p ambient output.band.box.yLower :=
  horizontalOfPathCertificate p ambient output.band.box.yLower
    output.bottomClearance

def SafeNewtonBandOutput.topLineClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    HorizontalLineClearance p ambient output.band.box.yUpper :=
  horizontalOfPathCertificate p ambient output.band.box.yUpper
    output.topClearance

/-- The eliminant nonvanishing proof is independent of the interval, so a
selected band side has positive clearance on any requested rational ambient
box. -/
def SafeNewtonBandOutput.leftLineClearanceIn {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r)
    (larger : CCL.RatBox) :
    VerticalLineClearance p larger output.band.box.xLower :=
  verticalOfPathCertificate p larger output.band.box.xLower
    (certificateOfCoprime output.leftCoprime (verticalInterval larger))

def SafeNewtonBandOutput.rightLineClearanceIn {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r)
    (larger : CCL.RatBox) :
    VerticalLineClearance p larger output.band.box.xUpper :=
  verticalOfPathCertificate p larger output.band.box.xUpper
    (certificateOfCoprime output.rightCoprime (verticalInterval larger))

def SafeNewtonBandOutput.bottomLineClearanceIn {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r)
    (larger : CCL.RatBox) :
    HorizontalLineClearance p larger output.band.box.yLower :=
  horizontalOfPathCertificate p larger output.band.box.yLower
    (certificateOfCoprime output.bottomCoprime (horizontalInterval larger))

def SafeNewtonBandOutput.topLineClearanceIn {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r)
    (larger : CCL.RatBox) :
    HorizontalLineClearance p larger output.band.box.yUpper :=
  horizontalOfPathCertificate p larger output.band.box.yUpper
    (certificateOfCoprime output.topCoprime (horizontalInterval larger))

/-- The minimum of the four safe-line margins is a single positive
clearance bound on the boundary of the selected Newton band. -/
def SafeNewtonBandOutput.boundaryClearance {p : GaussianPolynomial}
    {ambient source : CCL.RatBox} {D : ℕ} {r : ℚ}
    (output : SafeNewtonBandOutput p ambient source D r) :
    BoxBoundaryClearanceCertificate p output.band.box := by
  let left := output.leftClearance
  let right := output.rightClearance
  let bottom := output.bottomClearance
  let top := output.topClearance
  let bound := min left.bound (min right.bound (min bottom.bound top.bound))
  have hboundLeft : bound ≤ left.bound := min_le_left _ _
  have hboundRight : bound ≤ right.bound :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hboundBottom : bound ≤ bottom.bound :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hboundTop : bound ≤ top.bound :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact
    { bound := bound
      positive := lt_min left.positive
        (lt_min right.positive (lt_min bottom.positive top.positive))
      lower := by
        intro z hz
        have hzAmbient : ambient.Contains z := output.refines.contains hz.1
        rcases hz.2 with hleft | hright | hbottom | htop
        · have hline := left.lower z.im hzAmbient.2.2.1 hzAmbient.2.2.2
          have hpath :
              line (verticalBase output.band.box.xLower) verticalDirection z.im = z := by
            rw [line_vertical]
            ext
            · exact hleft.symm
            · rfl
          calc
            bound ≤ left.bound := hboundLeft
            _ ≤ normSq (p.eval z) := by
              simpa only [verticalPathReal, verticalPathImag, normSq,
                eval_pathReal, eval_pathImag, hpath] using hline
        · have hline := right.lower z.im hzAmbient.2.2.1 hzAmbient.2.2.2
          have hpath :
              line (verticalBase output.band.box.xUpper) verticalDirection z.im = z := by
            rw [line_vertical]
            ext
            · exact hright.symm
            · rfl
          calc
            bound ≤ right.bound := hboundRight
            _ ≤ normSq (p.eval z) := by
              simpa only [verticalPathReal, verticalPathImag, normSq,
                eval_pathReal, eval_pathImag, hpath] using hline
        · have hline := bottom.lower z.re hzAmbient.1 hzAmbient.2.1
          have hpath :
              line (horizontalBase output.band.box.yLower) horizontalDirection z.re = z := by
            rw [line_horizontal]
            ext
            · rfl
            · exact hbottom.symm
          calc
            bound ≤ bottom.bound := hboundBottom
            _ ≤ normSq (p.eval z) := by
              simpa only [horizontalPathReal, horizontalPathImag, normSq,
                eval_pathReal, eval_pathImag, hpath] using hline
        · have hline := top.lower z.re hzAmbient.1 hzAmbient.2.1
          have hpath :
              line (horizontalBase output.band.box.yUpper) horizontalDirection z.re = z := by
            rw [line_horizontal]
            ext
            · rfl
            · exact htop.symm
          calc
            bound ≤ top.bound := hboundTop
            _ ≤ normSq (p.eval z) := by
              simpa only [horizontalPathReal, horizontalPathImag, normSq,
                eval_pathReal, eval_pathImag, hpath] using hline }

/-- The four bounded eliminant searches, their positive full-cut clearance
certificates, and the local affine-dominance theorem assemble into the final
safe Newton-band rectangle of winding one. -/
def selectSafeNewtonBand
    {p : GaussianPolynomial} {ambient source : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (hsource : source.Refines ambient) {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    {r : ℚ} (hr : 0 < r)
    (inside : BandSquareInside ambient (rationalNewtonCenter p source) r)
    (hnear : centerResidualBound p ambient source /
        LocalExtraction.derivativeMargin squarefree ambient < r ^ 2 / 16)
    (htaylor : 300 * denseTaylorRemainderBound p ambient * r ^ 2 <
      LocalExtraction.derivativeMargin squarefree ambient) :
    SafeNewtonBandOutput p ambient source D r := by
  let center := rationalNewtonCenter p source
  let band := selectedBand elimination center r hr
  have hrefines : band.box.Refines ambient :=
    selectedBand_refines elimination center hr inside
  exact
    { radius_positive := hr
      elimination := elimination
      refines := hrefines
      raw_winding_four :=
        quadrupledBoxWinding_eq_four_of_newtonBandBox squarefree newton
        hsource hr band hrefines hnear htaylor }

end FTA.AxisSafeCuts
