import FTA.RawLocalExtraction
import FTA.RootTrackSeparation
import FTA.CentralBandGrid

/-!
# Constructive winding-one tracks

The complete local extraction theorem is stable under iteration because each
selected Newton band carries a new coefficient-computed boundary-clearance
certificate.  This module packages that iteration as the total finite
`WindingOneTrack` interface used by the separation and packing arguments.
-/

namespace FTA.ConstructiveTrack

open CCL
open FTA.AxisSafeCuts
open FTA.LocalExtraction
open FTA.RawLocalExtraction
open FTA.RootTrackSeparation
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- One requested-accuracy refinement of a winding-one state.  Every field is
computed by Theorem 7.3 and the four safe-line clearance certificates. -/
def refineState
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (current : WindingOneState p ambient)
    (ε : ℚ) (hε : 0 < ε) : WindingOneState p ambient := by
  let extracted := RawLocalExtraction.extract squarefree current.clearance
    current.proper current.rawWinding_ne hε elimination
  exact
    { box := extracted.band.band.box
      refinesAmbient := extracted.band.refines.trans current.refinesAmbient
      proper := extracted.band.band.proper extracted.band.radius_positive
      rawWindingFour := extracted.band.raw_winding_four
      clearance := extracted.band.boundaryClearance
      ambientLeftClearance := extracted.band.leftLineClearanceIn ambient
      ambientRightClearance := extracted.band.rightLineClearanceIn ambient
      ambientBottomClearance := extracted.band.bottomLineClearanceIn ambient
      ambientTopClearance := extracted.band.topLineClearanceIn ambient }

theorem refineState_refines
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (current : WindingOneState p ambient)
    (ε : ℚ) (hε : 0 < ε) :
    (refineState squarefree elimination current ε hε).box.Refines current.box := by
  exact (RawLocalExtraction.extract squarefree current.clearance current.proper
    current.rawWinding_ne hε elimination).band.refines

theorem refineState_accurate
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (current : WindingOneState p ambient)
    (ε : ℚ) (hε : 0 < ε) :
    (refineState squarefree elimination current ε hε).box.diagonalSq ≤ ε ^ 2 := by
  exact (RawLocalExtraction.extract squarefree current.clearance current.proper
    current.rawWinding_ne hε elimination).band_diagonalSq_le

/-- The concrete extractor improves mere nesting to strict nesting on every
positive request.  This stronger fact is useful when a later winding state
must be placed inside a common winding-one owner for maximality. -/
theorem refineState_strictInterior
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (current : WindingOneState p ambient)
    (ε : ℚ) (hε : 0 < ε) :
    FTA.CentralBandGrid.StrictInterior
      (refineState squarefree elimination current ε hε).box current.box := by
  let extracted := RawLocalExtraction.extract squarefree current.clearance
    current.proper current.rawWinding_ne hε elimination
  have strict := extracted.band_strictly_inside
  exact
    { left := by simpa only [refineState, extracted] using strict.1
      right := by simpa only [refineState, extracted] using strict.2.1
      bottom := by simpa only [refineState, extracted] using strict.2.2.1
      top := by simpa only [refineState, extracted] using strict.2.2.2 }

/-- Concrete total track generated from one initial winding-one box. -/
def ofInitial
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (initial : WindingOneState p ambient) : WindingOneTrack p ambient where
  initial := initial
  refine := refineState squarefree elimination
  nested := refineState_refines squarefree elimination
  strict := refineState_strictInterior squarefree elimination
  accurate := refineState_accurate squarefree elimination

end FTA.ConstructiveTrack
