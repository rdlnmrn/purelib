import RFAP.Newton.Band

/-!
# Choice-free shrinking winding-one tracks

The local Newton-square extractor is stable under iteration because every
returned square carries a new finite boundary-clearance certificate.  This
module packages those repeated finite calls as the numerical track interface
used by box isolation and any independently shrinking finite envelope.
-/

namespace RFAP.ShrinkingTrack

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate

open RFAP.Winding
open RFAP.RawSubdivision

/-- A clear winding-one box supported in a fixed ambient box. -/
structure WindingOneState (p : GaussianPolynomial) (ambient : Box) where
  box : Box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  rawWindingFour : quadrupledBoxWinding p box = 4
  ambientLeftClearance :
    RFAP.BoxClearance.VerticalLineClearance p ambient box.xLower
  ambientRightClearance :
    RFAP.BoxClearance.VerticalLineClearance p ambient box.xUpper
  ambientBottomClearance :
    RFAP.BoxClearance.HorizontalLineClearance p ambient box.yLower
  ambientTopClearance :
    RFAP.BoxClearance.HorizontalLineClearance p ambient box.yUpper

/-- Forget exact winding four while retaining its constructive nonzeroness. -/
def WindingOneState.raw
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) : RawWindingState p ambient :=
  { box := state.box
    refinesAmbient := state.refinesAmbient
    proper := state.proper
    clearance := state.clearance
    rawWinding_ne := by
      intro windingZero
      have fourZero : (4 : Int) = 0 := by
        rw [← state.rawWindingFour]
        exact windingZero
      exact ((show (4 : Int) ≠ 0 by decide) fourZero).elim }

/-- One requested-accuracy refinement of a winding-one state. -/
def refineState
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    WindingOneState p ambient := by
  let extracted := RFAP.NewtonBand.extract degreeAtLeastTwo
    squarefree elimination current.raw positive
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }

theorem refineState_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.Refines current.box := by
  exact (RFAP.NewtonBand.extract degreeAtLeastTwo squarefree
    elimination current.raw positive).strictCurrent.refines

theorem refineState_strict
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.StrictInterior current.box := by
  exact (RFAP.NewtonBand.extract degreeAtLeastTwo squarefree
    elimination current.raw positive).strictCurrent

theorem refineState_accurate
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.diagonalSq ≤ epsilon ^ 2 := by
  exact (RFAP.NewtonBand.extract degreeAtLeastTwo squarefree
    elimination current.raw positive).diagonalSq_le

/-- A total finite shrinking track, with strict nesting available in addition
to ordinary nesting and the displayed squared-diagonal request. -/
structure WindingOneTrack (p : GaussianPolynomial) (ambient : Box) where
  initial : WindingOneState p ambient
  refine : (current : WindingOneState p ambient) →
    (epsilon : Coordinate) → 0 < epsilon → WindingOneState p ambient
  nested : ∀ current epsilon positive,
    (refine current epsilon positive).box.Refines current.box
  strict : ∀ current epsilon positive,
    (refine current epsilon positive).box.StrictInterior current.box
  accurate : ∀ current epsilon positive,
    (refine current epsilon positive).box.diagonalSq ≤ epsilon ^ 2

/-- Concrete total track generated from one winding-one state. -/
def ofInitial
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (initial : WindingOneState p ambient) : WindingOneTrack p ambient where
  initial := initial
  refine := refineState degreeAtLeastTwo squarefree elimination
  nested := refineState_refines degreeAtLeastTwo squarefree elimination
  strict := refineState_strict degreeAtLeastTwo squarefree elimination
  accurate := refineState_accurate degreeAtLeastTwo squarefree elimination

end RFAP.ShrinkingTrack
