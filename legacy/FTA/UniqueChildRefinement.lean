import FTA.ExactIsolation
import FTA.RawSubdivision
import FTA.WindingArithmetic

/-!
# Deterministic unique-child refinement

This module implements Lemma 9.3 at the raw-winding normalization.  Two
coefficient-computed safe central-third cuts divide a winding-one box into
four clear children.  Global nonnegativity and local extraction prove that a
positive child has raw winding at least four; additivity therefore makes the
raw-winding-four child unique.  Iteration at an explicit geometric depth is a
total deterministic refinement to any requested rational squared diagonal.
-/

namespace FTA.UniqueChildRefinement

open scoped BigOperators

open CCL
open FTA.AxisSafeCuts
open FTA.BoxClearance
open FTA.ExactIsolation
open FTA.GlobalNonnegativity
open FTA.LocalExtraction
open FTA.PathClearance
open FTA.RawSubdivision
open FTA.RootTrackSeparation
open FTA.SafeCuts
open FTA.SturmTransducer
open FTA.Winding
open FTA.WindingArithmetic

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- Positive clearance on the selected vertical cut over any requested
rational ambient interval. -/
def verticalSafeCutClearanceIn
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (B : CCL.RatBox) (hB : B.Proper) (larger : CCL.RatBox) :
    VerticalLineClearance p larger (verticalSafeCoordinate elimination hB.1) :=
  verticalOfPathCertificate p larger (verticalSafeCoordinate elimination hB.1)
    (certificateOfCoprime
      (elimination.vertical_coprime _
        (verticalSafeCoordinate_spec elimination hB.1).1)
      (verticalInterval larger))

/-- Positive clearance on the full vertical safe cut through a proper box. -/
def verticalSafeCutClearance
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (B : CCL.RatBox) (hB : B.Proper) :
    VerticalLineClearance p B (verticalSafeCoordinate elimination hB.1) :=
  verticalSafeCutClearanceIn elimination B hB B

/-- Positive clearance on the selected horizontal cut over any requested
rational ambient interval. -/
def horizontalSafeCutClearanceIn
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (B : CCL.RatBox) (hB : B.Proper) (larger : CCL.RatBox) :
    HorizontalLineClearance p larger (horizontalSafeCoordinate elimination hB.2) :=
  horizontalOfPathCertificate p larger (horizontalSafeCoordinate elimination hB.2)
    (certificateOfCoprime
      (elimination.horizontal_coprime _
        (horizontalSafeCoordinate_spec elimination hB.2).1)
      (horizontalInterval larger))

/-- Positive clearance on the full horizontal safe cut through a proper box. -/
def horizontalSafeCutClearance
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (B : CCL.RatBox) (hB : B.Proper) :
    HorizontalLineClearance p B (horizontalSafeCoordinate elimination hB.2) :=
  horizontalSafeCutClearanceIn elimination B hB B

/-- A safe four-child grid with a quantitative clearance certificate on
every child boundary. -/
structure ClearFourGrid
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (parent : WindingOneState p ambient) where
  raw : RawFourGrid p parent.box
  lowerLeftClearance : BoxBoundaryClearanceCertificate p raw.lowerLeft
  upperLeftClearance : BoxBoundaryClearanceCertificate p raw.upperLeft
  lowerRightClearance : BoxBoundaryClearanceCertificate p raw.lowerRight
  upperRightClearance : BoxBoundaryClearanceCertificate p raw.upperRight
  lowerLeftAmbientLeft : VerticalLineClearance p ambient raw.lowerLeft.xLower
  lowerLeftAmbientRight : VerticalLineClearance p ambient raw.lowerLeft.xUpper
  lowerLeftAmbientBottom : HorizontalLineClearance p ambient raw.lowerLeft.yLower
  lowerLeftAmbientTop : HorizontalLineClearance p ambient raw.lowerLeft.yUpper
  upperLeftAmbientLeft : VerticalLineClearance p ambient raw.upperLeft.xLower
  upperLeftAmbientRight : VerticalLineClearance p ambient raw.upperLeft.xUpper
  upperLeftAmbientBottom : HorizontalLineClearance p ambient raw.upperLeft.yLower
  upperLeftAmbientTop : HorizontalLineClearance p ambient raw.upperLeft.yUpper
  lowerRightAmbientLeft : VerticalLineClearance p ambient raw.lowerRight.xLower
  lowerRightAmbientRight : VerticalLineClearance p ambient raw.lowerRight.xUpper
  lowerRightAmbientBottom : HorizontalLineClearance p ambient raw.lowerRight.yLower
  lowerRightAmbientTop : HorizontalLineClearance p ambient raw.lowerRight.yUpper
  upperRightAmbientLeft : VerticalLineClearance p ambient raw.upperRight.xLower
  upperRightAmbientRight : VerticalLineClearance p ambient raw.upperRight.xUpper
  upperRightAmbientBottom : HorizontalLineClearance p ambient raw.upperRight.yLower
  upperRightAmbientTop : HorizontalLineClearance p ambient raw.upperRight.yUpper

/-- Construct all four clear children from the parent boundary and the two
new safe-line certificates. -/
def buildClearFourGrid
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    (parent : WindingOneState p ambient) : ClearFourGrid p ambient parent := by
  let rawState : RawWindingState p ambient :=
    { box := parent.box
      refinesAmbient := parent.refinesAmbient
      proper := parent.proper
      rawWinding_ne := parent.rawWinding_ne }
  let raw := safeRawFourGrid elimination rawState
  let vertical := verticalSafeCutClearance elimination parent.box parent.proper
  let horizontal := horizontalSafeCutClearance elimination parent.box parent.proper
  let ambientVertical :=
    verticalSafeCutClearanceIn elimination parent.box parent.proper ambient
  let ambientHorizontal :=
    horizontalSafeCutClearanceIn elimination parent.box parent.proper ambient
  let parentLeft := leftOfBoundary parent.clearance
  let parentRight := rightOfBoundary parent.clearance
  let parentBottom := bottomOfBoundary parent.clearance
  let parentTop := topOfBoundary parent.clearance
  let lowerLeftClearance : BoxBoundaryClearanceCertificate p raw.lowerLeft := by
    apply boundaryOfLines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalLower] using
        parentLeft.restrict raw.lowerLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalLower] using
        vertical.restrict raw.lowerLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalLower] using
        parentBottom.restrict raw.lowerLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalLower] using
        horizontal.restrict raw.lowerLeft_refines
  let upperLeftClearance : BoxBoundaryClearanceCertificate p raw.upperLeft := by
    apply boundaryOfLines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalUpper] using
        parentLeft.restrict raw.upperLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalUpper] using
        vertical.restrict raw.upperLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalUpper] using
        horizontal.restrict raw.upperLeft_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
        CCL.RatBox.horizontalUpper] using
        parentTop.restrict raw.upperLeft_refines
  let lowerRightClearance : BoxBoundaryClearanceCertificate p raw.lowerRight := by
    apply boundaryOfLines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalLower] using
        vertical.restrict raw.lowerRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalLower] using
        parentRight.restrict raw.lowerRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalLower] using
        parentBottom.restrict raw.lowerRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalLower] using
        horizontal.restrict raw.lowerRight_refines
  let upperRightClearance : BoxBoundaryClearanceCertificate p raw.upperRight := by
    apply boundaryOfLines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalUpper] using
        vertical.restrict raw.upperRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalUpper] using
        parentRight.restrict raw.upperRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalUpper] using
        horizontal.restrict raw.upperRight_refines
    · simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
        CCL.RatBox.horizontalUpper] using
        parentTop.restrict raw.upperRight_refines
  exact
    { raw := raw
      lowerLeftClearance := lowerLeftClearance
      upperLeftClearance := upperLeftClearance
      lowerRightClearance := lowerRightClearance
      upperRightClearance := upperRightClearance
      lowerLeftAmbientLeft := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalLower] using parent.ambientLeftClearance
      lowerLeftAmbientRight := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalLower] using ambientVertical
      lowerLeftAmbientBottom := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalLower] using parent.ambientBottomClearance
      lowerLeftAmbientTop := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalLower] using ambientHorizontal
      upperLeftAmbientLeft := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalUpper] using parent.ambientLeftClearance
      upperLeftAmbientRight := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalUpper] using ambientVertical
      upperLeftAmbientBottom := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalUpper] using ambientHorizontal
      upperLeftAmbientTop := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalLeft,
          CCL.RatBox.horizontalUpper] using parent.ambientTopClearance
      lowerRightAmbientLeft := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalLower] using ambientVertical
      lowerRightAmbientRight := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalLower] using parent.ambientRightClearance
      lowerRightAmbientBottom := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalLower] using parent.ambientBottomClearance
      lowerRightAmbientTop := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalLower] using ambientHorizontal
      upperRightAmbientLeft := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalUpper] using ambientVertical
      upperRightAmbientRight := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalUpper] using parent.ambientRightClearance
      upperRightAmbientBottom := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalUpper] using ambientHorizontal
      upperRightAmbientTop := by
        simpa [raw, rawState, safeRawFourGrid, CCL.RatBox.verticalRight,
          CCL.RatBox.horizontalUpper] using parent.ambientTopClearance }

/-- Fixed child order: lower-left, upper-left, lower-right, upper-right. -/
def ClearFourGrid.childBox
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) : Fin 4 → CCL.RatBox :=
  Fin.cases grid.raw.lowerLeft
    (Fin.cases grid.raw.upperLeft
      (Fin.cases grid.raw.lowerRight
        (Fin.cases grid.raw.upperRight Fin.elim0)))

def ClearFourGrid.childClearance
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → BoxBoundaryClearanceCertificate p (grid.childBox i) :=
  Fin.cases grid.lowerLeftClearance
    (Fin.cases grid.upperLeftClearance
      (Fin.cases grid.lowerRightClearance
        (Fin.cases grid.upperRightClearance (fun i => Fin.elim0 i))))

def ClearFourGrid.childAmbientLeft
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → VerticalLineClearance p ambient (grid.childBox i).xLower :=
  Fin.cases grid.lowerLeftAmbientLeft
    (Fin.cases grid.upperLeftAmbientLeft
      (Fin.cases grid.lowerRightAmbientLeft
        (Fin.cases grid.upperRightAmbientLeft (fun i => Fin.elim0 i))))

def ClearFourGrid.childAmbientRight
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → VerticalLineClearance p ambient (grid.childBox i).xUpper :=
  Fin.cases grid.lowerLeftAmbientRight
    (Fin.cases grid.upperLeftAmbientRight
      (Fin.cases grid.lowerRightAmbientRight
        (Fin.cases grid.upperRightAmbientRight (fun i => Fin.elim0 i))))

def ClearFourGrid.childAmbientBottom
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → HorizontalLineClearance p ambient (grid.childBox i).yLower :=
  Fin.cases grid.lowerLeftAmbientBottom
    (Fin.cases grid.upperLeftAmbientBottom
      (Fin.cases grid.lowerRightAmbientBottom
        (Fin.cases grid.upperRightAmbientBottom (fun i => Fin.elim0 i))))

def ClearFourGrid.childAmbientTop
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → HorizontalLineClearance p ambient (grid.childBox i).yUpper :=
  Fin.cases grid.lowerLeftAmbientTop
    (Fin.cases grid.upperLeftAmbientTop
      (Fin.cases grid.lowerRightAmbientTop
        (Fin.cases grid.upperRightAmbientTop (fun i => Fin.elim0 i))))

theorem ClearFourGrid.child_refines_parent
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → (grid.childBox i).Refines parent.box :=
  Fin.cases grid.raw.lowerLeft_refines
    (Fin.cases grid.raw.upperLeft_refines
      (Fin.cases grid.raw.lowerRight_refines
        (Fin.cases grid.raw.upperRight_refines (fun i => Fin.elim0 i))))

theorem ClearFourGrid.child_proper
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    (i : Fin 4) → (grid.childBox i).Proper :=
  Fin.cases grid.raw.lowerLeft_proper
    (Fin.cases grid.raw.upperLeft_proper
      (Fin.cases grid.raw.lowerRight_proper
        (Fin.cases grid.raw.upperRight_proper (fun i => Fin.elim0 i))))

theorem ClearFourGrid.child_contracts
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) : ∀ i : Fin 4,
    (grid.childBox i).diagonalSq ≤
      (4 / 9 : ℚ) * parent.box.diagonalSq :=
  Fin.cases grid.raw.lowerLeft_contract
    (Fin.cases grid.raw.upperLeft_contract
      (Fin.cases grid.raw.lowerRight_contract
        (Fin.cases grid.raw.upperRight_contract (fun i => Fin.elim0 i))))

def ClearFourGrid.childRawWinding
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) (i : Fin 4) : ℤ :=
  quadrupledBoxWinding p (grid.childBox i)

theorem ClearFourGrid.childRawWinding_sum
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) :
    ∑ i, grid.childRawWinding i = quadrupledBoxWinding p parent.box := by
  simpa [ClearFourGrid.childRawWinding, ClearFourGrid.childBox,
    Fin.sum_univ_succ, add_assoc] using
    grid.raw.additive.symm

def ClearFourGrid.childRegion
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) (i : Fin 4) :
    ClearRegion p ambient where
  box := grid.childBox i
  refinesAmbient := (grid.child_refines_parent i).trans parent.refinesAmbient
  proper := grid.child_proper i
  clearance := grid.childClearance i

/-- A positive clear region has raw winding at least four.  Local extraction
removes a raw-winding-four band, and Theorem 9.1 makes the complete remainder
nonnegative. -/
theorem positive_clearRegion_rawWinding_ge_four
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (region : ClearRegion p (CCL.RatBox.symmetric R hR))
    (hpositive : 0 < quadrupledBoxWinding p region.box) :
    4 ≤ quadrupledBoxWinding p region.box := by
  let extracted := extractRegion squarefree elimination region hpositive
  let complements := complementRegions extracted.grid region.refinesAmbient
  have hnonnegative : ∀ member ∈ complements,
      0 ≤ quadrupledBoxWinding p member.box := by
    intro member _hmember
    exact quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
      elimination member.refinesAmbient member.proper member.clearance
  have htotalNonnegative : 0 ≤ totalRaw complements :=
    totalRaw_nonnegative complements hnonnegative
  have htotal := totalRaw_complementRegions
    extracted.grid region.refinesAmbient
  rw [extracted.track.initial.rawWindingFour] at htotal
  have htotal' : totalRaw complements =
      quadrupledBoxWinding p region.box - 4 := by
    simpa only [complements] using htotal
  omega

theorem ClearFourGrid.childRawWinding_nonnegative
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {parent : WindingOneState p (CCL.RatBox.symmetric R hR)}
    (grid : ClearFourGrid p (CCL.RatBox.symmetric R hR) parent)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (i : Fin 4) : 0 ≤ grid.childRawWinding i :=
  quadrupledBoxWinding_nonnegative p R hR squarefree hdegree elimination
    (grid.childRegion i).refinesAmbient (grid.child_proper i)
    (grid.childClearance i)

theorem ClearFourGrid.positive_childRawWinding_ge_four
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {parent : WindingOneState p (CCL.RatBox.symmetric R hR)}
    (grid : ClearFourGrid p (CCL.RatBox.symmetric R hR) parent)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (i : Fin 4) (hpositive : 0 < grid.childRawWinding i) :
    4 ≤ grid.childRawWinding i :=
  positive_clearRegion_rawWinding_ge_four p R hR squarefree hdegree
    elimination (grid.childRegion i) hpositive

/-- Concrete unique-child conclusion of Lemma 9.3 for one safe four-grid. -/
theorem ClearFourGrid.existsUnique_rawWindingFour
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {parent : WindingOneState p (CCL.RatBox.symmetric R hR)}
    (grid : ClearFourGrid p (CCL.RatBox.symmetric R hR) parent)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    ∃! i, grid.childRawWinding i = 4 := by
  apply existsUnique_four_of_positive_ge_four grid.childRawWinding
  · exact grid.childRawWinding_nonnegative squarefree hdegree elimination
  · exact grid.positive_childRawWinding_ge_four squarefree hdegree elimination
  · rw [grid.childRawWinding_sum, parent.rawWindingFour]

/-- First nonzero index in the fixed four-child order. -/
def firstNonzeroFour (w : Fin 4 → ℤ) : Fin 4 :=
  if w 0 ≠ 0 then 0
  else if w 1 ≠ 0 then 1
  else if w 2 ≠ 0 then 2
  else 3

theorem firstNonzeroFour_ne_zero (w : Fin 4 → ℤ)
    (hsum : ∑ i, w i = 4) : w (firstNonzeroFour w) ≠ 0 := by
  unfold firstNonzeroFour
  split
  · assumption
  split
  · assumption
  split
  · assumption
  rename_i hzero0 hzero1 hzero2
  have hsumExpanded : w 0 + (w 1 + (w 2 + w 3)) = 4 := by
    simpa [Fin.sum_univ_succ] using hsum
  omega

def ClearFourGrid.selectedIndex
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {parent : WindingOneState p ambient}
    (grid : ClearFourGrid p ambient parent) : Fin 4 :=
  firstNonzeroFour grid.childRawWinding

theorem ClearFourGrid.selected_rawWindingFour
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {parent : WindingOneState p (CCL.RatBox.symmetric R hR)}
    (grid : ClearFourGrid p (CCL.RatBox.symmetric R hR) parent)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    grid.childRawWinding grid.selectedIndex = 4 := by
  have hsum : ∑ i, grid.childRawWinding i = 4 := by
    rw [grid.childRawWinding_sum, parent.rawWindingFour]
  have hnonzero : grid.childRawWinding grid.selectedIndex ≠ 0 :=
    firstNonzeroFour_ne_zero grid.childRawWinding hsum
  have hnonnegative := grid.childRawWinding_nonnegative
    squarefree hdegree elimination grid.selectedIndex
  have hpositive : 0 < grid.childRawWinding grid.selectedIndex :=
    lt_of_le_of_ne hnonnegative (Ne.symm hnonzero)
  have hlower := grid.positive_childRawWinding_ge_four
    squarefree hdegree elimination grid.selectedIndex hpositive
  have hupper : grid.childRawWinding grid.selectedIndex ≤ 4 :=
    (value_le_sum grid.childRawWinding
      (grid.childRawWinding_nonnegative squarefree hdegree elimination)
      grid.selectedIndex).trans_eq hsum
  omega

theorem ClearFourGrid.rawWindingFour_iff_selected
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {parent : WindingOneState p (CCL.RatBox.symmetric R hR)}
    (grid : ClearFourGrid p (CCL.RatBox.symmetric R hR) parent)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (i : Fin 4) :
    grid.childRawWinding i = 4 ↔ i = grid.selectedIndex := by
  obtain ⟨unique, hunique, honly⟩ :=
    grid.existsUnique_rawWindingFour squarefree hdegree elimination
  have hselected :=
    grid.selected_rawWindingFour squarefree hdegree elimination
  constructor
  · intro hi
    exact (honly i hi).trans (honly grid.selectedIndex hselected).symm
  · rintro rfl
    exact hselected

/-- One deterministic safe unique-child refinement. -/
def refineOnce
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (parent : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    WindingOneState p (CCL.RatBox.symmetric R hR) := by
  let grid := buildClearFourGrid elimination parent
  let selected := grid.selectedIndex
  exact
    { box := grid.childBox selected
      refinesAmbient := (grid.child_refines_parent selected).trans
        parent.refinesAmbient
      proper := grid.child_proper selected
      rawWindingFour :=
        grid.selected_rawWindingFour squarefree hdegree elimination
      clearance := grid.childClearance selected
      ambientLeftClearance := grid.childAmbientLeft selected
      ambientRightClearance := grid.childAmbientRight selected
      ambientBottomClearance := grid.childAmbientBottom selected
      ambientTopClearance := grid.childAmbientTop selected }

theorem refineOnce_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (parent : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    (refineOnce squarefree hdegree elimination parent).box.Refines parent.box := by
  exact (buildClearFourGrid elimination parent).child_refines_parent
    (buildClearFourGrid elimination parent).selectedIndex

theorem refineOnce_contracts
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (parent : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    (refineOnce squarefree hdegree elimination parent).box.diagonalSq ≤
      (4 / 9 : ℚ) * parent.box.diagonalSq := by
  exact (buildClearFourGrid elimination parent).child_contracts
    (buildClearFourGrid elimination parent).selectedIndex

/-- Fixed-depth iteration of the unique-child operation. -/
def refineN
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    ℕ → WindingOneState p (CCL.RatBox.symmetric R hR) →
      WindingOneState p (CCL.RatBox.symmetric R hR)
  | 0, state => state
  | n + 1, state =>
      refineOnce squarefree hdegree elimination
        (refineN squarefree hdegree elimination n state)

theorem refineN_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (n : ℕ) (state : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    (refineN squarefree hdegree elimination n state).box.Refines state.box := by
  induction n with
  | zero => exact CCL.RatBox.refines_refl _
  | succ n ih =>
      exact (refineOnce_refines squarefree hdegree elimination
        (refineN squarefree hdegree elimination n state)).trans ih

theorem refineN_diagonalSq_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (n : ℕ) (state : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    (refineN squarefree hdegree elimination n state).box.diagonalSq ≤
      (4 / 9 : ℚ) ^ n * state.box.diagonalSq := by
  induction n with
  | zero => simp [refineN]
  | succ n ih =>
      calc
        (refineN squarefree hdegree elimination (n + 1) state).box.diagonalSq ≤
            (4 / 9 : ℚ) *
              (refineN squarefree hdegree elimination n state).box.diagonalSq :=
          refineOnce_contracts squarefree hdegree elimination
            (refineN squarefree hdegree elimination n state)
        _ ≤ (4 / 9 : ℚ) *
              ((4 / 9 : ℚ) ^ n * state.box.diagonalSq) := by
          gcongr
        _ = (4 / 9 : ℚ) ^ (n + 1) * state.box.diagonalSq := by
          rw [pow_succ]
          ring

def refinementDepth
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (state : WindingOneState p (CCL.RatBox.symmetric R hR))
    (threshold : ℚ) : ℕ :=
  geometricDepth state.box.diagonalSq threshold

/-- Lemma 9.3's total deterministic refinement at a requested squared
diagonal. -/
def refineTo
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p (CCL.RatBox.symmetric R hR))
    (threshold : ℚ) : WindingOneState p (CCL.RatBox.symmetric R hR) :=
  refineN squarefree hdegree elimination (refinementDepth state threshold) state

theorem refineTo_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p (CCL.RatBox.symmetric R hR))
    (threshold : ℚ) :
    (refineTo squarefree hdegree elimination state threshold).box.Refines
      state.box :=
  refineN_refines squarefree hdegree elimination
    (refinementDepth state threshold) state

theorem refineTo_diagonalSq_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p (CCL.RatBox.symmetric R hR))
    {threshold : ℚ} (hthreshold : 0 < threshold) :
    (refineTo squarefree hdegree elimination state threshold).box.diagonalSq ≤
      threshold := by
  let n := refinementDepth state threshold
  have hraw := refineN_diagonalSq_le squarefree hdegree elimination n state
  have hpow : (4 / 9 : ℚ) ^ n ≤ (2 / 3 : ℚ) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hscaled : (4 / 9 : ℚ) ^ n * state.box.diagonalSq ≤
      (2 / 3 : ℚ) ^ n * state.box.diagonalSq :=
    mul_le_mul_of_nonneg_right hpow state.box.diagonalSq_nonneg
  exact hraw.trans (hscaled.trans (by
    simpa only [n, refinementDepth] using
      geometricDepth_sufficient state.box.diagonalSq_nonneg hthreshold))

/-- The unique-child routine itself satisfies the finite track interface. -/
def trackOfInitial
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (squarefree : GaussianSquarefreeCertificate p)
    (_hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (initial : WindingOneState p (CCL.RatBox.symmetric R hR)) :
    WindingOneTrack p (CCL.RatBox.symmetric R hR) :=
  FTA.ConstructiveTrack.ofInitial squarefree elimination initial

end FTA.UniqueChildRefinement
