import FTA.AxisSafeCuts
import FTA.BoxClearance

/-!
# The eight-box complement of a central band

Removing a strictly interior rational rectangle from a parent rectangle
leaves the eight closed cells of the induced `3 × 3` grid.  This module
constructs those cells with quantitative boundary clearance, proves exact
raw-winding additivity, and supplies the negative-cell choice used by the
finite nonnegativity loop of Theorem 9.1.
-/

namespace FTA.CentralBandGrid

open scoped BigOperators

open CCL
open FTA.BoxClearance
open FTA.LocalExtraction
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- All four sides of `inner` lie strictly inside `outer`. -/
structure StrictInterior (inner outer : CCL.RatBox) : Prop where
  left : outer.xLower < inner.xLower
  right : inner.xUpper < outer.xUpper
  bottom : outer.yLower < inner.yLower
  top : inner.yUpper < outer.yUpper

instance (inner outer : CCL.RatBox) : Decidable (StrictInterior inner outer) := by
  by_cases hleft : outer.xLower < inner.xLower
  · by_cases hright : inner.xUpper < outer.xUpper
    · by_cases hbottom : outer.yLower < inner.yLower
      · by_cases htop : inner.yUpper < outer.yUpper
        · exact isTrue ⟨hleft, hright, hbottom, htop⟩
        · exact isFalse fun h => htop h.top
      · exact isFalse fun h => hbottom h.bottom
    · exact isFalse fun h => hright h.right
  · exact isFalse fun h => hleft h.left

theorem StrictInterior.refines {inner outer : CCL.RatBox}
    (h : StrictInterior inner outer) : inner.Refines outer :=
  ⟨h.left.le, h.right.le, h.bottom.le, h.top.le⟩

/-- Strict interiors of two closed cells are positively separated. -/
def InteriorSeparated (left right : CCL.RatBox) : Prop :=
  ∀ {smallLeft smallRight : CCL.RatBox},
    StrictInterior smallLeft left → StrictInterior smallRight right →
      smallLeft.Separated smallRight

theorem interiorSeparated_symm {left right : CCL.RatBox}
    (h : InteriorSeparated left right) : InteriorSeparated right left := by
  intro smallRight smallLeft hright hleft
  exact CCL.RatBox.separated_symm (h hleft hright)

theorem interiorSeparated_of_x_le
    {left right : CCL.RatBox} (h : left.xUpper ≤ right.xLower) :
    InteriorSeparated left right := by
  intro smallLeft smallRight hleft hright
  let gap := smallRight.xLower - smallLeft.xUpper
  refine ⟨gap, by dsimp only [gap]; linarith [hleft.right, hright.left], ?_⟩
  exact Or.inl (by dsimp only [gap]; linarith)

theorem interiorSeparated_of_y_le
    {bottom top : CCL.RatBox} (h : bottom.yUpper ≤ top.yLower) :
    InteriorSeparated bottom top := by
  intro smallBottom smallTop hbottom htop
  let gap := smallTop.yLower - smallBottom.yUpper
  refine ⟨gap, by dsimp only [gap]; linarith [hbottom.top, htop.bottom], ?_⟩
  exact Or.inr (Or.inr (Or.inl (by dsimp only [gap]; linarith)))

def southwest (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := outer.xLower
  xUpper := inner.xLower
  yLower := outer.yLower
  yUpper := inner.yLower
  x_valid := h.left.le
  y_valid := h.bottom.le

def west (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := outer.xLower
  xUpper := inner.xLower
  yLower := inner.yLower
  yUpper := inner.yUpper
  x_valid := h.left.le
  y_valid := inner.y_valid

def northwest (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := outer.xLower
  xUpper := inner.xLower
  yLower := inner.yUpper
  yUpper := outer.yUpper
  x_valid := h.left.le
  y_valid := h.top.le

def south (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := inner.xLower
  xUpper := inner.xUpper
  yLower := outer.yLower
  yUpper := inner.yLower
  x_valid := inner.x_valid
  y_valid := h.bottom.le

def north (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := inner.xLower
  xUpper := inner.xUpper
  yLower := inner.yUpper
  yUpper := outer.yUpper
  x_valid := inner.x_valid
  y_valid := h.top.le

def southeast (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := inner.xUpper
  xUpper := outer.xUpper
  yLower := outer.yLower
  yUpper := inner.yLower
  x_valid := h.right.le
  y_valid := h.bottom.le

def east (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := inner.xUpper
  xUpper := outer.xUpper
  yLower := inner.yLower
  yUpper := inner.yUpper
  x_valid := h.right.le
  y_valid := inner.y_valid

def northeast (outer inner : CCL.RatBox)
    (h : StrictInterior inner outer) : CCL.RatBox where
  xLower := inner.xUpper
  xUpper := outer.xUpper
  yLower := inner.yUpper
  yUpper := outer.yUpper
  x_valid := h.right.le
  y_valid := h.top.le

/-- One clear complement cell, including the side on which it touches the
removed central rectangle. -/
structure ClearCell
    (p : GaussianPolynomial) (outer center : CCL.RatBox) where
  box : CCL.RatBox
  refines : box.Refines outer
  proper : box.Proper
  clearance : BoxBoundaryClearanceCertificate p box
  touchesCenter :
    box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
      box.yUpper = center.yLower ∨ box.yLower = center.yUpper

def makeCell
    {p : GaussianPolynomial} {outer center box : CCL.RatBox}
    (hrefines : box.Refines outer) (hproper : box.Proper)
    (left : VerticalLineClearance p outer box.xLower)
    (right : VerticalLineClearance p outer box.xUpper)
    (bottom : HorizontalLineClearance p outer box.yLower)
    (top : HorizontalLineClearance p outer box.yUpper)
    (htouches :
      box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
        box.yUpper = center.yLower ∨ box.yLower = center.yUpper) :
    ClearCell p outer center where
  box := box
  refines := hrefines
  proper := hproper
  clearance := boundaryOfLines
    (left.restrict hrefines) (right.restrict hrefines)
    (bottom.restrict hrefines) (top.restrict hrefines)
  touchesCenter := htouches

/-- The exact eight-cell complement, with all inherited line certificates. -/
structure Grid
    (p : GaussianPolynomial) (outer center : CCL.RatBox) where
  centerProper : center.Proper
  centerInterior : StrictInterior center outer
  southwest : ClearCell p outer center
  west : ClearCell p outer center
  northwest : ClearCell p outer center
  south : ClearCell p outer center
  north : ClearCell p outer center
  southeast : ClearCell p outer center
  east : ClearCell p outer center
  northeast : ClearCell p outer center
  complementsPairwise :
    [southwest, west, northwest, south, north, southeast, east, northeast].Pairwise
      (fun left right => InteriorSeparated left.box right.box)
  covers : ∀ {z : QI}, outer.Contains z →
    center.Contains z ∨
      ∃ cell ∈ [southwest, west, northwest, south, north,
        southeast, east, northeast], cell.box.Contains z
  additive : quadrupledBoxWinding p outer =
    quadrupledBoxWinding p center +
      quadrupledBoxWinding p southwest.box +
      quadrupledBoxWinding p west.box +
      quadrupledBoxWinding p northwest.box +
      quadrupledBoxWinding p south.box +
      quadrupledBoxWinding p north.box +
      quadrupledBoxWinding p southeast.box +
      quadrupledBoxWinding p east.box +
      quadrupledBoxWinding p northeast.box

def Grid.complements
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (grid : Grid p outer center) : List (ClearCell p outer center) :=
  [grid.southwest, grid.west, grid.northwest, grid.south, grid.north,
    grid.southeast, grid.east, grid.northeast]

theorem Grid.complements_pairwise
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (grid : Grid p outer center) :
    grid.complements.Pairwise
      (fun left right => InteriorSeparated left.box right.box) := by
  simpa only [Grid.complements] using grid.complementsPairwise

private theorem box_ext
    {A B : CCL.RatBox}
    (hxLower : A.xLower = B.xLower) (hxUpper : A.xUpper = B.xUpper)
    (hyLower : A.yLower = B.yLower) (hyUpper : A.yUpper = B.yUpper) : A = B := by
  cases A
  cases B
  simp_all

/-- Exact raw additivity for the displayed `3 × 3` grid. -/
theorem raw_additivity
    (p : GaussianPolynomial) (outer center : CCL.RatBox)
    (h : StrictInterior center outer) :
    quadrupledBoxWinding p outer =
      quadrupledBoxWinding p center +
      quadrupledBoxWinding p (southwest outer center h) +
      quadrupledBoxWinding p (west outer center h) +
      quadrupledBoxWinding p (northwest outer center h) +
      quadrupledBoxWinding p (south outer center h) +
      quadrupledBoxWinding p (north outer center h) +
      quadrupledBoxWinding p (southeast outer center h) +
      quadrupledBoxWinding p (east outer center h) +
      quadrupledBoxWinding p (northeast outer center h) := by
  let hxLower : outer.xLower ≤ center.xLower ∧
      center.xLower ≤ outer.xUpper :=
    ⟨h.left.le, center.x_valid.trans h.right.le⟩
  let rightRemainder := outer.verticalRight center.xLower hxLower
  let hxUpper : rightRemainder.xLower ≤ center.xUpper ∧
      center.xUpper ≤ rightRemainder.xUpper :=
    ⟨center.x_valid, h.right.le⟩
  let leftColumn := outer.verticalLeft center.xLower hxLower
  let middleColumn := rightRemainder.verticalLeft center.xUpper hxUpper
  let rightColumn := rightRemainder.verticalRight center.xUpper hxUpper
  have hyLeftLower : leftColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ leftColumn.yUpper :=
    ⟨h.bottom.le, center.y_valid.trans h.top.le⟩
  let leftUpper := leftColumn.horizontalUpper center.yLower hyLeftLower
  have hyLeftUpper : leftUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ leftUpper.yUpper := ⟨center.y_valid, h.top.le⟩
  have hyMiddleLower : middleColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ middleColumn.yUpper :=
    ⟨h.bottom.le, center.y_valid.trans h.top.le⟩
  let middleUpper := middleColumn.horizontalUpper center.yLower hyMiddleLower
  have hyMiddleUpper : middleUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ middleUpper.yUpper := ⟨center.y_valid, h.top.le⟩
  have hyRightLower : rightColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ rightColumn.yUpper :=
    ⟨h.bottom.le, center.y_valid.trans h.top.le⟩
  let rightUpper := rightColumn.horizontalUpper center.yLower hyRightLower
  have hyRightUpper : rightUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ rightUpper.yUpper := ⟨center.y_valid, h.top.le⟩
  have hverticalLower := quadrupledBoxWinding_vertical_split
    p outer center.xLower hxLower
  have hverticalUpper := quadrupledBoxWinding_vertical_split
    p rightRemainder center.xUpper hxUpper
  have hleftLower := quadrupledBoxWinding_horizontal_split
    p leftColumn center.yLower hyLeftLower
  have hleftUpper := quadrupledBoxWinding_horizontal_split
    p leftUpper center.yUpper hyLeftUpper
  have hmiddleLower := quadrupledBoxWinding_horizontal_split
    p middleColumn center.yLower hyMiddleLower
  have hmiddleUpper := quadrupledBoxWinding_horizontal_split
    p middleUpper center.yUpper hyMiddleUpper
  have hrightLower := quadrupledBoxWinding_horizontal_split
    p rightColumn center.yLower hyRightLower
  have hrightUpper := quadrupledBoxWinding_horizontal_split
    p rightUpper center.yUpper hyRightUpper
  have hsw : leftColumn.horizontalLower center.yLower hyLeftLower =
      southwest outer center h := by
    apply box_ext <;> rfl
  have hw : leftUpper.horizontalLower center.yUpper hyLeftUpper =
      west outer center h := by
    apply box_ext <;> rfl
  have hnw : leftUpper.horizontalUpper center.yUpper hyLeftUpper =
      northwest outer center h := by
    apply box_ext <;> rfl
  have hs : middleColumn.horizontalLower center.yLower hyMiddleLower =
      south outer center h := by
    apply box_ext <;> rfl
  have hc : middleUpper.horizontalLower center.yUpper hyMiddleUpper = center := by
    apply box_ext <;> rfl
  have hn : middleUpper.horizontalUpper center.yUpper hyMiddleUpper =
      north outer center h := by
    apply box_ext <;> rfl
  have hse : rightColumn.horizontalLower center.yLower hyRightLower =
      southeast outer center h := by
    apply box_ext <;> rfl
  have he : rightUpper.horizontalLower center.yUpper hyRightUpper =
      east outer center h := by
    apply box_ext <;> rfl
  have hne : rightUpper.horizontalUpper center.yUpper hyRightUpper =
      northeast outer center h := by
    apply box_ext <;> rfl
  rw [hverticalLower, hverticalUpper, hleftLower, hleftUpper,
    hmiddleLower, hmiddleUpper, hrightLower, hrightUpper,
    hsw, hw, hnw, hs, hc, hn, hse, he, hne]
  ring

private theorem complementBoxes_pairwise
    (outer center : CCL.RatBox) (h : StrictInterior center outer) :
    [southwest outer center h, west outer center h,
      northwest outer center h, south outer center h, north outer center h,
      southeast outer center h, east outer center h,
      northeast outer center h].Pairwise InteriorSeparated := by
  simp [List.pairwise_cons]
  repeat' apply And.intro
  all_goals
    first
    | apply interiorSeparated_of_x_le;
      dsimp [southwest, west, northwest, south, north, southeast, east,
        northeast]; linarith [center.x_valid, center.y_valid]
    | apply interiorSeparated_of_y_le;
      dsimp [southwest, west, northwest, south, north, southeast, east,
        northeast]; linarith [center.x_valid, center.y_valid]

private theorem complementBoxes_cover
    (outer center : CCL.RatBox) (h : StrictInterior center outer)
    {z : QI} (hz : outer.Contains z) :
    center.Contains z ∨
      ∃ box ∈ [southwest outer center h, west outer center h,
        northwest outer center h, south outer center h, north outer center h,
        southeast outer center h, east outer center h,
        northeast outer center h], box.Contains z := by
  by_cases hxLeft : z.re ≤ center.xLower
  · by_cases hyBottom : z.im ≤ center.yLower
    · exact Or.inr ⟨southwest outer center h, by simp,
        ⟨hz.1, hxLeft, hz.2.2.1, hyBottom⟩⟩
    · by_cases hyTop : z.im ≤ center.yUpper
      · exact Or.inr ⟨west outer center h, by simp,
          ⟨hz.1, hxLeft, le_of_not_ge hyBottom, hyTop⟩⟩
      · exact Or.inr ⟨northwest outer center h, by simp,
          ⟨hz.1, hxLeft, le_of_not_ge hyTop, hz.2.2.2⟩⟩
  · by_cases hxRight : z.re ≤ center.xUpper
    · by_cases hyBottom : z.im ≤ center.yLower
      · exact Or.inr ⟨south outer center h, by simp,
          ⟨le_of_not_ge hxLeft, hxRight, hz.2.2.1, hyBottom⟩⟩
      · by_cases hyTop : z.im ≤ center.yUpper
        · exact Or.inl
            ⟨le_of_not_ge hxLeft, hxRight, le_of_not_ge hyBottom, hyTop⟩
        · exact Or.inr ⟨north outer center h, by simp,
            ⟨le_of_not_ge hxLeft, hxRight, le_of_not_ge hyTop, hz.2.2.2⟩⟩
    · by_cases hyBottom : z.im ≤ center.yLower
      · exact Or.inr ⟨southeast outer center h, by simp,
          ⟨le_of_not_ge hxRight, hz.2.1, hz.2.2.1, hyBottom⟩⟩
      · by_cases hyTop : z.im ≤ center.yUpper
        · exact Or.inr ⟨east outer center h, by simp,
            ⟨le_of_not_ge hxRight, hz.2.1, le_of_not_ge hyBottom, hyTop⟩⟩
        · exact Or.inr ⟨northeast outer center h, by simp,
            ⟨le_of_not_ge hxRight, hz.2.1, le_of_not_ge hyTop, hz.2.2.2⟩⟩
/-- Assemble the proof-bearing eight-cell complement from the parent-edge
and four safe-cut line certificates. -/
def build
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (outerClearance : BoxBoundaryClearanceCertificate p outer)
    (centerProper : center.Proper) (interior : StrictInterior center outer)
    (innerLeft : VerticalLineClearance p outer center.xLower)
    (innerRight : VerticalLineClearance p outer center.xUpper)
    (innerBottom : HorizontalLineClearance p outer center.yLower)
    (innerTop : HorizontalLineClearance p outer center.yUpper) :
    Grid p outer center := by
  let outerLeft := leftOfBoundary outerClearance
  let outerRight := rightOfBoundary outerClearance
  let outerBottom := bottomOfBoundary outerClearance
  let outerTop := topOfBoundary outerClearance
  let sw := southwest outer center interior
  let w := west outer center interior
  let nw := northwest outer center interior
  let s := south outer center interior
  let n := north outer center interior
  let se := southeast outer center interior
  let e := east outer center interior
  let ne := northeast outer center interior
  let swCell : ClearCell p outer center := makeCell
    (box := sw)
    ⟨le_rfl, center.x_valid.trans interior.right.le,
      le_rfl, center.y_valid.trans interior.top.le⟩
    ⟨interior.left, interior.bottom⟩
    outerLeft innerLeft outerBottom innerBottom (Or.inl rfl)
  let wCell : ClearCell p outer center := makeCell
    (box := w)
    ⟨le_rfl, center.x_valid.trans interior.right.le,
      interior.bottom.le, interior.top.le⟩
    ⟨interior.left, centerProper.2⟩
    outerLeft innerLeft innerBottom innerTop (Or.inl rfl)
  let nwCell : ClearCell p outer center := makeCell
    (box := nw)
    ⟨le_rfl, center.x_valid.trans interior.right.le,
      (interior.bottom.le.trans center.y_valid), le_rfl⟩
    ⟨interior.left, interior.top⟩
    outerLeft innerLeft innerTop outerTop (Or.inl rfl)
  let sCell : ClearCell p outer center := makeCell
    (box := s)
    ⟨interior.left.le, interior.right.le,
      le_rfl, center.y_valid.trans interior.top.le⟩
    ⟨centerProper.1, interior.bottom⟩
    innerLeft innerRight outerBottom innerBottom
      (Or.inr (Or.inr (Or.inl rfl)))
  let nCell : ClearCell p outer center := makeCell
    (box := n)
    ⟨interior.left.le, interior.right.le,
      (interior.bottom.le.trans center.y_valid), le_rfl⟩
    ⟨centerProper.1, interior.top⟩
    innerLeft innerRight innerTop outerTop
      (Or.inr (Or.inr (Or.inr rfl)))
  let seCell : ClearCell p outer center := makeCell
    (box := se)
    ⟨(interior.left.le.trans center.x_valid), le_rfl,
      le_rfl, center.y_valid.trans interior.top.le⟩
    ⟨interior.right, interior.bottom⟩
    innerRight outerRight outerBottom innerBottom
      (Or.inr (Or.inl rfl))
  let eCell : ClearCell p outer center := makeCell
    (box := e)
    ⟨(interior.left.le.trans center.x_valid), le_rfl,
      interior.bottom.le, interior.top.le⟩
    ⟨interior.right, centerProper.2⟩
    innerRight outerRight innerBottom innerTop
      (Or.inr (Or.inl rfl))
  let neCell : ClearCell p outer center := makeCell
    (box := ne)
    ⟨(interior.left.le.trans center.x_valid), le_rfl,
      (interior.bottom.le.trans center.y_valid), le_rfl⟩
    ⟨interior.right, interior.top⟩
    innerRight outerRight innerTop outerTop
      (Or.inr (Or.inl rfl))
  exact
    { centerProper := centerProper
      centerInterior := interior
      southwest := swCell
      west := wCell
      northwest := nwCell
      south := sCell
      north := nCell
      southeast := seCell
      east := eCell
      northeast := neCell
      complementsPairwise := by
        rw [← List.pairwise_map]
        simpa only [List.map, swCell, wCell, nwCell, sCell, nCell, seCell, eCell,
          neCell, makeCell, sw, w, nw, s, n, se, e, ne] using
          complementBoxes_pairwise outer center interior
      covers := by
        intro z hz
        rcases complementBoxes_cover outer center interior hz with
          hcenter | ⟨box, hbox, hcontains⟩
        · exact Or.inl hcenter
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbox
          rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inr ⟨swCell, by simp,
              by simpa only [swCell, makeCell, sw] using hcontains⟩
          · exact Or.inr ⟨wCell, by simp,
              by simpa only [wCell, makeCell, w] using hcontains⟩
          · exact Or.inr ⟨nwCell, by simp,
              by simpa only [nwCell, makeCell, nw] using hcontains⟩
          · exact Or.inr ⟨sCell, by simp,
              by simpa only [sCell, makeCell, s] using hcontains⟩
          · exact Or.inr ⟨nCell, by simp,
              by simpa only [nCell, makeCell, n] using hcontains⟩
          · exact Or.inr ⟨seCell, by simp,
              by simpa only [seCell, makeCell, se] using hcontains⟩
          · exact Or.inr ⟨eCell, by simp,
              by simpa only [eCell, makeCell, e] using hcontains⟩
          · exact Or.inr ⟨neCell, by simp,
              by simpa only [neCell, makeCell, ne] using hcontains⟩
      additive := by
        simpa only [swCell, wCell, nwCell, sCell, nCell, seCell, eCell,
          neCell, makeCell, sw, w, nw, s, n, se, e, ne] using
          raw_additivity p outer center interior }

/-- Any box strictly inside one complement cell has a positive coordinate
gap from the removed center. -/
theorem ClearCell.center_separated_from_strictInterior
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (cell : ClearCell p outer center) {small : CCL.RatBox}
    (hsmall : StrictInterior small cell.box) : center.Separated small := by
  rcases cell.touchesCenter with hwest | heast | hsouth | hnorth
  · let gap := center.xLower - small.xUpper
    refine ⟨gap, by dsimp only [gap]; linarith [hsmall.right], ?_⟩
    exact Or.inr (Or.inl (by dsimp only [gap]; linarith))
  · let gap := small.xLower - center.xUpper
    refine ⟨gap, by dsimp only [gap]; linarith [hsmall.left], ?_⟩
    exact Or.inl (by dsimp only [gap]; linarith)
  · let gap := center.yLower - small.yUpper
    refine ⟨gap, by dsimp only [gap]; linarith [hsmall.top], ?_⟩
    exact Or.inr (Or.inr (Or.inr (by dsimp only [gap]; linarith)))
  · let gap := small.yLower - center.yUpper
    refine ⟨gap, by dsimp only [gap]; linarith [hsmall.bottom], ?_⟩
    exact Or.inr (Or.inr (Or.inl (by dsimp only [gap]; linarith)))

/-- Fixed finite order for choosing a negative complement cell. -/
def Grid.firstNegative
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (grid : Grid p outer center) : ClearCell p outer center :=
  if quadrupledBoxWinding p grid.southwest.box < 0 then grid.southwest
  else if quadrupledBoxWinding p grid.west.box < 0 then grid.west
  else if quadrupledBoxWinding p grid.northwest.box < 0 then grid.northwest
  else if quadrupledBoxWinding p grid.south.box < 0 then grid.south
  else if quadrupledBoxWinding p grid.north.box < 0 then grid.north
  else if quadrupledBoxWinding p grid.southeast.box < 0 then grid.southeast
  else if quadrupledBoxWinding p grid.east.box < 0 then grid.east
  else grid.northeast

theorem Grid.firstNegative_rawWinding_neg
    {p : GaussianPolynomial} {outer center : CCL.RatBox}
    (grid : Grid p outer center)
    (houter : quadrupledBoxWinding p outer < 0)
    (hcenter : quadrupledBoxWinding p center = 4) :
    quadrupledBoxWinding p grid.firstNegative.box < 0 := by
  by_cases hsw : quadrupledBoxWinding p grid.southwest.box < 0
  · simp [Grid.firstNegative, hsw]
  by_cases hw : quadrupledBoxWinding p grid.west.box < 0
  · simp [Grid.firstNegative, hsw, hw]
  by_cases hnw : quadrupledBoxWinding p grid.northwest.box < 0
  · simp [Grid.firstNegative, hsw, hw, hnw]
  by_cases hs : quadrupledBoxWinding p grid.south.box < 0
  · simp [Grid.firstNegative, hsw, hw, hnw, hs]
  by_cases hn : quadrupledBoxWinding p grid.north.box < 0
  · simp [Grid.firstNegative, hsw, hw, hnw, hs, hn]
  by_cases hse : quadrupledBoxWinding p grid.southeast.box < 0
  · simp [Grid.firstNegative, hsw, hw, hnw, hs, hn, hse]
  by_cases he : quadrupledBoxWinding p grid.east.box < 0
  · simp [Grid.firstNegative, hsw, hw, hnw, hs, hn, hse, he]
  have hne : quadrupledBoxWinding p grid.northeast.box < 0 := by
    have hswNonneg := le_of_not_gt hsw
    have hwNonneg := le_of_not_gt hw
    have hnwNonneg := le_of_not_gt hnw
    have hsNonneg := le_of_not_gt hs
    have hnNonneg := le_of_not_gt hn
    have hseNonneg := le_of_not_gt hse
    have heNonneg := le_of_not_gt he
    rw [grid.additive, hcenter] at houter
    omega
  simpa [Grid.firstNegative, hsw, hw, hnw, hs, hn, hse, he] using hne

end FTA.CentralBandGrid
