import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Newton.Band

/-!
# Choice-free eight-cell complement of a central band

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the selected Newton band; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace RFAP.CentralBandGrid

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev VerticalLineClearance :=
  RFAP.BoxClearance.VerticalLineClearance
abbrev HorizontalLineClearance :=
  RFAP.BoxClearance.HorizontalLineClearance

open RFAP.BoxClearance
open RFAP.GlobalWinding
open RFAP.Winding

def southwest (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := strict.left.le
  y_valid := strict.bottom.le

def west (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := center.yLower
  yUpper := center.yUpper
  x_valid := strict.left.le
  y_valid := center.y_valid

def northwest (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := strict.left.le
  y_valid := strict.top.le

def south (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := center.xLower
  xUpper := center.xUpper
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := center.x_valid
  y_valid := strict.bottom.le

def north (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := center.xLower
  xUpper := center.xUpper
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := center.x_valid
  y_valid := strict.top.le

def southeast (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := strict.right.le
  y_valid := strict.bottom.le

def east (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := center.yLower
  yUpper := center.yUpper
  x_valid := strict.right.le
  y_valid := center.y_valid

def northeast (outer center : Box)
    (strict : center.StrictInterior outer) : Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := strict.right.le
  y_valid := strict.top.le

/-- One clear complement cell, including a side on which it touches the
removed center. -/
structure ClearCell
    (p : GaussianPolynomial) (outer center : Box) where
  box : Box
  refines : box.Refines outer
  proper : box.Proper
  clearance : BoundaryClearance p box
  touchesCenter :
    box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
      box.yUpper = center.yLower ∨ box.yLower = center.yUpper

def makeCell
    {p : GaussianPolynomial} {outer center box : Box}
    (refines : box.Refines outer) (proper : box.Proper)
    (left : VerticalLineClearance p outer box.xLower)
    (right : VerticalLineClearance p outer box.xUpper)
    (bottom : HorizontalLineClearance p outer box.yLower)
    (top : HorizontalLineClearance p outer box.yUpper)
    (touches :
      box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
        box.yUpper = center.yLower ∨ box.yLower = center.yUpper) :
    ClearCell p outer center where
  box := box
  refines := refines
  proper := proper
  clearance := boundaryOfLines
    (left.restrict refines) (right.restrict refines)
    (bottom.restrict refines) (top.restrict refines)
  touchesCenter := touches

/-- The eight clear complement cells and exact raw additivity. -/
structure Grid
    (p : GaussianPolynomial) (outer center : Box) where
  centerProper : center.Proper
  centerInterior : center.StrictInterior outer
  southwest : ClearCell p outer center
  west : ClearCell p outer center
  northwest : ClearCell p outer center
  south : ClearCell p outer center
  north : ClearCell p outer center
  southeast : ClearCell p outer center
  east : ClearCell p outer center
  northeast : ClearCell p outer center
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
  complementsPairwise :
    [southwest, west, northwest, south, north, southeast, east,
      northeast].Pairwise
        (fun left right => left.box.InteriorSeparated right.box)
  covers : ∀ {z}, outer.Contains z →
    center.Contains z ∨
      ∃ cell ∈ [southwest, west, northwest, south, north, southeast, east,
        northeast], cell.box.Contains z

/-- The fixed finite complement order used by isolation and deterministic
negative-cell selection. -/
def Grid.complements
    {p : GaussianPolynomial} {outer center : Box}
    (grid : Grid p outer center) : List (ClearCell p outer center) :=
  [grid.southwest, grid.west, grid.northwest, grid.south, grid.north,
    grid.southeast, grid.east, grid.northeast]

theorem Grid.complements_pairwise
    {p : GaussianPolynomial} {outer center : Box}
    (grid : Grid p outer center) :
    grid.complements.Pairwise
      (fun left right => left.box.InteriorSeparated right.box) :=
  grid.complementsPairwise

private theorem box_ext
    {left right : Box}
    (xLower : left.xLower = right.xLower)
    (xUpper : left.xUpper = right.xUpper)
    (yLower : left.yLower = right.yLower)
    (yUpper : left.yUpper = right.yUpper) : left = right := by
  cases left
  cases right
  simp_all

/-- Exact raw additivity for the displayed `3 × 3` grid. -/
theorem raw_additivity
    (p : GaussianPolynomial) (outer center : Box)
    (strict : center.StrictInterior outer) :
    quadrupledBoxWinding p outer =
      quadrupledBoxWinding p center +
      quadrupledBoxWinding p (southwest outer center strict) +
      quadrupledBoxWinding p (west outer center strict) +
      quadrupledBoxWinding p (northwest outer center strict) +
      quadrupledBoxWinding p (south outer center strict) +
      quadrupledBoxWinding p (north outer center strict) +
      quadrupledBoxWinding p (southeast outer center strict) +
      quadrupledBoxWinding p (east outer center strict) +
      quadrupledBoxWinding p (northeast outer center strict) := by
  let xLowerInside : outer.xLower ≤ center.xLower ∧
      center.xLower ≤ outer.xUpper :=
    ⟨strict.left.le, center.x_valid.trans strict.right.le⟩
  let rightRemainder := outer.verticalRight center.xLower xLowerInside
  let xUpperInside : rightRemainder.xLower ≤ center.xUpper ∧
      center.xUpper ≤ rightRemainder.xUpper :=
    ⟨center.x_valid, strict.right.le⟩
  let leftColumn := outer.verticalLeft center.xLower xLowerInside
  let middleColumn := rightRemainder.verticalLeft center.xUpper xUpperInside
  let rightColumn := rightRemainder.verticalRight center.xUpper xUpperInside
  have leftLowerInside : leftColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ leftColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let leftUpper := leftColumn.horizontalUpper center.yLower leftLowerInside
  have leftUpperInside : leftUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ leftUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have middleLowerInside : middleColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ middleColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let middleUpper := middleColumn.horizontalUpper center.yLower
    middleLowerInside
  have middleUpperInside : middleUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ middleUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have rightLowerInside : rightColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ rightColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let rightUpper := rightColumn.horizontalUpper center.yLower
    rightLowerInside
  have rightUpperInside : rightUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ rightUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have verticalLower := quadrupledBoxWinding_vertical_split
    p outer center.xLower xLowerInside
  have verticalUpper := quadrupledBoxWinding_vertical_split
    p rightRemainder center.xUpper xUpperInside
  have leftLower := quadrupledBoxWinding_horizontal_split
    p leftColumn center.yLower leftLowerInside
  have leftTop := quadrupledBoxWinding_horizontal_split
    p leftUpper center.yUpper leftUpperInside
  have middleLower := quadrupledBoxWinding_horizontal_split
    p middleColumn center.yLower middleLowerInside
  have middleTop := quadrupledBoxWinding_horizontal_split
    p middleUpper center.yUpper middleUpperInside
  have rightLower := quadrupledBoxWinding_horizontal_split
    p rightColumn center.yLower rightLowerInside
  have rightTop := quadrupledBoxWinding_horizontal_split
    p rightUpper center.yUpper rightUpperInside
  have southwestEq :
      leftColumn.horizontalLower center.yLower leftLowerInside =
        southwest outer center strict := by
    apply box_ext <;> rfl
  have westEq : leftUpper.horizontalLower center.yUpper leftUpperInside =
      west outer center strict := by
    apply box_ext <;> rfl
  have northwestEq : leftUpper.horizontalUpper center.yUpper leftUpperInside =
      northwest outer center strict := by
    apply box_ext <;> rfl
  have southEq : middleColumn.horizontalLower center.yLower
      middleLowerInside = south outer center strict := by
    apply box_ext <;> rfl
  have centerEq : middleUpper.horizontalLower center.yUpper
      middleUpperInside = center := by
    apply box_ext <;> rfl
  have northEq : middleUpper.horizontalUpper center.yUpper
      middleUpperInside = north outer center strict := by
    apply box_ext <;> rfl
  have southeastEq : rightColumn.horizontalLower center.yLower
      rightLowerInside = southeast outer center strict := by
    apply box_ext <;> rfl
  have eastEq : rightUpper.horizontalLower center.yUpper rightUpperInside =
      east outer center strict := by
    apply box_ext <;> rfl
  have northeastEq : rightUpper.horizontalUpper center.yUpper
      rightUpperInside = northeast outer center strict := by
    apply box_ext <;> rfl
  rw [verticalLower, verticalUpper, leftLower, leftTop, middleLower,
    middleTop, rightLower, rightTop, southwestEq, westEq, northwestEq,
    southEq, centerEq, northEq, southeastEq, eastEq, northeastEq]
  ring1

/-- Assemble all eight cells from the parent boundary and four clear band
sides. -/
def build
    {p : GaussianPolynomial} {outer center : Box}
    (outerClearance : BoundaryClearance p outer)
    (centerProper : center.Proper)
    (strict : center.StrictInterior outer)
    (innerLeft : VerticalLineClearance p outer center.xLower)
    (innerRight : VerticalLineClearance p outer center.xUpper)
    (innerBottom : HorizontalLineClearance p outer center.yLower)
    (innerTop : HorizontalLineClearance p outer center.yUpper) :
    Grid p outer center := by
  let outerLeft := leftOfBoundary outerClearance
  let outerRight := rightOfBoundary outerClearance
  let outerBottom := bottomOfBoundary outerClearance
  let outerTop := topOfBoundary outerClearance
  let sw := southwest outer center strict
  let w := west outer center strict
  let nw := northwest outer center strict
  let s := south outer center strict
  let n := north outer center strict
  let se := southeast outer center strict
  let e := east outer center strict
  let ne := northeast outer center strict
  let swCell : ClearCell p outer center := makeCell
    (box := sw)
    ⟨le_rfl, center.x_valid.trans strict.right.le,
      le_rfl, center.y_valid.trans strict.top.le⟩
    ⟨strict.left, strict.bottom⟩
    outerLeft innerLeft outerBottom innerBottom (Or.inl rfl)
  let wCell : ClearCell p outer center := makeCell
    (box := w)
    ⟨le_rfl, center.x_valid.trans strict.right.le,
      strict.bottom.le, strict.top.le⟩
    ⟨strict.left, centerProper.2⟩
    outerLeft innerLeft innerBottom innerTop (Or.inl rfl)
  let nwCell : ClearCell p outer center := makeCell
    (box := nw)
    ⟨le_rfl, center.x_valid.trans strict.right.le,
      strict.bottom.le.trans center.y_valid, le_rfl⟩
    ⟨strict.left, strict.top⟩
    outerLeft innerLeft innerTop outerTop (Or.inl rfl)
  let sCell : ClearCell p outer center := makeCell
    (box := s)
    ⟨strict.left.le, strict.right.le,
      le_rfl, center.y_valid.trans strict.top.le⟩
    ⟨centerProper.1, strict.bottom⟩
    innerLeft innerRight outerBottom innerBottom
      (Or.inr (Or.inr (Or.inl rfl)))
  let nCell : ClearCell p outer center := makeCell
    (box := n)
    ⟨strict.left.le, strict.right.le,
      strict.bottom.le.trans center.y_valid, le_rfl⟩
    ⟨centerProper.1, strict.top⟩
    innerLeft innerRight innerTop outerTop
      (Or.inr (Or.inr (Or.inr rfl)))
  let seCell : ClearCell p outer center := makeCell
    (box := se)
    ⟨strict.left.le.trans center.x_valid, le_rfl,
      le_rfl, center.y_valid.trans strict.top.le⟩
    ⟨strict.right, strict.bottom⟩
    innerRight outerRight outerBottom innerBottom
      (Or.inr (Or.inl rfl))
  let eCell : ClearCell p outer center := makeCell
    (box := e)
    ⟨strict.left.le.trans center.x_valid, le_rfl,
      strict.bottom.le, strict.top.le⟩
    ⟨strict.right, centerProper.2⟩
    innerRight outerRight innerBottom innerTop
      (Or.inr (Or.inl rfl))
  let neCell : ClearCell p outer center := makeCell
    (box := ne)
    ⟨strict.left.le.trans center.x_valid, le_rfl,
      strict.bottom.le.trans center.y_valid, le_rfl⟩
    ⟨strict.right, strict.top⟩
    innerRight outerRight innerTop outerTop
      (Or.inr (Or.inl rfl))
  exact
    { centerProper := centerProper
      centerInterior := strict
      southwest := swCell
      west := wCell
      northwest := nwCell
      south := sCell
      north := nCell
      southeast := seCell
      east := eCell
      northeast := neCell
      additive := by
        simpa only [swCell, wCell, nwCell, sCell, nCell, seCell, eCell,
          neCell, makeCell, sw, w, nw, s, n, se, e, ne] using
          raw_additivity p outer center strict
      complementsPairwise := by
        apply List.pairwise_cons.mpr
        constructor
        · intro cell member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inl le_rfl))
          · exact Or.inr (Or.inr (Or.inl center.y_valid))
          · exact Or.inl le_rfl
          · exact Or.inl le_rfl
          · exact Or.inl center.x_valid
          · exact Or.inl center.x_valid
          · exact Or.inl center.x_valid
        · apply List.pairwise_cons.mpr
          constructor
          · intro cell member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inr (Or.inr (Or.inl le_rfl))
            · exact Or.inl le_rfl
            · exact Or.inl le_rfl
            · exact Or.inl center.x_valid
            · exact Or.inl center.x_valid
            · exact Or.inl center.x_valid
          · apply List.pairwise_cons.mpr
            constructor
            · intro cell member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl | rfl | rfl
              · exact Or.inl le_rfl
              · exact Or.inl le_rfl
              · exact Or.inl center.x_valid
              · exact Or.inl center.x_valid
              · exact Or.inl center.x_valid
            · apply List.pairwise_cons.mpr
              constructor
              · intro cell member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl | rfl
                · exact Or.inr (Or.inr (Or.inl center.y_valid))
                · exact Or.inl le_rfl
                · exact Or.inl le_rfl
                · exact Or.inl le_rfl
              · apply List.pairwise_cons.mpr
                constructor
                · intro cell member
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with rfl | rfl | rfl
                  · exact Or.inl le_rfl
                  · exact Or.inl le_rfl
                  · exact Or.inl le_rfl
                · apply List.pairwise_cons.mpr
                  constructor
                  · intro cell member
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    rcases member with rfl | rfl
                    · exact Or.inr (Or.inr (Or.inl le_rfl))
                    · exact Or.inr (Or.inr (Or.inl center.y_valid))
                  · apply List.pairwise_cons.mpr
                    constructor
                    · intro cell member
                      have equal : cell = neCell := List.mem_singleton.mp member
                      subst cell
                      exact Or.inr (Or.inr (Or.inl le_rfl))
                    · exact QuotientFreeList.pairwise_singleton _ _
      covers := by
        intro z inside
        by_cases westSide : z.re ≤ center.xLower
        · by_cases southSide : z.im ≤ center.yLower
          · right
            refine ⟨swCell, by simp, ?_⟩
            change (southwest outer center strict).Contains z
            exact ⟨inside.1, westSide, inside.2.2.1, southSide⟩
          · by_cases northSide : center.yUpper ≤ z.im
            · right
              refine ⟨nwCell, by simp, ?_⟩
              change (northwest outer center strict).Contains z
              exact ⟨inside.1, westSide, northSide, inside.2.2.2⟩
            · right
              refine ⟨wCell, by simp, ?_⟩
              change (west outer center strict).Contains z
              exact ⟨inside.1, westSide, (lt_of_not_ge southSide).le,
                (lt_of_not_ge northSide).le⟩
        · by_cases eastSide : center.xUpper ≤ z.re
          · by_cases southSide : z.im ≤ center.yLower
            · right
              refine ⟨seCell, by simp, ?_⟩
              change (southeast outer center strict).Contains z
              exact ⟨eastSide, inside.2.1, inside.2.2.1, southSide⟩
            · by_cases northSide : center.yUpper ≤ z.im
              · right
                refine ⟨neCell, by simp, ?_⟩
                change (northeast outer center strict).Contains z
                exact ⟨eastSide, inside.2.1, northSide, inside.2.2.2⟩
              · right
                refine ⟨eCell, by simp, ?_⟩
                change (east outer center strict).Contains z
                exact ⟨eastSide, inside.2.1,
                  (lt_of_not_ge southSide).le,
                  (lt_of_not_ge northSide).le⟩
          · by_cases southSide : z.im ≤ center.yLower
            · right
              refine ⟨sCell, by simp, ?_⟩
              change (south outer center strict).Contains z
              exact ⟨(lt_of_not_ge westSide).le,
                (lt_of_not_ge eastSide).le, inside.2.2.1, southSide⟩
            · by_cases northSide : center.yUpper ≤ z.im
              · right
                refine ⟨nCell, by simp, ?_⟩
                change (north outer center strict).Contains z
                exact ⟨(lt_of_not_ge westSide).le,
                  (lt_of_not_ge eastSide).le, northSide, inside.2.2.2⟩
              · left
                exact ⟨(lt_of_not_ge westSide).le,
                  (lt_of_not_ge eastSide).le,
                  (lt_of_not_ge southSide).le,
                  (lt_of_not_ge northSide).le⟩ }

/-- Any box strictly inside a complement cell is separated from the removed
center by one strict coordinate inequality. -/
theorem ClearCell.center_separated_from_strictInterior
    {p : GaussianPolynomial} {outer center : Box}
    (cell : ClearCell p outer center) {small : Box}
    (strict : small.StrictInterior cell.box) : center.Separated small := by
  rcases cell.touchesCenter with westTouch | eastTouch | southTouch | northTouch
  · exact Or.inr (Or.inl (strict.right.trans_eq westTouch))
  · exact Or.inl (eastTouch.symm.trans_lt strict.left)
  · exact Or.inr (Or.inr (Or.inr (strict.top.trans_eq southTouch)))
  · exact Or.inr (Or.inr (Or.inl (northTouch.symm.trans_lt strict.bottom)))

/-- Fixed finite order for choosing a negative complement cell. -/
def Grid.firstNegative
    {p : GaussianPolynomial} {outer center : Box}
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
    {p : GaussianPolynomial} {outer center : Box}
    (grid : Grid p outer center)
    (outerNegative : quadrupledBoxWinding p outer < 0)
    (centerFour : quadrupledBoxWinding p center = 4) :
    quadrupledBoxWinding p grid.firstNegative.box < 0 := by
  by_cases swNegative : quadrupledBoxWinding p grid.southwest.box < 0
  · simp [Grid.firstNegative, swNegative]
  by_cases wNegative : quadrupledBoxWinding p grid.west.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative]
  by_cases nwNegative : quadrupledBoxWinding p grid.northwest.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative, nwNegative]
  by_cases sNegative : quadrupledBoxWinding p grid.south.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative, nwNegative, sNegative]
  by_cases nNegative : quadrupledBoxWinding p grid.north.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative, nwNegative, sNegative,
      nNegative]
  by_cases seNegative : quadrupledBoxWinding p grid.southeast.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative, nwNegative, sNegative,
      nNegative, seNegative]
  by_cases eNegative : quadrupledBoxWinding p grid.east.box < 0
  · simp [Grid.firstNegative, swNegative, wNegative, nwNegative, sNegative,
      nNegative, seNegative, eNegative]
  have neNegative : quadrupledBoxWinding p grid.northeast.box < 0 := by
    have swNonnegative := le_of_not_gt swNegative
    have wNonnegative := le_of_not_gt wNegative
    have nwNonnegative := le_of_not_gt nwNegative
    have sNonnegative := le_of_not_gt sNegative
    have nNonnegative := le_of_not_gt nNegative
    have seNonnegative := le_of_not_gt seNegative
    have eNonnegative := le_of_not_gt eNegative
    rw [grid.additive, centerFour] at outerNegative
    omega
  simpa [Grid.firstNegative, swNegative, wNegative, nwNegative, sNegative,
    nNegative, seNegative, eNegative] using neNegative

end RFAP.CentralBandGrid
