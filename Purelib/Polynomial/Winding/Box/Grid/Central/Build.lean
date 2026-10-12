module
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Membership
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Grid.Central
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Grid.Central.Build
import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Additivity
public import Purelib.Polynomial.Winding.Box.Grid.Central.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Winding.Box.Basic

open Purelib.Data
open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Winding decomposition around a central box

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the retained central box; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace Purelib.Polynomial.Winding.Box.Grid.Central.Build

/-- Assemble the eight winding cells around a strictly interior central box.

The builder retains the original corner and side boxes, their quantitative
boundary clearances, fixed complement order and exact winding additivity.
Direct finite membership certificates establish their separation and covering. -/
@[expose] public def build
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (outerClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p outer)
    (centerProper : center.Proper)
    (strict : center.StrictInterior outer)
    (innerLeft : Clearance.Box.Line.Basic.VerticalLineClearance p outer center.xLower)
    (innerRight : Clearance.Box.Line.Basic.VerticalLineClearance p outer center.xUpper)
    (innerBottom : Clearance.Box.Line.Basic.HorizontalLineClearance p outer center.yLower)
    (innerTop : Clearance.Box.Line.Basic.HorizontalLineClearance p outer center.yUpper) :
    Basic.Arrangement p outer center := open Purelib in by
  let outerLeft := Clearance.Box.Boundary.Lines.leftOfBoundary outerClearance
  let outerRight := Clearance.Box.Boundary.Lines.rightOfBoundary outerClearance
  let outerBottom := Clearance.Box.Boundary.Lines.bottomOfBoundary outerClearance
  let outerTop := Clearance.Box.Boundary.Lines.topOfBoundary outerClearance
  let sw := Box.Grid.Central.southwest outer center strict
  let w := Box.Grid.Central.west outer center strict
  let nw := Box.Grid.Central.northwest outer center strict
  let s := Box.Grid.Central.south outer center strict
  let n := Box.Grid.Central.north outer center strict
  let se := Box.Grid.Central.southeast outer center strict
  let e := Box.Grid.Central.east outer center strict
  let ne := Box.Grid.Central.northeast outer center strict
  let swCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := sw)
    ⟨(Rat.Fraction.Order.Basic.le_refl _), center.x_valid.trans strict.right.le,
      (Rat.Fraction.Order.Basic.le_refl _), center.y_valid.trans strict.top.le⟩
    ⟨strict.left, strict.bottom⟩
    outerLeft innerLeft outerBottom innerBottom (Or.inl rfl)
  let wCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := w)
    ⟨(Rat.Fraction.Order.Basic.le_refl _), center.x_valid.trans strict.right.le,
      strict.bottom.le, strict.top.le⟩
    ⟨strict.left, centerProper.2⟩
    outerLeft innerLeft innerBottom innerTop (Or.inl rfl)
  let nwCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := nw)
    ⟨(Rat.Fraction.Order.Basic.le_refl _), center.x_valid.trans strict.right.le,
      strict.bottom.le.trans center.y_valid, (Rat.Fraction.Order.Basic.le_refl _)⟩
    ⟨strict.left, strict.top⟩
    outerLeft innerLeft innerTop outerTop (Or.inl rfl)
  let sCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := s)
    ⟨strict.left.le, strict.right.le,
      (Rat.Fraction.Order.Basic.le_refl _), center.y_valid.trans strict.top.le⟩
    ⟨centerProper.1, strict.bottom⟩
    innerLeft innerRight outerBottom innerBottom
      (Or.inr (Or.inr (Or.inl rfl)))
  let nCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := n)
    ⟨strict.left.le, strict.right.le,
      strict.bottom.le.trans center.y_valid, (Rat.Fraction.Order.Basic.le_refl _)⟩
    ⟨centerProper.1, strict.top⟩
    innerLeft innerRight innerTop outerTop
      (Or.inr (Or.inr (Or.inr rfl)))
  let seCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := se)
    ⟨strict.left.le.trans center.x_valid, (Rat.Fraction.Order.Basic.le_refl _),
      (Rat.Fraction.Order.Basic.le_refl _), center.y_valid.trans strict.top.le⟩
    ⟨strict.right, strict.bottom⟩
    innerRight outerRight outerBottom innerBottom
      (Or.inr (Or.inl rfl))
  let eCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := e)
    ⟨strict.left.le.trans center.x_valid, (Rat.Fraction.Order.Basic.le_refl _),
      strict.bottom.le, strict.top.le⟩
    ⟨strict.right, centerProper.2⟩
    innerRight outerRight innerBottom innerTop
      (Or.inr (Or.inl rfl))
  let neCell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center := Clearance.Box.Grid.Central.Build.makeCell
    (box := ne)
    ⟨strict.left.le.trans center.x_valid, (Rat.Fraction.Order.Basic.le_refl _),
      strict.bottom.le.trans center.y_valid, (Rat.Fraction.Order.Basic.le_refl _)⟩
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
          neCell, Clearance.Box.Grid.Central.Build.makeCell, sw, w, nw, s, n, se, e, ne] using
          Winding.Box.Grid.Central.Additivity.raw_additivity p outer center strict
      complementsPairwise := by
        apply List.pairwise_cons.mpr
        constructor
        · intro cell member
          rcases List.Membership.mem_cons.mp member with rfl | member
          · exact Or.inr (Or.inr (Or.inl (Rat.Fraction.Order.Basic.le_refl _)))
          · rcases List.Membership.mem_cons.mp member with rfl | member
            · exact Or.inr (Or.inr (Or.inl center.y_valid))
            · rcases List.Membership.mem_cons.mp member with rfl | member
              · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
              · rcases List.Membership.mem_cons.mp member with rfl | member
                · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                · rcases List.Membership.mem_cons.mp member with rfl | member
                  · exact Or.inl center.x_valid
                  · rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inl center.x_valid
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inl center.x_valid
        · apply List.pairwise_cons.mpr
          constructor
          · intro cell member
            rcases List.Membership.mem_cons.mp member with rfl | member
            · exact Or.inr (Or.inr (Or.inl (Rat.Fraction.Order.Basic.le_refl _)))
            · rcases List.Membership.mem_cons.mp member with rfl | member
              · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
              · rcases List.Membership.mem_cons.mp member with rfl | member
                · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                · rcases List.Membership.mem_cons.mp member with rfl | member
                  · exact Or.inl center.x_valid
                  · rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inl center.x_valid
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inl center.x_valid
          · apply List.pairwise_cons.mpr
            constructor
            · intro cell member
              rcases List.Membership.mem_cons.mp member with rfl | member
              · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
              · rcases List.Membership.mem_cons.mp member with rfl | member
                · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                · rcases List.Membership.mem_cons.mp member with rfl | member
                  · exact Or.inl center.x_valid
                  · rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inl center.x_valid
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inl center.x_valid
            · apply List.pairwise_cons.mpr
              constructor
              · intro cell member
                rcases List.Membership.mem_cons.mp member with rfl | member
                · exact Or.inr (Or.inr (Or.inl center.y_valid))
                · rcases List.Membership.mem_cons.mp member with rfl | member
                  · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                  · rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
              · apply List.pairwise_cons.mpr
                constructor
                · intro cell member
                  rcases List.Membership.mem_cons.mp member with rfl | member
                  · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                  · rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inl (Rat.Fraction.Order.Basic.le_refl _)
                · apply List.pairwise_cons.mpr
                  constructor
                  · intro cell member
                    rcases List.Membership.mem_cons.mp member with rfl | member
                    · exact Or.inr (Or.inr (Or.inl (Rat.Fraction.Order.Basic.le_refl _)))
                    · have equal : cell = _ := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inr (Or.inr (Or.inl center.y_valid))
                  · apply List.pairwise_cons.mpr
                    constructor
                    · intro cell member
                      have equal : cell = neCell := List.Membership.mem_singleton.mp member
                      subst cell
                      exact Or.inr (Or.inr (Or.inl (Rat.Fraction.Order.Basic.le_refl _)))
                    · exact Data.List.Pairwise.pairwise_singleton _ _
      covers := by
        intro z inside
        by_cases westSide : z.re ≤ center.xLower
        · by_cases southSide : z.im ≤ center.yLower
          · right
            refine ⟨swCell, List.Mem.head _, ?_⟩
            change (Box.Grid.Central.southwest outer center strict).Contains z
            exact ⟨inside.1, westSide, inside.2.2.1, southSide⟩
          · by_cases northSide : center.yUpper ≤ z.im
            · right
              refine ⟨nwCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.head _)), ?_⟩
              change (Box.Grid.Central.northwest outer center strict).Contains z
              exact ⟨inside.1, westSide, northSide, inside.2.2.2⟩
            · right
              refine ⟨wCell, List.Mem.tail swCell (List.Mem.head _), ?_⟩
              change (Box.Grid.Central.west outer center strict).Contains z
              exact ⟨inside.1, westSide, (lt_of_not_ge southSide).le,
                (lt_of_not_ge northSide).le⟩
        · by_cases eastSide : center.xUpper ≤ z.re
          · by_cases southSide : z.im ≤ center.yLower
            · right
              refine ⟨seCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.tail nwCell (List.Mem.tail sCell
                (List.Mem.tail nCell (List.Mem.head _))))), ?_⟩
              change (Box.Grid.Central.southeast outer center strict).Contains z
              exact ⟨eastSide, inside.2.1, inside.2.2.1, southSide⟩
            · by_cases northSide : center.yUpper ≤ z.im
              · right
                refine ⟨neCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.tail nwCell (List.Mem.tail sCell
                  (List.Mem.tail nCell (List.Mem.tail seCell (List.Mem.tail eCell (List.Mem.head _))))))), ?_⟩
                change (Box.Grid.Central.northeast outer center strict).Contains z
                exact ⟨eastSide, inside.2.1, northSide, inside.2.2.2⟩
              · right
                refine ⟨eCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.tail nwCell (List.Mem.tail sCell
                  (List.Mem.tail nCell (List.Mem.tail seCell (List.Mem.head _)))))), ?_⟩
                change (Box.Grid.Central.east outer center strict).Contains z
                exact ⟨eastSide, inside.2.1,
                  (lt_of_not_ge southSide).le,
                  (lt_of_not_ge northSide).le⟩
          · by_cases southSide : z.im ≤ center.yLower
            · right
              refine ⟨sCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.tail nwCell (List.Mem.head _))), ?_⟩
              change (Box.Grid.Central.south outer center strict).Contains z
              exact ⟨(lt_of_not_ge westSide).le,
                (lt_of_not_ge eastSide).le, inside.2.2.1, southSide⟩
            · by_cases northSide : center.yUpper ≤ z.im
              · right
                refine ⟨nCell, List.Mem.tail swCell (List.Mem.tail wCell (List.Mem.tail nwCell (List.Mem.tail sCell
                  (List.Mem.head _)))), ?_⟩
                change (Box.Grid.Central.north outer center strict).Contains z
                exact ⟨(lt_of_not_ge westSide).le,
                  (lt_of_not_ge eastSide).le, northSide, inside.2.2.2⟩
              · left
                exact ⟨(lt_of_not_ge westSide).le,
                  (lt_of_not_ge eastSide).le,
                  (lt_of_not_ge southSide).le,
                  (lt_of_not_ge northSide).le⟩ }
end Purelib.Polynomial.Winding.Box.Grid.Central.Build
