import CCL.Riemann.FinitePeriodCurves
import CCL.Riemann.FinitePeriodTheorem

/-!
# Explicit finite branch data for the cyclic quartic

This file supplies four audited rational winding boxes for
`y² = x⁴ - 1`.  Their centres are the exact Gaussian-rational roots
`-1`, `1`, `-i`, and `i`.  Every box has horizontal radius `1/4` and vertical
radius `1/2`; the narrow horizontal direction keeps the four interiors
separated while the lower boundary places the canonical connectors in the
balanced corridor between the horizontal and vertical branch points.
Factorwise boundary clearance and an exact quadrupled winding calculation
turn the boxes into a
degree-complete shrinking branch family.  Thus the period programs below use
the explicit-data theorem path and do not execute the generic global root
isolator while elaborating the example.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

open CCL.Riemann.FinitePeriodExamples

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

def point (x y : Coordinate) : Gaussian := ⟨x, y⟩

def factor (x y : Coordinate) : GaussianPolynomial :=
  RFAP.AffineWinding.translatedCoordinate (point x y)

def boxAt (x y : Coordinate) : Box :=
  { xLower := x - 1 / 4
    xUpper := x + 1 / 4
    yLower := y - 1 / 2
    yUpper := y + 1 / 2
    x_valid := by
      apply le_of_lt
      calc
        x - 1 / 4 < x := by
          simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
        _ < x + 1 / 4 := by
          simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
    y_valid := by
      apply le_of_lt
      calc
        y - 1 / 2 < y := by
          simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (by decide : (0 : Coordinate) < 1 / 2) y
        _ < y + 1 / 2 := by
          simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
            (by decide : (0 : Coordinate) < 1 / 2) y }

theorem boxAt_proper (x y : Coordinate) : (boxAt x y).Proper := by
  constructor
  · change x - 1 / 4 < x + 1 / 4
    calc
      x - 1 / 4 < x := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
      _ < x + 1 / 4 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
  · change y - 1 / 2 < y + 1 / 2
    calc
      y - 1 / 2 < y := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) y
      _ < y + 1 / 2 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) y

def factors : GaussianPolynomial :=
  ((factor (-1) 0 * factor 1 0) * factor 0 (-1)) * factor 0 1

theorem quarticPolynomial_eq_factors : quarticPolynomial = factors := by
  decide

def selfClearance (x y : Coordinate) :
    RFAP.BoxClearance.BoundaryClearance (factor x y) (boxAt x y) := by
  exact RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox
    (point x y) (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 2) y)
    (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 2) y)

def leftClearance (rootX rootY boxX boxY : Coordinate)
    (separated : rootX < boxX - 1 / 4) :
    RFAP.BoxClearance.BoundaryClearance
      (factor rootX rootY) (boxAt boxX boxY) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_left
    (point rootX rootY) (by
      unfold boxAt point
      exact separated)

def rightClearance (rootX rootY boxX boxY : Coordinate)
    (separated : boxX + 1 / 4 < rootX) :
    RFAP.BoxClearance.BoundaryClearance
      (factor rootX rootY) (boxAt boxX boxY) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_right
    (point rootX rootY) (by
      unfold boxAt point
      exact separated)

def belowClearance (rootX rootY boxX boxY : Coordinate)
    (separated : rootY < boxY - 1 / 2) :
    RFAP.BoxClearance.BoundaryClearance
      (factor rootX rootY) (boxAt boxX boxY) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_below
    (point rootX rootY) (by
      unfold boxAt point
      exact separated)

def aboveClearance (rootX rootY boxX boxY : Coordinate)
    (separated : boxY + 1 / 2 < rootY) :
    RFAP.BoxClearance.BoundaryClearance
      (factor rootX rootY) (boxAt boxX boxY) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_above
    (point rootX rootY) (by
      unfold boxAt point
      exact separated)

def factorsClearanceMinusOne :
    RFAP.BoxClearance.BoundaryClearance factors (boxAt (-1) 0) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (RFAP.BoxClearance.BoundaryClearance.mul
        (selfClearance (-1) 0)
        (rightClearance 1 0 (-1) 0 (by decide)))
      (rightClearance 0 (-1) (-1) 0 (by decide)))
    (rightClearance 0 1 (-1) 0 (by decide))

def factorsClearanceOne :
    RFAP.BoxClearance.BoundaryClearance factors (boxAt 1 0) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (RFAP.BoxClearance.BoundaryClearance.mul
        (leftClearance (-1) 0 1 0 (by decide))
        (selfClearance 1 0))
      (leftClearance 0 (-1) 1 0 (by decide)))
    (leftClearance 0 1 1 0 (by decide))

def factorsClearanceMinusI :
    RFAP.BoxClearance.BoundaryClearance factors (boxAt 0 (-1)) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (RFAP.BoxClearance.BoundaryClearance.mul
        (leftClearance (-1) 0 0 (-1) (by decide))
        (rightClearance 1 0 0 (-1) (by decide)))
      (selfClearance 0 (-1)))
    (aboveClearance 0 1 0 (-1) (by decide))

def factorsClearanceI :
    RFAP.BoxClearance.BoundaryClearance factors (boxAt 0 1) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (RFAP.BoxClearance.BoundaryClearance.mul
        (leftClearance (-1) 0 0 1 (by decide))
        (rightClearance 1 0 0 1 (by decide)))
      (belowClearance 0 (-1) 0 1 (by decide)))
    (selfClearance 0 1)

def polynomialClearanceMinusOne :
    RFAP.BoxClearance.BoundaryClearance quarticPolynomial (boxAt (-1) 0) := by
  rw [quarticPolynomial_eq_factors]
  exact factorsClearanceMinusOne

def polynomialClearanceOne :
    RFAP.BoxClearance.BoundaryClearance quarticPolynomial (boxAt 1 0) := by
  rw [quarticPolynomial_eq_factors]
  exact factorsClearanceOne

def polynomialClearanceMinusI :
    RFAP.BoxClearance.BoundaryClearance quarticPolynomial (boxAt 0 (-1)) := by
  rw [quarticPolynomial_eq_factors]
  exact factorsClearanceMinusI

def polynomialClearanceI :
    RFAP.BoxClearance.BoundaryClearance quarticPolynomial (boxAt 0 1) := by
  rw [quarticPolynomial_eq_factors]
  exact factorsClearanceI

def factorsVerticalClearance (x : Coordinate)
    (apartMinusOne : x ≠ -1) (apartOne : x ≠ 1)
    (apartZero : x ≠ 0) :
    RFAP.BoxClearance.VerticalLineClearance factors
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) x :=
  RFAP.BoxClearance.VerticalLineClearance.mul
    (RFAP.BoxClearance.VerticalLineClearance.mul
      (RFAP.BoxClearance.VerticalLineClearance.mul
        (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
          (point (-1) 0) _ x apartMinusOne)
        (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
          (point 1 0) _ x apartOne))
      (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
        (point 0 (-1)) _ x apartZero))
    (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
      (point 0 1) _ x apartZero)

def polynomialVerticalClearance (x : Coordinate)
    (apartMinusOne : x ≠ -1) (apartOne : x ≠ 1)
    (apartZero : x ≠ 0) :
    RFAP.BoxClearance.VerticalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) x := by
  rw [quarticPolynomial_eq_factors]
  exact factorsVerticalClearance x apartMinusOne apartOne apartZero

def factorsHorizontalClearance (y : Coordinate)
    (apartZero : y ≠ 0) (apartMinusOne : y ≠ -1)
    (apartOne : y ≠ 1) :
    RFAP.BoxClearance.HorizontalLineClearance factors
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) y :=
  RFAP.BoxClearance.HorizontalLineClearance.mul
    (RFAP.BoxClearance.HorizontalLineClearance.mul
      (RFAP.BoxClearance.HorizontalLineClearance.mul
        (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
          (point (-1) 0) _ y apartZero)
        (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
          (point 1 0) _ y apartZero))
      (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
        (point 0 (-1)) _ y apartMinusOne))
    (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
      (point 0 1) _ y apartOne)

def polynomialHorizontalClearance (y : Coordinate)
    (apartZero : y ≠ 0) (apartMinusOne : y ≠ -1)
    (apartOne : y ≠ 1) :
    RFAP.BoxClearance.HorizontalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) y := by
  rw [quarticPolynomial_eq_factors]
  exact factorsHorizontalClearance y apartZero apartMinusOne apartOne

theorem refinesAmbient (x y : Coordinate)
    (lowerX : -RFAP.GlobalWinding.denseLargeSquareRadius quarticPolynomial ≤
      (boxAt x y).xLower)
    (upperX : (boxAt x y).xUpper ≤
      RFAP.GlobalWinding.denseLargeSquareRadius quarticPolynomial)
    (lowerY : -RFAP.GlobalWinding.denseLargeSquareRadius quarticPolynomial ≤
      (boxAt x y).yLower)
    (upperY : (boxAt x y).yUpper ≤
      RFAP.GlobalWinding.denseLargeSquareRadius quarticPolynomial) :
    (boxAt x y).Refines
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) := by
  unfold RFAP.Boxes.Box.Refines RFAP.GlobalWinding.largeSquareBox
    RFAP.Boxes.Box.symmetric
  exact ⟨lowerX, upperX, lowerY, upperY⟩

theorem windingMinusOne :
    RFAP.Winding.quadrupledBoxWinding quarticPolynomial
      (boxAt (-1) 0) = 4 := by decide

theorem windingOne :
    RFAP.Winding.quadrupledBoxWinding quarticPolynomial
      (boxAt 1 0) = 4 := by decide

theorem windingMinusI :
    RFAP.Winding.quadrupledBoxWinding quarticPolynomial
      (boxAt 0 (-1)) = 4 := by decide

theorem windingI :
    RFAP.Winding.quadrupledBoxWinding quarticPolynomial
      (boxAt 0 1) = 4 := by decide

def rawMinusOne : RFAP.RawSubdivision.RawWindingState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) where
  box := boxAt (-1) 0
  refinesAmbient := refinesAmbient (-1) 0 (by decide) (by decide)
    (by decide) (by decide)
  proper := boxAt_proper (-1) 0
  clearance := polynomialClearanceMinusOne
  rawWinding_ne := by
    rw [windingMinusOne]
    decide

def rawOne : RFAP.RawSubdivision.RawWindingState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) where
  box := boxAt 1 0
  refinesAmbient := refinesAmbient 1 0 (by decide) (by decide)
    (by decide) (by decide)
  proper := boxAt_proper 1 0
  clearance := polynomialClearanceOne
  rawWinding_ne := by
    rw [windingOne]
    decide

def rawMinusI : RFAP.RawSubdivision.RawWindingState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) where
  box := boxAt 0 (-1)
  refinesAmbient := refinesAmbient 0 (-1) (by decide) (by decide)
    (by decide) (by decide)
  proper := boxAt_proper 0 (-1)
  clearance := polynomialClearanceMinusI
  rawWinding_ne := by
    rw [windingMinusI]
    decide

def rawI : RFAP.RawSubdivision.RawWindingState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) where
  box := boxAt 0 1
  refinesAmbient := refinesAmbient 0 1 (by decide) (by decide)
    (by decide) (by decide)
  proper := boxAt_proper 0 1
  clearance := polynomialClearanceI
  rawWinding_ne := by
    rw [windingI]
    decide

def stateOfRaw
    (raw : RFAP.RawSubdivision.RawWindingState quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial))
    (windingFour : RFAP.Winding.quadrupledBoxWinding quarticPolynomial
      raw.box = 4)
    (left : RFAP.BoxClearance.VerticalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) raw.box.xLower)
    (right : RFAP.BoxClearance.VerticalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) raw.box.xUpper)
    (bottom : RFAP.BoxClearance.HorizontalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) raw.box.yLower)
    (top : RFAP.BoxClearance.HorizontalLineClearance quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) raw.box.yUpper) :
    RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
      (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) where
  box := raw.box
  refinesAmbient := raw.refinesAmbient
  proper := raw.proper
  clearance := raw.clearance
  rawWindingFour := windingFour
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

def stateMinusOne : RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) :=
  stateOfRaw rawMinusOne windingMinusOne
    (polynomialVerticalClearance (boxAt (-1) 0).xLower
      (by decide) (by decide) (by decide))
    (polynomialVerticalClearance (boxAt (-1) 0).xUpper
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt (-1) 0).yLower
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt (-1) 0).yUpper
      (by decide) (by decide) (by decide))

def stateOne : RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) :=
  stateOfRaw rawOne windingOne
    (polynomialVerticalClearance (boxAt 1 0).xLower
      (by decide) (by decide) (by decide))
    (polynomialVerticalClearance (boxAt 1 0).xUpper
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 1 0).yLower
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 1 0).yUpper
      (by decide) (by decide) (by decide))

def stateMinusI : RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) :=
  stateOfRaw rawMinusI windingMinusI
    (polynomialVerticalClearance (boxAt 0 (-1)).xLower
      (by decide) (by decide) (by decide))
    (polynomialVerticalClearance (boxAt 0 (-1)).xUpper
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 0 (-1)).yLower
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 0 (-1)).yUpper
      (by decide) (by decide) (by decide))

def stateI : RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial) :=
  stateOfRaw rawI windingI
    (polynomialVerticalClearance (boxAt 0 1).xLower
      (by decide) (by decide) (by decide))
    (polynomialVerticalClearance (boxAt 0 1).xUpper
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 0 1).yLower
      (by decide) (by decide) (by decide))
    (polynomialHorizontalClearance (boxAt 0 1).yUpper
      (by decide) (by decide) (by decide))

def rawAt : Fin 4 → RFAP.RawSubdivision.RawWindingState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial)
  | ⟨0, _⟩ => rawMinusOne
  | ⟨1, _⟩ => rawOne
  | ⟨2, _⟩ => rawMinusI
  | ⟨3, _⟩ => rawI

def stateAt : Fin 4 → RFAP.ShrinkingTrack.WindingOneState quarticPolynomial
    (RFAP.GlobalWinding.largeSquareBox quarticPolynomial)
  | ⟨0, _⟩ => stateMinusOne
  | ⟨1, _⟩ => stateOne
  | ⟨2, _⟩ => stateMinusI
  | ⟨3, _⟩ => stateI

theorem rawAt_pairwise : ∀ left right : Fin 4, left ≠ right →
    (rawAt left).box.InteriorSeparated (rawAt right).box
  | ⟨0, _⟩, ⟨0, _⟩, different => (different rfl).elim
  | ⟨0, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) ≤ 3 / 4
      decide)
  | ⟨0, _⟩, ⟨2, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) ≤ -1 / 4
      decide)
  | ⟨0, _⟩, ⟨3, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) ≤ -1 / 4
      decide)
  | ⟨1, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) ≤ 3 / 4
      decide))
  | ⟨1, _⟩, ⟨1, _⟩, different => (different rfl).elim
  | ⟨1, _⟩, ⟨2, _⟩, _ => Or.inr (Or.inl (by
      change (1 / 4 : Coordinate) ≤ 3 / 4
      decide))
  | ⟨1, _⟩, ⟨3, _⟩, _ => Or.inr (Or.inl (by
      change (1 / 4 : Coordinate) ≤ 3 / 4
      decide))
  | ⟨2, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) ≤ -1 / 4
      decide))
  | ⟨2, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (1 / 4 : Coordinate) ≤ 3 / 4
      decide)
  | ⟨2, _⟩, ⟨2, _⟩, different => (different rfl).elim
  | ⟨2, _⟩, ⟨3, _⟩, _ => Or.inr (Or.inr (Or.inl (by
      change (-1 / 2 : Coordinate) ≤ 1 / 2
      decide)))
  | ⟨3, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) ≤ -1 / 4
      decide))
  | ⟨3, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (1 / 4 : Coordinate) ≤ 3 / 4
      decide)
  | ⟨3, _⟩, ⟨2, _⟩, _ => Or.inr (Or.inr (Or.inr (by
      change (-1 / 2 : Coordinate) ≤ 1 / 2
      decide)))
  | ⟨3, _⟩, ⟨3, _⟩, different => (different rfl).elim

theorem stateAt_pairwise : ∀ left right : Fin 4, left ≠ right →
    (stateAt left).box.Separated (stateAt right).box
  | ⟨0, _⟩, ⟨0, _⟩, different => (different rfl).elim
  | ⟨0, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) < 3 / 4
      decide)
  | ⟨0, _⟩, ⟨2, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide)
  | ⟨0, _⟩, ⟨3, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide)
  | ⟨1, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) < 3 / 4
      decide))
  | ⟨1, _⟩, ⟨1, _⟩, different => (different rfl).elim
  | ⟨1, _⟩, ⟨2, _⟩, _ => Or.inr (Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide))
  | ⟨1, _⟩, ⟨3, _⟩, _ => Or.inr (Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide))
  | ⟨2, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide))
  | ⟨2, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide)
  | ⟨2, _⟩, ⟨2, _⟩, different => (different rfl).elim
  | ⟨2, _⟩, ⟨3, _⟩, _ => Or.inr (Or.inr (Or.inl (by
      change (-1 / 2 : Coordinate) < 1 / 2
      decide)))
  | ⟨3, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide))
  | ⟨3, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide)
  | ⟨3, _⟩, ⟨2, _⟩, _ => Or.inr (Or.inr (Or.inr (by
      change (-1 / 2 : Coordinate) < 1 / 2
      decide)))
  | ⟨3, _⟩, ⟨3, _⟩, different => (different rfl).elim

def curveRawAt (index : Fin quarticCurve.polynomial.natDegree) :
    RFAP.RawSubdivision.RawWindingState quarticCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox quarticCurve.polynomial) :=
  rawAt (Fin.cast quartic_degree index)

def curveStateAt (index : Fin quarticCurve.polynomial.natDegree) :
    RFAP.ShrinkingTrack.WindingOneState quarticCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox quarticCurve.polynomial) :=
  stateAt (Fin.cast quartic_degree index)

theorem curveRawAt_pairwise
    (left right : Fin quarticCurve.polynomial.natDegree)
    (different : left ≠ right) :
    (curveRawAt left).box.InteriorSeparated (curveRawAt right).box := by
  apply rawAt_pairwise
  intro equal
  apply different
  apply Fin.ext
  exact congrArg Fin.val equal

theorem curveStateAt_pairwise
    (left right : Fin quarticCurve.polynomial.natDegree)
    (different : left ≠ right) :
    (curveStateAt left).box.Separated (curveStateAt right).box := by
  apply stateAt_pairwise
  intro equal
  apply different
  apply Fin.ext
  exact congrArg Fin.val equal

/-- Four explicit, pairwise-separated shrinking branch tracks for
`y² = x⁴ - 1`. -/
def branchData : CCL.Riemann.BranchIsolation.Data quarticCurve :=
  CCL.Riemann.BranchIsolation.Data.ofStates quarticCurve
    (by
      change 1 < quarticPolynomial.natDegree
      rw [quartic_degree]
      decide)
    curveStateAt curveStateAt_pairwise

theorem branchData_siteCount : branchData.siteCount = 4 := rfl

/-! ## Explicit quadratic sheet owners at the branch-box anchors -/

/-- Refinement-zero endpoints of the four displayed branch tracks. -/
def squareRootEndpointPoint : Fin 4 → Gaussian
  | ⟨0, _⟩ => point (-5 / 4) (-1 / 2)
  | ⟨1, _⟩ => point (3 / 4) (-1 / 2)
  | ⟨2, _⟩ => point (-1 / 4) (-3 / 2)
  | ⟨3, _⟩ => point (-1 / 4) (1 / 2)

/-- Exact nonzero quartic radicand at each branch-box endpoint. -/
def squareRootParameter (index : Fin 4) : Gaussian :=
  quarticPolynomial.eval (squareRootEndpointPoint index)

private theorem sixteen_ne : (16 : Coordinate) ≠ 0 := by decide

private theorem thirtyTwo_ne : (32 : Coordinate) ≠ 0 := by
  rw [show (32 : Coordinate) = 2 * 16 by ring1]
  exact RFAP.ConstructiveFraction.mul_ne_zero_direct (by decide) sixteen_ne

private theorem sixtyFour_ne : (64 : Coordinate) ≠ 0 := by
  rw [show (64 : Coordinate) = 4 * 16 by ring1]
  exact RFAP.ConstructiveFraction.mul_ne_zero_direct (by decide) sixteen_ne

private theorem twoFiftySix_ne : (256 : Coordinate) ≠ 0 := by
  rw [show (256 : Coordinate) = 16 * 16 by ring1]
  exact RFAP.ConstructiveFraction.mul_ne_zero_direct sixteen_ne sixteen_ne

private theorem firstEndpointSquare_real :
    (21 / 16 : Coordinate) * (21 / 16) - (5 / 4) * (5 / 4) =
      41 / 256 := by
  rw [RFAP.ConstructiveFraction.div_mul_div_direct,
    RFAP.ConstructiveFraction.div_mul_div_direct]
  rw [RFAP.ConstructiveFraction.div_sub_div_direct _ _ _ _
    (by decide) (by decide)]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct
      (RFAP.ConstructiveFraction.mul_ne_zero_direct sixteen_ne sixteen_ne)
      (RFAP.ConstructiveFraction.mul_ne_zero_direct (by decide) (by decide)))
    twoFiftySix_ne
  ring1

private theorem firstEndpointProduct :
    (21 / 16 : Coordinate) * (5 / 4) = 105 / 64 := by
  rw [RFAP.ConstructiveFraction.div_mul_div_direct]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct sixteen_ne (by decide))
    sixtyFour_ne
  ring1

private theorem firstEndpointSquare_imag :
    (21 / 16 : Coordinate) * (5 / 4) + (5 / 4) * (21 / 16) =
      105 / 32 := by
  rw [firstEndpointProduct]
  rw [RFAP.ConstructiveFraction.mul_comm (5 / 4 : Coordinate) (21 / 16),
    firstEndpointProduct]
  calc
    (105 / 64 : Coordinate) + 105 / 64 = 2 * (105 / 64) := by ring1
    _ = (2 / 1 : Coordinate) * (105 / 64) := by
      rw [show (2 / 1 : Coordinate) = 2 by decide]
    _ = (2 * 105) / (1 * 64) :=
      RFAP.ConstructiveFraction.div_mul_div_direct 2 1 105 64
    _ = 105 / 32 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (RFAP.ConstructiveFraction.mul_ne_zero_direct
          (by decide) sixtyFour_ne)
        thirtyTwo_ne
      ring1

private theorem firstEndpointSubOne :
    (41 / 256 : Coordinate) - 1 = -215 / 256 := by
  rw [show (1 : Coordinate) = 1 / 1 by decide]
  rw [RFAP.ConstructiveFraction.div_sub_div_direct _ _ _ _
    twoFiftySix_ne (by decide)]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct twoFiftySix_ne (by decide))
    twoFiftySix_ne
  ring1

/-- Cached exact quartic radicand at the first displayed branch-box
endpoint. -/
theorem squareRootParameter_zero_eq :
    squareRootParameter 0 = point (-215 / 256) (105 / 32) := by
  unfold squareRootParameter squareRootEndpointPoint quarticPolynomial
  rw [CCL.PowerMonodromy.polynomial_eval]
  change point (-5 / 4) (-1 / 2) ^ 4 - 1 =
    point (-215 / 256) (105 / 32)
  have square : point (-5 / 4) (-1 / 2) ^ 2 =
      point (21 / 16) (5 / 4) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have fourth : point (-5 / 4) (-1 / 2) ^ 4 =
      point (21 / 16) (5 / 4) ^ 2 := by
    calc
      point (-5 / 4) (-1 / 2) ^ 4 =
          point (-5 / 4) (-1 / 2) ^ 2 *
            point (-5 / 4) (-1 / 2) ^ 2 := by ring1
      _ = point (21 / 16) (5 / 4) ^ 2 := by
        rw [square]
        simp only [pow_two]
  rw [fourth]
  have squareAgain : point (21 / 16) (5 / 4) ^ 2 =
      point (41 / 256) (105 / 32) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact firstEndpointSquare_real
    · exact firstEndpointSquare_imag
  rw [squareAgain]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · exact firstEndpointSubOne
  · change (105 / 32 : Coordinate) - 0 = 105 / 32
    ring1

/-- One short rational approximation to a square root of each endpoint
radicand.  Its negative supplies the other sheet owner. -/
def positiveSquareRootCenter : Fin 4 → Gaussian
  | ⟨0, _⟩ => point 1 2
  | ⟨1, _⟩ => point 0 (-3 / 2)
  | ⟨2, _⟩ => point 2 (-1)
  | ⟨3, _⟩ => point 0 1

def squareRootCenter (index : Fin 4) : Fin 2 → Gaussian
  | ⟨0, _⟩ => positiveSquareRootCenter index
  | ⟨1, _⟩ => -positiveSquareRootCenter index

def squareRootOwnerBox (index : Fin 4) (sheet : Fin 2) : Box :=
  RFAP.AffineWinding.centeredSquare (squareRootCenter index sheet)
    (3 / 4) (by decide)

def squareRootPolynomial (index : Fin 4) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial (squareRootParameter index)
    CCL.Riemann.SquareRootSheets.degreeTwo

theorem squareRootParameter_nonzero :
    ∀ index : Fin 4, squareRootParameter index ≠ 0 := by
  decide +revert

theorem squareRootOwner_leftNonzero : ∀ index : Fin 4, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xLower ≠
        0 := by
  decide +revert

theorem squareRootOwner_rightNonzero : ∀ index : Fin 4, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xUpper ≠
        0 := by
  decide +revert

theorem squareRootOwner_bottomNonzero :
    ∀ index : Fin 4, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yLower ≠
        0 := by
  decide +revert

theorem squareRootOwner_topNonzero : ∀ index : Fin 4, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yUpper ≠
        0 := by
  decide +revert

/-- Both displayed boxes have winding one around their selected quadratic
root, in the repository's quadrupled convention. -/
theorem squareRootOwner_windingFour :
    ∀ index : Fin 4, ∀ sheet : Fin 2,
    RFAP.Winding.quadrupledBoxWinding (squareRootPolynomial index)
      (squareRootOwnerBox index sheet) = 4 := by
  decide +revert

/-- A complete local owner for either sheet at any quartic branch-box
endpoint, constructed without running the generic all-root isolator. -/
def squareRootOwner (index : Fin 4) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (squareRootParameter index) :=
  CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox
    (squareRootParameter index) (squareRootParameter_nonzero index)
    (squareRootOwnerBox index sheet)
    (RFAP.AffineWinding.centeredSquare_proper
      (squareRootCenter index sheet) (by decide))
    (squareRootOwner_leftNonzero index sheet)
    (squareRootOwner_rightNonzero index sheet)
    (squareRootOwner_bottomNonzero index sheet)
    (squareRootOwner_topNonzero index sheet)
    (squareRootOwner_windingFour index sheet)

theorem quarticDegreeGtOne : 1 < quarticCurve.polynomial.natDegree := by
  change 1 < quarticPolynomial.natDegree
  rw [quartic_degree]
  decide

/-- Explicit reindexing from the four displayed boxes to the branch-data
interface, avoiding any implicit reduction through the degree proof. -/
def branchIndex (index : Fin 4) :
    CCL.Riemann.BranchIsolation.Data.Index branchData :=
  Fin.cast branchData_siteCount.symm index

theorem refinedTrackAnchor_eq_squareRootEndpointPoint : ∀ index : Fin 4,
    CCL.Riemann.BranchCuts.refinedTrackAnchor branchData quarticDegreeGtOne
        (branchIndex index) 0 =
      squareRootEndpointPoint index
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-- The local quadratic owner, with its parameter type aligned to the actual
refinement-zero branch-track endpoint. -/
def branchSquareRootOwner (index : Fin 4) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (quarticCurve.polynomial.eval
        (CCL.Riemann.BranchCuts.refinedTrackAnchor branchData
          quarticDegreeGtOne (branchIndex index) 0)) := by
  rw [refinedTrackAnchor_eq_squareRootEndpointPoint]
  exact squareRootOwner index sheet

/-! ## Cached affine Horner data for the first measured connector cell -/

open RFAP.ComputablePolynomial.DensePolynomial

/-- Coefficients of multiplying a normalized quadratic parameter polynomial
by an affine Gaussian line.  This short symbolic lemma lets the explicit
quartic cache certify its last two Horner stages coefficient by coefficient,
without normalizing the complete composition in one reduction. -/
theorem mulLine_three_coeffs
    (origin direction a b c : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : GaussianPolynomial)
    (coeffs : p.coeffs = [a, b, c]) :
    (RFAP.PathPolynomial.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a,
        direction * c + origin * b, origin * c] := by
  unfold RFAP.PathPolynomial.mulLine
  have normalized : p.normalize.coeffs = [a, b, c] := by
    rw [normalize_coeffs, coeffs]
    simp [leadingNonzero]
  let originScaled : GaussianPolynomial :=
    ⟨[origin * a, origin * b, origin * c]⟩
  let directionScaled : GaussianPolynomial :=
    ⟨[direction * a, direction * b, direction * c]⟩
  have originScaleEq : scale origin p = originScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : scale direction p = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have directionScaledNormalized :
      directionScaled.normalize = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  unfold shift
  rw [if_neg]
  · rw [congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      directionScaledNormalized]
    change (RFAP.ComputablePolynomial.DensePolynomial.add originScaled
      ⟨[direction * a, direction * b, direction * c, 0]⟩).coeffs = _
    unfold RFAP.ComputablePolynomial.DensePolynomial.add originScaled normalize
    simp [padLeft, directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
    constructor <;> exact add_comm _ _
  · unfold isZero
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]

/-- Four-coefficient companion to `mulLine_three_coeffs`, used by the final
quartic Horner stage of each cached connector cell. -/
theorem mulLine_four_coeffs
    (origin direction a b c d : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : GaussianPolynomial)
    (coeffs : p.coeffs = [a, b, c, d]) :
    (RFAP.PathPolynomial.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a,
        direction * c + origin * b, direction * d + origin * c,
          origin * d] := by
  unfold RFAP.PathPolynomial.mulLine
  have normalized : p.normalize.coeffs = [a, b, c, d] := by
    rw [normalize_coeffs, coeffs]
    simp [leadingNonzero]
  let originScaled : GaussianPolynomial :=
    ⟨[origin * a, origin * b, origin * c, origin * d]⟩
  let directionScaled : GaussianPolynomial :=
    ⟨[direction * a, direction * b, direction * c, direction * d]⟩
  have originScaleEq : scale origin p = originScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : scale direction p = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have directionScaledNormalized :
      directionScaled.normalize = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  unfold shift
  rw [if_neg]
  · rw [congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      directionScaledNormalized]
    change (RFAP.ComputablePolynomial.DensePolynomial.add originScaled
      ⟨[direction * a, direction * b, direction * c, direction * d, 0]⟩).coeffs = _
    unfold RFAP.ComputablePolynomial.DensePolynomial.add originScaled normalize
    simp [padLeft, directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct, add_comm]
  · unfold isZero
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]

/-- Adding a constant to an exact quartic coefficient list changes only the
trailing coefficient. -/
theorem quartic_add_constant
    {leading : Gaussian} (second third fourth trailing constantTerm : Gaussian)
    (leadingNonzero : leading ≠ 0) :
    (⟨[leading, second, third, fourth, trailing]⟩ : GaussianPolynomial) +
        constant constantTerm =
      ⟨[leading, second, third, fourth, trailing + constantTerm]⟩ := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  change (RFAP.ComputablePolynomial.DensePolynomial.add
      ⟨[leading, second, third, fourth, trailing]⟩
        (constant constantTerm)).coeffs = _
  simp [RFAP.ComputablePolynomial.DensePolynomial.add, padLeft, normalize,
    constant, leadingNonzero]

/-- Closed five-coefficient formula for the dense Lipschitz cache on the unit
parameter interval.  Explicit quartic cells can now certify this bound from
four small coefficient norms instead of reducing the complete Horner fold. -/
theorem denseLipschitzBound_five_coeffs_parameterAmbient
    (a b c d e : Gaussian) :
    RFAP.PolynomialBounds.denseLipschitzBound
        (⟨[a, b, c, d, e]⟩ : GaussianPolynomial)
        CCL.Riemann.ClearSheetContinuation.parameterAmbient =
      max 1
        (1024 * RFAP.ConstructiveGaussian.Gaussian.normSq a +
          192 * RFAP.ConstructiveGaussian.Gaussian.normSq b +
          32 * RFAP.ConstructiveGaussian.Gaussian.normSq c +
          4 * RFAP.ConstructiveGaussian.Gaussian.normSq d) := by
  have parameterNormSqBound :
      CCL.Riemann.ClearSheetContinuation.parameterAmbient.normSqBound =
        (2 : Coordinate) := by
    with_unfolding_all decide
  unfold RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds
  simp only [List.foldl_cons, List.foldl_nil]
  rw [parameterNormSqBound]
  unfold RFAP.PolynomialBounds.HornerNormBounds.step
  dsimp only
  apply congrArg (max 1)
  ring1

theorem normalize_mulLine (origin direction : Gaussian)
    (polynomial : GaussianPolynomial) :
    (RFAP.PathPolynomial.mulLine origin direction polynomial).normalize =
      RFAP.PathPolynomial.mulLine origin direction polynomial := by
  unfold RFAP.PathPolynomial.mulLine
  exact normalize_add _ _

private def firstConnectorHornerOrigin : Gaussian :=
  point (-5 / 4) (-1 / 2)

private def firstConnectorHornerDirection : Gaussian :=
  point (1 / 4) 0

private def firstConnectorHornerStage1 : GaussianPolynomial :=
  RFAP.PathPolynomial.mulLine firstConnectorHornerOrigin
      firstConnectorHornerDirection 0 +
    constant (1 : Gaussian)

private def firstConnectorHornerStage2 : GaussianPolynomial :=
  RFAP.PathPolynomial.mulLine firstConnectorHornerOrigin
      firstConnectorHornerDirection firstConnectorHornerStage1 +
    constant (0 : Gaussian)

private def firstConnectorHornerStage3 : GaussianPolynomial :=
  RFAP.PathPolynomial.mulLine firstConnectorHornerOrigin
      firstConnectorHornerDirection firstConnectorHornerStage2 +
    constant (0 : Gaussian)

private def firstConnectorHornerStage4 : GaussianPolynomial :=
  RFAP.PathPolynomial.mulLine firstConnectorHornerOrigin
      firstConnectorHornerDirection firstConnectorHornerStage3 +
    constant (0 : Gaussian)

private def firstConnectorHornerStage5 : GaussianPolynomial :=
  RFAP.PathPolynomial.mulLine firstConnectorHornerOrigin
      firstConnectorHornerDirection firstConnectorHornerStage4 +
    constant (-1 : Gaussian)

private def firstConnectorHornerCache1 : GaussianPolynomial :=
  ⟨[point 1 0]⟩

private def firstConnectorHornerCache2 : GaussianPolynomial :=
  ⟨[point (1 / 4) 0, point (-5 / 4) (-1 / 2)]⟩

private def firstConnectorHornerCache3 : GaussianPolynomial :=
  ⟨[point (1 / (4 * 4)) 0,
    point (-(5 / 8)) (-(1 / 4)),
    point (21 / (4 * 4)) (5 / 4)]⟩

private def firstConnectorHornerCache4 : GaussianPolynomial :=
  ⟨[point (1 / (8 * 8)) 0,
    point (-(15 / (8 * 8))) (-(3 / (4 * 8))),
    point ((3 * 21) / (8 * 8)) ((3 * 5) / (2 * 8)),
    point (-((5 * 13) / (8 * 8)))
      (-(((7 * 10) + 1) / (4 * 8)))]⟩

private def firstConnectorHornerCache5 : GaussianPolynomial :=
  ⟨[point (1 / (4 * 8 * 8)) 0,
    point (-(5 / (8 * 8))) (-(1 / (4 * 8))),
    point ((3 * 21) / (16 * 8)) ((3 * 5) / (4 * 8)),
    point (-((5 * 13) / (8 * 8)))
      (-(((7 * 10) + 1) / (4 * 8))),
    point (-((5 * 43) / (4 * 8 * 8))) ((15 * 7) / (4 * 8))]⟩

private theorem firstConnectorHornerStage1_eq :
    firstConnectorHornerStage1 = firstConnectorHornerCache1 := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem firstConnectorHornerStage2_eq :
    firstConnectorHornerStage2 = firstConnectorHornerCache2 := by
  unfold firstConnectorHornerStage2
  rw [firstConnectorHornerStage1_eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem firstConnectorHornerStage3_eq :
    firstConnectorHornerStage3 = firstConnectorHornerCache3 := by
  unfold firstConnectorHornerStage3
  rw [firstConnectorHornerStage2_eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem firstConnectorHornerStage4_eq :
    firstConnectorHornerStage4 = firstConnectorHornerCache4 := by
  unfold firstConnectorHornerStage4
  rw [firstConnectorHornerStage3_eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [add_constant_zero, normalize_mulLine]
  rw [mulLine_three_coeffs firstConnectorHornerOrigin
    firstConnectorHornerDirection
    (point (1 / (4 * 4)) 0)
    (point (-(5 / 8)) (-(1 / 4)))
    (point (21 / (4 * 4)) (5 / 4))
    (by with_unfolding_all decide) (by with_unfolding_all decide)
    (by with_unfolding_all decide) firstConnectorHornerCache3 rfl]
  have firstCoefficient :
      firstConnectorHornerDirection * point (1 / (4 * 4)) 0 =
        point (1 / (8 * 8)) 0 := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have secondCoefficient :
      firstConnectorHornerDirection * point (-(5 / 8)) (-(1 / 4)) +
        firstConnectorHornerOrigin * point (1 / (4 * 4)) 0 =
          point (-(15 / (8 * 8))) (-(3 / (4 * 8))) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have thirdLeft :
      firstConnectorHornerDirection * point (21 / (4 * 4)) (5 / 4) =
        point (21 / (4 * 4 * 4)) (5 / (4 * 4)) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have thirdRight :
      firstConnectorHornerOrigin * point (-(5 / 8)) (-(1 / 4)) =
        point (21 / (4 * 8)) (5 / 8) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have thirdCoefficient :
      firstConnectorHornerDirection * point (21 / (4 * 4)) (5 / 4) +
        firstConnectorHornerOrigin * point (-(5 / 8)) (-(1 / 4)) =
          point ((3 * 21) / (8 * 8)) ((3 * 5) / (2 * 8)) := by
    rw [thirdLeft, thirdRight]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have originSplit : firstConnectorHornerOrigin =
      point (-5 / 4) 0 + point 0 (-1 / 2) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have fourthLeft :
      point (-5 / 4) 0 * point (21 / (4 * 4)) (5 / 4) =
        point (-(15 * 7 / (8 * 8))) (-(25 / (4 * 4))) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have fourthRight :
      point 0 (-1 / 2) * point (21 / (4 * 4)) (5 / 4) =
        point (5 / 8) (-(21 / (4 * 8))) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  have fourthCoefficient :
      firstConnectorHornerOrigin * point (21 / (4 * 4)) (5 / 4) =
        point (-((5 * 13) / (8 * 8)))
          (-(((7 * 10) + 1) / (4 * 8))) := by
    rw [originSplit, add_mul, fourthLeft, fourthRight]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide
  unfold firstConnectorHornerCache4
  rw [firstCoefficient, secondCoefficient, thirdCoefficient,
    fourthCoefficient]

private theorem firstConnectorHornerStage5_eq :
    firstConnectorHornerStage5 = firstConnectorHornerCache5 := by
  unfold firstConnectorHornerStage5
  rw [firstConnectorHornerStage4_eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

theorem quarticPolynomial_coeffs : quarticPolynomial.coeffs =
    [(1 : Gaussian), 0, 0, 0, -1] := by
  with_unfolding_all rfl

/-- The exact coefficient cache for the first horizontal quarter-segment of
the measured `0`-to-`1` connector. -/
private theorem firstConnectorSegmentPolynomial_eq :
    RFAP.PathPolynomial.composeLine quarticPolynomial
        firstConnectorHornerOrigin firstConnectorHornerDirection =
      firstConnectorHornerCache5 := by
  unfold RFAP.PathPolynomial.composeLine
    RFAP.PathPolynomial.composeLineCoeffs
  rw [quarticPolynomial_coeffs]
  change firstConnectorHornerStage5 = firstConnectorHornerCache5
  exact firstConnectorHornerStage5_eq

private theorem firstConnectorDenseVariationCacheLower : (4 * 8 : Coordinate) ≤
    RFAP.PolynomialBounds.denseLipschitzBound firstConnectorHornerCache5
      CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  with_unfolding_all decide

private theorem firstConnectorDenseVariationCacheLowerThirtyNine :
    (39 : Coordinate) ≤
      RFAP.PolynomialBounds.denseLipschitzBound firstConnectorHornerCache5
        CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  with_unfolding_all decide

private theorem firstConnectorDenseVariationCacheUpper :
    RFAP.PolynomialBounds.denseLipschitzBound firstConnectorHornerCache5
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (8 * 8 : Coordinate) := by
  with_unfolding_all decide

private def firstConnectorNormStage0 :
    RFAP.PolynomialBounds.HornerNormBounds := ⟨0, 0⟩

private def firstConnectorNormStage1 :=
  RFAP.PolynomialBounds.HornerNormBounds.step 2 firstConnectorNormStage0
    (point (1 / (4 * 8 * 8)) 0)

private def firstConnectorNormStage2 :=
  RFAP.PolynomialBounds.HornerNormBounds.step 2 firstConnectorNormStage1
    (point (-(5 / (8 * 8))) (-(1 / (4 * 8))))

private def firstConnectorNormStage3 :=
  RFAP.PolynomialBounds.HornerNormBounds.step 2 firstConnectorNormStage2
    (point ((3 * 21) / (16 * 8)) ((3 * 5) / (4 * 8)))

private def firstConnectorNormStage4 :=
  RFAP.PolynomialBounds.HornerNormBounds.step 2 firstConnectorNormStage3
    (point (-((5 * 13) / (8 * 8)))
      (-(((7 * 10) + 1) / (4 * 8))))

private def firstConnectorNormStage5 :=
  RFAP.PolynomialBounds.HornerNormBounds.step 2 firstConnectorNormStage4
    (point (-((5 * 43) / (4 * 8 * 8))) ((15 * 7) / (4 * 8)))

private def firstConnectorHornerUnit : Coordinate := 1 / 256

private theorem firstConnectorCastPositive (n : Nat) (positive : 0 < n) :
    (0 : Coordinate) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private theorem firstConnectorFiveSixtyFour :
    (5 / 64 : Coordinate) = 20 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (5 / 64 : Coordinate) = 20 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 64 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 20 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorOneThirtyTwo :
    (1 / 32 : Coordinate) = 8 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (1 / 32 : Coordinate) = 8 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 32 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 8 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorSixtyThreeOneTwentyEight :
    (63 / 128 : Coordinate) = 126 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (63 / 128 : Coordinate) = 126 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 128 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 126 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorFifteenThirtyTwo :
    (15 / 32 : Coordinate) = 120 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (15 / 32 : Coordinate) = 120 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 32 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 120 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorSixtyFiveSixtyFour :
    (65 / 64 : Coordinate) = 260 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (65 / 64 : Coordinate) = 260 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 64 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 260 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorSeventyOneThirtyTwo :
    (71 / 32 : Coordinate) = 568 * firstConnectorHornerUnit := by
  unfold firstConnectorHornerUnit
  calc
    (71 / 32 : Coordinate) = 568 / 256 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (ne_of_gt (firstConnectorCastPositive 32 (by omega)))
        (ne_of_gt (firstConnectorCastPositive 256 (by omega)))
      ring1
    _ = 568 * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorCoefficient1Norm :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point (1 / (4 * 8 * 8)) 0) =
      firstConnectorHornerUnit ^ 2 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq point
    firstConnectorHornerUnit
  rw [show (4 * 8 * 8 : Coordinate) = 256 by ring1]
  ring1

private theorem firstConnectorCoefficient2Norm :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point (-(5 / (8 * 8))) (-(1 / (4 * 8)))) =
      464 * firstConnectorHornerUnit ^ 2 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq point
  rw [show (8 * 8 : Coordinate) = 64 by ring1,
    show (4 * 8 : Coordinate) = 32 by ring1,
    firstConnectorFiveSixtyFour, firstConnectorOneThirtyTwo]
  ring1

private theorem firstConnectorCoefficient3Norm :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point ((3 * 21) / (16 * 8)) ((3 * 5) / (4 * 8))) =
      30276 * firstConnectorHornerUnit ^ 2 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq point
  rw [show (3 * 21 : Coordinate) = 63 by ring1,
    show (16 * 8 : Coordinate) = 128 by ring1,
    show (3 * 5 : Coordinate) = 15 by ring1,
    show (4 * 8 : Coordinate) = 32 by ring1,
    firstConnectorSixtyThreeOneTwentyEight,
    firstConnectorFifteenThirtyTwo]
  ring1

private theorem firstConnectorCoefficient4Norm :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point (-((5 * 13) / (8 * 8)))
          (-(((7 * 10) + 1) / (4 * 8)))) =
      390224 * firstConnectorHornerUnit ^ 2 := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq point
  rw [show (5 * 13 : Coordinate) = 65 by ring1,
    show (8 * 8 : Coordinate) = 64 by ring1,
    show ((7 * 10) + 1 : Coordinate) = 71 by ring1,
    show (4 * 8 : Coordinate) = 32 by ring1,
    firstConnectorSixtyFiveSixtyFour,
    firstConnectorSeventyOneThirtyTwo]
  ring1

private theorem firstConnectorNormStage5_slope_formula :
    firstConnectorNormStage5.slope =
      1024 * RFAP.ConstructiveGaussian.Gaussian.normSq
          (point (1 / (4 * 8 * 8)) 0) +
        192 * RFAP.ConstructiveGaussian.Gaussian.normSq
          (point (-(5 / (8 * 8))) (-(1 / (4 * 8)))) +
        32 * RFAP.ConstructiveGaussian.Gaussian.normSq
          (point ((3 * 21) / (16 * 8)) ((3 * 5) / (4 * 8))) +
        4 * RFAP.ConstructiveGaussian.Gaussian.normSq
          (point (-((5 * 13) / (8 * 8)))
            (-(((7 * 10) + 1) / (4 * 8)))) := by
  unfold firstConnectorNormStage5 firstConnectorNormStage4
    firstConnectorNormStage3 firstConnectorNormStage2
    firstConnectorNormStage1 firstConnectorNormStage0
    RFAP.PolynomialBounds.HornerNormBounds.step
  dsimp only
  ring1

private theorem firstConnectorNormStage5_slope_normalized :
    firstConnectorNormStage5.slope =
      2619840 * firstConnectorHornerUnit ^ 2 := by
  rw [firstConnectorNormStage5_slope_formula,
    firstConnectorCoefficient1Norm, firstConnectorCoefficient2Norm,
    firstConnectorCoefficient3Norm, firstConnectorCoefficient4Norm]
  ring1

private theorem firstConnectorHornerUnit_square :
    firstConnectorHornerUnit ^ 2 = 1 / (256 * 256) := by
  unfold firstConnectorHornerUnit
  rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
  rw [RFAP.ConstructiveFraction.one_mul]

private theorem firstConnectorDenseVariationCacheUpperForty :
    RFAP.PolynomialBounds.denseLipschitzBound firstConnectorHornerCache5
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (40 : Coordinate) := by
  unfold RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds firstConnectorHornerCache5
  simp only [List.foldl_cons, List.foldl_nil]
  change max 1 firstConnectorNormStage5.slope < (40 : Coordinate)
  rw [firstConnectorNormStage5_slope_normalized]
  apply max_lt
  · exact RFAP.ConstructiveFraction.natCast_lt_direct
      (m := 1) (n := 40) (by omega)
  · rw [firstConnectorHornerUnit_square]
    rw [show (2619840 : Coordinate) * (1 / (256 * 256)) =
        2619840 / (256 * 256) by
          simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
            RFAP.ConstructiveFraction.one_mul]]
    have denominatorPositive : (0 : Coordinate) < 256 * 256 :=
      RFAP.ConstructiveFraction.mul_pos_direct
        (firstConnectorCastPositive 256 (by omega))
        (firstConnectorCastPositive 256 (by omega))
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    rw [show (40 : Coordinate) * (256 * 256) = 2621440 by ring1]
    exact RFAP.ConstructiveFraction.natCast_lt_direct
      (m := 2619840) (n := 2621440) (by omega)

/-- A shallow lower bound on the exact dense-Horner scan used to show that
the inherited owner genuinely misses the first measured edge. -/
theorem firstConnectorDenseVariationLower : (4 * 8 : Coordinate) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        (point (-5 / 4) (-1 / 2)) (point (1 / 4) 0))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  change (4 * 8 : Coordinate) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        firstConnectorHornerOrigin firstConnectorHornerDirection)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient
  rw [firstConnectorSegmentPolynomial_eq]
  exact firstConnectorDenseVariationCacheLower

/-- Sharp lower endpoint of the cached first-cell Lipschitz bracket. -/
theorem firstConnectorDenseVariationLowerThirtyNine : (39 : Coordinate) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        (point (-5 / 4) (-1 / 2)) (point (1 / 4) 0))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  change (39 : Coordinate) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        firstConnectorHornerOrigin firstConnectorHornerDirection)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient
  rw [firstConnectorSegmentPolynomial_eq]
  exact firstConnectorDenseVariationCacheLowerThirtyNine

/-- A shallow strict upper bound on the same cached dense-Horner scan.  After
multiplication by the first cell's `1/64` parameter factor this shows that a
recentered owner with unit clearance carries the cell. -/
theorem firstConnectorDenseVariationUpper :
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        (point (-5 / 4) (-1 / 2)) (point (1 / 4) 0))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (8 * 8 : Coordinate) := by
  change
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        firstConnectorHornerOrigin firstConnectorHornerDirection)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (8 * 8 : Coordinate)
  rw [firstConnectorSegmentPolynomial_eq]
  exact firstConnectorDenseVariationCacheUpper

/-- Sharp upper endpoint of the same finite Lipschitz bracket. -/
theorem firstConnectorDenseVariationUpperForty :
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        (point (-5 / 4) (-1 / 2)) (point (1 / 4) 0))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (40 : Coordinate) := by
  change
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine quarticPolynomial
        firstConnectorHornerOrigin firstConnectorHornerDirection)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient <
        (40 : Coordinate)
  rw [firstConnectorSegmentPolynomial_eq]
  exact firstConnectorDenseVariationCacheUpperForty

/-- Outer subdivision used to tighten the Horner majorant on long canonical
connectors before running the local continuation checker. -/
def connectorOuterDepth : Nat := 3

/-- Outer subdivision used on the four local winding-boundary sides. -/
def boundaryOuterDepth : Nat := 3

/-- Local continuation depth on every restricted working segment. -/
def workingInnerDepth : Nat := 3

/-- Squared-diameter target for every cached local quadratic owner. -/
def workingRootDiameter : Coordinate := 5

theorem workingRootDiameter_positive : 0 < workingRootDiameter := by
  unfold workingRootDiameter
  decide

abbrev WorkingBank {ambient : Box} {start finish : Gaussian}
    (path : CCL.Riemann.BranchCuts.ClearPath quarticCurve.polynomial ambient
      start finish)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (quarticCurve.polynomial.eval start)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank
    workingInnerDepth workingRootDiameter workingRootDiameter_positive path
      owner

def rawConnector (left right : Fin 4) :=
  CCL.Riemann.BranchCuts.finiteConnectorAt branchData quarticDegreeGtOne
    (branchIndex left) (branchIndex right) 0

theorem rawConnector_withinAmbient (left right : Fin 4) :
    (rawConnector left right).WithinAmbient :=
  CCL.Riemann.BranchCuts.finiteConnectorAt_withinAmbient branchData
    quarticDegreeGtOne (branchIndex left) (branchIndex right) 0

/-- The working connector has the same endpoints as the canonical raw
connector, but its restricted segments carry substantially tighter finite
polynomial majorants. -/
def workingConnector (left right : Fin 4) :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

theorem workingConnector_withinAmbient (left right : Fin 4) :
    (workingConnector left right).WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

def workingBackwardConnector (left right : Fin 4) :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse (workingConnector left right)

theorem workingBackwardConnector_withinAmbient (left right : Fin 4) :
    (workingBackwardConnector left right).WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
    (workingConnector left right) (workingConnector_withinAmbient left right)

def branchState (index : Fin 4) :=
  CCL.Riemann.BranchCuts.refinedState branchData quarticDegreeGtOne
    (branchIndex index) 0

def rawBoundary (index : Fin 4) :=
  CCL.Riemann.BranchCutLifts.ownerBoundaryPath (branchState index)

theorem rawBoundary_withinAmbient (index : Fin 4) :
    (rawBoundary index).WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ownerBoundaryPath_withinAmbient
    (branchState index)

def workingBoundary (index : Fin 4) :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

theorem workingBoundary_withinAmbient (index : Fin 4) :
    (workingBoundary index).WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

def aForwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingConnector 0 1) (workingConnector_withinAmbient 0 1)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aRightBoundaryBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBoundary 1) (workingBoundary_withinAmbient 1)
    (branchSquareRootOwner 1 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aBackwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBackwardConnector 0 1)
    (workingBackwardConnector_withinAmbient 0 1)
    (branchSquareRootOwner 1 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aLeftBoundaryBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBoundary 0) (workingBoundary_withinAmbient 0)
    (branchSquareRootOwner 0 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def executedABoundaryData
    (forward : WorkingBank (workingConnector 0 1)
      (branchSquareRootOwner 0 0))
    (rightBoundary : WorkingBank (workingBoundary 1)
      (branchSquareRootOwner 1 0))
    (backward : WorkingBank (workingBackwardConnector 0 1)
      (branchSquareRootOwner 1 1))
    (leftBoundary : WorkingBank (workingBoundary 0)
      (branchSquareRootOwner 0 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath quarticCurve :=
  { leftAmbient := CCL.Riemann.BranchCuts.Ambient quarticCurve
    rightAmbient := CCL.Riemann.BranchCuts.Ambient quarticCurve
    connectorAmbient := CCL.Riemann.BranchCuts.Ambient quarticCurve
    leftState := branchState 0
    rightState := branchState 1
    connector := workingConnector 0 1
    rightBoundaryPath := workingBoundary 1
    leftBoundaryPath := workingBoundary 0
    forwardDepth := workingInnerDepth
    rightBoundaryDepth := workingInnerDepth
    backwardDepth := workingInnerDepth
    leftBoundaryDepth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    rightBoundaryOwner := branchSquareRootOwner 1 0
    rightBoundaryChecked := rightBoundary
    backwardOwner := branchSquareRootOwner 1 1
    backwardChecked := backward
    leftBoundaryOwner := branchSquareRootOwner 0 1
    leftBoundaryChecked := leftBoundary }

/-- The unsubdivided owner-boundary cycle represented by the prepared
quartic A-cycle data. -/
def rawACycleTarget : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
    (branchState 0) (branchState 1) (rawConnector 0 1)

/-- Prepared quartic cycle data cached together with its raw geometric
realization.  Carrying the proof with the data avoids reconstructing a large
dependent equality after all executable banks have been assembled. -/
structure RealizedPreparedCycle
    (raw : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2) where
  data : CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve
  realizes :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw data raw

/-- Conservative total A-cycle construction retained as a proof-producing
fallback if an explicitly bounded execution reports failure. -/
def totalPreparedACycleWitness (_ : Unit) :
    RealizedPreparedCycle rawACycleTarget := by
  let boundary :=
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.ofFiniteConnectorAtWithOwners
      branchData quarticDegreeGtOne (branchIndex 0) (branchIndex 1) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 1 0)
      (branchSquareRootOwner 1 1) (branchSquareRootOwner 0 1)
  exact
    { data := .finiteCut boundary
      realizes := by
        unfold rawACycleTarget rawConnector branchState branchIndex
        exact .finiteCut boundary rfl rfl }

/-- Data projection of the conservative A-cycle witness. -/
def totalPreparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve :=
  (totalPreparedACycleWitness token).data

/-- Execute all four measured A-cycle banks and cache their raw-realization
proof together with the resulting prepared data. -/
def executedACycleWitness? (token : Unit) :
    Option (RealizedPreparedCycle rawACycleTarget) :=
  match aForwardBank? token with
  | none => none
  | some forward =>
      match aRightBoundaryBank? token with
      | none => none
      | some rightBoundary =>
          match aBackwardBank? token with
          | none => none
          | some backward =>
              match aLeftBoundaryBank? token with
              | none => none
              | some leftBoundary =>
                  let boundary := executedABoundaryData forward rightBoundary
                    backward leftBoundary
                  some
                    { data := .finiteCut boundary
                      realizes :=
                        .finiteCutDyadic boundary (rawConnector 0 1)
                          (rawConnector_withinAmbient 0 1)
                          connectorOuterDepth rfl
                          (rawBoundary_withinAmbient 1) boundaryOuterDepth rfl
                          (rawBoundary_withinAmbient 0) boundaryOuterDepth rfl }

/-- Data-only compatibility projection of the executed A-cycle checker. -/
def executedACycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve) :=
  match executedACycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached A-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  The opaque definition
is an elaboration cache boundary: compiled evaluation still runs the finite
selector, while downstream proofs consume only the checked realization
record instead of normalizing every bank again. -/
opaque preparedACycleWitness (token : Unit) :
    RealizedPreparedCycle rawACycleTarget :=
  match executedACycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedACycleWitness token

/-- Canonical genus-one A cut.  The measured executable banks are preferred;
the total finite theorem remains the constructive fallback. -/
def preparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve :=
  (preparedACycleWitness token).data

def bForwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingConnector 0 2) (workingConnector_withinAmbient 0 2)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def bBackwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBackwardConnector 0 2)
    (workingBackwardConnector_withinAmbient 0 2)
    (branchSquareRootOwner 2 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def executedBDoubleData
    (forward : WorkingBank (workingConnector 0 2)
      (branchSquareRootOwner 0 0))
    (backward : WorkingBank (workingBackwardConnector 0 2)
      (branchSquareRootOwner 2 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath quarticCurve :=
  { ambient := CCL.Riemann.BranchCuts.Ambient quarticCurve
    start := (branchState 0).box.anchor
    finish := (branchState 2).box.anchor
    basePath := workingConnector 0 2
    depth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    backwardOwner := branchSquareRootOwner 2 1
    backwardChecked := backward }

/-- The unsubdivided double lift represented by the prepared quartic B-cycle
data. -/
def rawBCycleTarget : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLift (rawConnector 0 2)

/-- Conservative total B-cycle construction retained as a fallback. -/
def totalPreparedBCycleWitness (_ : Unit) :
    RealizedPreparedCycle rawBCycleTarget := by
  let bridge :=
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath.ofFiniteConnectorAtWithOwners
      branchData quarticDegreeGtOne (branchIndex 0) (branchIndex 2) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 2 1)
  exact
    { data := .bridge bridge
      realizes := by
        unfold rawBCycleTarget rawConnector branchIndex
        exact .bridge bridge }

/-- Data projection of the conservative B-cycle witness. -/
def totalPreparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve :=
  (totalPreparedBCycleWitness token).data

/-- Execute both measured B-cycle banks and cache their raw-realization proof
together with the resulting prepared data. -/
def executedBCycleWitness? (token : Unit) :
    Option (RealizedPreparedCycle rawBCycleTarget) :=
  match bForwardBank? token with
  | none => none
  | some forward =>
      match bBackwardBank? token with
      | none => none
      | some backward =>
          let bridge := executedBDoubleData forward backward
          some
            { data := .bridge bridge
              realizes :=
                .bridgeDyadic bridge (rawConnector 0 2)
                  (rawConnector_withinAmbient 0 2) connectorOuterDepth rfl }

/-- Data-only compatibility projection of the executed B-cycle checker. -/
def executedBCycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve) :=
  match executedBCycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached B-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  As for the A-cycle,
opacity shares the completed finite selection without changing its compiled
program. -/
opaque preparedBCycleWitness (token : Unit) :
    RealizedPreparedCycle rawBCycleTarget :=
  match executedBCycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedBCycleWitness token

/-- Canonical genus-one B bridge, preferring the measured executable banks. -/
def preparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData quarticCurve :=
  (preparedBCycleWitness token).data

def branchFamily :=
  CCL.Riemann.BranchCutLifts.familyOfData quarticCurve branchData

end CCL.Riemann.ExplicitQuarticBranches
