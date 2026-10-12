module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Nonempty vertex neighborhoods on a proper enclosing frame

Both endpoint lines are retained, so a vertex has one, two or four incident
cells. A neighborhood with fewer than four cells lies on the outer frame.
This rules out the empty-axis/singleton-axis cases without a search premise.
-/

namespace Purelib.Polynomial.Geometry.Grid.FramedVertexStar

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
  {point : Gaussian.Basic.Canonical}

/-- A vertex of a proper framed grid has one or two incident cells on the frame, or four incident cells.

The alternatives retain the frame-coordinate witness in the smaller cases. -/
theorem framed_size_cases (star : ClearGrid.VertexStar grid point) (frame :
  FramedClearGrid.AmbientFrame grid)
    (proper : ambient.Proper) :
    (star.cells.length = 1 ∨ star.cells.length = 2) ∧
        (point.re = ambient.xLower ∨ point.re = ambient.xUpper ∨
          point.im = ambient.yLower ∨ point.im = ambient.yUpper) ∨
      star.cells.length = 4 := by
  have xCases := star.x.framed_size_cases frame.xLower frame.xUpper proper.1 (fun line _ => line.inside)
  have yCases := star.y.framed_size_cases frame.yLower frame.yUpper proper.2 (fun line _ => line.inside)
  have length := star.length_eq_product
  rcases xCases with ⟨xOne, xBoundary⟩ | xTwo
  · have boundary : point.re = ambient.xLower ∨ point.re = ambient.xUpper ∨
        point.im = ambient.yLower ∨ point.im = ambient.yUpper :=
      xBoundary.elim Or.inl (fun equal => Or.inr (Or.inl equal))
    rcases yCases with ⟨yOne, _⟩ | yTwo
    · exact Or.inl ⟨Or.inl (by simpa only [xOne, yOne] using length), boundary⟩
    · exact Or.inl ⟨Or.inr (by simpa only [xOne, yTwo] using length), boundary⟩
  · rcases yCases with ⟨yOne, yBoundary⟩ | yTwo
    · exact Or.inl ⟨Or.inr (by simpa only [xTwo, yOne] using length), Or.inr (Or.inr yBoundary)⟩
    · exact Or.inr (by simpa only [xTwo, yTwo] using length)

open Purelib.Polynomial.Geometry.Grid.FramedVertexStar in
/-- The incident-cell star of a vertex in a proper framed grid is nonempty. -/
theorem length_pos (star : ClearGrid.VertexStar grid point) (frame :
  FramedClearGrid.AmbientFrame grid)
    (proper : ambient.Proper) : 0 < star.cells.length := by
  rcases framed_size_cases star frame proper with ⟨one | two, _⟩ | four <;> omega

end Purelib.Polynomial.Geometry.Grid.FramedVertexStar
