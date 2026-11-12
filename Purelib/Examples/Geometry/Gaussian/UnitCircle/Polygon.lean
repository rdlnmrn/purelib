module

public import Purelib.Geometry.Gaussian.UnitCircle.Polygon
import Purelib.Geometry.Polygons.SignedArea.Operations

/-! Two small inscribed polygons use the same finite chart and signed-area API. -/

namespace Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon

open Purelib.Data.Rat
open Purelib.Geometry

/-- Four cardinal vertices generated from one original interval per quarter. -/
@[expose] public def diamond : List (Plane.Point Fraction.Rational) :=
  Gaussian.UnitCircle.Polygon.vertices 0

/-- Eight rational vertices generated from two original intervals per quarter. -/
@[expose] public def octagon : List (Plane.Point Fraction.Rational) :=
  Gaussian.UnitCircle.Polygon.vertices 1

/-- The actual four-vertex shoelace computation has area two. -/
public theorem diamond_area : Polygons.SignedArea.Basic.polygonSignedArea diamond = 2 := by decide

/-- Move the first actual diamond vertex to the end of its ordered vertex list. -/
@[expose] public def rotatedDiamond : List (Plane.Point Fraction.Rational) :=
  match diamond with
  | [] => []
  | first :: rest => rest ++ [first]

/-- The nontrivial cyclic shift changes the retained ordered vertex list. -/
public theorem diamond_ne_rotated : diamond ≠ rotatedDiamond := by decide

/-- The original and cyclically shifted diamond have the same signed area. -/
public theorem diamond_rotated_area :
    Polygons.SignedArea.Basic.polygonSignedArea rotatedDiamond =
      Polygons.SignedArea.Basic.polygonSignedArea diamond := by
  cases h : diamond with
  | nil =>
    have rotated : rotatedDiamond = [] := by rw [rotatedDiamond, h]
    rw [rotated]
  | cons first rest =>
    simp only [rotatedDiamond, h]
    unfold Polygons.SignedArea.Basic.polygonSignedArea
    rw [Polygons.SignedArea.Operations.polygonDoubleSignedArea_rotate_last]

/-- The actual eight-vertex shoelace computation has area fourteen fifths. -/
public theorem octagon_area : Polygons.SignedArea.Basic.polygonSignedArea octagon = 14 / 5 := by decide

end Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon
