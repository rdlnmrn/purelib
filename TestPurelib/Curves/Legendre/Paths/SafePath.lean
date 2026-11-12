module

import Purelib.Curves.Legendre.Paths.SafePath
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation

/-! # Original safe-path vertices and internally selected shared charts -/

namespace TestPurelib.Curves.Legendre.Paths.SafePath

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian.Coordinates

/-- Intrinsic whole-unit avoidance constructs the same original finite axis family without a supplied clearance. -/
example (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1) :
    (SafePath.ofAxisSegments size points axes avoidsZero avoidsOne).FollowsAxes size points axes :=
  SafePath.ofAxisSegments_followsAxes size points axes avoidsZero avoidsOne

/-- The safety fold preserves every input axis ordinal and all original vertex readings. -/
example {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)}
    (follows : original.FollowsAxes size points axes) (index : Fin (size + 1)) :
    original.vertices (Fin.cast (congrArg (fun count : Nat => count + 1) follows.stepCount).symm index) =
      points index :=
  follows.vertices index

/-- The raw geometric family retains every original unit point in its same actual safety fold. -/
example {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)}
    (follows : original.FollowsAxes size points axes) (index : Fin size) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) : original.Visits ((axes index).pointAt parameter) :=
  follows.visits index parameter inside

/-- The shared chart separates every original vertex from intrinsic start regularity and actual segment safety. -/
example {start finish : Gaussian} (path : SafePath start finish) (nonzero : start ≠ 0) (notOne : start ≠ 1)
    (index : Fin (path.stepCount + 1)) :
    (Rotation.rotate path.projectionSlope (path.vertices index)).re ≠ 0 ∧
      (Rotation.rotate path.projectionSlope (path.vertices index)).re ≠ 1 :=
  path.projectionSlope_separates nonzero notOne index

/-- The vertex family retains both actual original endpoint indices, including an empty path. -/
example {start finish : Gaussian} (path : SafePath start finish) :
    path.vertices 0 = start ∧ path.vertices ⟨path.stepCount, Nat.lt_succ_self path.stepCount⟩ = finish :=
  ⟨path.vertices_source, path.vertices_target⟩

/-- The original empty owner itself permits a singular point; its constructor is not a regularity certificate. -/
example : (SafePath.nil 0).vertices 0 = (0 : Gaussian) := rfl

/-- An original point on any retained head remains an actual point of the same complete safe path. -/
example {start middle finish : Gaussian} (segment : AxisSegment start middle) (safe : AxisSegment.Safe segment)
    (tail : SafePath middle finish) (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (SafePath.cons segment safe tail).Visits (segment.pointAt parameter) :=
  SafePath.Visits.cons_head segment safe parameter inside rfl

end TestPurelib.Curves.Legendre.Paths.SafePath
