module

import Purelib.Curves.Legendre.Paths.AxisSegment
import Purelib.Curves.Legendre.Paths

/-! # Equal original axis endpoints retain constant geometry and compute both singular-value clearances -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Curves.Legendre.Paths

/-- Every original axis direction with equal endpoints retains the same point at all parameters. -/
example {point : Gaussian} (segment : AxisSegment point point) (parameter : Coordinate) :
    segment.pointAt parameter = point := segment.pointAt_self parameter

/-- A real regular constant segment retains its original horizontal direction. -/
def original : AxisSegment (gaussian (1 / 2) 0) (gaussian (1 / 2) 0) := .horizontal (1 / 2) (1 / 2) 0

/-- The original checker computes constant-segment safety directly from its point's two intrinsic exclusions. -/
def safe : original.Safe := AxisSegment.Safe.ofEqualEndpoints original (by decide +kernel) (by decide +kernel)

/-- Both computed original constant clearances retain their exact positive numerical bounds. -/
example : safe.avoidsZero.bound = 1 / 4 ∧ safe.avoidsOne.bound = 1 / 4 := by
  constructor <;> decide +kernel

/-- The same intrinsic construction retains every original constant geometry's whole-unit safety certificate. -/
example {point : Gaussian} (segment : AxisSegment point point) (nonzero : point ≠ 0) (notOne : point ≠ 1)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    segment.pointAt parameter ≠ 0 ∧ segment.pointAt parameter ≠ 1 :=
  ⟨(AxisSegment.Safe.ofEqualEndpoints segment nonzero notOne).avoidsZero.avoids _ inside.1 inside.2,
    (AxisSegment.Safe.ofEqualEndpoints segment nonzero notOne).avoidsOne.avoids _ inside.1 inside.2⟩

end TestPurelib.Curves.Legendre.Paths.AxisSegment
