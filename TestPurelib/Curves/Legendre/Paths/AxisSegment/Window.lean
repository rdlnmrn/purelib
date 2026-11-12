module

import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-! # Original axis windows, displacement and restricted safety -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Window

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Rat
open Purelib.Data.Gaussian

/-- The original moving root crosses the zero projection at height one. -/
def aboveZero : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) :=
  .horizontal (1 / 8) (-1 / 8) 1

/-- The retained midpoint is the actual computed projection event. -/
example : aboveZero.projectionParameter 0 0 = 1 / 2 := by decide +kernel

/-- The original endpoint velocity and squared allowance determine the exact radius one over sixty-eight. -/
example : aboveZero.windowRadius (1 / 2) (1 / 64) = 1 / 68 := by decide +kernel

/-- Materialize the original computed interval around that same event parameter. -/
def selected : Interval.Bounds := aboveZero.window (1 / 2) (1 / 64)
  (by constructor <;> decide) (by decide +kernel)

/-- Both actual computed endpoints retain the exact affine parameters. -/
example : selected.lower = 33 / 68 ∧ selected.upper = 35 / 68 := by
  constructor <;> decide +kernel

/-- Reversal computes the same parameter window from the reversed original endpoint velocity. -/
example : (aboveZero.reverse.window (1 / 2) (1 / 64) (by constructor <;> decide) (by decide +kernel)).lower =
    selected.lower := by decide +kernel

/-- Every arbitrary original point of that computed window pays the same squared displacement allowance. -/
example (parameter : Coordinate) (inside : selected.Contains parameter) :
    Norm.Basic.normSq (aboveZero.pointAt parameter - aboveZero.pointAt (1 / 2)) < 1 / 64 :=
  aboveZero.window_normSq_lt (1 / 2) (1 / 64) _ _ parameter inside

/-- Restrict the original geometry to the same retained interval endpoints. -/
def piece : AxisSegment (aboveZero.pointAt selected.lower) (aboveZero.pointAt selected.upper) :=
  aboveZero.restrict selected.lower selected.upper

/-- Both retained restricted endpoints are exact original point evaluations. -/
example : aboveZero.pointAt selected.lower = gaussian (1 / 272) 1 ∧
    aboveZero.pointAt selected.upper = gaussian (-1 / 272) 1 := by
  constructor <;> decide +kernel

/-- Every restricted point retains its original affine parameter, not only the two endpoints. -/
example (parameter : Coordinate) : piece.pointAt parameter =
    aboveZero.pointAt (selected.lower + parameter * (selected.upper - selected.lower)) :=
  aboveZero.restrict_pointAt _ _ parameter

/-- The original whole segment avoids zero by its fixed nonzero height. -/
theorem avoidsZero : aboveZero.Avoids (0 : Gaussian) := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original whole segment avoids one by that same fixed nonzero height. -/
theorem avoidsOne : aboveZero.Avoids (1 : Gaussian) := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original window restriction retains intrinsic zero avoidance. -/
theorem pieceAvoidsZero : piece.Avoids 0 := avoidsZero.window_restrict (1 / 2) (1 / 64) _ _

/-- The original window restriction retains intrinsic one avoidance. -/
theorem pieceAvoidsOne : piece.Avoids 1 := avoidsOne.window_restrict (1 / 2) (1 / 64) _ _

/-- The original safety constructor computes both restricted singular-parameter clearances from intrinsic avoidance. -/
def safe : AxisSegment.Safe piece := AxisSegment.Safe.ofAvoidance piece pieceAvoidsZero pieceAvoidsOne

/-- The computed original clearances retain the actual fixed height and nearest endpoint gaps. -/
example : safe.avoidsZero.bound = 1 ∧ safe.avoidsOne.bound = 1 + (271 / 272) ^ 2 := by
  constructor <;> decide +kernel

/-- A stationary original segment still produces a proper affordable window. -/
example : (AxisSegment.horizontal 2 2 1).windowRadius (1 / 2) 1 = 1 / 4 := by decide +kernel

/-- A vertical original segment uses its actual squared imaginary velocity to allocate the window. -/
example : (AxisSegment.vertical (1 / 2) (-1) 1).windowRadius (1 / 2) (1 / 4) = 1 / 20 := by decide +kernel

/-- The initial original endpoint has a computed proper one-sided window with the same velocity payment. -/
def initial : Interval.Bounds := aboveZero.window 0 (1 / 64) (by constructor <;> decide) (by decide +kernel)

/-- The initial one-sided window retains parameter zero and its exact positive upper endpoint. -/
example : initial.lower = 0 ∧ initial.upper = 1 / 68 := by constructor <;> decide +kernel

/-- The final original endpoint has its own computed proper one-sided window. -/
def final : Interval.Bounds := aboveZero.window 1 (1 / 64) (by constructor <;> decide) (by decide +kernel)

/-- The final one-sided window retains parameter one and its exact lower endpoint. -/
example : final.lower = 67 / 68 ∧ final.upper = 1 := by constructor <;> decide +kernel

/-- Every original point in the initial endpoint window pays the same strict squared displacement allowance. -/
example (parameter : Coordinate) (inside : initial.Contains parameter) :
    Norm.Basic.normSq (aboveZero.pointAt parameter - aboveZero.pointAt 0) < 1 / 64 :=
  aboveZero.window_normSq_lt 0 (1 / 64) _ _ parameter inside

/-- Every original point in the final endpoint window pays that same strict squared displacement allowance. -/
example (parameter : Coordinate) (inside : final.Contains parameter) :
    Norm.Basic.normSq (aboveZero.pointAt parameter - aboveZero.pointAt 1) < 1 / 64 :=
  aboveZero.window_normSq_lt 1 (1 / 64) _ _ parameter inside

/-- Clipping at the initial endpoint preserves the original squared sample radius. -/
example : Interval.Radius.sampleRadiusSq initial 0 = aboveZero.windowRadius 0 (1 / 64) ^ 2 :=
  aboveZero.window_sampleRadiusSq 0 (1 / 64) _ _

/-- Clipping at the final endpoint also preserves the same original squared sample-radius identity. -/
example : Interval.Radius.sampleRadiusSq final 1 = aboveZero.windowRadius 1 (1 / 64) ^ 2 :=
  aboveZero.window_sampleRadiusSq 1 (1 / 64) _ _

/-- Intrinsic avoidance restricts to the initial one-sided window including the exact original parameter zero. -/
example : (aboveZero.restrict initial.lower initial.upper).Avoids 0 := avoidsZero.window_restrict 0 (1 / 64) _ _

/-- Intrinsic avoidance restricts to the final one-sided window including the exact original parameter one. -/
example : (aboveZero.restrict final.lower final.upper).Avoids 1 := avoidsOne.window_restrict 1 (1 / 64) _ _

/-- A reversed restriction retains every original point at its corresponding affine parameter. -/
example (parameter : Coordinate) : (aboveZero.restrict (3 / 4) (1 / 4)).pointAt parameter =
    aboveZero.pointAt (3 / 4 + parameter * (1 / 4 - 3 / 4)) := aboveZero.restrict_pointAt _ _ parameter

/-- The public window bound applies to any original axis segment and every contained rational parameter. -/
example {start finish : Gaussian} (original : AxisSegment start finish) (anchor allowance : Coordinate)
    (bounds : 0 ≤ anchor ∧ anchor ≤ 1) (positive : 0 < allowance) (parameter : Coordinate)
    (inside : (original.window anchor allowance bounds positive).Contains parameter) :
    Norm.Basic.normSq (original.pointAt parameter - original.pointAt anchor) < allowance :=
  original.window_normSq_lt anchor allowance bounds positive parameter inside

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Window
