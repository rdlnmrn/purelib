module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Branches.SquareRootSheets

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Geometry

open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Riemann.Branches

@[expose] public section

/-!
Kernel regressions for the generated local numerical cell.  These exercise
the actual reduction, clearance, coefficient and CellModel constructors, not
the expensive complete continuation or period-observation runners.
-/

namespace Test.Riemann.SquareFactorCellTests

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput

/-- The retained positively oriented unit parameter span. -/
public def span : CellModels.Span := ⟨unitInterval, by decide⟩

/-- The exact rational root window centered at negative nine with coordinate radius one. -/
public def rootBox : Rational.Box :=
  ⟨-10, -8, -1, 1, by decide, by decide⟩

/-- The fixture selects `z=-9` at `x=3`; the generated radicand is `81`. Its exact residual and root-window membership
are checked in this function, not supplied as proof arguments to it. -/
public def snapshot (request : SquareFactor.Request) : Option (SquareFactor.Gaussian × SquareFactor.Gaussian × Bool) :=
  match PathInput.prepare ⟨[1, 1, 0, 0]⟩ request ⟨3, ⟨13/4, 0⟩⟩ with
  | .error _ => none
  | .ok preparedPath =>
      match preparedPath.outcome with
      | .accepted safe =>
          let root : Gaussian := -9
          if rootInside : rootBox.Contains root then
            if residual : Data.Gaussian.Norm.Basic.normSq
                (root * root - preparedPath.prepared.reduction.radicand.eval
                  ((⟨3, ⟨13/4, 0⟩⟩ : PathInput.Segment).point span.interval.lower)) ≤
                SquareRootSheets.residualTarget
                  (preparedPath.prepared.reduction.radicand.eval
                    ((⟨3, ⟨13/4, 0⟩⟩ : PathInput.Segment).point span.interval.lower)) then
              let model := CellModels.make safe span rootBox root rootInside residual
              some (model.cell.integralSample, model.center, decide (0 < model.allowance))
            else none
          else none
      | .endpointObstruction .. | .inconclusive .. => none

/-- The original and normalized differentials produce genuinely different ordinary cell samples. The physical
displacement `1/4` occurs once. -/
theorem original_and_normalized_cell_samples :
    snapshot (.original 0) = some (⟨1/24, 0⟩, ⟨1/6, 0⟩, true) ∧
      snapshot (.normalized 0) = some (⟨-1/36, 0⟩, ⟨-1/9, 0⟩, true) := by
  constructor <;> decide +kernel

end Test.Riemann.SquareFactorCellTests
