module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Scale
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-! # Scaling an ordered original polynomial integration path -/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

/-- Scale each original cell without changing its endpoints, order or observation parameters. -/
@[expose] def scale (factor : Basic.Canonical) (path : PathModel) : PathModel :=
  ⟨path.cells.map (CellModel.scale factor)⟩

/-- The scaled path has exactly the original number of ordered cells. -/
theorem scale_cells_length (factor : Basic.Canonical) (path : PathModel) :
    (path.scale factor).cells.length = path.cells.length := Map.length_map _ path.cells

/-- The scaled path sample is the coefficient times the original finite integral sample. -/
theorem scale_integralSample (factor : Basic.Canonical) (path : PathModel) :
    (path.scale factor).integralSample = factor * path.integralSample := by
  cases path with
  | mk cells =>
    induction cells with
    | nil => exact (Basic.mul_zero factor).symm
    | cons cell tail inductionHypothesis =>
      change (cell.scale factor).integralSample + (scale factor ⟨tail⟩).integralSample =
        factor * (cell.integralSample + (⟨tail⟩ : PathModel).integralSample)
      rw [cell.scale_integralSample, inductionHypothesis]
      ring1

/-- Scaling every original weighted error scales their ordered sum by the coefficient's squared norm. -/
theorem scale_totalWeightedAllowance (factor : Basic.Canonical) (path : PathModel) :
    (path.scale factor).totalWeightedAllowance =
      Basic.Canonical.normSq factor * path.totalWeightedAllowance := by
  cases path with
  | mk cells =>
    induction cells with
    | nil => exact (Purelib.Data.Rat.Fraction.Field.mul_zero_direct _).symm
    | cons cell tail inductionHypothesis =>
      change (cell.scale factor).weightedAllowance + (scale factor ⟨tail⟩).totalWeightedAllowance =
        Basic.Canonical.normSq factor * (cell.weightedAllowance + (⟨tail⟩ : PathModel).totalWeightedAllowance)
      rw [cell.scale_weightedAllowance, inductionHypothesis]
      ring1

/-- The original cell count gives the same scaled aggregate error budget. -/
theorem scale_aggregateAllowance (factor : Basic.Canonical) (path : PathModel) :
    (path.scale factor).aggregateAllowance =
      Basic.Canonical.normSq factor * path.aggregateAllowance := by
  change ((path.scale factor).cells.length : Purelib.Data.Rat.Fraction.Rational) *
    (path.scale factor).totalWeightedAllowance = _
  rw [scale_cells_length, scale_totalWeightedAllowance]
  change (path.cells.length : Purelib.Data.Rat.Fraction.Rational) *
    (Basic.Canonical.normSq factor * path.totalWeightedAllowance) =
      Basic.Canonical.normSq factor *
        ((path.cells.length : Purelib.Data.Rat.Fraction.Rational) * path.totalWeightedAllowance)
  ring1

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
end
