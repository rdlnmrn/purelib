module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Scale
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_scale_mono)

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- Present an original refinement program through stagewise identical retained models.

The supplied exact model equalities transport the original allowance, closeness and sample bounds; the original error
and center scales are reused. -/
def withEquivalentModels (program :
  Gaussian.Basic.RefinementProgram)
    (models : Nat -> Basic.PathModel)
    (models_eq : forall index, models index = program.model index) :
    Gaussian.Basic.RefinementProgram where
  model := models
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [models_eq index]
    exact program.modelAllowance_le index
  later_close := by
    intro earlier later order
    rw [models_eq later, models_eq earlier]
    exact program.later_close order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [models_eq index]
    exact program.sample_bounded index

open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- Increase the retained program's nonnegative error scale under its supplied domination proof.

The original model sequence and center bound remain unchanged, and geometric scale monotonicity transports the original
allowance and closeness bounds. -/
def withLargerErrorScale (program :
  Gaussian.Basic.RefinementProgram)
    (scale : Fraction.Rational) (scaleNonnegative : 0 <= scale)
    (dominates : program.errorScale <= scale) : Gaussian.Basic.RefinementProgram where
  model := program.model
  errorScale := scale
  errorScale_nonneg := scaleNonnegative
  modelAllowance_le := by
    intro index
    exact (program.modelAllowance_le index).trans
      (quarterRadius_scale_mono dominates index)
  later_close := by
    intro earlier later order
    exact (program.later_close order).trans
      (quarterRadius_scale_mono dominates earlier)
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
