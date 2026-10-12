module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Integration.Polynomial.Rational.Cell.Arithmetic
public import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Rational.Cell.Basic (CellModel)

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Path.Basic
namespace PathModel

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Scale every retained path cell's polynomial and local allowance in the original list order.

The cell scaling operation preserves endpoints, squares the allowance factor and resets each cell's observations. -/
def scaleIntegrand (factor : Fraction.Rational)
  (path : Rational.Path.Basic.PathModel) : Rational.Path.Basic.PathModel :=
  ⟨path.cells.map (CellModel.scaleIntegrand factor)⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Scaling a path scales its integral sample by the same rational factor. -/
theorem integralSample_scaleIntegrand (factor :
  Fraction.Rational)
    (path : Rational.Path.Basic.PathModel) :
    (path.scaleIntegrand factor).integralSample =
      Scale.scale factor path.integralSample := by
  unfold scaleIntegrand Rational.Path.Basic.PathModel.integralSample
  induction path.cells with
  | nil =>
      apply Basic.ext <;>
        simp only [List.map_nil, List.foldr_nil,
          Scale.scale_re,
          Scale.scale_im, Basic.zero_re, Basic.zero_im] <;> ring1
  | cons cell remaining induction =>
      simp only [List.map_cons, List.foldr_cons]
      rw [CellModel.scaleIntegrand_integralSample, induction]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.add_re, Basic.add_im] <;> ring1

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Scaling a path multiplies the recursively aggregated allowance by the factor squared.

Every original cell is scaled by the same rational factor, while the ordered cell list and recursive allowance sum are
retained. -/
theorem aggregateAllowance_scaleIntegrand (factor :
  Fraction.Rational)
    (path : Rational.Path.Basic.PathModel) :
    (path.scaleIntegrand factor).aggregateAllowance =
      factor ^ 2 * path.aggregateAllowance := by
  unfold scaleIntegrand Rational.Path.Basic.PathModel.aggregateAllowance
  induction path.cells with
  | nil =>
      simp only [List.map_nil, List.foldr_nil,
        Fraction.Field.mul_zero_direct, -eq_self, -iff_self]
      rfl
  | cons cell remaining induction =>
      simp only [List.map_cons, List.foldr_cons]
      rw [CellModel.scaleIntegrand_weightedAllowance, induction]
      ring1
end PathModel

end Purelib.Integration.Polynomial.Rational.Path.Basic

end
