module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Constant
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel (ConstantCells)

open Purelib.Integration.Polynomial.Gaussian

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Polynomial.ConstantComparison

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- List the original constant cells' displacement-weighted coefficient deviations from the reference.

The dependent constant-cell witnesses retain each original coefficient and polynomial identity in the original cell
order. -/
def constantReferenceErrorTerms : forall {cells : List
  Basic.CellModel},
    ConstantCells cells ->
      Basic.Canonical -> List Basic.Canonical
  | [], .nil, _reference => []
  | cell :: _, .cons head tail, reference =>
      cell.displacement * (head.coefficient - reference) ::
        constantReferenceErrorTerms tail reference

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- There is exactly one retained reference-error term per original constant cell.

The dependent constant-cell certificate follows the original cell list, so each recursive retained tail contributes the
same number of entries. -/
@[simp] theorem constantReferenceErrorTerms_length :
    forall {cells : List Basic.CellModel}
      (constant :
        ConstantCells cells)
      (reference : Basic.Canonical),
      (constantReferenceErrorTerms constant reference).length = cells.length
  | [], .nil, _ => rfl
  | _ :: _, .cons _ tail, reference => by
      simp only [constantReferenceErrorTerms, List.length_cons,
        constantReferenceErrorTerms_length tail reference, -eq_self,
          -iff_self]
      rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original cell count times the squared-norm sum of the retained reference-error terms. -/
def constantReferenceErrorAllowance {cells : List
  Basic.CellModel}
    (constant :
      ConstantCells cells)
    (reference : Basic.Canonical) :
    Fraction.Rational :=
  (cells.length : Fraction.Rational) *
    Norm.Sum.Basic.gaussianNormSqSum
      (constantReferenceErrorTerms constant reference)

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Split the original constant-cell integral sample into reference times total displacement and the retained error sum.

Every original coefficient and cell displacement remains in its own error term; the equality follows the exact ordered
model list. -/
theorem constantPathIntegralSample_eq_reference_add_error :
    forall {cells : List Basic.CellModel}
      (constant :
        ConstantCells cells)
      (reference : Basic.Canonical),
      (Basic.PathModel.mk cells).integralSample =
        Basic.PathModel.displacementSum cells *
          reference +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (constantReferenceErrorTerms constant reference)
  | [], .nil, reference => by
      unfold Basic.PathModel.integralSample
        Basic.PathModel.displacementSum
        constantReferenceErrorTerms
      change (0 : Basic.Canonical) = 0 * reference + 0
      rw [Basic.zero_mul,
        Basic.add_zero]
  | cell :: cells, .cons head tail, reference => by
      rw [Basic.PathModel.integralSample]
      simp only [List.foldr_cons]
      rw [Cell.Basic.CellModel.integralSample_constant
        cell head.coefficient head.polynomial_eq]
      change cell.displacement * head.coefficient +
        (Basic.PathModel.mk cells).integralSample = _
      rw [constantPathIntegralSample_eq_reference_add_error tail
        reference]
      simp only [Basic.PathModel.displacementSum_cons,
        constantReferenceErrorTerms,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      apply Basic.ext <;>
        simp only [Basic.add_re,
          Basic.add_im,
          Basic.sub_re,
          Basic.sub_im,
          Basic.mul_re,
          Basic.mul_im] <;> ring1

/-- The retained reference-error allowance bounds the squared norm of the original error sum. -/
theorem constantReferenceErrorSum_le {cells : List
  Basic.CellModel}
    (constant :
      ConstantCells cells)
    (reference : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (constantReferenceErrorTerms constant reference)) <=
      constantReferenceErrorAllowance constant reference := by
  unfold constantReferenceErrorAllowance
  have finiteCauchy :=
    Norm.Sum.Basic.normSq_gaussianSum_le
      (constantReferenceErrorTerms constant reference)
  rw [constantReferenceErrorTerms_length constant reference] at finiteCauchy
  simpa only [Norm.Basic.normSq_eq_canonical] using finiteCauchy

end Purelib.Integration.Polynomial.ConstantComparison

end
