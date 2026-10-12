module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Topology.Polygon.Stokes

import Purelib.Riemann.Periods.PrimitiveTriangleBilinear
public import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Tactic.Ring

@[expose] public section

/-! The local wedge estimate on the actual finite affine basis readings.
The existing energy budget supplies all four cached scales. -/

namespace Purelib.Riemann.Periods.AffineBasisBilinear

section
open Purelib.Data
/-- The exact Gaussian rational carrier used for the finite affine-basis readings. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational carrier of the retained triangle and surface budgets. -/
private abbrev Coordinate := Rat.Fraction.Rational
end

open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Readings.AffineBasisEnergy.AffineBasis (TriangleBudget SurfaceBudget)

open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {vertexCount faceCount count : Nat}
  {triangulation : Purelib.Topology.Polygon.Stokes.Triangulation vertexCount faceCount}
  {coordinate : Fin vertexCount → Canonical} {basis : AffineBasis triangulation coordinate
    count}
  {face : Fin faceCount}

namespace TriangleBudget

open Purelib.Data in
/-- The local squared bilinear allowance from the four retained affine and error scales. -/
def bilinearSquare (budget : TriangleBudget basis face) : Rat.Fraction.Rational :=
  16 * (budget.firstAffine.scale * budget.secondError.scale +
    budget.secondAffine.scale * budget.firstError.scale + budget.firstError.scale * budget.secondError.scale)

open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann.Periods.AffineBasisBilinear in
/-- Bound the local bilinear allowance by sixty-four times the retained energy budget squared.

The three existing product certificates and their nonnegative cached budgets pay the affine-error and error-error terms.
-/
theorem bilinearSquare_le_total_sq (budget : TriangleBudget basis face) :
    (TriangleBudget.bilinearSquare budget) ≤ 64 * budget.total ^ 2 := by
  have first := (Field.div_le_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 4)).mp budget.products.first_bound
  have second := (Field.div_le_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 4)).mp budget.products.second_bound
  have mixed := (Field.div_le_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 4)).mp budget.products.mixed_bound
  have products := add_le_add (add_le_add second first) mixed
  have squares : budget.products.first ^ 2 + budget.products.second ^ 2 + budget.products.mixed ^ 2 ≤
      budget.total ^ 2 := by
    apply Arithmetic.le_of_sub_nonneg_direct
    rw [budget.total_eq]
    have equal : (budget.products.first + budget.products.second + budget.products.mixed) ^ 2 -
        (budget.products.first ^ 2 + budget.products.second ^ 2 + budget.products.mixed ^ 2) =
        2 * (budget.products.first * budget.products.second + budget.products.first * budget.products.mixed +
          budget.products.second * budget.products.mixed) := by ring1
    rw [equal]
    exact Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (add_nonneg
        (Arithmetic.mul_nonneg_direct budget.products.first_nonnegative budget.products.second_nonnegative)
        (Arithmetic.mul_nonneg_direct budget.products.first_nonnegative budget.products.mixed_nonnegative))
        (Arithmetic.mul_nonneg_direct budget.products.second_nonnegative budget.products.mixed_nonnegative))
  calc
    (TriangleBudget.bilinearSquare budget) = 16 * (budget.firstAffine.scale * budget.secondError.scale +
        budget.firstError.scale * budget.secondAffine.scale + budget.firstError.scale * budget.secondError.scale) := by
      unfold bilinearSquare
      ring1
    _ ≤ 16 * (budget.products.second ^ 2 * 4 + budget.products.first ^ 2 * 4 + budget.products.mixed ^ 2 * 4) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct products (by decide)
    _ = 64 * (budget.products.first ^ 2 + budget.products.second ^ 2 + budget.products.mixed ^ 2) := by ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct squares (by decide +kernel)

open Purelib.Data.Gaussian.Norm in
open Purelib.Integration in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann in
open Purelib.Riemann.Periods.AffineBasisBilinear in
/-- Bound the actual two-function wedge on one triangle of the retained affine basis.

Both coefficient vectors use the same face and coordinate realization. The four retained scales pay every signed affine
approximation error through the local bilinear allowance. -/
theorem bilinear_bound (budget : TriangleBudget basis face) (left right : LinearAlgebra.Gaussian.Energy.GaussianVector
  count) :
    Data.Gaussian.Norm.Basic.normSq (triangleWedgeArea
      ⟨basis.value left (triangulation.faces face).first, basis.value right (triangulation.faces face).first⟩
      ⟨basis.value left (triangulation.faces face).second, basis.value right (triangulation.faces face).second⟩
      ⟨basis.value left (triangulation.faces face).third, basis.value right (triangulation.faces face).third⟩) ≤
      coefficientNormSq left * coefficientNormSq right * (TriangleBudget.bilinearSquare budget) := by
  have affine (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (first last : Fin vertexCount) :
      (basis.coefficient coefficients face) * (coordinate last - coordinate first) =
        Energy.AffineTriangle.affinePrimitiveIncrement (basis.coefficient coefficients face) (coordinate first)
          (coordinate last) := by
    unfold Energy.AffineTriangle.affinePrimitiveIncrement
    ring1
  have error (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (first last : Fin vertexCount) :
      basis.value coefficients last - basis.value coefficients first -
        basis.coefficient coefficients face * (coordinate last - coordinate first) =
      Energy.AffineTriangle.affinePrimitiveIncrementError (basis.coefficient coefficients face) (coordinate first)
        (coordinate last)
        (basis.value coefficients first) (basis.value coefficients last) := by
    unfold Energy.AffineTriangle.affinePrimitiveIncrementError Energy.AffineTriangle.affinePrimitiveIncrement
    ring1
  unfold triangleWedgeArea bilinearSquare
  rw [Basic.normSq_eq_canonical]
  apply Periods.PrimitiveTriangleBilinear.bilinearDeterminant_bound
    (basis.coefficient left face) (basis.coefficient right face)
    (coordinate (triangulation.faces face).second - coordinate (triangulation.faces face).first)
    (coordinate (triangulation.faces face).third - coordinate (triangulation.faces face).first)
  · rw [affine, basis.affine_increment]; simpa only [Basic.normSq_eq_canonical] using budget.firstAffine.bound left
  · rw [affine, basis.affine_increment]; simpa only [Basic.normSq_eq_canonical] using budget.secondAffine.bound left
  · rw [affine, basis.affine_increment]; simpa only [Basic.normSq_eq_canonical] using budget.firstAffine.bound right
  · rw [affine, basis.affine_increment]; simpa only [Basic.normSq_eq_canonical] using budget.secondAffine.bound right
  · rw [error, basis.affine_error]; simpa only [Basic.normSq_eq_canonical] using budget.firstError.bound left
  · rw [error, basis.affine_error]; simpa only [Basic.normSq_eq_canonical] using budget.secondError.bound left
  · rw [error, basis.affine_error]; simpa only [Basic.normSq_eq_canonical] using budget.firstError.bound right
  · rw [error, basis.affine_error]; simpa only [Basic.normSq_eq_canonical] using budget.secondError.bound right

end TriangleBudget

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_mul_left)

open Purelib.Algebra in
open Purelib.Data in
/-- The sum of the retained nonnegative triangle budgets is nonnegative. -/
theorem SurfaceBudget.total_nonnegative (budget : SurfaceBudget basis) : 0 ≤ budget.total := by
  rw [budget.total_eq]
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin faceCount => (0 : Rat.Fraction.Rational))
    (fun face => (budget.triangles.get face).total) (fun face => by
      rw [(budget.triangles.get face).total_eq]
      exact add_nonneg (add_nonneg (budget.triangles.get face).products.first_nonnegative
        (budget.triangles.get face).products.second_nonnegative) (budget.triangles.get face).products.mixed_nonnegative)
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Riemann.Periods.AffineBasisBilinear in
set_option genInjectivity false in
/-- Materialized bilinear allowances for every face of the same retained surface budget.

The vector caches each triangle's coefficient-independent allowance, and the total retains the full face-incidence
factor multiplying their finite sum. -/
structure BilinearBudget (budget : SurfaceBudget basis) where
  /-- The cached rational bilinear allowance for each original face. -/ triangles : Data.Vector
    Rat.Fraction.Rational faceCount
  /-- Each cached entry is the bilinear allowance of its retained triangle budget. -/ triangles_eq : ∀ face, triangles
    face = (TriangleBudget.bilinearSquare (budget.triangles.get face))
  /-- The cached allowance for the complete face-incidence sum. -/ total : Rat.Fraction.Rational
  /-- The total is the face count times the finite sum of the cached triangle allowances. -/ total_eq : total =
    (faceCount : Rat.Fraction.Rational) * FiniteSum.Fin.sumFin triangles

constructive_injectivity BilinearBudget

namespace BilinearBudget

variable {budget : SurfaceBudget basis}

open Purelib.Algebra in
open Purelib.Approximation.Rational.Budget in
open Purelib.Data in
open Purelib.Riemann.Periods.AffineBasisBilinear in
/-- Materialize each face allowance and its full incidence-sum total once.

The vector entries come from the exact retained surface budget, with pointwise readback and the total equation stored
alongside the values. -/
def build (budget : SurfaceBudget basis) : BilinearBudget budget :=
  let triangles := Vector.Basic.vectorOfFn fun face => (TriangleBudget.bilinearSquare (budget.triangles.get face))
  ⟨triangles, Vector.Basic.vectorOfFn_apply _,
    Aggregate.countCoordinate faceCount * FiniteSum.Fin.sumFin triangles,
    by rw [Aggregate.countCoordinate_eq]⟩

open Purelib.Algebra in
open Purelib.Data in
/-- A finite constant rational sum is its count times the constant. -/
private theorem sum_constant (size : Nat) (value : Rat.Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin size => value) = (size : Rat.Fraction.Rational) * value := by
  induction size with
  | zero => change 0 = 0 * value; ring1
  | succ size ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann.Periods.AffineBasisBilinear in
/-- Uniform per-face payment bounds the cached bilinear total by the retained surface energy squared.

The actual face count is paid before squaring, using the existing energy total of the same surface and the supplied
equality of all local budgets. -/
theorem total_le_energy_sq (cached : BilinearBudget budget) (perFace : Rat.Fraction.Rational)
    (uniform : ∀ face, (budget.triangles.get face).total = perFace) :
    cached.total ≤ 64 * budget.total ^ 2 := by
  have localBound (face : Fin faceCount) : cached.triangles face ≤ 64 * perFace ^ 2 := by
    rw [cached.triangles_eq]
    exact (TriangleBudget.bilinearSquare_le_total_sq (budget.triangles.get face)).trans_eq
      (congrArg (fun value : Rat.Fraction.Rational => 64 * value ^ 2) (uniform face))
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ localBound)
    (Order.natCast_le_direct (Nat.zero_le faceCount))
  rw [sum_constant] at bound
  rw [cached.total_eq, budget.total_eq,
    FiniteSum.Fin.sumFin_congr uniform, sum_constant]
  exact bound.trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann.Periods.AffineBasisBilinear in
open Purelib.Topology in
/-- Transfer the actual two-function triangle wedge bounds to the same triangulation's boundary.

Exact incidence and the cached face allowances charge every face occurrence; the two coefficient norms multiply the
retained bilinear total. -/
theorem boundary_bound (cached : BilinearBudget budget) (left right : LinearAlgebra.Gaussian.Energy.GaussianVector
  count) :
    Data.Gaussian.Norm.Basic.normSq (Polygon.Stokes.edgeListArea
      (fun vertex => ⟨basis.value left vertex, basis.value right vertex⟩) triangulation.boundary) ≤
      coefficientNormSq left * coefficientNormSq right * cached.total := by
  rw [← triangulation.wedgeSum_eq_boundaryArea]
  have estimate := Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun face => triangleWedgeArea
      ⟨basis.value left (triangulation.faces face).first, basis.value right (triangulation.faces face).first⟩
      ⟨basis.value left (triangulation.faces face).second, basis.value right (triangulation.faces face).second⟩
      ⟨basis.value left (triangulation.faces face).third, basis.value right (triangulation.faces face).third⟩)
    (fun face => (coefficientNormSq left * coefficientNormSq right) * cached.triangles face)
    (fun face => by
        rw [cached.triangles_eq];
        exact TriangleBudget.bilinear_bound (budget.triangles.get face) left right)
  rw [FiniteSum.Fin.sumFin_mul_left] at estimate
  exact estimate.trans_eq (by rw [cached.total_eq]; ring1)

end BilinearBudget
end Purelib.Riemann.Periods.AffineBasisBilinear
