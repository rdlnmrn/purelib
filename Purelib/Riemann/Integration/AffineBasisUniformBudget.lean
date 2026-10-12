module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Topology.Polygon.Stokes

public import Purelib.Riemann.Readings.AffineBasisEnergy
public import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PrimitiveTriangleEnergy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Uniform product budgets on a retained affine basis

Explicit bounds on the four finite basis sums supply the existing cached
triangle and surface certificate interface. The total per-face allowance is
linear in the squared leaf diameter, so the actual dyadic face count can be
paid before coefficients are supplied.
-/

namespace Purelib.Riemann.Integration.AffineBasisUniformBudget

open Purelib.Riemann.Readings.PrimitiveTriangleEnergy (TriangleProductBudget)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis WeightedNormBudget)
open Purelib.Riemann.Readings.AffineBasisEnergy.AffineBasis (TriangleBudget)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data.Rat in
/-- Restrict original product budgets to smaller nonnegative affine and error bounds.

The first, second and mixed budget values remain exactly the same; only their certificates are transported through the
supplied bounds on the four original scales. -/
public def restrictProducts {firstAffine secondAffine firstError secondError upperAffine upperError :
  Fraction.Rational}
    (budget : TriangleProductBudget upperAffine upperAffine upperError upperError)
    (firstAffineNonnegative : 0 ≤ firstAffine) (secondAffineNonnegative : 0 ≤ secondAffine)
    (firstErrorNonnegative : 0 ≤ firstError) (secondErrorNonnegative : 0 ≤ secondError)
    (firstAffineLe : firstAffine ≤ upperAffine) (secondAffineLe : secondAffine ≤ upperAffine)
    (firstErrorLe : firstError ≤ upperError) (secondErrorLe : secondError ≤ upperError) :
    TriangleProductBudget firstAffine secondAffine firstError secondError := by
  have product {first second upperFirst upperSecond : Fraction.Rational} (firstNonnegative : 0 ≤ first)
      (secondNonnegative : 0 ≤ second) (firstLe : first ≤ upperFirst) (secondLe : second ≤ upperSecond) :
      first * second / 4 ≤ upperFirst * upperSecond / 4 := by
    have divided := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_direct firstLe secondLe secondNonnegative (firstNonnegative.trans firstLe))
      (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)
    simpa only [Fraction.Field.div_eq_mul_inv_direct] using divided
  exact
    { first := budget.first
      second := budget.second
      mixed := budget.mixed
      first_nonnegative := budget.first_nonnegative
      second_nonnegative := budget.second_nonnegative
      mixed_nonnegative := budget.mixed_nonnegative
      first_bound := (product firstErrorNonnegative secondAffineNonnegative firstErrorLe secondAffineLe).trans
        budget.first_bound
      second_bound := (product firstAffineNonnegative secondErrorNonnegative firstAffineLe secondErrorLe).trans
        budget.second_bound
      mixed_bound := (product firstErrorNonnegative secondErrorNonnegative firstErrorLe secondErrorLe).trans
        budget.mixed_bound }

namespace AffineBasis.TriangleBudget

variable {vertexCount faceCount count : Nat} {triangulation : Purelib.Topology.Polygon.Stokes.Triangulation vertexCount
  faceCount}
  {coordinate : Fin vertexCount → Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Riemann.Topology in
/-- Construct the exact original face budget from uniform affine and increment-error bounds.

The retained weighted norm banks keep their original face vertices and basis rows. Their two edge scales are bounded by
the common coefficient, tolerance and distance before reusing the uniform product budgets. -/
def uniform (basis : AffineBasis triangulation coordinate count) (face : Fin faceCount)
    (coefficient epsilon distance : Fraction.Rational) (coefficientNonnegative : 0 ≤ coefficient)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonLe : epsilon ≤ 1) (distanceNonnegative : 0 ≤ distance)
    (affineBound : ∀ last, last = (triangulation.faces face).second ∨ last = (triangulation.faces face).third →
      (count : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (AffineTriangle.affinePrimitiveIncrement (basis.coefficients row face)
        (coordinate (triangulation.faces face).first) (coordinate last))) ≤ coefficient * distance)
    (errorBound : ∀ last, last = (triangulation.faces face).second ∨ last = (triangulation.faces face).third →
      (count : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (AffineTriangle.affinePrimitiveIncrementError (basis.coefficients row face)
        (coordinate (triangulation.faces face).first) (coordinate last)
        (basis.values row (triangulation.faces face).first) (basis.values row last))) ≤ 2 * epsilon ^ 2 * distance) :
    TriangleBudget basis face :=
  let first := (triangulation.faces face).first
  let second := (triangulation.faces face).second
  let third := (triangulation.faces face).third
  let firstAffine := WeightedNormBudget.build (fun row => AffineTriangle.affinePrimitiveIncrement (basis.coefficients
    row face) (coordinate first) (coordinate second))
  let secondAffine := WeightedNormBudget.build (fun row => AffineTriangle.affinePrimitiveIncrement (basis.coefficients
    row face) (coordinate first) (coordinate third))
  let firstError := WeightedNormBudget.build (fun row => AffineTriangle.affinePrimitiveIncrementError
    (basis.coefficients row face)
    (coordinate first) (coordinate second) (basis.values row first) (basis.values row second))
  let secondError := WeightedNormBudget.build (fun row => AffineTriangle.affinePrimitiveIncrementError
    (basis.coefficients row face)
    (coordinate first) (coordinate third) (basis.values row first) (basis.values row third))
  let products := restrictProducts (PrimitiveSurfaceBudget.TriangleProductBudget.uniform coefficient epsilon
    distance coefficientNonnegative epsilonNonnegative epsilonLe distanceNonnegative)
    firstAffine.nonnegative secondAffine.nonnegative firstError.nonnegative secondError.nonnegative
    (firstAffine.scale_eq.trans_le (affineBound _ (Or.inl rfl))) (secondAffine.scale_eq.trans_le (affineBound _ (Or.inr
      rfl)))
    (firstError.scale_eq.trans_le (errorBound _ (Or.inl rfl))) (secondError.scale_eq.trans_le (errorBound _ (Or.inr
      rfl)))
  ⟨firstAffine, secondAffine, firstError, secondError, products, epsilon * distance * (2 * coefficient + 3), by
    change epsilon * distance * (2 * coefficient + 3) = epsilon * distance * (coefficient + 1) +
      epsilon * distance * (coefficient + 1) + epsilon * distance
    ring1⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- The original uniform face budget total is exactly tolerance times distance times twice the coefficient plus three.
-/
theorem uniform_total (basis : AffineBasis triangulation coordinate count) (face : Fin faceCount)
    (coefficient epsilon distance : Fraction.Rational) (coefficientNonnegative : 0 ≤ coefficient)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonLe : epsilon ≤ 1) (distanceNonnegative : 0 ≤ distance)
    (affineBound : ∀ last, last = (triangulation.faces face).second ∨ last = (triangulation.faces face).third →
      (count : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (AffineTriangle.affinePrimitiveIncrement (basis.coefficients row face)
        (coordinate (triangulation.faces face).first) (coordinate last))) ≤ coefficient * distance)
    (errorBound : ∀ last, last = (triangulation.faces face).second ∨ last = (triangulation.faces face).third →
      (count : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
        (AffineTriangle.affinePrimitiveIncrementError (basis.coefficients row face)
        (coordinate (triangulation.faces face).first) (coordinate last)
        (basis.values row (triangulation.faces face).first) (basis.values row last))) ≤ 2 * epsilon ^ 2 * distance) :
    (uniform basis face coefficient epsilon distance coefficientNonnegative epsilonNonnegative epsilonLe
      distanceNonnegative affineBound errorBound).total =
      epsilon * distance * (2 * coefficient + 3) := rfl

end AffineBasis.TriangleBudget
end Purelib.Riemann.Integration.AffineBasisUniformBudget
