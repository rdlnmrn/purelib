module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Polygon
import Purelib.Topology.Polygon.Stokes

public import Purelib.Riemann.Readings.PrimitiveTriangleEnergy
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Homogeneous affine errors for a fixed finite primitive basis

All bounds are calculated from the actual retained basis readings before a
coefficient vector is supplied. Linear combinations reuse those readings;
the resulting affine error is exactly the squared coefficient norm times a
cached basis budget, including at the zero vector.
-/

namespace Purelib.Riemann.Readings.AffineBasisEnergy

open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_mul)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left sumFin_mul_right sumFin_sub)
open Purelib.Riemann.Readings.PrimitiveTriangleEnergy (TriangleProductBudget)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (AffineSurfaceSample)

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- A finite sum of nonnegative rational entries is nonnegative. -/
public theorem sum_nonnegative {count : Nat} (values : Fin count → Fraction.Rational) (nonnegative : ∀ index, 0 ≤
  values index) :
    0 ≤ FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- Every original coefficient squared norm is bounded by the same vector's total squared norm. -/
private theorem coefficient_entry_le {count : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
  (row : Fin count)
  :
    Data.Gaussian.Norm.Basic.normSq (coefficients row) ≤ coefficientNormSq coefficients := by
  have norms : FiniteSum.Fin.sumFin (fun index => Data.Gaussian.Norm.Basic.normSq (coefficients index)) =
      coefficientNormSq coefficients := by
    unfold coefficientNormSq
    exact FiniteSum.Fin.sumFin_congr (fun index => Norm.Basic.normSq_eq_canonical (coefficients index))
  rw [← norms]
  rw [← FiniteSum.Fin.sumFin_ite_eq row (fun index => Data.Gaussian.Norm.Basic.normSq (coefficients index))]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro index
  if equal : index = row then rw [if_pos equal]
  else rw [if_neg equal]; exact Norm.Basic.normSq_nonneg _

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- The cached count-weighted sum of the original Gaussian entries' squared norms.

Its defining equation retains the exact finite count and indexed values, providing a uniform scalar bound for arbitrary
coefficients on that same index type. -/
structure WeightedNormBudget {count : Nat} (values : Fin count → Basic.Canonical) where
  /-- The cached common scale for coefficient-weighted readings of the original entries. -/ scale : Fraction.Rational
  /-- The scale is the original count times the finite sum of entry squared norms. -/ scale_eq : scale = (count :
    Fraction.Rational) * FiniteSum.Fin.sumFin (fun index => Data.Gaussian.Norm.Basic.normSq (values index))

constructive_injectivity WeightedNormBudget

namespace WeightedNormBudget

variable {count : Nat} {values : Fin count → Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Cache the exact original count-weighted sum of squared Gaussian norms. -/
def build (values : Fin count → Basic.Canonical) : WeightedNormBudget values :=
  ⟨Budget.Aggregate.countCoordinate count * FiniteSum.Fin.sumFin (fun index => Data.Gaussian.Norm.Basic.normSq (values
    index)), by
    rw [Budget.Aggregate.countCoordinate_eq]⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained weighted squared-norm scale is nonnegative. -/
theorem nonnegative (budget : WeightedNormBudget values) : 0 ≤ budget.scale := by
  rw [budget.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
    (sum_nonnegative _ (fun _ => Norm.Basic.normSq_nonneg _))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The original weighted Gaussian sum is bounded by coefficient squared norm times its retained scale. -/
theorem bound (budget : WeightedNormBudget values) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index => coefficients index * values index)) ≤
      coefficientNormSq coefficients * budget.scale := by
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin (fun index => coefficients index * values index)
    (fun index => coefficientNormSq coefficients * Data.Gaussian.Norm.Basic.normSq (values index)) (fun index => by
      rw [Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (coefficient_entry_le coefficients index)
        (Norm.Basic.normSq_nonneg _))
  rw [FiniteSum.Fin.sumFin_mul_left] at estimate
  exact estimate.trans_eq (by rw [budget.scale_eq]; ring1)

end WeightedNormBudget

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
set_option genInjectivity false in
/-- Original vertex primitive values and face coefficients over one retained triangulation.

Both matrices preserve the same finite basis index and the original geometric vertex and face indices; weighted
readbacks use these exact cached entries. -/
structure AffineBasis {vertexCount faceCount : Nat}
    (triangulation : Stokes.Triangulation vertexCount faceCount) (coordinate : Fin vertexCount → Basic.Canonical) (count
      : Nat) where
  /-- The original basis-by-vertex matrix of cached primitive values. -/ values : Data.Vector
    (Data.Vector Basic.Canonical vertexCount) count
  /-- The original basis-by-face matrix of cached affine coefficients. -/ coefficients : Data.Vector
    (Data.Vector Basic.Canonical faceCount) count

constructive_injectivity AffineBasis

namespace AffineBasis

variable {vertexCount faceCount count : Nat} {triangulation : Purelib.Topology.Polygon.Stokes.Triangulation vertexCount
  faceCount}
  {coordinate : Fin vertexCount → Purelib.Data.Gaussian.Basic.Canonical}

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Gaussian
/-- The finite coefficient-weighted sum of original basis values at one retained vertex. -/
def value (basis : AffineBasis triangulation coordinate count) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector count)
  (vertex : Fin vertexCount) : Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun row => coefficients row * basis.values row vertex)

/-- The finite coefficient-weighted sum of original affine coefficients at one retained face. -/
def coefficient (basis : AffineBasis triangulation coordinate count) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector count)
  (face : Fin faceCount) : Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun row => coefficients row * basis.coefficients row face)

end

section
open Purelib.Algebra
open Purelib.Integration.Energy
open Purelib.LinearAlgebra.Gaussian
/-- The weighted basis's affine increment equals the same weighted sum of original basis increments. -/
theorem affine_increment (basis : AffineBasis triangulation coordinate count) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector count)
    (face : Fin faceCount) (first last : Fin vertexCount) :
    AffineTriangle.affinePrimitiveIncrement (basis.coefficient coefficients face) (coordinate first) (coordinate last) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * AffineTriangle.affinePrimitiveIncrement (basis.coefficients
        row face) (coordinate first) (coordinate last)) := by
  unfold AffineTriangle.affinePrimitiveIncrement coefficient
  rw [← FiniteSum.Fin.sumFin_mul_right, ← FiniteSum.Fin.sumFin_mul_right, ← FiniteSum.Fin.sumFin_sub]
  exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)

/-- The weighted basis's increment error equals the same weighted sum of original basis errors. -/
theorem affine_error (basis : AffineBasis triangulation coordinate count) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector
  count)
    (face : Fin faceCount) (first last : Fin vertexCount) :
    AffineTriangle.affinePrimitiveIncrementError (basis.coefficient coefficients face) (coordinate first) (coordinate
      last)
      (basis.value coefficients first) (basis.value coefficients last) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * AffineTriangle.affinePrimitiveIncrementError
        (basis.coefficients row face)
        (coordinate first) (coordinate last) (basis.values row first) (basis.values row last)) := by
  unfold AffineTriangle.affinePrimitiveIncrementError value
  rw [basis.affine_increment, ← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
  exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)

end

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
set_option genInjectivity false in
/-- Separate weighted bounds for both affine edges and both errors on one original face.

The exact retained face vertices determine four count-weighted norm budgets and their certified first, second and mixed
products, with a cached total. -/
structure TriangleBudget (basis : AffineBasis triangulation coordinate count) (face : Fin faceCount) where
  /-- The weighted norm budget for the original face's first affine edge. -/ firstAffine : WeightedNormBudget (fun row
    => AffineTriangle.affinePrimitiveIncrement (basis.coefficients row face)
    (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).second))
  /-- The weighted norm budget for the original face's second affine edge. -/ secondAffine : WeightedNormBudget (fun row
    => AffineTriangle.affinePrimitiveIncrement (basis.coefficients row face)
    (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).third))
  /-- The weighted norm budget for the original face's first increment error. -/ firstError : WeightedNormBudget (fun
    row => AffineTriangle.affinePrimitiveIncrementError (basis.coefficients row face)
    (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).second)
    (basis.values row (triangulation.faces face).first) (basis.values row (triangulation.faces face).second))
  /-- The weighted norm budget for the original face's second increment error. -/ secondError : WeightedNormBudget (fun
    row => AffineTriangle.affinePrimitiveIncrementError (basis.coefficients row face)
    (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).third)
    (basis.values row (triangulation.faces face).first) (basis.values row (triangulation.faces face).third))
  /-- The certified first, second and mixed budgets for these exact retained scales. -/ products : TriangleProductBudget
    firstAffine.scale secondAffine.scale firstError.scale secondError.scale
  /-- The cached total of the exact retained budget entries. -/ total : Fraction.Rational
  /-- The triangle total is exactly the sum of its first, second and mixed product budgets. -/ total_eq : total =
    products.first + products.second + products.mixed

constructive_injectivity TriangleBudget

namespace TriangleBudget

variable {basis : AffineBasis triangulation coordinate count} {face : Fin faceCount}

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- Build the four exact original face-edge norm budgets and their certified product allowances.

The retained triangulation supplies all three vertices, and the same positive radius bounds the first, second and mixed
products of those cached scales. -/
def build (basis : AffineBasis triangulation coordinate count) (face : Fin faceCount) (radius : Fraction.Rational)
  (positive : 0 < radius) :
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
  let products := TriangleProductBudget.build firstAffine.nonnegative secondAffine.nonnegative firstError.nonnegative
    secondError.nonnegative radius positive
  ⟨firstAffine, secondAffine, firstError, secondError, products, products.first + products.second + products.mixed, rfl⟩

open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.LinearAlgebra.Gaussian in
/-- Certify the original weighted affine triangle from its retained four norm budgets.

The coefficient vector scales every original product budget by the same squared norm, preserving the exact face's
vertices, coefficients and primitive values. -/
def certificate (budget : TriangleBudget basis face) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  count) :
    AffineTriangle.AffineTriangleErrorCertificate (basis.coefficient coefficients face)
      (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).second) (coordinate
        (triangulation.faces face).third)
      (basis.value coefficients (triangulation.faces face).first) (basis.value coefficients (triangulation.faces
        face).second)
      (basis.value coefficients (triangulation.faces face).third) :=
  budget.products.certificate (coefficientNormSq coefficients) (sum_nonnegative _ (fun _ =>
    Basic.Canonical.normSq_nonneg _)) _ _ _ _ _ _ _
    (by
        rw [basis.affine_increment];
        simpa only [Norm.Basic.normSq_eq_canonical]
          using budget.firstAffine.bound coefficients)
    (by
        rw [basis.affine_increment];
        simpa only [Norm.Basic.normSq_eq_canonical]
          using budget.secondAffine.bound coefficients)
    (by rw [basis.affine_error]; simpa only [Norm.Basic.normSq_eq_canonical] using budget.firstError.bound coefficients)
    (by
        rw [basis.affine_error];
        simpa only [Norm.Basic.normSq_eq_canonical]
          using budget.secondError.bound coefficients)

open Purelib.LinearAlgebra.Gaussian in
/-- The original triangle certificate total is coefficient squared norm times its retained budget total. -/
theorem certificate_total (budget : TriangleBudget basis face) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    (budget.certificate coefficients).totalBudget = coefficientNormSq coefficients * budget.total := by
  change coefficientNormSq coefficients * budget.products.first + coefficientNormSq coefficients *
    budget.products.second +
    coefficientNormSq coefficients * budget.products.mixed = _
  rw [budget.total_eq]; ring1

end TriangleBudget

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- An indexed bank of original triangle budgets and their cached finite total.

Each entry is owned by the same retained triangulation face and affine basis; the total equation refers to those exact
entries. -/
structure SurfaceBudget (basis : AffineBasis triangulation coordinate count) where
  /-- The dependent bank of triangle budgets at the original face indices. -/ triangles : Vector.DependentVector (fun
    face => TriangleBudget basis face)
  /-- The cached total of the exact retained budget entries. -/ total : Fraction.Rational
  /-- The surface total is exactly the finite sum of the original indexed triangle totals. -/ total_eq : total =
    FiniteSum.Fin.sumFin (fun face => (triangles.get face).total)

constructive_injectivity SurfaceBudget

namespace SurfaceBudget

variable {basis : AffineBasis triangulation coordinate count}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Cache every original face triangle budget and its finite total with the same positive radius. -/
def build (basis : AffineBasis triangulation coordinate count) (radius : Fraction.Rational) (positive : 0 < radius) :
  SurfaceBudget basis :=
  let triangles := Vector.DependentVector.ofFn (fun face => TriangleBudget.build basis face radius positive)
  ⟨triangles, FiniteSum.Fin.sumFin (fun face => (triangles.get face).total), rfl⟩

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.LinearAlgebra.Gaussian in
/-- Transport an original triangle certificate to exact cached vertex values and face coefficient.

The supplied pointwise and scalar equalities preserve the retained budgets and all original proof fields while allowing
the sample to consume its existing caches. -/
public def cachedCertificate (budget : TriangleBudget basis face) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector count)
    (values : Data.Vector Basic.Canonical vertexCount) (valueEq : ∀ vertex, values vertex = basis.value
      coefficients vertex)
    (coefficient : Basic.Canonical) (coefficientEq : coefficient = basis.coefficient coefficients face) :
    AffineTriangle.AffineTriangleErrorCertificate coefficient
      (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).second) (coordinate
        (triangulation.faces face).third)
      (values (triangulation.faces face).first) (values (triangulation.faces face).second) (values (triangulation.faces
        face).third) :=
  let original := budget.certificate coefficients
  { firstBudget := original.firstBudget
    secondBudget := original.secondBudget
    mixedBudget := original.mixedBudget
    firstBudget_nonnegative := original.firstBudget_nonnegative
    secondBudget_nonnegative := original.secondBudget_nonnegative
    mixedBudget_nonnegative := original.mixedBudget_nonnegative
    firstProductBound := by rw [coefficientEq, valueEq, valueEq]; exact original.firstProductBound
    secondProductBound := by rw [coefficientEq, valueEq, valueEq]; exact original.secondProductBound
    mixedProductBound := by rw [coefficientEq, valueEq, valueEq, valueEq]; exact original.mixedProductBound }

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Topology.Polygon in
/-- Cache the weighted primitive values and face coefficients for one certified affine surface sample.

The sample retains the original triangulation, uses those exact caches in every face certificate and boundary readback,
and stores the homogeneous total error without recomputing its entries. -/
def sample (budget : SurfaceBudget basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
  AffineSurfaceSample
  vertexCount faceCount :=
  let values := Vector.Basic.vectorOfFn (basis.value coefficients)
  let faceCoefficients := Vector.Basic.vectorOfFn (basis.coefficient coefficients)
  let errors := fun face => cachedCertificate (budget.triangles.get face) coefficients values
    (Vector.Basic.vectorOfFn_apply _)
    (faceCoefficients face) (Vector.Basic.vectorOfFn_apply _ face)
  { triangulation := triangulation
    coordinate := coordinate
    primitiveValue := fun vertex => values vertex
    faceCoefficient := fun face => faceCoefficients face
    faceError := errors
    affineEnergy := FiniteSum.Fin.sumFin (fun face => AffineTriangle.coordinateTriangleArea
      (coordinate (triangulation.faces face).first) (coordinate (triangulation.faces face).second) (coordinate
        (triangulation.faces face).third) *
      Data.Gaussian.Norm.Basic.normSq (faceCoefficients face))
    affineEnergy_eq := rfl
    errorBudget := coefficientNormSq coefficients * budget.total
    errorBudget_eq := by
      rw [budget.total_eq, ← FiniteSum.Fin.sumFin_mul_left]
      exact FiniteSum.Fin.sumFin_congr (fun face => ((budget.triangles.get face).certificate_total coefficients).symm)
    boundaryArea := Stokes.edgeListArea (fun vertex => Polygon.energyPrimitivePoint (values vertex))
      triangulation.boundary
    boundaryArea_eq := rfl }

section
open Purelib.Data
open Purelib.LinearAlgebra.Gaussian
/-- The cached surface primitive value equals the exact original weighted basis readback. -/
theorem sample_value (budget : SurfaceBudget basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
  (vertex : Fin
  vertexCount) :
    (budget.sample coefficients).primitiveValue vertex = basis.value coefficients vertex :=
      Vector.Basic.vectorOfFn_apply _ vertex

/-- The cached surface face coefficient equals the exact original weighted coefficient readback. -/
theorem sample_coefficient (budget : SurfaceBudget basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  count) (face :
  Fin faceCount) :
    (budget.sample coefficients).faceCoefficient face = basis.coefficient coefficients face :=
      Vector.Basic.vectorOfFn_apply _ face

end

open Purelib.LinearAlgebra.Gaussian
/-- The sampled total error is the coefficient squared norm times the original retained surface budget. -/
theorem sample_error (budget : SurfaceBudget basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
  :
    (budget.sample coefficients).errorBudget = coefficientNormSq coefficients * budget.total := rfl

/-- The original sampled affine energy minus its homogeneous error is bounded by its signed boundary energy. -/
theorem energy_lower (budget : SurfaceBudget basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
  :
    (budget.sample coefficients).affineEnergy - coefficientNormSq coefficients * budget.total ≤
      (budget.sample coefficients).boundaryArea.im / 4 :=
  (budget.sample coefficients).affineEnergy_sub_errorBudget_le_boundaryEnergy

end SurfaceBudget
end AffineBasis
end Purelib.Riemann.Readings.AffineBasisEnergy
