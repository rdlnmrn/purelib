module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Global finite surface-energy error accounting

This is the pre-normalization comparison layer for arbitrary genus.  Local
affine models may incur signed energy errors on individual triangles, and
the finite primitive boundary need only approximate the actual period
commutators.  We pay both losses before claiming a positive global bound.

The finite geometry, primitive construction, and quantitative coercivity
remain separate obligations.  In particular, the constructors below do not
assert that arbitrary supplied period programs have positive energy.

All sums consumed downstream are cached with their exact defining equations.
There are no new algebra imports: the finite rational, Gaussian, and incidence
lemmas are inherited from the existing prepared-surface implementation.
-/

namespace Purelib.Riemann.Topology.PreparedSurfaceCoercivity

open Purelib.LinearAlgebra

section
open Purelib.Data
/-- The rational scalar type for finite surface-energy and error bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational coordinate and primitive-value type. -/
abbrev Gaussian := Gaussian.Basic.Canonical

end

/-- Compute a rational error budget as squared error divided by positive radius plus that radius. -/
def squareErrorBudget (squared radius : Coordinate) : Coordinate :=
  squared / radius + radius

section
open Purelib.Data
/-- Nonnegative squared error and positive radius give a nonnegative computed budget. -/
theorem squareErrorBudget_nonnegative {squared radius : Coordinate}
    (squaredNonnegative : 0 <= squared) (radiusPositive : 0 < radius) :
    0 <= squareErrorBudget squared radius :=
  add_nonneg (Rat.Fraction.Order.Field.div_nonneg_direct
    squaredNonnegative radiusPositive.le) radiusPositive.le

/-- The computed rational budget's square bounds the supplied nonnegative squared error. -/
theorem squared_le_squareErrorBudget_sq {squared radius : Coordinate}
    (squaredNonnegative : 0 <= squared) (radiusPositive : 0 < radius) :
    squared <= squareErrorBudget squared radius ^ 2 := by
  have cancel := Rat.Fraction.Field.div_mul_cancel_of_ne
    squared radius radiusPositive.ne'
  have identity : squareErrorBudget squared radius ^ 2 - squared =
      (squared / radius) ^ 2 + squared + radius ^ 2 := by
    unfold squareErrorBudget
    calc
      _ = (squared / radius) ^ 2 +
          2 * ((squared / radius) * radius) + radius ^ 2 - squared := by ring1
      _ = _ := by rw [cancel]; ring1
  apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [identity]
  exact add_nonneg
    (add_nonneg (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _) squaredNonnegative)
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- A quadratic squared-error rate gives a linear rate for the computed rational budget. -/
theorem squareErrorBudget_le_of_squared_le {squared radius factor : Coordinate}
    (radiusPositive : 0 < radius) (bounded : squared <= factor * radius ^ 2) :
    squareErrorBudget squared radius <= (factor + 1) * radius := by
  have divided : squared / radius <= factor * radius :=
    (Rat.Fraction.Order.Field.div_le_iff_pos radiusPositive).2
      (bounded.trans_eq (by ring1))
  calc
    squareErrorBudget squared radius <= factor * radius + radius :=
      Rat.Fraction.Order.Arithmetic.add_le_add_right_direct divided radius
    _ = (factor + 1) * radius := by ring1

/-- One quarter of the product of the two Gaussian quadrances. -/
def crossErrorSquare (first second : Gaussian) : Coordinate :=
  Gaussian.Norm.Basic.normSq first *
    Gaussian.Norm.Basic.normSq second / 4

/-- The cross-error squared allowance is nonnegative. -/
public theorem crossErrorSquare_nonnegative (first second : Gaussian) :
    0 <= crossErrorSquare first second :=
  Rat.Fraction.Order.Field.div_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Gaussian.Norm.Basic.normSq_nonneg first)
      (Gaussian.Norm.Basic.normSq_nonneg second)) (by decide)

end

section
open Purelib.Integration
/-- Compute all three certified affine triangle error allowances from a positive rational radius.

The fixed formula bounds the two mixed affine-error products and the error-error product using the exact supplied
coordinates, primitive readings and coefficient. -/
def computedAffineTriangleError
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian)
    (radius : Coordinate) (radiusPositive : 0 < radius) :
    Energy.AffineTriangle.AffineTriangleErrorCertificate coefficient
      coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird := by
  let first := Energy.AffineTriangle.affinePrimitiveIncrement coefficient coordinateFirst coordinateSecond
  let second := Energy.AffineTriangle.affinePrimitiveIncrement coefficient coordinateFirst coordinateThird
  let firstError := Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateSecond primitiveFirst primitiveSecond
  let secondError := Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateThird primitiveFirst primitiveThird
  exact
    { firstBudget := squareErrorBudget (crossErrorSquare firstError second) radius
      secondBudget := squareErrorBudget (crossErrorSquare first secondError) radius
      mixedBudget := squareErrorBudget (crossErrorSquare firstError secondError) radius
      firstBudget_nonnegative := squareErrorBudget_nonnegative
        (crossErrorSquare_nonnegative _ _) radiusPositive
      secondBudget_nonnegative := squareErrorBudget_nonnegative
        (crossErrorSquare_nonnegative _ _) radiusPositive
      mixedBudget_nonnegative := squareErrorBudget_nonnegative
        (crossErrorSquare_nonnegative _ _) radiusPositive
      firstProductBound := squared_le_squareErrorBudget_sq
        (crossErrorSquare_nonnegative _ _) radiusPositive
      secondProductBound := squared_le_squareErrorBudget_sq
        (crossErrorSquare_nonnegative _ _) radiusPositive
      mixedProductBound := squared_le_squareErrorBudget_sq
        (crossErrorSquare_nonnegative _ _) radiusPositive }

/-- Quadratic bounds on all three cross errors give a linear total triangle-error allowance.

The coefficient is the sum of the three retained factors plus three, multiplied by the same positive radius. -/
theorem computedAffineTriangleError_totalBudget_le
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian)
    (radius : Coordinate) (radiusPositive : 0 < radius)
    (firstFactor secondFactor mixedFactor : Coordinate)
    (firstBound : crossErrorSquare
        (Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst coordinateSecond
          primitiveFirst primitiveSecond)
        (Energy.AffineTriangle.affinePrimitiveIncrement coefficient coordinateFirst coordinateThird) <=
      firstFactor * radius ^ 2)
    (secondBound : crossErrorSquare
        (Energy.AffineTriangle.affinePrimitiveIncrement coefficient coordinateFirst coordinateSecond)
        (Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst coordinateThird
          primitiveFirst primitiveThird) <= secondFactor * radius ^ 2)
    (mixedBound : crossErrorSquare
        (Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst coordinateSecond
          primitiveFirst primitiveSecond)
        (Energy.AffineTriangle.affinePrimitiveIncrementError coefficient coordinateFirst coordinateThird
          primitiveFirst primitiveThird) <= mixedFactor * radius ^ 2) :
    (computedAffineTriangleError coefficient
      coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird radius radiusPositive).totalBudget <=
      (firstFactor + secondFactor + mixedFactor + 3) * radius := by
  have first := squareErrorBudget_le_of_squared_le radiusPositive firstBound
  have second := squareErrorBudget_le_of_squared_le radiusPositive secondBound
  have mixed := squareErrorBudget_le_of_squared_le radiusPositive mixedBound
  exact (add_le_add (add_le_add first second) mixed).trans_eq (by ring1)

end

open Purelib.Integration in
open Purelib.Data in
/-- An exact affine primitive gives total computed triangle allowance exactly three times the radius. -/
theorem computedAffineTriangleError_exact_totalBudget
    (coefficient first second third : Gaussian)
    (radius : Coordinate) (radiusPositive : 0 < radius) :
    (computedAffineTriangleError coefficient first second third
      (coefficient * first) (coefficient * second) (coefficient * third)
      radius radiusPositive).totalBudget = 3 * radius := by
  simp only [computedAffineTriangleError, Energy.AffineTriangle.AffineTriangleErrorCertificate.totalBudget,
    Energy.AffineTriangle.affinePrimitiveIncrementError, Energy.AffineTriangle.affinePrimitiveIncrement,
    Gaussian.Basic.sub_self, crossErrorSquare,
    Gaussian.Norm.Basic.normSq_zero,
    Rat.Fraction.Field.zero_mul_direct,
    Rat.Fraction.Field.mul_zero_direct, squareErrorBudget,
    Rat.Fraction.Field.div_eq_mul_inv_direct,
    _root_.zero_add]
  ring1

set_option genInjectivity false in
open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Finite affine surface readings with cached energy, error allowance and primitive boundary area.

The triangulation retains independently indexed vertices and faces. Each face carries its actual affine-error
certificate; the aggregate estimates permit signed local energies. -/
structure AffineSurfaceSample (vertexCount faceCount : Nat) where
  /-- The retained finite oriented triangulation and its boundary. -/ triangulation :
    Polygon.Stokes.Triangulation vertexCount faceCount
  /-- The actual Gaussian coordinate at each retained vertex. -/ coordinate : Fin vertexCount -> Gaussian
  /-- The actual Gaussian primitive reading at each retained vertex. -/ primitiveValue : Fin vertexCount -> Gaussian
  /-- The retained Gaussian affine coefficient on each face. -/ faceCoefficient : Fin faceCount -> Gaussian
  /-- Each face's certified error for its exact coordinates, primitive readings and coefficient. -/ faceError : forall
    face : Fin faceCount,
    Energy.AffineTriangle.AffineTriangleErrorCertificate (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third)
  /-- The cached total signed affine face energy. -/ affineEnergy : Coordinate
  /-- The energy cache sums actual triangle area times face-coefficient quadrance. -/ affineEnergy_eq : affineEnergy =
    FiniteSum.Fin.sumFin (fun face =>
    Energy.AffineTriangle.coordinateTriangleArea
        (coordinate (triangulation.faces face).first)
        (coordinate (triangulation.faces face).second)
        (coordinate (triangulation.faces face).third) *
      Gaussian.Norm.Basic.normSq (faceCoefficient face))
  /-- The cached sum of retained face-error allowances. -/ errorBudget : Coordinate
  /-- The error cache equals the finite sum of each actual face certificate's total budget. -/ errorBudget_eq :
    errorBudget = FiniteSum.Fin.sumFin (fun face => (faceError face).totalBudget)
  /-- The cached primitive area on the retained triangulation boundary. -/ boundaryArea : Gaussian
  /-- The boundary cache reads the energy primitive points of the original vertex readings. -/ boundaryArea_eq :
    boundaryArea =
    Polygon.Stokes.edgeListArea
      (fun vertex => Energy.Polygon.energyPrimitivePoint (primitiveValue vertex))
      triangulation.boundary

constructive_injectivity AffineSurfaceSample

namespace AffineSurfaceSample

variable {vertexCount faceCount : Nat}

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Cache the affine energy, total error and boundary area of the retained face bank. -/
def ofFaces
    (triangulation :
      Polygon.Stokes.Triangulation vertexCount faceCount)
    (coordinate primitiveValue : Fin vertexCount -> Gaussian)
    (faceCoefficient : Fin faceCount -> Gaussian)
    (faceError : forall face : Fin faceCount,
      Energy.AffineTriangle.AffineTriangleErrorCertificate (faceCoefficient face)
        (coordinate (triangulation.faces face).first)
        (coordinate (triangulation.faces face).second)
        (coordinate (triangulation.faces face).third)
        (primitiveValue (triangulation.faces face).first)
        (primitiveValue (triangulation.faces face).second)
        (primitiveValue (triangulation.faces face).third)) :
    AffineSurfaceSample vertexCount faceCount where
  triangulation := triangulation
  coordinate := coordinate
  primitiveValue := primitiveValue
  faceCoefficient := faceCoefficient
  faceError := faceError
  affineEnergy := FiniteSum.Fin.sumFin (fun face =>
    Energy.AffineTriangle.coordinateTriangleArea
        (coordinate (triangulation.faces face).first)
        (coordinate (triangulation.faces face).second)
        (coordinate (triangulation.faces face).third) *
      Gaussian.Norm.Basic.normSq (faceCoefficient face))
  affineEnergy_eq := rfl
  errorBudget := FiniteSum.Fin.sumFin (fun face => (faceError face).totalBudget)
  errorBudget_eq := rfl
  boundaryArea := Polygon.Stokes.edgeListArea
    (fun vertex => Energy.Polygon.energyPrimitivePoint (primitiveValue vertex))
    triangulation.boundary
  boundaryArea_eq := rfl

open Purelib.Topology in
/-- Compute local affine-error certificates and aggregate surface caches from finite vertex readings.

The supplied positive radius determines each face's three rational allowances, with their square checks discharged by
the fixed formula. -/
def ofVertices
    (triangulation :
      Polygon.Stokes.Triangulation vertexCount faceCount)
    (coordinate primitiveValue : Fin vertexCount -> Gaussian)
    (faceCoefficient : Fin faceCount -> Gaussian)
    (radius : Coordinate) (radiusPositive : 0 < radius) :
    AffineSurfaceSample vertexCount faceCount :=
  ofFaces triangulation coordinate primitiveValue faceCoefficient (fun face =>
    computedAffineTriangleError (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third) radius radiusPositive)

open Purelib.Algebra in
open Purelib.Topology in
/-- Exact common affine primitive readings give the finite sum of three-radius face allowances. -/
theorem ofVertices_exact_errorBudget
    (triangulation :
      Polygon.Stokes.Triangulation vertexCount faceCount)
    (coordinate : Fin vertexCount -> Gaussian) (coefficient : Gaussian)
    (radius : Coordinate) (radiusPositive : 0 < radius) :
    (ofVertices triangulation coordinate
      (fun vertex => coefficient * coordinate vertex) (fun _ => coefficient)
      radius radiusPositive).errorBudget =
      FiniteSum.Fin.sumFin (fun _ : Fin faceCount => 3 * radius) := by
  change FiniteSum.Fin.sumFin _ = FiniteSum.Fin.sumFin _
  apply FiniteSum.Fin.sumFin_congr
  intro face
  exact computedAffineTriangleError_exact_totalBudget coefficient
    (coordinate (triangulation.faces face).first)
    (coordinate (triangulation.faces face).second)
    (coordinate (triangulation.faces face).third) radius radiusPositive

open Purelib.Algebra in
/-- The cached total face-error allowance is nonnegative. -/
theorem errorBudget_nonnegative (sample : AffineSurfaceSample vertexCount faceCount) :
    0 <= sample.errorBudget := by
  rw [sample.errorBudget_eq]
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun _ : Fin faceCount => (0 : Coordinate))
    (fun face => (sample.faceError face).totalBudget)
    (fun face => (sample.faceError face).totalBudget_nonnegative)
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Finite Stokes identifies total primitive face energy with one quarter of cached boundary imaginary area. -/
theorem triangleEnergySum_eq_boundaryEnergy
    (sample : AffineSurfaceSample vertexCount faceCount) :
    FiniteSum.Fin.sumFin (fun face => Energy.AffineTriangle.triangleEnergy
        (fun vertex => Energy.Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
        (sample.triangulation.faces face)) = sample.boundaryArea.im / 4 := by
  rw [sample.boundaryArea_eq]
  rw [<- sample.triangulation.wedgeSum_eq_boundaryArea
    (fun vertex => Energy.Polygon.energyPrimitivePoint (sample.primitiveValue vertex))]
  unfold Energy.AffineTriangle.triangleEnergy Polygon.Stokes.triangleWedgeSum
  rw [Gaussian.Energy.sumFin_im]
  simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
  exact FiniteSum.Fin.sumFin_mul_right _ _

open Purelib.Algebra in
/-- Paying the total face-error allowance leaves a lower bound for cached boundary energy.

Individual face energies may be signed; the finite estimate sums the retained local inequalities. -/
theorem affineEnergy_sub_errorBudget_le_boundaryEnergy
    (sample : AffineSurfaceSample vertexCount faceCount) :
    sample.affineEnergy - sample.errorBudget <= sample.boundaryArea.im / 4 := by
  rw [sample.affineEnergy_eq, sample.errorBudget_eq, <- FiniteSum.Fin.sumFin_sub]
  exact (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
    (fun face => (sample.faceError face).affineEnergy_sub_totalBudget_le)).trans_eq
      sample.triangleEnergySum_eq_boundaryEnergy

end AffineSurfaceSample

section
open Purelib.Data
/-- A Gaussian quadrance error check bounds the loss in imaginary boundary energy.

For nonnegative budget, squared discrepancy at most (four times budget) squared pays the actual imaginary-area
difference divided by four. -/
theorem boundaryEnergy_sub_budget_le (actual reference : Gaussian)
    (budget : Coordinate) (nonnegative : 0 <= budget)
    (close : Gaussian.Norm.Basic.normSq (actual - reference) <=
      (4 * budget) ^ 2) :
    actual.im / 4 - budget <= reference.im / 4 := by
  have imaginarySquare : (actual - reference).im ^ 2 <=
      Gaussian.Norm.Basic.normSq (actual - reference) :=
    le_add_of_nonneg_left
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (actual - reference).re)
  have imaginaryBound := Rat.Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Coordinate) <= 4 by decide) nonnegative)
    (imaginarySquare.trans close)
  have scaled := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    imaginaryBound (show (0 : Coordinate) <= (4 : Coordinate)⁻¹ by decide)
  have shifted := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    scaled (reference.im / 4 - budget)
  simpa only [Gaussian.Basic.sub_im,
    Rat.Fraction.Field.div_eq_mul_inv_direct] using
    (show actual.im * (4 : Coordinate)⁻¹ - budget <=
      reference.im * (4 : Coordinate)⁻¹ from by
      calc
        actual.im * (4 : Coordinate)⁻¹ - budget =
            (actual - reference).im * (4 : Coordinate)⁻¹ +
              (reference.im / 4 - budget) := by
          simp only [Gaussian.Basic.sub_im,
            Rat.Fraction.Field.div_eq_mul_inv_direct]
          ring1
        _ <= 4 * budget * (4 : Coordinate)⁻¹ +
            (reference.im / 4 - budget) := shifted
        _ = reference.im * (4 : Coordinate)⁻¹ := by
          rw [show (4 : Coordinate)⁻¹ = (1 / 4 : Coordinate) by decide]
          simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
          have fourCancel : (4 : Coordinate) * (4 : Coordinate)⁻¹ = 1 := by decide
          calc
            _ = budget * ((4 : Coordinate) * (4 : Coordinate)⁻¹) +
                reference.im * (4 : Coordinate)⁻¹ - budget := by ring1
            _ = _ := by rw [fourCancel]; ring1)

/-- A squared imaginary-coordinate error check bounds the corresponding boundary-energy loss. -/
theorem boundaryEnergy_sub_budget_le_of_im (actual reference : Gaussian)
    (budget : Coordinate) (nonnegative : 0 <= budget)
    (close : (actual - reference).im ^ 2 <= (4 * budget) ^ 2) :
    actual.im / 4 - budget <= reference.im / 4 := by
  have imaginaryBound := Rat.Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Coordinate) <= 4 by decide) nonnegative)
    close
  have scaled := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    imaginaryBound (show (0 : Coordinate) <= (4 : Coordinate)⁻¹ by decide)
  have shifted := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    scaled (reference.im / 4 - budget)
  simpa only [Gaussian.Basic.sub_im,
    Rat.Fraction.Field.div_eq_mul_inv_direct] using
    (show actual.im * (4 : Coordinate)⁻¹ - budget <=
      reference.im * (4 : Coordinate)⁻¹ from by
      calc
        actual.im * (4 : Coordinate)⁻¹ - budget =
            (actual - reference).im * (4 : Coordinate)⁻¹ +
              (reference.im / 4 - budget) := by
          simp only [Gaussian.Basic.sub_im,
            Rat.Fraction.Field.div_eq_mul_inv_direct]
          ring1
        _ <= 4 * budget * (4 : Coordinate)⁻¹ +
            (reference.im / 4 - budget) := shifted
        _ = reference.im * (4 : Coordinate)⁻¹ := by
          rw [show (4 : Coordinate)⁻¹ = (1 / 4 : Coordinate) by decide]
          simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
          have fourCancel : (4 : Coordinate) * (4 : Coordinate)⁻¹ = 1 := by decide
          calc
            _ = budget * ((4 : Coordinate) * (4 : Coordinate)⁻¹) +
                reference.im * (4 : Coordinate)⁻¹ - budget := by ring1
            _ = _ := by rw [fourCancel]; ring1)

end

namespace AffineSurfaceSample

variable {vertexCount faceCount genus : Nat}

open Purelib.Integration in
open Purelib.Data in
/-- Pay both affine-face error and boundary matching error before comparing with actual period-pairing energy.

The supplied boundary quadrance check identifies the same cached surface boundary with the displayed A/B period
commutator boundary. -/
theorem affineEnergy_sub_budgets_le_periodPairing
    (sample : AffineSurfaceSample vertexCount faceCount)
    (aPeriods bPeriods : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (boundaryBudget : Coordinate) (nonnegative : 0 <= boundaryBudget)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea aPeriods bPeriods) <=
      (4 * boundaryBudget) ^ 2) :
    sample.affineEnergy - sample.errorBudget - boundaryBudget <=
      Gaussian.Energy.periodPairingEnergy aPeriods bPeriods := by
  rw [Energy.Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four]
  exact (Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct sample.affineEnergy_sub_errorBudget_le_boundaryEnergy
    boundaryBudget).trans
      (boundaryEnergy_sub_budget_le _ _ boundaryBudget nonnegative close)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- The paid affine surface estimate bounds the raw energy form at the actual synchronized A/B sample.

The coefficient vector, sample index and boundary discrepancy are retained explicitly before period normalization. -/
theorem affineEnergy_sub_budgets_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (sample : AffineSurfaceSample vertexCount faceCount)
    (data : Periods.PeriodMatrix.PeriodData curve)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (sampleIndex : Nat) (boundaryBudget : Coordinate)
    (nonnegative : 0 <= boundaryBudget)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.aMatrix sampleIndex))
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.bMatrix sampleIndex))) <=
      (4 * boundaryBudget) ^ 2) :
    sample.affineEnergy - sample.errorBudget - boundaryBudget <=
      Gaussian.Energy.unnormalizedEnergyForm coefficients
        (Periods.PeriodMatrix.sampledMatrix data.aMatrix sampleIndex)
        (Periods.PeriodMatrix.sampledMatrix data.bMatrix sampleIndex) :=
  sample.affineEnergy_sub_budgets_le_periodPairing _ _ boundaryBudget nonnegative close

end AffineSurfaceSample

section
open Purelib.Approximation
/-- Compute a refinement index whose geometric allowance falls below half the supplied energy lower bound. -/
def energyRefinementIndex (scale lower : Coordinate) (current : Nat) : Nat :=
  Rational.Geometric.Search.firstQuarterBelow scale current (lower / 2)

/-- The computed energy-refinement index is at least the requested starting index. -/
theorem energyRefinementIndex_ge (scale lower : Coordinate) (current : Nat) :
    current <= energyRefinementIndex scale lower current :=
  Rational.Geometric.Search.firstQuarterBelow_ge scale current (lower / 2)

end

open Purelib.Approximation in
open Purelib.Data in
/-- Every index beyond the computed refinement has geometric error below half the positive energy floor. -/
theorem error_lt_half_at_energyRefinement {scale lower : Coordinate}
    (scaleNonnegative : 0 <= scale) (lowerPositive : 0 < lower)
    (current index : Nat)
    (refined : energyRefinementIndex scale lower current <= index) :
    Rational.Geometric.Basic.quarterRadius scale index < lower / 2 :=
  (quarterRadius_antitone scaleNonnegative refined).trans_lt
    (Rational.Geometric.Search.firstQuarterBelow_accurate scale scaleNonnegative
      current (lower / 2)
      (Rat.Fraction.Order.Field.div_pos_direct lowerPositive (by decide)))

namespace AffineSurfaceSample

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- A certified surface lower bound and geometric error rate give a strict period-energy margin after finite refinement.

The retained boundary comparison pays the actual boundary loss, and the computed stage leaves more than half the
positive lower bound. -/
theorem half_lower_lt_periodPairing_of_refined
    {vertexCount faceCount genus : Nat}
    (sample : AffineSurfaceSample vertexCount faceCount)
    (aPeriods bPeriods : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {scale lower boundaryBudget : Coordinate}
    (scaleNonnegative : 0 <= scale) (lowerPositive : 0 < lower)
    (boundaryNonnegative : 0 <= boundaryBudget)
    (current index : Nat)
    (refined : energyRefinementIndex scale lower current <= index)
    (surfaceLower : lower <= sample.affineEnergy)
    (errorDecay : sample.errorBudget + boundaryBudget <=
      Rational.Geometric.Basic.quarterRadius scale index)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea aPeriods bPeriods) <=
      (4 * boundaryBudget) ^ 2) :
    lower / 2 < Gaussian.Energy.periodPairingEnergy aPeriods bPeriods := by
  have errorSmall := errorDecay.trans_lt
    (error_lt_half_at_energyRefinement scaleNonnegative lowerPositive
      current index refined)
  have halfIdentity : lower - lower / 2 = lower / 2 := by
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    have twoCancel : (2 : Coordinate) * (2 : Coordinate)⁻¹ = 1 := by decide
    calc
      _ = lower * ((2 : Coordinate) * (2 : Coordinate)⁻¹) -
          lower * (2 : Coordinate)⁻¹ := by rw [twoCancel]; ring1
      _ = _ := by ring1
  have margin := Rat.Fraction.Order.Arithmetic.sub_lt_sub_left_direct errorSmall lower
  rw [halfIdentity] at margin
  calc
    lower / 2 < lower - (sample.errorBudget + boundaryBudget) := margin
    _ <= sample.affineEnergy - (sample.errorBudget + boundaryBudget) :=
      Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct surfaceLower _
    _ = sample.affineEnergy - sample.errorBudget - boundaryBudget := by ring1
    _ <= Gaussian.Energy.periodPairingEnergy aPeriods bPeriods :=
      sample.affineEnergy_sub_budgets_le_periodPairing aPeriods bPeriods
        boundaryBudget boundaryNonnegative close

open Purelib.Integration in
open Purelib.Data in
/-- A displayed total allowance below half the surface lower bound gives the strict period-energy margin.

The conclusion consumes the retained face error and actual boundary comparison directly at the supplied sample. -/
theorem half_lower_lt_periodPairing_of_allowance
    {vertexCount faceCount genus : Nat}
    (sample : AffineSurfaceSample vertexCount faceCount)
    (aPeriods bPeriods : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {lower boundaryBudget : Coordinate}
    (boundaryNonnegative : 0 <= boundaryBudget)
    (surfaceLower : lower <= sample.affineEnergy)
    (allowance : sample.errorBudget + boundaryBudget < lower / 2)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea aPeriods bPeriods) <=
      (4 * boundaryBudget) ^ 2) :
    lower / 2 < Gaussian.Energy.periodPairingEnergy aPeriods bPeriods := by
  have halfIdentity : lower - lower / 2 = lower / 2 := by
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    have twoCancel : (2 : Coordinate) * (2 : Coordinate)⁻¹ = 1 := by decide
    calc
      _ = lower * ((2 : Coordinate) * (2 : Coordinate)⁻¹) -
          lower * (2 : Coordinate)⁻¹ := by rw [twoCancel]; ring1
      _ = _ := by ring1
  have margin := Rat.Fraction.Order.Arithmetic.sub_lt_sub_left_direct allowance lower
  rw [halfIdentity] at margin
  calc
    lower / 2 < lower - (sample.errorBudget + boundaryBudget) := margin
    _ <= sample.affineEnergy - (sample.errorBudget + boundaryBudget) :=
      Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct surfaceLower _
    _ = sample.affineEnergy - sample.errorBudget - boundaryBudget := by ring1
    _ <= Gaussian.Energy.periodPairingEnergy aPeriods bPeriods :=
      sample.affineEnergy_sub_budgets_le_periodPairing aPeriods bPeriods
        boundaryBudget boundaryNonnegative close

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- The certified finite refinement gives a strict margin for the actual raw sampled A/B energy form.

Both sampled matrices use the same retained stage and coefficient vector, and the boundary comparison identifies their
actual commutator area. -/
theorem half_lower_lt_unnormalizedEnergyForm_of_refined
    {vertexCount faceCount genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (sample : AffineSurfaceSample vertexCount faceCount)
    (data : Periods.PeriodMatrix.PeriodData curve)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {scale lower boundaryBudget : Coordinate}
    (scaleNonnegative : 0 <= scale) (lowerPositive : 0 < lower)
    (boundaryNonnegative : 0 <= boundaryBudget)
    (current index : Nat)
    (refined : energyRefinementIndex scale lower current <= index)
    (surfaceLower : lower <= sample.affineEnergy)
    (errorDecay : sample.errorBudget + boundaryBudget <=
      Rational.Geometric.Basic.quarterRadius scale index)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.aMatrix index))
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.bMatrix index))) <=
      (4 * boundaryBudget) ^ 2) :
    lower / 2 < Gaussian.Energy.unnormalizedEnergyForm coefficients
      (Periods.PeriodMatrix.sampledMatrix data.aMatrix index)
      (Periods.PeriodMatrix.sampledMatrix data.bMatrix index) :=
  sample.half_lower_lt_periodPairing_of_refined
    (Gaussian.Energy.periodCombination coefficients
      (Periods.PeriodMatrix.sampledMatrix data.aMatrix index))
    (Gaussian.Energy.periodCombination coefficients
      (Periods.PeriodMatrix.sampledMatrix data.bMatrix index))
    scaleNonnegative lowerPositive boundaryNonnegative current index refined
    surfaceLower errorDecay close

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- A displayed paid allowance gives the strict raw energy margin at the actual synchronized A/B sample. -/
theorem half_lower_lt_unnormalizedEnergyForm_of_allowance
    {vertexCount faceCount genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (sample : AffineSurfaceSample vertexCount faceCount)
    (data : Periods.PeriodMatrix.PeriodData curve)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {lower boundaryBudget : Coordinate}
    (boundaryNonnegative : 0 <= boundaryBudget)
    (surfaceLower : lower <= sample.affineEnergy)
    (allowance : sample.errorBudget + boundaryBudget < lower / 2)
    (close : Gaussian.Norm.Basic.normSq
        (sample.boundaryArea - Energy.Polygon.energyBoundaryArea
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.aMatrix index))
          (Gaussian.Energy.periodCombination coefficients
            (Periods.PeriodMatrix.sampledMatrix data.bMatrix index))) <=
      (4 * boundaryBudget) ^ 2) :
    lower / 2 < Gaussian.Energy.unnormalizedEnergyForm coefficients
      (Periods.PeriodMatrix.sampledMatrix data.aMatrix index)
      (Periods.PeriodMatrix.sampledMatrix data.bMatrix index) :=
  sample.half_lower_lt_periodPairing_of_allowance
    (Gaussian.Energy.periodCombination coefficients
      (Periods.PeriodMatrix.sampledMatrix data.aMatrix index))
    (Gaussian.Energy.periodCombination coefficients
      (Periods.PeriodMatrix.sampledMatrix data.bMatrix index))
    boundaryNonnegative surfaceLower allowance close

end AffineSurfaceSample

end Purelib.Riemann.Topology.PreparedSurfaceCoercivity
