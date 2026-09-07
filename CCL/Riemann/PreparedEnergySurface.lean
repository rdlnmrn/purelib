import CCL.Riemann.PreparedEnergy
import CCL.Riemann.FiniteMatrixApproximation
import CCL.Riemann.FinitePolygonStokes
import CCL.Riemann.BranchCuts
import CCL.Riemann.PreparedClearPathModels

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

namespace CCL.Riemann.PreparedEnergySurface

open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianVector (size : Nat) :=
  CCL.Riemann.FiniteEnergy.GaussianVector size
abbrev PrimitivePoint := CCL.Riemann.FinitePolygonStokes.PrimitivePoint
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev SurfaceCell {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) :=
  CCL.Riemann.PreparedEnergy.SurfaceCell curve coefficients

def lowerLeft (box : RFAP.Boxes.Box) : Gaussian :=
  RFAP.Winding.point box.xLower box.yLower

def lowerRight (box : RFAP.Boxes.Box) : Gaussian :=
  RFAP.Winding.point box.xUpper box.yLower

def upperRight (box : RFAP.Boxes.Box) : Gaussian :=
  RFAP.Winding.point box.xUpper box.yUpper

def upperLeft (box : RFAP.Boxes.Box) : Gaussian :=
  RFAP.Winding.point box.xLower box.yUpper

namespace SurfaceCell

/-- The checked denominator lower bound supplies a horizontal clearance on
the bottom side of the rational surface box. -/
def bottomClearance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    RFAP.BoxClearance.HorizontalLineClearance curve.polynomial cell.box
      cell.box.yLower where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro x lower upper
    exact cell.denominator_apart (RFAP.Winding.point x cell.box.yLower)
      ⟨lower, upper, le_rfl, cell.box.y_valid⟩

def topClearance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    RFAP.BoxClearance.HorizontalLineClearance curve.polynomial cell.box
      cell.box.yUpper where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro x lower upper
    exact cell.denominator_apart (RFAP.Winding.point x cell.box.yUpper)
      ⟨lower, upper, cell.box.y_valid, le_rfl⟩

def leftClearance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    RFAP.BoxClearance.VerticalLineClearance curve.polynomial cell.box
      cell.box.xLower where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro y lower upper
    exact cell.denominator_apart (RFAP.Winding.point cell.box.xLower y)
      ⟨le_rfl, cell.box.x_valid, lower, upper⟩

def rightClearance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    RFAP.BoxClearance.VerticalLineClearance curve.polynomial cell.box
      cell.box.xUpper where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro y lower upper
    exact cell.denominator_apart (RFAP.Winding.point cell.box.xUpper y)
      ⟨cell.box.x_valid, le_rfl, lower, upper⟩

/-- Counterclockwise bottom edge of the automatically clear box boundary. -/
def bottomSegment {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.BranchCuts.ClearSegment curve.polynomial cell.box
      (lowerLeft cell.box) (lowerRight cell.box) := by
  unfold lowerLeft lowerRight
  exact .horizontal cell.box.xLower cell.box.xUpper cell.box.yLower
    le_rfl cell.box.x_valid cell.box.x_valid le_rfl cell.bottomClearance

def rightSegment {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.BranchCuts.ClearSegment curve.polynomial cell.box
      (lowerRight cell.box) (upperRight cell.box) := by
  unfold lowerRight upperRight
  exact .vertical cell.box.xUpper cell.box.yLower cell.box.yUpper
    le_rfl cell.box.y_valid cell.box.y_valid le_rfl cell.rightClearance

def topSegment {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.BranchCuts.ClearSegment curve.polynomial cell.box
      (upperRight cell.box) (upperLeft cell.box) := by
  unfold upperRight upperLeft
  exact .horizontal cell.box.xUpper cell.box.xLower cell.box.yUpper
    cell.box.x_valid le_rfl le_rfl cell.box.x_valid cell.topClearance

def leftSegment {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.BranchCuts.ClearSegment curve.polynomial cell.box
      (upperLeft cell.box) (lowerLeft cell.box) := by
  unfold upperLeft lowerLeft
  exact .vertical cell.box.xLower cell.box.yUpper cell.box.yLower
    cell.box.y_valid le_rfl le_rfl cell.box.y_valid cell.leftClearance

theorem bottomSegment_within {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    cell.bottomSegment.WithinAmbient :=
  ⟨le_rfl, cell.box.y_valid⟩

theorem rightSegment_within {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    cell.rightSegment.WithinAmbient :=
  ⟨cell.box.x_valid, le_rfl⟩

theorem topSegment_within {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    cell.topSegment.WithinAmbient :=
  ⟨cell.box.y_valid, le_rfl⟩

theorem leftSegment_within {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    cell.leftSegment.WithinAmbient :=
  ⟨le_rfl, cell.box.x_valid⟩

/-- Counterclockwise four-edge boundary path of the checked surface box. -/
def boundaryPath {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    CCL.Riemann.BranchCuts.ClearPath curve.polynomial cell.box
      (lowerLeft cell.box) (lowerLeft cell.box) :=
  .cons cell.bottomSegment
    (.cons cell.rightSegment
      (.cons cell.topSegment
        (.cons cell.leftSegment (.nil (lowerLeft cell.box)))))

theorem boundaryPath_within {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) :
    cell.boundaryPath.WithinAmbient :=
  .cons cell.bottomSegment_within
    (.cons cell.rightSegment_within
      (.cons cell.topSegment_within
        (.cons cell.leftSegment_within (.nil (lowerLeft cell.box)))))

/-- Either explicitly indexed square-root owner at the lower-left corner can
seed continuation around the entire clear box boundary. -/
def boundaryOwner {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (curve.polynomial.eval (lowerLeft cell.box)) :=
  CCL.Riemann.SquareRootContinuationChain.Owner.independent
    cell.bottomSegment.start_eval_ne_zero sheet

/-- Total prepared square-root continuation and integration geometry around
the checked box.  The sufficient dyadic depths are computed internally for
the requested positive root diameter. -/
def preparedBoundary {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    CCL.Riemann.PreparedClearPathModels.PreparedPath cell.boundaryPath
      (cell.boundaryOwner sheet) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.total cell.boundaryPath
    cell.boundaryPath_within (cell.boundaryOwner sheet) rootDiameter
      rootDiameterPositive

/-- The prepared boundary immediately supplies the certified finite
integration model for any standard algebraic differential. -/
def certifiedBoundary {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (differential : CCL.Riemann.AlgebraicDifferentials.Differential genus) :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.Certified curve
      differential sheet
      (cell.preparedBoundary sheet rootDiameter rootDiameterPositive) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.certify curve differential
    sheet
    (cell.preparedBoundary sheet rootDiameter rootDiameterPositive)

end SurfaceCell

/-- The conjugate/value primitive pair whose oriented determinant is the
second-bilinear energy density. -/
def energyPrimitivePoint (value : Gaussian) : PrimitivePoint :=
  ⟨RFAP.ConstructiveGaussian.Gaussian.conj value, value⟩

/-- Exact doubled oriented boundary of all displayed symplectic handles for
one differential combination. -/
def energyBoundaryArea {size : Nat}
    (aPeriods bPeriods : GaussianVector size) : Gaussian :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
    CCL.Riemann.FinitePolygonStokes.commutatorBoundaryArea
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
      (energyPrimitivePoint (aPeriods cycle))
      (energyPrimitivePoint (bPeriods cycle))

/-- The imaginary boundary area is four times the rational energy convention
used by `FiniteEnergy`: two from the commutator polygon and two from the
antisymmetric pairing normalization. -/
theorem periodPairingEnergy_eq_boundaryArea_im_div_four {size : Nat}
    (aPeriods bPeriods : GaussianVector size) :
    CCL.Riemann.FiniteEnergy.periodPairingEnergy aPeriods bPeriods =
      (energyBoundaryArea aPeriods bPeriods).im / 4 := by
  unfold energyBoundaryArea
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun cycle => 2 *
      (bPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
          (aPeriods cycle) -
        aPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
          (bPeriods cycle)))
    (fun cycle => by
      rw [CCL.Riemann.FinitePolygonStokes.commutatorBoundaryArea_eq]
      unfold energyPrimitivePoint
      dsimp only
      ring1)]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_im,
    show (2 : Gaussian).re = (2 : Coordinate) by decide,
    show (2 : Gaussian).im = (0 : Coordinate) by decide,
    RFAP.ConstructiveFraction.zero_mul_direct, _root_.add_zero]
  change CCL.Riemann.FiniteEnergy.periodPairingEnergy aPeriods bPeriods =
    (2 * (RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
      bPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
          (aPeriods cycle) -
        aPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
          (bPeriods cycle)).im) / 4
  rw [CCL.Riemann.FiniteEnergy.sumFin_im]
  unfold CCL.Riemann.FiniteEnergy.periodPairingEnergy
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [show (2 : Coordinate)⁻¹ = 2 * (4 : Coordinate)⁻¹ by decide]
  ring1

/-- Ordinary local energy of one oriented primitive triangle.  The finite
polygon algebra uses doubled wedge areas, hence division by four. -/
def triangleEnergy {vertexCount : Nat}
    (primitive : Fin vertexCount -> PrimitivePoint)
    (triangle :
      CCL.Riemann.FinitePolygonStokes.OrientedTriangle vertexCount) :
    Coordinate :=
  (CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
    (primitive triangle.first) (primitive triangle.second)
      (primitive triangle.third)).im / 4

/-- Local energy written directly on three primitive points. -/
def primitiveTriangleEnergy
    (first second third : PrimitivePoint) : Coordinate :=
  (CCL.Riemann.FinitePolygonStokes.triangleWedgeArea first second third).im / 4

/-- Conjugate/value primitive of the affine local differential model
`coefficient * dz`.  Translation of the primitive is immaterial to every
triangle determinant, so the canonical primitive is based at zero. -/
def affineEnergyPrimitive (coefficient point : Gaussian) : PrimitivePoint :=
  energyPrimitivePoint (coefficient * point)

/-- Signed ordinary coordinate area of an oriented rational triangle. -/
def coordinateTriangleArea
    (first second third : Gaussian) : Coordinate :=
  ((second.re - first.re) * (third.im - first.im) -
    (second.im - first.im) * (third.re - first.re)) / 2

/-- Exact local second-bilinear identity for an affine differential model.
The conjugate/value primitive has Jacobian `normSq coefficient`, so its
oriented triangle energy is coordinate area times that squared norm. -/
theorem affinePrimitiveTriangleEnergy_eq
    (coefficient first second third : Gaussian) :
    primitiveTriangleEnergy
        (affineEnergyPrimitive coefficient first)
        (affineEnergyPrimitive coefficient second)
        (affineEnergyPrimitive coefficient third) =
      coordinateTriangleArea first second third *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
  have wedgeImaginary :
      (CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
        (affineEnergyPrimitive coefficient first)
        (affineEnergyPrimitive coefficient second)
        (affineEnergyPrimitive coefficient third)).im =
      2 *
        ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
    unfold affineEnergyPrimitive energyPrimitivePoint
      CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      RFAP.ConstructiveGaussian.Gaussian.conj
      RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im]
    ring1
  unfold primitiveTriangleEnergy
  rw [wedgeImaginary]
  unfold coordinateTriangleArea
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    (2 *
          ((second.re - first.re) * (third.im - first.im) -
            (second.im - first.im) * (third.re - first.re)) *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient) * 4⁻¹ =
        ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient *
            (2 * 4⁻¹) := by ring1
    _ = ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient * 2⁻¹ := by
      rw [show (2 : Coordinate) * 4⁻¹ = 2⁻¹ by decide]
    _ = (((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) * 2⁻¹) *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by ring1

/-- Oriented energy of two complex primitive increments. -/
def crossEnergy (first second : Gaussian) : Coordinate :=
  (RFAP.ConstructiveGaussian.Gaussian.conj first * second).im / 2

/-- A conjugate/value primitive triangle depends only on its two increments
from the first vertex. -/
theorem primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy
    (first second third : Gaussian) :
    primitiveTriangleEnergy (energyPrimitivePoint first)
        (energyPrimitivePoint second) (energyPrimitivePoint third) =
      crossEnergy (second - first) (third - first) := by
  unfold primitiveTriangleEnergy energyPrimitivePoint crossEnergy
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
    RFAP.ConstructiveGaussian.Gaussian.conj
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [show (2 : Coordinate)⁻¹ = 2 * (4 : Coordinate)⁻¹ by decide]
  ring1

/-- Bilinearity exposes the three finite error terms when both primitive
increments are perturbed. -/
theorem crossEnergy_add_add (first second firstError secondError : Gaussian) :
    crossEnergy (first + firstError) (second + secondError) =
      crossEnergy first second + crossEnergy firstError second +
        crossEnergy first secondError + crossEnergy firstError secondError := by
  unfold crossEnergy RFAP.ConstructiveGaussian.Gaussian.conj
  simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

/-- Square-root-free Cauchy bound for one oriented cross-energy term. -/
theorem crossEnergy_sq_le (first second : Gaussian) :
    crossEnergy first second ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq first *
        RFAP.ConstructiveGaussian.Gaussian.normSq second / 4 := by
  let product := RFAP.ConstructiveGaussian.Gaussian.conj first * second
  have imaginarySquare : product.im ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq product := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct product.re)
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    imaginarySquare (show (0 : Coordinate) <= (4 : Coordinate)⁻¹ by decide)
  dsimp only [product] at scaled
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_conj] at scaled
  unfold crossEnergy
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  have halfSquare : (2 : Coordinate)⁻¹ ^ 2 = (4 : Coordinate)⁻¹ := by decide
  calc
    ((RFAP.ConstructiveGaussian.Gaussian.conj first * second).im * 2⁻¹) ^ 2 =
        (RFAP.ConstructiveGaussian.Gaussian.conj first * second).im ^ 2 *
          4⁻¹ := by
      rw [← halfSquare]
      ring1
    _ <= RFAP.ConstructiveGaussian.Gaussian.normSq first *
          RFAP.ConstructiveGaussian.Gaussian.normSq second * 4⁻¹ := scaled

/-- A nonnegative rational square budget bounds a cross-energy term from
below without taking a square root. -/
theorem neg_budget_le_crossEnergy (first second : Gaussian)
    (budget : Coordinate) (budgetNonnegative : 0 <= budget)
    (productBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq first *
          RFAP.ConstructiveGaussian.Gaussian.normSq second / 4 <=
        budget ^ 2) :
    -budget <= crossEnergy first second :=
  RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct budgetNonnegative
    ((crossEnergy_sq_le first second).trans productBound)

/-- Three explicit square budgets control the loss of oriented energy under
simultaneous perturbation of both primitive increments.  This is the finite
stability estimate needed to pay prepared-integration errors locally. -/
theorem crossEnergy_sub_budget_le_add_add
    (first second firstError secondError : Gaussian)
    (firstBudget secondBudget mixedBudget : Coordinate)
    (firstBudgetNonnegative : 0 <= firstBudget)
    (secondBudgetNonnegative : 0 <= secondBudget)
    (mixedBudgetNonnegative : 0 <= mixedBudget)
    (firstProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq firstError *
          RFAP.ConstructiveGaussian.Gaussian.normSq second / 4 <=
        firstBudget ^ 2)
    (secondProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq first *
          RFAP.ConstructiveGaussian.Gaussian.normSq secondError / 4 <=
        secondBudget ^ 2)
    (mixedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq firstError *
          RFAP.ConstructiveGaussian.Gaussian.normSq secondError / 4 <=
        mixedBudget ^ 2) :
    crossEnergy first second -
        (firstBudget + secondBudget + mixedBudget) <=
      crossEnergy (first + firstError) (second + secondError) := by
  rw [crossEnergy_add_add]
  have firstLower := neg_budget_le_crossEnergy firstError second firstBudget
    firstBudgetNonnegative firstProductBound
  have secondLower := neg_budget_le_crossEnergy first secondError secondBudget
    secondBudgetNonnegative secondProductBound
  have mixedLower := neg_budget_le_crossEnergy firstError secondError
    mixedBudget mixedBudgetNonnegative mixedProductBound
  calc
    crossEnergy first second -
          (firstBudget + secondBudget + mixedBudget) =
        crossEnergy first second + -firstBudget + -secondBudget +
          -mixedBudget := by ring1
    _ <= crossEnergy first second + crossEnergy firstError second +
          crossEnergy first secondError + crossEnergy firstError secondError :=
      add_le_add
        (add_le_add (add_le_add le_rfl firstLower) secondLower) mixedLower

/-- Primitive increment predicted by one affine coefficient between two
rational coordinate vertices. -/
def affinePrimitiveIncrement
    (coefficient start finish : Gaussian) : Gaussian :=
  coefficient * finish - coefficient * start

/-- Error of one displayed primitive increment against its affine model. -/
def affinePrimitiveIncrementError
    (coefficient coordinateStart coordinateFinish
      primitiveStart primitiveFinish : Gaussian) : Gaussian :=
  (primitiveFinish - primitiveStart) -
    affinePrimitiveIncrement coefficient coordinateStart coordinateFinish

/-- The displayed increment is exactly its affine reference plus the
explicit rational error. -/
theorem affinePrimitiveIncrement_add_error
    (coefficient coordinateStart coordinateFinish
      primitiveStart primitiveFinish : Gaussian) :
    affinePrimitiveIncrement coefficient coordinateStart coordinateFinish +
        affinePrimitiveIncrementError coefficient coordinateStart
          coordinateFinish primitiveStart primitiveFinish =
      primitiveFinish - primitiveStart := by
  unfold affinePrimitiveIncrementError affinePrimitiveIncrement
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;> ring1

/-- Error-controlled local affine energy theorem.  Three rational square
checks compare an arbitrary displayed primitive triangle with the exact
affine triangle on the same coordinate vertices. -/
theorem affineTriangleEnergy_sub_budget_le
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian)
    (firstBudget secondBudget mixedBudget : Coordinate)
    (firstBudgetNonnegative : 0 <= firstBudget)
    (secondBudgetNonnegative : 0 <= secondBudget)
    (mixedBudgetNonnegative : 0 <= mixedBudget)
    (firstProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateSecond primitiveFirst primitiveSecond) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrement coefficient coordinateFirst
              coordinateThird) / 4 <= firstBudget ^ 2)
    (secondProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrement coefficient coordinateFirst
              coordinateSecond) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateThird primitiveFirst primitiveThird) / 4 <=
        secondBudget ^ 2)
    (mixedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateSecond primitiveFirst primitiveSecond) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateThird primitiveFirst primitiveThird) / 4 <=
        mixedBudget ^ 2) :
    coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
        (firstBudget + secondBudget + mixedBudget) <=
      primitiveTriangleEnergy
        (energyPrimitivePoint primitiveFirst)
        (energyPrimitivePoint primitiveSecond)
        (energyPrimitivePoint primitiveThird) := by
  let first := affinePrimitiveIncrement coefficient coordinateFirst
    coordinateSecond
  let second := affinePrimitiveIncrement coefficient coordinateFirst
    coordinateThird
  let firstError := affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateSecond primitiveFirst primitiveSecond
  let secondError := affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateThird primitiveFirst primitiveThird
  have referenceEnergy :
      crossEnergy first second =
        coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
    calc
      crossEnergy first second =
          primitiveTriangleEnergy
            (energyPrimitivePoint (coefficient * coordinateFirst))
            (energyPrimitivePoint (coefficient * coordinateSecond))
            (energyPrimitivePoint (coefficient * coordinateThird)) := by
        rw [primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy]
        rfl
      _ = coordinateTriangleArea coordinateFirst coordinateSecond
            coordinateThird *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient :=
        affinePrimitiveTriangleEnergy_eq coefficient coordinateFirst
          coordinateSecond coordinateThird
  have stable := crossEnergy_sub_budget_le_add_add first second firstError
    secondError firstBudget secondBudget mixedBudget firstBudgetNonnegative
    secondBudgetNonnegative mixedBudgetNonnegative firstProductBound
    secondProductBound mixedProductBound
  calc
    coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
            RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
          (firstBudget + secondBudget + mixedBudget) =
        crossEnergy first second -
          (firstBudget + secondBudget + mixedBudget) := by rw [referenceEnergy]
    _ <= crossEnergy (first + firstError) (second + secondError) := stable
    _ = crossEnergy (primitiveSecond - primitiveFirst)
          (primitiveThird - primitiveFirst) := by
      rw [affinePrimitiveIncrement_add_error coefficient coordinateFirst
          coordinateSecond primitiveFirst primitiveSecond,
        affinePrimitiveIncrement_add_error coefficient coordinateFirst
          coordinateThird primitiveFirst primitiveThird]
    _ = primitiveTriangleEnergy
          (energyPrimitivePoint primitiveFirst)
          (energyPrimitivePoint primitiveSecond)
          (energyPrimitivePoint primitiveThird) :=
      (primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy
        primitiveFirst primitiveSecond primitiveThird).symm

/-- Reusable finite sidecar for one approximate affine primitive triangle.
All fields are decidable rational inequalities on displayed Gaussian values. -/
structure AffineTriangleErrorCertificate
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian) where
  firstBudget : Coordinate
  secondBudget : Coordinate
  mixedBudget : Coordinate
  firstBudget_nonnegative : 0 <= firstBudget
  secondBudget_nonnegative : 0 <= secondBudget
  mixedBudget_nonnegative : 0 <= mixedBudget
  firstProductBound :
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateSecond primitiveFirst primitiveSecond) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrement coefficient coordinateFirst
            coordinateThird) / 4 <= firstBudget ^ 2
  secondProductBound :
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrement coefficient coordinateFirst
            coordinateSecond) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateThird primitiveFirst primitiveThird) / 4 <=
      secondBudget ^ 2
  mixedProductBound :
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateSecond primitiveFirst primitiveSecond) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateThird primitiveFirst primitiveThird) / 4 <=
      mixedBudget ^ 2

namespace AffineTriangleErrorCertificate

/-- Complete displayed loss budget for one approximate affine face. -/
def totalBudget
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian}
    (certificate : AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) : Coordinate :=
  certificate.firstBudget + certificate.secondBudget + certificate.mixedBudget

theorem totalBudget_nonnegative
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian}
    (certificate : AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) :
    0 <= certificate.totalBudget :=
  add_nonneg
    (add_nonneg certificate.firstBudget_nonnegative
      certificate.secondBudget_nonnegative)
    certificate.mixedBudget_nonnegative

/-- The packaged rational checks give the reusable lower comparison. -/
theorem affineEnergy_sub_totalBudget_le
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Gaussian}
    (certificate : AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) :
    coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
        certificate.totalBudget <=
      primitiveTriangleEnergy
        (energyPrimitivePoint primitiveFirst)
        (energyPrimitivePoint primitiveSecond)
        (energyPrimitivePoint primitiveThird) :=
  affineTriangleEnergy_sub_budget_le coefficient coordinateFirst
    coordinateSecond coordinateThird primitiveFirst primitiveSecond
    primitiveThird certificate.firstBudget certificate.secondBudget
    certificate.mixedBudget certificate.firstBudget_nonnegative
    certificate.secondBudget_nonnegative certificate.mixedBudget_nonnegative
    certificate.firstProductBound certificate.secondProductBound
    certificate.mixedProductBound

end AffineTriangleErrorCertificate

/-! ## Extracting affine errors from prepared constant path models -/

/-- Exact weighted coefficient-error terms of a cellwise constant path model
relative to one displayed affine reference coefficient. -/
def constantReferenceErrorTerms : forall {cells : List CellModel},
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells ->
      Gaussian -> List Gaussian
  | [], .nil, _reference => []
  | cell :: _, .cons head tail, reference =>
      cell.displacement * (head.coefficient - reference) ::
        constantReferenceErrorTerms tail reference

@[simp] theorem constantReferenceErrorTerms_length :
    forall {cells : List CellModel}
      (constant :
        CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells)
      (reference : Gaussian),
      (constantReferenceErrorTerms constant reference).length = cells.length
  | [], .nil, _ => rfl
  | _ :: _, .cons _ tail, reference => by
      simp only [constantReferenceErrorTerms, List.length_cons,
        constantReferenceErrorTerms_length tail reference]

/-- Exact rational squared-error allowance obtained by finite
Cauchy--Schwarz from all displayed constant-cell coefficient differences. -/
def constantReferenceErrorAllowance {cells : List CellModel}
    (constant :
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells)
    (reference : Gaussian) :
    Coordinate :=
  (cells.length : Coordinate) *
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      (constantReferenceErrorTerms constant reference)

/-- A constant path model is its reference affine integral plus the explicit
finite weighted coefficient-error sum. -/
theorem constantPathIntegralSample_eq_reference_add_error :
    forall {cells : List CellModel}
      (constant :
        CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells)
      (reference : Gaussian),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk cells).integralSample =
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum cells *
          reference +
          RFAP.ConstructiveFiniteNorm.gaussianSum
            (constantReferenceErrorTerms constant reference)
  | [], .nil, reference => by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
        constantReferenceErrorTerms
      change (0 : Gaussian) = 0 * reference + 0
      rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
  | cell :: cells, .cons head tail, reference => by
      rw [CCL.ProgressiveGaussianIntegration.PathModel.integralSample]
      simp only [List.foldr_cons]
      rw [CCL.ProgressiveGaussianIntegration.PathModel.CellModel.integralSample_constant
        cell head.coefficient head.polynomial_eq]
      change cell.displacement * head.coefficient +
        (CCL.ProgressiveGaussianIntegration.PathModel.mk cells).integralSample = _
      rw [constantPathIntegralSample_eq_reference_add_error tail reference]
      simp only [CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons,
        constantReferenceErrorTerms,
        RFAP.ConstructiveFiniteNorm.gaussianSum]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;> ring1

/-- The explicit aggregate allowance bounds the complete affine-reference
error of the displayed path model. -/
theorem constantReferenceErrorSum_le {cells : List CellModel}
    (constant :
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells)
    (reference : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteNorm.gaussianSum
          (constantReferenceErrorTerms constant reference)) <=
      constantReferenceErrorAllowance constant reference := by
  unfold constantReferenceErrorAllowance
  have finiteCauchy :=
    RFAP.ConstructiveFiniteNorm.normSq_gaussianSum_le
      (constantReferenceErrorTerms constant reference)
  rw [constantReferenceErrorTerms_length constant reference] at finiteCauchy
  exact finiteCauchy

/-- When the constant cells follow an actual lifted path, telescoping turns
the reference term into the affine primitive increment between its endpoints. -/
theorem constantFollowedPathIntegralSample_eq_affine_add_error
    {cells : List CellModel} {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    {path : CCL.Riemann.LiftedPaths.LiftedPath 2 start finish}
    (constant :
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells cells)
    (follows : path.FollowedBy cells)
    (reference : Gaussian) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk cells).integralSample =
      affinePrimitiveIncrement reference start.coordinate finish.coordinate +
        RFAP.ConstructiveFiniteNorm.gaussianSum
          (constantReferenceErrorTerms constant reference) := by
  rw [constantPathIntegralSample_eq_reference_add_error constant reference,
    CCL.Riemann.LiftedPaths.LiftedPath.followedBy_displacementSum follows]
  unfold affinePrimitiveIncrement
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;> ring1

namespace SurfaceCell

/-- The automatically certified clear box boundary is cellwise constant, as
inherited from every accepted prepared subdivision. -/
def boundaryConstantCells {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (differential : CCL.Riemann.AlgebraicDifferentials.Differential genus) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (cell.certifiedBoundary sheet rootDiameter rootDiameterPositive
        differential).cells :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.certify_constantCells
    curve differential sheet
      (cell.preparedBoundary sheet rootDiameter rootDiameterPositive)

/-- On the closed prepared box boundary the affine endpoint increment is
zero.  Hence the complete displayed boundary sample is exactly its finite
weighted coefficient-error sum relative to any rational reference. -/
theorem boundaryIntegralSample_eq_referenceError {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (differential : CCL.Riemann.AlgebraicDifferentials.Differential genus)
    (reference : Gaussian) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (cell.certifiedBoundary sheet rootDiameter rootDiameterPositive
        differential).cells).integralSample =
      RFAP.ConstructiveFiniteNorm.gaussianSum
        (constantReferenceErrorTerms
          (cell.boundaryConstantCells sheet rootDiameter rootDiameterPositive
            differential) reference) := by
  let certified := cell.certifiedBoundary sheet rootDiameter
    rootDiameterPositive differential
  let constant := cell.boundaryConstantCells sheet rootDiameter
    rootDiameterPositive differential
  have comparison :=
    constantFollowedPathIntegralSample_eq_affine_add_error constant
      certified.certificates.toFollowedBy reference
  simpa only [certified, constant, affinePrimitiveIncrement,
    RFAP.ConstructiveGaussian.Gaussian.sub_self,
    RFAP.ConstructiveGaussian.Gaussian.zero_add] using comparison

/-- The computed finite reference allowance bounds the complete prepared
closed-boundary residual. -/
theorem boundaryIntegralSample_normSq_le_referenceAllowance {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (differential : CCL.Riemann.AlgebraicDifferentials.Differential genus)
    (reference : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveGaussianIntegration.PathModel.mk
          (cell.certifiedBoundary sheet rootDiameter rootDiameterPositive
            differential).cells).integralSample) <=
      constantReferenceErrorAllowance
        (cell.boundaryConstantCells sheet rootDiameter rootDiameterPositive
          differential) reference := by
  rw [cell.boundaryIntegralSample_eq_referenceError sheet rootDiameter
    rootDiameterPositive differential reference]
  exact constantReferenceErrorSum_le
    (cell.boundaryConstantCells sheet rootDiameter rootDiameterPositive
      differential) reference

end SurfaceCell

/-- First counterclockwise affine triangle of a rational box, along the
diagonal from lower-left to upper-right. -/
def lowerBoxAffineTriangleEnergy (box : RFAP.Boxes.Box)
    (coefficient : Gaussian) : Coordinate :=
  primitiveTriangleEnergy
    (affineEnergyPrimitive coefficient (lowerLeft box))
    (affineEnergyPrimitive coefficient (lowerRight box))
    (affineEnergyPrimitive coefficient (upperRight box))

/-- Second counterclockwise affine triangle of the same diagonal split. -/
def upperBoxAffineTriangleEnergy (box : RFAP.Boxes.Box)
    (coefficient : Gaussian) : Coordinate :=
  primitiveTriangleEnergy
    (affineEnergyPrimitive coefficient (lowerLeft box))
    (affineEnergyPrimitive coefficient (upperRight box))
    (affineEnergyPrimitive coefficient (upperLeft box))

/-- Each half of the affine box has exactly half the box energy. -/
theorem lowerBoxAffineTriangleEnergy_eq (box : RFAP.Boxes.Box)
    (coefficient : Gaussian) :
    lowerBoxAffineTriangleEnergy box coefficient =
      RFAP.FiniteMeasure.boxContent box / 2 *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
  unfold lowerBoxAffineTriangleEnergy
  rw [affinePrimitiveTriangleEnergy_eq]
  unfold coordinateTriangleArea lowerLeft lowerRight upperRight
    RFAP.FiniteMeasure.boxContent RFAP.Boxes.Box.widthX
    RFAP.Boxes.Box.widthY RFAP.Winding.point
  change
    (((box.xUpper - box.xLower) * (box.yUpper - box.yLower) -
        (box.yLower - box.yLower) * (box.xUpper - box.xLower)) / 2) *
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient =
    ((box.xUpper - box.xLower) * (box.yUpper - box.yLower)) / 2 *
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient
  simp only [sub_self, zero_mul, sub_zero]

/-- The upper affine triangle has the same exact positive orientation. -/
theorem upperBoxAffineTriangleEnergy_eq (box : RFAP.Boxes.Box)
    (coefficient : Gaussian) :
    upperBoxAffineTriangleEnergy box coefficient =
      RFAP.FiniteMeasure.boxContent box / 2 *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
  unfold upperBoxAffineTriangleEnergy
  rw [affinePrimitiveTriangleEnergy_eq]
  unfold coordinateTriangleArea lowerLeft upperRight upperLeft
    RFAP.FiniteMeasure.boxContent RFAP.Boxes.Box.widthX
    RFAP.Boxes.Box.widthY RFAP.Winding.point
  change
    (((box.xUpper - box.xLower) * (box.yUpper - box.yLower) -
        (box.yUpper - box.yLower) * (box.xLower - box.xLower)) / 2) *
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient =
    ((box.xUpper - box.xLower) * (box.yUpper - box.yLower)) / 2 *
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient
  simp only [sub_self, mul_zero, sub_zero]

/-- Exact finite Stokes energy of the two-triangle affine box patch. -/
theorem boxAffineTriangleEnergy_add
    (box : RFAP.Boxes.Box) (coefficient : Gaussian) :
    lowerBoxAffineTriangleEnergy box coefficient +
        upperBoxAffineTriangleEnergy box coefficient =
      RFAP.FiniteMeasure.boxContent box *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
  rw [lowerBoxAffineTriangleEnergy_eq, upperBoxAffineTriangleEnergy_eq]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    RFAP.FiniteMeasure.boxContent box * 2⁻¹ *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient +
        RFAP.FiniteMeasure.boxContent box * 2⁻¹ *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient =
      RFAP.FiniteMeasure.boxContent box *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient *
          (2⁻¹ + 2⁻¹) := by ring1
    _ = RFAP.FiniteMeasure.boxContent box *
        RFAP.ConstructiveGaussian.Gaussian.normSq coefficient := by
      rw [show (2 : Coordinate)⁻¹ + 2⁻¹ = 1 by decide]
      ring1

/-- A rational affine coefficient whose squared norm dominates the checked
cell density turns the exact two-triangle box identity into the required
local surface-energy lower bound. -/
theorem SurfaceCell.contribution_le_boxAffineTriangleEnergy
    {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {coefficients : GaussianVector genus}
    (cell : SurfaceCell curve coefficients) (coefficient : Gaussian)
    (densityLower : cell.densityLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient) :
    CCL.Riemann.FiniteEnergy.Cell.contribution cell.toEnergyCell <=
      lowerBoxAffineTriangleEnergy cell.box coefficient +
        upperBoxAffineTriangleEnergy cell.box coefficient := by
  rw [boxAffineTriangleEnergy_add]
  unfold CCL.Riemann.FiniteEnergy.Cell.contribution
    CCL.Riemann.PreparedEnergy.SurfaceCell.toEnergyCell
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    densityLower (RFAP.FiniteMeasure.boxContent_nonneg cell.box)

theorem primitiveTriangleEnergy_zero_left_add
    (left right : PrimitivePoint) :
    primitiveTriangleEnergy
        CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero left
          (left.add right) =
      (left.left * right.right - right.left * left.right).im / 4 := by
  unfold primitiveTriangleEnergy
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
  dsimp only
  apply congrArg (fun value : Gaussian => value.im / 4)
  ring1

theorem primitiveTriangleEnergy_zero_add_right
    (left right : PrimitivePoint) :
    primitiveTriangleEnergy
        CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
          (left.add right) right =
      (left.left * right.right - right.left * left.right).im / 4 := by
  unfold primitiveTriangleEnergy
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
  dsimp only
  apply congrArg (fun value : Gaussian => value.im / 4)
  ring1

/-! ## Canonical genus-one cut polygon -/

private def commutatorEdge01 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨0, 1⟩

private def commutatorEdge12 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨1, 2⟩

private def commutatorEdge20 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨2, 0⟩

private def commutatorEdge02 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨0, 2⟩

private def commutatorEdge23 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨2, 3⟩

private def commutatorEdge30 :
    CCL.Riemann.FinitePolygonStokes.OrientedEdge 4 := ⟨3, 0⟩

/-- The two counterclockwise triangles of the standard commutator square.
The second triangle is written cyclically as `(2,3,0)`, making its outer
edges literal while retaining the same diagonal as `(0,2,3)`. -/
def genusOneCommutatorFaces (face : Fin 2) :
    CCL.Riemann.FinitePolygonStokes.OrientedTriangle 4 :=
  if face = 0 then ⟨0, 1, 2⟩ else ⟨2, 3, 0⟩

@[simp] theorem genusOneCommutatorFaces_zero :
    genusOneCommutatorFaces 0 = ⟨0, 1, 2⟩ := by
  simp only [genusOneCommutatorFaces, if_pos]

@[simp] theorem genusOneCommutatorFaces_one :
    genusOneCommutatorFaces 1 = ⟨2, 3, 0⟩ := by
  simp only [genusOneCommutatorFaces, if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- Exact two-face triangulation of `0,a,a+b,b`.  Its sole internal diagonal
occurs as `(2,0)` and `(0,2)`; the incidence proof explicitly moves that pair
behind the four outer commutator edges. -/
def genusOneCommutatorTriangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation 4 2 where
  faces := genusOneCommutatorFaces
  boundary :=
    [commutatorEdge01, commutatorEdge12, commutatorEdge23, commutatorEdge30]
  internalEdges := [commutatorEdge20]
  incidence := by
    change CCL.Riemann.FinitePolygonStokes.EdgeReordering
      [commutatorEdge01, commutatorEdge12, commutatorEdge20,
        commutatorEdge23, commutatorEdge30, commutatorEdge02]
      [commutatorEdge01, commutatorEdge12, commutatorEdge23,
        commutatorEdge30, commutatorEdge20, commutatorEdge02]
    exact .cons commutatorEdge01 (.cons commutatorEdge12
      (.trans
        (.swap commutatorEdge20 commutatorEdge23
          [commutatorEdge30, commutatorEdge02])
        (.cons commutatorEdge23
          (.swap commutatorEdge20 commutatorEdge30
            [commutatorEdge02]))))

/-- Primitive vertices of the standard cut polygon, in boundary order
`0,a,a+b,b`. -/
def genusOneCommutatorPrimitive (a b : PrimitivePoint) (vertex : Fin 4) :
    PrimitivePoint :=
  if vertex = 0 then CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
  else if vertex = 1 then a
  else if vertex = 2 then a.add b
  else b

@[simp] theorem genusOneCommutatorPrimitive_zero (a b : PrimitivePoint) :
    genusOneCommutatorPrimitive a b 0 =
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero := by
  simp only [genusOneCommutatorPrimitive, if_pos]

@[simp] theorem genusOneCommutatorPrimitive_one (a b : PrimitivePoint) :
    genusOneCommutatorPrimitive a b 1 = a := by
  simp only [genusOneCommutatorPrimitive,
    if_neg (by decide : (1 : Fin 4) ≠ 0), if_pos]

@[simp] theorem genusOneCommutatorPrimitive_two (a b : PrimitivePoint) :
    genusOneCommutatorPrimitive a b 2 = a.add b := by
  simp only [genusOneCommutatorPrimitive,
    if_neg (by decide : (2 : Fin 4) ≠ 0),
    if_neg (by decide : (2 : Fin 4) ≠ 1), if_pos]

@[simp] theorem genusOneCommutatorPrimitive_three (a b : PrimitivePoint) :
    genusOneCommutatorPrimitive a b 3 = b := by
  simp only [genusOneCommutatorPrimitive,
    if_neg (by decide : (3 : Fin 4) ≠ 0),
    if_neg (by decide : (3 : Fin 4) ≠ 1),
    if_neg (by decide : (3 : Fin 4) ≠ 2)]

/-- The explicit triangulation's outer boundary is definitionally the
standard genus-one commutator boundary. -/
theorem genusOneCommutatorTriangulation_boundaryArea
    (a b : PrimitivePoint) :
    CCL.Riemann.FinitePolygonStokes.edgeListArea
        (genusOneCommutatorPrimitive a b)
        genusOneCommutatorTriangulation.boundary =
      CCL.Riemann.FinitePolygonStokes.commutatorBoundaryArea
        CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero a b := by
  unfold genusOneCommutatorTriangulation
    CCL.Riemann.FinitePolygonStokes.commutatorBoundaryArea
    CCL.Riemann.FinitePolygonStokes.commutatorVertices
    commutatorEdge01 commutatorEdge12 commutatorEdge23 commutatorEdge30
  simp only [CCL.Riemann.FinitePolygonStokes.edgeListArea,
    CCL.Riemann.FinitePolygonStokes.polygonBoundaryArea,
    CCL.Riemann.FinitePolygonStokes.pathToAnchorArea,
    genusOneCommutatorPrimitive_zero,
    genusOneCommutatorPrimitive_one, genusOneCommutatorPrimitive_two,
    genusOneCommutatorPrimitive_three]
  unfold CCL.Riemann.FinitePolygonStokes.edgeArea
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
  dsimp only
  ring1

/-- The first face of the explicit commutator mesh is the triangle
`(0,a,a+b)`. -/
@[simp] theorem genusOneCommutatorFirstFaceEnergy
    (a b : PrimitivePoint) :
    triangleEnergy (genusOneCommutatorPrimitive a b)
        (genusOneCommutatorTriangulation.faces 0) =
      primitiveTriangleEnergy
        CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero a (a.add b) := by
  unfold genusOneCommutatorTriangulation
  change triangleEnergy (genusOneCommutatorPrimitive a b)
    (genusOneCommutatorFaces 0) = _
  rw [genusOneCommutatorFaces_zero]
  unfold triangleEnergy primitiveTriangleEnergy
  rw [genusOneCommutatorPrimitive_zero,
    genusOneCommutatorPrimitive_one, genusOneCommutatorPrimitive_two]

/-- The cyclically written second face has the same energy as the triangle
`(0,a+b,b)`. -/
@[simp] theorem genusOneCommutatorSecondFaceEnergy
    (a b : PrimitivePoint) :
    triangleEnergy (genusOneCommutatorPrimitive a b)
        (genusOneCommutatorTriangulation.faces 1) =
      primitiveTriangleEnergy
        CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero (a.add b) b := by
  unfold genusOneCommutatorTriangulation
  change triangleEnergy (genusOneCommutatorPrimitive a b)
    (genusOneCommutatorFaces 1) = _
  rw [genusOneCommutatorFaces_one]
  unfold triangleEnergy primitiveTriangleEnergy
  rw [genusOneCommutatorPrimitive_two,
    genusOneCommutatorPrimitive_three, genusOneCommutatorPrimitive_zero]
  apply congrArg (fun value : Gaussian => value.im / 4)
  unfold CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
  dsimp only
  ring1

/-- First triangle of the canonical genus-one commutator polygon
`0, a, a+b, b`, using the conjugate/value energy primitive. -/
def genusOneUnitFirstTriangleEnergy
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) : Coordinate :=
  let a := energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0)
  let b := energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)
  primitiveTriangleEnergy
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero a (a.add b)

/-- Second triangle of the same canonical handle subdivision. -/
def genusOneUnitSecondTriangleEnergy
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) : Coordinate :=
  let a := energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0)
  let b := energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)
  primitiveTriangleEnergy
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero (a.add b) b

/-- The diagonal subdivision splits the handle energy into two equal oriented
triangles. -/
theorem genusOneUnitFirstTriangleEnergy_eq_second
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex =
      genusOneUnitSecondTriangleEnergy data sampleIndex := by
  unfold genusOneUnitFirstTriangleEnergy genusOneUnitSecondTriangleEnergy
  rw [primitiveTriangleEnergy_zero_left_add,
    primitiveTriangleEnergy_zero_add_right]

/-- The two canonical triangle energies add to the displayed unit
second-bilinear period pairing. -/
theorem genusOneUnitTriangleEnergy_add_eq_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex +
        genusOneUnitSecondTriangleEnergy data sampleIndex =
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  unfold genusOneUnitFirstTriangleEnergy genusOneUnitSecondTriangleEnergy
  rw [primitiveTriangleEnergy_zero_left_add,
    primitiveTriangleEnergy_zero_add_right]
  unfold energyPrimitivePoint CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
  rw [CCL.Riemann.FiniteEnergy.periodPairingEnergy_one_eq]
  simp only [CCL.Riemann.FiniteEnergy.periodCombination_genusOne_unit,
    RFAP.ConstructiveGaussian.Gaussian.conj,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [show (2 : Coordinate)⁻¹ = 2 * (4 : Coordinate)⁻¹ by decide]
  ring1

/-! ## Direct refinement-program readings

The public period matrices are names generated from finite refinement
programs.  Sampling such a name does not manufacture a new analytic value:
it asks the originating program for one explicitly indexed later model.  The
two matrix entries may reach different internal indices, so the direct
interface below records both indices independently. -/

/-- Internal refinement-program index selected by the canonical sampler of a
name generated from `program`. -/
def resampledRefinementIndex
    (program : CCL.ProgressiveGaussianIntegration.RefinementProgram)
    (sampleIndex : Nat) : Nat :=
  CCL.ProgressiveSampling.stateAt program.approximation.toProcess
    (show program.approximation.toProcess.State from (0 : Nat)) sampleIndex

/-- Every later external sampler request advances (or retains) the direct
refinement-program index selected by the first request. -/
theorem resampledRefinementIndex_zero_le
    (program : CCL.ProgressiveGaussianIntegration.RefinementProgram) :
    forall sampleIndex : Nat,
      resampledRefinementIndex program 0 <=
        resampledRefinementIndex program sampleIndex
  | 0 => Nat.le_refl _
  | sampleIndex + 1 => by
      have previous := resampledRefinementIndex_zero_le program sampleIndex
      apply previous.trans
      unfold resampledRefinementIndex
      rw [CCL.ProgressiveSampling.stateAt_succ]
      simpa only [CCL.ProgressiveApproximation.Approximation.toProcess] using
        program.approximation.refineIndex_ge _ _
          (CCL.ProgressiveSampling.refinementTarget_pos (sampleIndex + 1))

/-- The direct A-program reading at one explicitly displayed internal
refinement index. -/
def genusOneDirectASample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) : Gaussian :=
  ((data.aProgram 0 0).integral.model index).integralSample

/-- The direct B-program reading at one explicitly displayed internal
refinement index. -/
def genusOneDirectBSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) : Gaussian :=
  ((data.bProgram 0 0).integral.model index).integralSample

/-- Antisymmetric genus-one pairing of two independently refined direct
program readings. -/
def genusOneDirectPairing
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (aIndex bIndex : Nat) : Gaussian :=
  let a := genusOneDirectASample data aIndex
  let b := genusOneDirectBSample data bIndex
  a.conj * b - b.conj * a

/-- A synchronized named A-period sample is definitionally a direct reading
of its originating finite refinement program. -/
theorem sampledAEntry_eq_direct
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    sampledMatrix data.aMatrix sampleIndex 0 0 =
      genusOneDirectASample data
        (resampledRefinementIndex
          (data.aProgram 0 0).integral sampleIndex) := by
  rw [sampledMatrix_apply, PeriodData.aMatrix_apply]
  rfl

/-- The analogous direct-reading identity for the B-period. -/
theorem sampledBEntry_eq_direct
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    sampledMatrix data.bMatrix sampleIndex 0 0 =
      genusOneDirectBSample data
        (resampledRefinementIndex
          (data.bProgram 0 0).integral sampleIndex) := by
  rw [sampledMatrix_apply, PeriodData.bMatrix_apply]
  rfl

/-- Synchronized finite approximation to the antisymmetric genus-one period
pairing `conj(A) B - conj(B) A`.  The construction retains the same sampler
index in all four factors and binds each period sample once, so its geometric
tail estimate applies directly to the canonical commutator face without
re-running either finite period program inside the pointwise product. -/
def genusOnePairingApproximation
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) :
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation :=
  let a := CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
    (data.aMatrix 0 0).name
  let b := CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
    (data.bMatrix 0 0).name
  let base := CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sub
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.conj a) b)
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.conj b) a)
  { sample := fun sampleIndex =>
      let aSample := a.sample sampleIndex
      let bSample := b.sample sampleIndex
      aSample.conj * bSample - bSample.conj * aSample
    errorScale := base.errorScale
    errorScale_nonneg := base.errorScale_nonneg
    later_close := by
      intro earlier later order
      change RFAP.ConstructiveGaussian.Gaussian.normSq
          (base.sample later - base.sample earlier) <=
        CCL.FiniteGeometric.quarterRadius base.errorScale earlier
      exact base.later_close order
    centerBound := base.centerBound
    centerBound_nonneg := base.centerBound_nonneg
    sample_bounded := by
      intro sampleIndex
      change RFAP.ConstructiveGaussian.Gaussian.normSq
          (base.sample sampleIndex) <= base.centerBound
      exact base.sample_bounded sampleIndex }

@[simp] theorem genusOnePairingApproximation_sample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    (genusOnePairingApproximation data).sample sampleIndex =
      RFAP.ConstructiveGaussian.Gaussian.conj
          (sampledMatrix data.aMatrix sampleIndex 0 0) *
        sampledMatrix data.bMatrix sampleIndex 0 0 -
      RFAP.ConstructiveGaussian.Gaussian.conj
          (sampledMatrix data.bMatrix sampleIndex 0 0) *
        sampledMatrix data.aMatrix sampleIndex 0 0 := by
  simp only [genusOnePairingApproximation,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed_sample,
    sampledMatrix_apply]

/-- The first commutator triangle is exactly one quarter of the imaginary
antisymmetric period pairing at the same finite sample index. -/
theorem genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex =
      ((genusOnePairingApproximation data).sample sampleIndex).im / 4 := by
  unfold genusOneUnitFirstTriangleEnergy
  rw [primitiveTriangleEnergy_zero_left_add]
  rw [genusOnePairingApproximation_sample]
  rfl

/-- A direct-program form of the canonical genus-one face bound.  It is
deliberately asynchronous: the productive A and B names can answer one
external request using different internal refinement indices.  Proving the
bound for every displayed pair of direct readings therefore suffices for the
actual synchronized named matrix. -/
structure DirectGenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  lower : forall aIndex bIndex : Nat,
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      (genusOneDirectPairing data aIndex bIndex).im / 4

/-- Tail-only direct-program form of the canonical face theorem.  The first
external sample has already advanced each originating refinement program to
its independently computed initial accuracy index; only direct readings at or
beyond those two finite indices can occur in the named period matrix. -/
structure DirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  lower : forall aIndex bIndex : Nat,
    resampledRefinementIndex (data.aProgram 0 0).integral 0 <= aIndex ->
    resampledRefinementIndex (data.bProgram 0 0).integral 0 <= bIndex ->
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      (genusOneDirectPairing data aIndex bIndex).im / 4

/-- Minimal local genus-one face theorem.  The reference box energy is split
equally across the two canonical commutator triangles, so only one local
triangle inequality is independent. -/
structure GenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  lower : forall sampleIndex : Nat,
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      genusOneUnitFirstTriangleEnergy data sampleIndex

namespace DirectGenusOneCanonicalFaceLowerCertificate

/-- Transport a direct-program lower theorem through the exact finite sampler
indices selected independently for the A and B names. -/
theorem toCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : DirectGenusOneCanonicalFaceLowerCertificate data) :
    GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    rw [genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four,
      genusOnePairingApproximation_sample,
      sampledAEntry_eq_direct, sampledBEntry_eq_direct]
    exact certificate.lower
      (resampledRefinementIndex
        (data.aProgram 0 0).integral sampleIndex)
      (resampledRefinementIndex
        (data.bProgram 0 0).integral sampleIndex)

end DirectGenusOneCanonicalFaceLowerCertificate

namespace DirectTailGenusOneCanonicalFaceLowerCertificate

/-- Transport a tail theorem for the two direct refinement programs through
the monotonically advancing internal indices selected by named sampling. -/
theorem toCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : DirectTailGenusOneCanonicalFaceLowerCertificate data) :
    GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    rw [genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four,
      genusOnePairingApproximation_sample,
      sampledAEntry_eq_direct, sampledBEntry_eq_direct]
    exact certificate.lower
      (resampledRefinementIndex
        (data.aProgram 0 0).integral sampleIndex)
      (resampledRefinementIndex
        (data.bProgram 0 0).integral sampleIndex)
      (resampledRefinementIndex_zero_le
        (data.aProgram 0 0).integral sampleIndex)
      (resampledRefinementIndex_zero_le
        (data.bProgram 0 0).integral sampleIndex)

end DirectTailGenusOneCanonicalFaceLowerCertificate

/-- A uniform squared-movement allowance for the independently advancing
direct A/B readings after the first public sample.  Each period program is
compared with its own initial internal index, so no artificial synchronization
of the two executable refiners is required. -/
def genusOneDirectTailMovementBound
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  let aAnchor := resampledRefinementIndex aProgram 0
  let bAnchor := resampledRefinementIndex bProgram 0
  8 *
    (CCL.FiniteGeometric.quarterRadius aProgram.errorScale aAnchor *
        bProgram.centerBound +
      aProgram.centerBound *
        CCL.FiniteGeometric.quarterRadius bProgram.errorScale bAnchor)

/-- Independent later A/B readings move their antisymmetric pairing by at
most the displayed finite rectangle-tail allowance.  The factor eight pays
first for the two product differences and then for antisymmetrization. -/
theorem genusOneDirectPairing_sub_anchor_normSq_le
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (aIndex bIndex : Nat)
    (aOrder :
      resampledRefinementIndex (data.aProgram 0 0).integral 0 <= aIndex)
    (bOrder :
      resampledRefinementIndex (data.bProgram 0 0).integral 0 <= bIndex) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data
            (resampledRefinementIndex (data.aProgram 0 0).integral 0)
            (resampledRefinementIndex (data.bProgram 0 0).integral 0)) <=
      genusOneDirectTailMovementBound data := by
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  let aAnchor := resampledRefinementIndex aProgram 0
  let bAnchor := resampledRefinementIndex bProgram 0
  let a := genusOneDirectASample data aIndex
  let b := genusOneDirectBSample data bIndex
  let aBase := genusOneDirectASample data aAnchor
  let bBase := genusOneDirectBSample data bAnchor
  let productDifference := a.conj * b - aBase.conj * bBase
  have aMovement :
      RFAP.ConstructiveGaussian.Gaussian.normSq (a - aBase) <=
        CCL.FiniteGeometric.quarterRadius aProgram.errorScale aAnchor := by
    exact aProgram.later_close aOrder
  have bMovement :
      RFAP.ConstructiveGaussian.Gaussian.normSq (b - bBase) <=
        CCL.FiniteGeometric.quarterRadius bProgram.errorScale bAnchor := by
    exact bProgram.later_close bOrder
  have aBaseBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq aBase <=
        aProgram.centerBound :=
    aProgram.sample_bounded aAnchor
  have bBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq b <=
        bProgram.centerBound :=
    bProgram.sample_bounded bIndex
  have productIdentity :
      productDifference =
        (a - aBase).conj * b + aBase.conj * (b - bBase) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [productDifference,
        RFAP.ConstructiveGaussian.Gaussian.conj,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;> ring1
  have firstProduct :
      RFAP.ConstructiveGaussian.Gaussian.normSq ((a - aBase).conj * b) <=
        CCL.FiniteGeometric.quarterRadius aProgram.errorScale aAnchor *
          bProgram.centerBound := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_conj]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct aMovement bBound
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
      (CCL.FiniteGeometric.quarterRadius_nonneg
        aProgram.errorScale_nonneg aAnchor)
  have secondProduct :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (aBase.conj * (b - bBase)) <=
        aProgram.centerBound *
          CCL.FiniteGeometric.quarterRadius bProgram.errorScale bAnchor := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_conj]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct aBaseBound bMovement
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
      aProgram.centerBound_nonneg
  have productBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq productDifference <=
        2 *
          (CCL.FiniteGeometric.quarterRadius aProgram.errorScale aAnchor *
              bProgram.centerBound +
            aProgram.centerBound *
              CCL.FiniteGeometric.quarterRadius bProgram.errorScale
                bAnchor) := by
    rw [productIdentity]
    exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstProduct secondProduct) (by decide))
  have pairingIdentity :
      genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data aAnchor bAnchor =
        productDifference - productDifference.conj := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [genusOneDirectPairing, a, b, aBase, bBase,
        productDifference,
        RFAP.ConstructiveGaussian.Gaussian.conj,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;> ring1
  rw [pairingIdentity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (productDifference - productDifference.conj) <=
      2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq productDifference +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            productDifference.conj) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
    _ = 4 * RFAP.ConstructiveGaussian.Gaussian.normSq productDifference := by
      rw [RFAP.ConstructiveGaussian.Gaussian.normSq_conj]
      ring1
    _ <= 4 *
        (2 *
          (CCL.FiniteGeometric.quarterRadius aProgram.errorScale aAnchor *
              bProgram.centerBound +
            aProgram.centerBound *
              CCL.FiniteGeometric.quarterRadius bProgram.errorScale
                bAnchor)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ = genusOneDirectTailMovementBound data := by
      unfold genusOneDirectTailMovementBound aProgram bProgram aAnchor bAnchor
      ring1

/-- Finite asynchronous tail certificate for the canonical genus-one face.
One exact positive margin at the pair of first internal readings controls all
later independently refined A/B readings when the rectangle-tail movement is
smaller than the squared margin. -/
structure FiniteDirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  tailMarginPositive :
    0 <
      (genusOneDirectPairing data
        (resampledRefinementIndex (data.aProgram 0 0).integral 0)
        (resampledRefinementIndex (data.bProgram 0 0).integral 0)).im -
          4 * (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2)
  tailMovementSmall :
    genusOneDirectTailMovementBound data <
      ((genusOneDirectPairing data
        (resampledRefinementIndex (data.aProgram 0 0).integral 0)
        (resampledRefinementIndex (data.bProgram 0 0).integral 0)).im -
          4 * (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2)) ^ 2

namespace FiniteDirectTailGenusOneCanonicalFaceLowerCertificate

/-- Promote one finite asynchronous anchor calculation to the universal
direct-tail face inequality. -/
theorem toDirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      FiniteDirectTailGenusOneCanonicalFaceLowerCertificate data) :
    DirectTailGenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro aIndex bIndex aOrder bOrder
    let target := CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2
    let aAnchor :=
      resampledRefinementIndex (data.aProgram 0 0).integral 0
    let bAnchor :=
      resampledRefinementIndex (data.bProgram 0 0).integral 0
    let anchorValue := (genusOneDirectPairing data aAnchor bAnchor).im
    let sampleValue := (genusOneDirectPairing data aIndex bIndex).im
    let margin := anchorValue - 4 * target
    have marginPositive : 0 < margin := certificate.tailMarginPositive
    apply (RFAP.ConstructiveFraction.le_div_iff_pos
      (by decide : (0 : Coordinate) < 4)).2
    change target * 4 <= sampleValue
    by_cases enough : 4 * target <= sampleValue
    · simpa only [mul_comm target] using enough
    · have sampleBelow : sampleValue < 4 * target :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct enough
      have marginBelowDifference :
          margin < anchorValue - sampleValue :=
        RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          sampleBelow anchorValue
      have differencePositive : 0 < anchorValue - sampleValue :=
        marginPositive.trans marginBelowDifference
      have firstProduct :
          margin * margin < margin * (anchorValue - sampleValue) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          marginPositive marginBelowDifference
      have secondProduct :
          margin * (anchorValue - sampleValue) <
            (anchorValue - sampleValue) * (anchorValue - sampleValue) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          marginBelowDifference differencePositive
      have squareStrict :
          margin ^ 2 < (anchorValue - sampleValue) ^ 2 := by
        simpa only [pow_two] using firstProduct.trans secondProduct
      have imaginarySquareLe :
          (anchorValue - sampleValue) ^ 2 <=
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (genusOneDirectPairing data aIndex bIndex -
                genusOneDirectPairing data aAnchor bAnchor) := by
        change (anchorValue - sampleValue) ^ 2 <=
          ((genusOneDirectPairing data aIndex bIndex).re -
              (genusOneDirectPairing data aAnchor bAnchor).re) ^ 2 +
            (sampleValue - anchorValue) ^ 2
        have reflected :
            (anchorValue - sampleValue) ^ 2 =
              (sampleValue - anchorValue) ^ 2 := by ring1
        rw [reflected]
        exact le_add_of_nonneg_left
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      have movement := genusOneDirectPairing_sub_anchor_normSq_le
        data aIndex bIndex aOrder bOrder
      have forbidden : margin ^ 2 < genusOneDirectTailMovementBound data :=
        squareStrict.trans_le (imaginarySquareLe.trans movement)
      have cycle := certificate.tailMovementSmall.trans forbidden
      exact (lt_irrefl _ cycle).elim

/-- Direct route from the finite asynchronous anchor to the canonical face
certificate consumed by the finite Riemann period theorem. -/
theorem toCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      FiniteDirectTailGenusOneCanonicalFaceLowerCertificate data) :
    GenusOneCanonicalFaceLowerCertificate data :=
  certificate.toDirectTailGenusOneCanonicalFaceLowerCertificate.toCanonicalFaceLowerCertificate

end FiniteDirectTailGenusOneCanonicalFaceLowerCertificate

/-- Finite form of the canonical genus-one face lower theorem.  Only the
samples before `anchor` are checked separately.  One positive imaginary
margin at the anchor, together with a squared geometric tail bound smaller
than that margin, controls every later sample. -/
structure FiniteGenusOneCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  anchor : Nat
  prefix_lower : forall sampleIndex, sampleIndex < anchor ->
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      genusOneUnitFirstTriangleEnergy data sampleIndex
  tailMarginPositive :
    0 < ((genusOnePairingApproximation data).sample anchor).im -
      4 * (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2)
  tailMovementSmall :
    CCL.FiniteGeometric.quarterRadius
        (genusOnePairingApproximation data).errorScale anchor <
      (((genusOnePairingApproximation data).sample anchor).im -
        4 * (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2)) ^ 2

namespace FiniteGenusOneCanonicalFaceLowerCertificate

/-- Promote the bounded prefix and one tail check to the universal canonical
face lower theorem.  The proof compares imaginary-coordinate motion with the
full Gaussian squared-motion bound; it uses no limit or completeness
principle. -/
theorem toCanonicalFaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : FiniteGenusOneCanonicalFaceLowerCertificate data) :
    GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    by_cases before : sampleIndex < certificate.anchor
    · exact certificate.prefix_lower sampleIndex before
    · have order : certificate.anchor <= sampleIndex := Nat.le_of_not_gt before
      let approximation := genusOnePairingApproximation data
      let target := CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2
      let anchorValue := (approximation.sample certificate.anchor).im
      let sampleValue := (approximation.sample sampleIndex).im
      let margin := anchorValue - 4 * target
      have marginPositive : 0 < margin := certificate.tailMarginPositive
      have movement := approximation.later_close order
      have targetOriented :
          genusOneUnitFirstTriangleEnergy data sampleIndex =
            sampleValue / 4 := by
        exact genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four
          data sampleIndex
      rw [targetOriented]
      apply (RFAP.ConstructiveFraction.le_div_iff_pos
        (by decide : (0 : Coordinate) < 4)).2
      change target * 4 <= sampleValue
      by_cases enough : 4 * target <= sampleValue
      · simpa only [mul_comm target] using enough
      · have sampleBelow : sampleValue < 4 * target :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct enough
        have marginBelowDifference :
            margin < anchorValue - sampleValue :=
          RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            sampleBelow anchorValue
        have differencePositive : 0 < anchorValue - sampleValue :=
          marginPositive.trans marginBelowDifference
        have firstProduct :
            margin * margin < margin * (anchorValue - sampleValue) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            marginPositive marginBelowDifference
        have secondProduct :
            margin * (anchorValue - sampleValue) <
              (anchorValue - sampleValue) * (anchorValue - sampleValue) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
            marginBelowDifference differencePositive
        have squareStrict :
            margin ^ 2 < (anchorValue - sampleValue) ^ 2 := by
          simpa only [pow_two] using firstProduct.trans secondProduct
        have imaginarySquareLe :
            (anchorValue - sampleValue) ^ 2 <=
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (approximation.sample sampleIndex -
                  approximation.sample certificate.anchor) := by
          change (anchorValue - sampleValue) ^ 2 <=
            ((approximation.sample sampleIndex).re -
                (approximation.sample certificate.anchor).re) ^ 2 +
              (sampleValue - anchorValue) ^ 2
          have reflected :
              (anchorValue - sampleValue) ^ 2 =
                (sampleValue - anchorValue) ^ 2 := by ring1
          rw [reflected]
          exact le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        have forbidden : margin ^ 2 <
            CCL.FiniteGeometric.quarterRadius approximation.errorScale
              certificate.anchor :=
          squareStrict.trans_le (imaginarySquareLe.trans movement)
        have cycle := certificate.tailMovementSmall.trans forbidden
        exact (lt_irrefl _ cycle).elim

end FiniteGenusOneCanonicalFaceLowerCertificate

namespace GenusOneCanonicalFaceLowerCertificate

/-- The duplicated local face inequality and exact diagonal subdivision
derive the complete unit surface lower theorem. -/
theorem toUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    have secondLower :
        CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
          genusOneUnitSecondTriangleEnergy data sampleIndex := by
      rw [← genusOneUnitFirstTriangleEnergy_eq_second data sampleIndex]
      exact certificate.lower sampleIndex
    calc
      CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve =
          CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 +
            CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        calc
          CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve =
              CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve *
                ((2 : Coordinate)⁻¹ + (2 : Coordinate)⁻¹) := by
            rw [show (2 : Coordinate)⁻¹ + (2 : Coordinate)⁻¹ = 1 by decide]
            ring1
          _ = CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve * 2⁻¹ +
              CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve * 2⁻¹ := by
            ring1
      _ <= genusOneUnitFirstTriangleEnergy data sampleIndex +
          genusOneUnitSecondTriangleEnergy data sampleIndex :=
        add_le_add (certificate.lower sampleIndex) secondLower
      _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) :=
        genusOneUnitTriangleEnergy_add_eq_raw data sampleIndex

end GenusOneCanonicalFaceLowerCertificate

/-- One completely finite cut-surface energy sample.  Faces and surface cells
share an index, so every checked local lower contribution is assigned to an
actual oriented triangle. -/
structure TriangulatedRawEnergySample {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> SurfaceCell curve coefficients) where
  vertexCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount cellCount
  primitive : Fin vertexCount -> PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  face_energy_lower : forall face : Fin cellCount,
    CCL.Riemann.FiniteEnergy.Cell.contribution
        ((cells face).toEnergyCell) <=
      triangleEnergy primitive (triangulation.faces face)

namespace TriangulatedRawEnergySample

/-- Exact incidence cancellation identifies the sum of local triangle
energies with the displayed raw A/B pairing. -/
theorem triangleEnergySum_eq_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : TriangulatedRawEnergySample data coefficients sampleIndex cells) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  let aPeriods := CCL.Riemann.FiniteEnergy.periodCombination coefficients
    (sampledMatrix data.aMatrix sampleIndex)
  let bPeriods := CCL.Riemann.FiniteEnergy.periodCombination coefficients
    (sampledMatrix data.bMatrix sampleIndex)
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face)) =
        (CCL.Riemann.FinitePolygonStokes.triangleWedgeSum sample.primitive
          sample.triangulation.faces).im / 4 := by
      unfold triangleEnergy CCL.Riemann.FinitePolygonStokes.triangleWedgeSum
      rw [CCL.Riemann.FiniteEnergy.sumFin_im]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_right
        (fun face =>
          (CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
            (sample.primitive (sample.triangulation.faces face).first)
            (sample.primitive (sample.triangulation.faces face).second)
            (sample.primitive
              (sample.triangulation.faces face).third)).im)
        ((4 : Coordinate)⁻¹)
    _ = (CCL.Riemann.FinitePolygonStokes.edgeListArea sample.primitive
          sample.triangulation.boundary).im / 4 := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = (energyBoundaryArea aPeriods bPeriods).im / 4 := by
      rw [sample.boundary_matches]
    _ = CCL.Riemann.FiniteEnergy.periodPairingEnergy aPeriods bPeriods :=
      (periodPairingEnergy_eq_boundaryArea_im_div_four aPeriods bPeriods).symm
    _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := rfl

/-- The global surface lower inequality is a theorem of the local face
inequalities and exact finite Stokes incidence. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : TriangulatedRawEnergySample data coefficients sampleIndex cells) :
    CCL.Riemann.PreparedEnergy.surfaceEnergy cells <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  unfold CCL.Riemann.PreparedEnergy.surfaceEnergy
    CCL.Riemann.FiniteEnergy.cellEnergy
    CCL.Riemann.PreparedEnergy.energyCells
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        CCL.Riemann.FiniteEnergy.Cell.contribution
          ((cells face).toEnergyCell)) <=
        RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
          triangleEnergy sample.primitive
            (sample.triangulation.faces face)) := by
      apply CCL.Riemann.FinitePositivity.sumFin_mono
      exact sample.face_energy_lower
    _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) :=
      sample.triangleEnergySum_eq_raw

/-- Materialize the legacy exact decomposition only after the triangulated
surface calculation has proved its global inequality. -/
def toRawBoundaryReduction {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : TriangulatedRawEnergySample data coefficients sampleIndex cells) :
    CCL.Riemann.PreparedEnergy.RawBoundaryReduction data coefficients
      sampleIndex cells := by
  let raw := CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
    (sampledMatrix data.aMatrix sampleIndex)
    (sampledMatrix data.bMatrix sampleIndex)
  let localEnergy := CCL.Riemann.PreparedEnergy.surfaceEnergy cells
  exact
    { edgePairCount := 0
      edgePairValues := fun edge => Fin.elim0 edge
      remainder := raw - localEnergy
      remainder_nonnegative :=
        RFAP.ConstructiveFraction.sub_nonneg_direct sample.surfaceEnergy_le_raw
      raw_eq_decomposition := by
        rw [CCL.Riemann.PreparedEnergy.pairedBoundarySum_zero]
        unfold raw localEnergy
        ring1 }

end TriangulatedRawEnergySample

/-- A stronger local-analytic presentation of a triangulated raw-energy
sample.  Each face carries an affine coefficient and rational coordinate
triangle.  Its three global primitive values are checked against that one
affine primitive, while the triangle's coordinate area and coefficient norm
dominate the assigned surface cell.  The face-energy inequality is therefore
derived from the exact affine Jacobian theorem above. -/
structure AffineTriangulatedRawEnergySample {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> SurfaceCell curve coefficients) where
  vertexCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount cellCount
  coordinate : Fin vertexCount -> Gaussian
  primitive : Fin vertexCount -> PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  faceCoefficient : Fin cellCount -> Gaussian
  primitive_first : forall face : Fin cellCount,
    primitive (triangulation.faces face).first =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).first)
  primitive_second : forall face : Fin cellCount,
    primitive (triangulation.faces face).second =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).second)
  primitive_third : forall face : Fin cellCount,
    primitive (triangulation.faces face).third =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).third)
  cell_area_le_triangle : forall face : Fin cellCount,
    RFAP.FiniteMeasure.boxContent (cells face).box <=
      coordinateTriangleArea
        (coordinate (triangulation.faces face).first)
        (coordinate (triangulation.faces face).second)
        (coordinate (triangulation.faces face).third)
  cell_density_le_coefficient : forall face : Fin cellCount,
    (cells face).densityLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (faceCoefficient face)

namespace AffineTriangulatedRawEnergySample

/-- Exact affine local algebra derives, rather than assumes, the energy lower
bound on every oriented face. -/
theorem face_energy_lower {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : AffineTriangulatedRawEnergySample data coefficients sampleIndex
      cells)
    (face : Fin cellCount) :
    CCL.Riemann.FiniteEnergy.Cell.contribution
        ((cells face).toEnergyCell) <=
      triangleEnergy sample.primitive (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient face
  have areaNonnegative :
      0 <= coordinateTriangleArea first second third :=
    (RFAP.FiniteMeasure.boxContent_nonneg (cells face).box).trans
      (sample.cell_area_le_triangle face)
  calc
    CCL.Riemann.FiniteEnergy.Cell.contribution
        ((cells face).toEnergyCell) =
        RFAP.FiniteMeasure.boxContent (cells face).box *
          (cells face).densityLower := rfl
    _ <= coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (sample.cell_area_le_triangle face)
        (sample.cell_density_le_coefficient face)
        (cells face).densityLower_nonnegative areaNonnegative
    _ = primitiveTriangleEnergy
          (affineEnergyPrimitive coefficient first)
          (affineEnergyPrimitive coefficient second)
          (affineEnergyPrimitive coefficient third) :=
      (affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = triangleEnergy sample.primitive
          (sample.triangulation.faces face) := by
      unfold triangleEnergy primitiveTriangleEnergy
      rw [sample.primitive_first face, sample.primitive_second face,
        sample.primitive_third face]

/-- Forget the affine sidecar only after constructing every local face lower
inequality from coordinate area and coefficient norm. -/
def toTriangulatedRawEnergySample {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : AffineTriangulatedRawEnergySample data coefficients sampleIndex
      cells) :
    TriangulatedRawEnergySample data coefficients sampleIndex cells where
  vertexCount := sample.vertexCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  face_energy_lower := sample.face_energy_lower

/-- Consequently the affine local model plus exact triangulation incidence
proves the complete raw surface lower theorem. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : AffineTriangulatedRawEnergySample data coefficients sampleIndex
      cells) :
    CCL.Riemann.PreparedEnergy.surfaceEnergy cells <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toTriangulatedRawEnergySample.surfaceEnergy_le_raw

end AffineTriangulatedRawEnergySample

/-- Error-controlled affine triangulation.  Global primitive vertices are
arbitrary displayed Gaussian values.  Each face compares them with one local
affine coefficient through an `AffineTriangleErrorCertificate`; a checked
margin pays that error before the exact incidence theorem is applied. -/
structure ErrorControlledAffineTriangulatedRawEnergySample
    {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> SurfaceCell curve coefficients) where
  vertexCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount cellCount
  coordinate : Fin vertexCount -> Gaussian
  primitiveValue : Fin vertexCount -> Gaussian
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea
        (fun vertex => energyPrimitivePoint (primitiveValue vertex))
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  faceCoefficient : Fin cellCount -> Gaussian
  faceError : forall face : Fin cellCount,
    AffineTriangleErrorCertificate (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third)
  cell_energy_add_error_le_affine : forall face : Fin cellCount,
    CCL.Riemann.FiniteEnergy.Cell.contribution ((cells face).toEnergyCell) +
        (faceError face).totalBudget <=
      coordinateTriangleArea
          (coordinate (triangulation.faces face).first)
          (coordinate (triangulation.faces face).second)
          (coordinate (triangulation.faces face).third) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (faceCoefficient face)

namespace ErrorControlledAffineTriangulatedRawEnergySample

/-- Paying the explicit affine comparison budget derives the local face lower
required by the exact triangulation layer. -/
theorem face_energy_lower {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells)
    (face : Fin cellCount) :
    CCL.Riemann.FiniteEnergy.Cell.contribution
        ((cells face).toEnergyCell) <=
      triangleEnergy
        (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
        (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let coefficient := sample.faceCoefficient face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let primitiveFirst := sample.primitiveValue triangle.first
  let primitiveSecond := sample.primitiveValue triangle.second
  let primitiveThird := sample.primitiveValue triangle.third
  let error := sample.faceError face
  let contribution := CCL.Riemann.FiniteEnergy.Cell.contribution
    ((cells face).toEnergyCell)
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    (sample.cell_energy_add_error_le_affine face) (-error.totalBudget)
  calc
    CCL.Riemann.FiniteEnergy.Cell.contribution
        ((cells face).toEnergyCell) =
        (contribution + error.totalBudget) + -error.totalBudget := by
      unfold contribution
      ring1
    _ <= coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient +
            -error.totalBudget := shifted
    _ = coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
            error.totalBudget := by ring1
    _ <= primitiveTriangleEnergy
          (energyPrimitivePoint primitiveFirst)
          (energyPrimitivePoint primitiveSecond)
          (energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = triangleEnergy
          (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces face) := rfl

/-- Forget error and affine sidecars only after deriving every local lower. -/
def toTriangulatedRawEnergySample {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells) :
    TriangulatedRawEnergySample data coefficients sampleIndex cells where
  vertexCount := sample.vertexCount
  triangulation := sample.triangulation
  primitive := fun vertex => energyPrimitivePoint (sample.primitiveValue vertex)
  boundary_matches := sample.boundary_matches
  face_energy_lower := sample.face_energy_lower

/-- Local quadrature budgets, exact incidence, and boundary matching prove
the complete raw surface inequality. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> SurfaceCell curve coefficients}
    (sample : ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells) :
    CCL.Riemann.PreparedEnergy.surfaceEnergy cells <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toTriangulatedRawEnergySample.surfaceEnergy_le_raw

end ErrorControlledAffineTriangulatedRawEnergySample

/-- Genus-generic raw surface theorem assembled from locally error-controlled
affine primitive triangles. -/
structure ErrorControlledAffineTriangulatedRawEnergyCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  sample : forall (coefficients : GaussianVector genus) (sampleIndex : Nat)
    (cell : SurfaceCell curve coefficients),
    ErrorControlledAffineTriangulatedRawEnergySample data coefficients
      sampleIndex (fun _ : Fin 1 => cell)

namespace ErrorControlledAffineTriangulatedRawEnergyCertificate

theorem toRawSurfaceLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate :
      ErrorControlledAffineTriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

def toRawCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate :
      ErrorControlledAffineTriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end ErrorControlledAffineTriangulatedRawEnergyCertificate

/-- Genus-generic raw surface theorem whose local analytic input is given by
affine coordinate triangles, not by preassembled face-energy inequalities. -/
structure AffineTriangulatedRawEnergyCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  sample : forall (coefficients : GaussianVector genus) (sampleIndex : Nat)
    (cell : SurfaceCell curve coefficients),
    AffineTriangulatedRawEnergySample data coefficients sampleIndex
      (fun _ : Fin 1 => cell)

namespace AffineTriangulatedRawEnergyCertificate

/-- The affine Jacobian calculation and finite incidence construct the
minimal inverse-independent surface lower certificate. -/
theorem toRawSurfaceLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : AffineTriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

def toRawCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : AffineTriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end AffineTriangulatedRawEnergyCertificate

/-- Genus-generic triangulated replacement for the global raw surface-lower
field.  The only analytic hypotheses are local face inequalities. -/
structure TriangulatedRawEnergyCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  sample : forall (coefficients : GaussianVector genus) (sampleIndex : Nat)
    (cell : SurfaceCell curve coefficients),
    TriangulatedRawEnergySample data coefficients sampleIndex
      (fun _ : Fin 1 => cell)

namespace TriangulatedRawEnergyCertificate

theorem toRawSurfaceLowerCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : TriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

def toRawCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : TriangulatedRawEnergyCertificate data) :
    CCL.Riemann.PreparedEnergy.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end TriangulatedRawEnergyCertificate

/-- One genus-one unit-differential triangulation with its positive lower
energy distributed across an arbitrary finite bank of faces.  Unlike the
selected-face interface below, this records the genuinely local situation in
which several triangles jointly carry the reference-box energy. -/
structure GenusOneUnitDistributedTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  primitive : Fin vertexCount -> PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  faceLower : Fin faceCount -> Coordinate
  unit_energy_le_faceLowerSum :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      RFAP.ConstructiveFiniteMatrix.sumFin faceLower
  face_energy_lower : forall face : Fin faceCount,
    faceLower face <= triangleEnergy primitive (triangulation.faces face)

namespace GenusOneUnitDistributedTriangulatedSurfaceSample

/-- Exact cancellation of internal oriented edges identifies the sum of all
face energies with the displayed unit-differential period pairing. -/
theorem triangleEnergySum_eq_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  let coefficients := CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
  let aPeriods := CCL.Riemann.FiniteEnergy.periodCombination coefficients
    (sampledMatrix data.aMatrix sampleIndex)
  let bPeriods := CCL.Riemann.FiniteEnergy.periodCombination coefficients
    (sampledMatrix data.bMatrix sampleIndex)
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face)) =
        (CCL.Riemann.FinitePolygonStokes.triangleWedgeSum sample.primitive
          sample.triangulation.faces).im / 4 := by
      unfold triangleEnergy CCL.Riemann.FinitePolygonStokes.triangleWedgeSum
      rw [CCL.Riemann.FiniteEnergy.sumFin_im]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_right
        (fun face =>
          (CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
            (sample.primitive (sample.triangulation.faces face).first)
            (sample.primitive (sample.triangulation.faces face).second)
            (sample.primitive
              (sample.triangulation.faces face).third)).im)
        ((4 : Coordinate)⁻¹)
    _ = (CCL.Riemann.FinitePolygonStokes.edgeListArea sample.primitive
          sample.triangulation.boundary).im / 4 := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = (energyBoundaryArea aPeriods bPeriods).im / 4 := by
      rw [sample.boundary_matches]
    _ = CCL.Riemann.FiniteEnergy.periodPairingEnergy aPeriods bPeriods :=
      (periodPairingEnergy_eq_boundaryArea_im_div_four aPeriods bPeriods).symm
    _ = CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := rfl

/-- Pointwise local lower bounds sum to the complete unit surface inequality;
no one triangle is required to dominate the entire reference energy. -/
theorem unitEnergy_le_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.unit_energy_le_faceLowerSum.trans
    ((CCL.Riemann.FinitePositivity.sumFin_mono sample.faceLower
      (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face))
      sample.face_energy_lower).trans_eq sample.triangleEnergySum_eq_raw)

end GenusOneUnitDistributedTriangulatedSurfaceSample

namespace GenusOneCanonicalFaceLowerCertificate

/-- The explicit commutator boundary is the unit coefficient combination of
the two sampled genus-one period entries. -/
theorem commutatorBoundary_matches
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    CCL.Riemann.FinitePolygonStokes.edgeListArea
        (genusOneCommutatorPrimitive
          (energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
          (energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
        genusOneCommutatorTriangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex)) := by
  rw [genusOneCommutatorTriangulation_boundaryArea]
  unfold energyBoundaryArea
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
    CCL.Riemann.FiniteEnergy.periodCombination_genusOne_unit,
    CCL.Riemann.FiniteEnergy.periodCombination_genusOne_unit]
  change _ = _ + 0
  rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]

/-- Two identical half-energy lower entries sum to the full reference energy. -/
theorem unitEnergy_le_halfFaceLowerSum
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1} :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      RFAP.ConstructiveFiniteMatrix.sumFin (fun _ : Fin 2 =>
        CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2) := by
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
    RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 +
      (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 + 0)
  rw [_root_.add_zero]
  apply le_of_eq
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve =
        CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve *
          ((2 : Coordinate)⁻¹ + (2 : Coordinate)⁻¹) := by
      rw [show (2 : Coordinate)⁻¹ + (2 : Coordinate)⁻¹ = 1 by decide]
      ring1
    _ = CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve * 2⁻¹ +
        CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve * 2⁻¹ := by
      ring1

/-- The one independent canonical face bound supplies both oriented faces of
the explicit commutator triangulation. -/
theorem halfFaceLower_le_triangleEnergy
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) (face : Fin 2) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      triangleEnergy
        (genusOneCommutatorPrimitive
          (energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
          (energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
        (genusOneCommutatorTriangulation.faces face) := by
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) face
  · rw [genusOneCommutatorFirstFaceEnergy]
    exact certificate.lower sampleIndex
  · change CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
      triangleEnergy
        (genusOneCommutatorPrimitive
          (energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
          (energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
        (genusOneCommutatorTriangulation.faces (1 : Fin 2))
    rw [genusOneCommutatorSecondFaceEnergy]
    have secondLower :
        CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2 <=
          genusOneUnitSecondTriangleEnergy data sampleIndex := by
      rw [← genusOneUnitFirstTriangleEnergy_eq_second data sampleIndex]
      exact certificate.lower sampleIndex
    exact secondLower

/-- Realize the canonical half-face certificate on the explicit two-triangle
commutator mesh.  Each face receives exactly half of the checked reference
energy, so the distributed lower sum is the full unit energy. -/
def toDistributedTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) :
    GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex where
    vertexCount := 4
    faceCount := 2
    triangulation := genusOneCommutatorTriangulation
    primitive := genusOneCommutatorPrimitive
      (energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
      (energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0))
    boundary_matches := commutatorBoundary_matches data sampleIndex
    faceLower := fun _ =>
      CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve / 2
    unit_energy_le_faceLowerSum := unitEnergy_le_halfFaceLowerSum
    face_energy_lower :=
      certificate.halfFaceLower_le_triangleEnergy sampleIndex

/-- The canonical two-face mesh derives the same unit surface theorem through
actual finite incidence, rather than bypassing the triangulation algebra. -/
theorem unitEnergy_le_raw_via_commutatorTriangulation
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  GenusOneUnitDistributedTriangulatedSurfaceSample.unitEnergy_le_raw
    (certificate.toDistributedTriangulatedSurfaceSample sampleIndex)

end GenusOneCanonicalFaceLowerCertificate

/-- One genus-one unit-differential triangulation.  Its number of triangles
is independent of the single reference box: one selected face dominates that
box's positive lower energy, while every other oriented face is nonnegative. -/
structure GenusOneUnitTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  primitive : Fin vertexCount -> PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  face_energy_nonnegative : forall face : Fin faceCount,
    0 <= triangleEnergy primitive (triangulation.faces face)
  positiveFace : Fin faceCount
  unit_energy_le_face : CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
    triangleEnergy primitive (triangulation.faces positiveFace)

namespace GenusOneUnitTriangulatedSurfaceSample

/-- View the selected-face presentation as a distributed lower certificate:
the selected face receives the full reference lower and every other face
receives zero. -/
def toDistributedTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  faceLower := fun face =>
    if face = sample.positiveFace then
      CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve
    else 0
  unit_energy_le_faceLowerSum := by
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq]
  face_energy_lower := by
    intro face
    by_cases equal : face = sample.positiveFace
    · rw [if_pos equal, equal]
      exact sample.unit_energy_le_face
    · rw [if_neg equal]
      exact sample.face_energy_nonnegative face

/-- Exact incidence cancellation identifies the whole oriented triangle bank
with the unit-differential raw period energy. -/
theorem triangleEnergySum_eq_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  GenusOneUnitDistributedTriangulatedSurfaceSample.triangleEnergySum_eq_raw
    sample.toDistributedTriangulatedSurfaceSample

/-- One locally positive face and nonnegativity of the remaining finite face
bank derive the unit surface lower theorem at this sample. -/
theorem unitEnergy_le_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  GenusOneUnitDistributedTriangulatedSurfaceSample.unitEnergy_le_raw
    sample.toDistributedTriangulatedSurfaceSample

end GenusOneUnitTriangulatedSurfaceSample

/-- Affine local presentation of one genus-one unit surface.  Every face is
an explicitly oriented rational coordinate triangle carrying one rational
constant differential model.  Nonnegativity and the selected positive-face
lower bound are transported to primitive energy by the exact affine
Jacobian theorem. -/
structure GenusOneUnitAffineTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  coordinate : Fin vertexCount -> Gaussian
  primitive : Fin vertexCount -> PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  faceCoefficient : Fin faceCount -> Gaussian
  primitive_first : forall face : Fin faceCount,
    primitive (triangulation.faces face).first =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).first)
  primitive_second : forall face : Fin faceCount,
    primitive (triangulation.faces face).second =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).second)
  primitive_third : forall face : Fin faceCount,
    primitive (triangulation.faces face).third =
      affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).third)
  face_area_nonnegative : forall face : Fin faceCount,
    0 <= coordinateTriangleArea
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
  positiveFace : Fin faceCount
  unit_energy_le_affine_face :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      coordinateTriangleArea
          (coordinate (triangulation.faces positiveFace).first)
          (coordinate (triangulation.faces positiveFace).second)
          (coordinate (triangulation.faces positiveFace).third) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (faceCoefficient positiveFace)

namespace GenusOneUnitAffineTriangulatedSurfaceSample

/-- Affine coordinate orientation proves nonnegativity of the actual
conjugate/value primitive triangle. -/
theorem face_energy_nonnegative
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex)
    (face : Fin sample.faceCount) :
    0 <= triangleEnergy sample.primitive
      (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient face
  calc
    0 <= coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (sample.face_area_nonnegative face)
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg coefficient)
    _ = primitiveTriangleEnergy
          (affineEnergyPrimitive coefficient first)
          (affineEnergyPrimitive coefficient second)
          (affineEnergyPrimitive coefficient third) :=
      (affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = triangleEnergy sample.primitive
          (sample.triangulation.faces face) := by
      unfold triangleEnergy primitiveTriangleEnergy
      rw [sample.primitive_first face, sample.primitive_second face,
        sample.primitive_third face]

/-- The selected affine face lower is exactly the selected primitive face
lower required by the triangulated unit-surface theorem. -/
theorem unit_energy_le_face
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      triangleEnergy sample.primitive
        (sample.triangulation.faces sample.positiveFace) := by
  let triangle := sample.triangulation.faces sample.positiveFace
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient sample.positiveFace
  calc
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
        coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient :=
      sample.unit_energy_le_affine_face
    _ = primitiveTriangleEnergy
          (affineEnergyPrimitive coefficient first)
          (affineEnergyPrimitive coefficient second)
          (affineEnergyPrimitive coefficient third) :=
      (affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = triangleEnergy sample.primitive
          (sample.triangulation.faces sample.positiveFace) := by
      unfold triangleEnergy primitiveTriangleEnergy
      rw [sample.primitive_first sample.positiveFace,
        sample.primitive_second sample.positiveFace,
        sample.primitive_third sample.positiveFace]

/-- Forget affine coordinate data only after it has generated all local
energy inequalities. -/
def toUnitTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex) :
    GenusOneUnitTriangulatedSurfaceSample data sampleIndex where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  face_energy_nonnegative := sample.face_energy_nonnegative
  positiveFace := sample.positiveFace
  unit_energy_le_face := sample.unit_energy_le_face

/-- Exact incidence now yields the unit raw-energy lower at this sample. -/
theorem unitEnergy_le_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toUnitTriangulatedSurfaceSample.unitEnergy_le_raw

end GenusOneUnitAffineTriangulatedSurfaceSample

/-- Error-controlled affine presentation of one genus-one unit surface.
Primitive vertices may differ from their local affine models; each face pays
the resulting three-term square budget. -/
structure GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  coordinate : Fin vertexCount -> Gaussian
  primitiveValue : Fin vertexCount -> Gaussian
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea
        (fun vertex => energyPrimitivePoint (primitiveValue vertex))
        triangulation.boundary =
      energyBoundaryArea
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (CCL.Riemann.FiniteEnergy.periodCombination
          CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  faceCoefficient : Fin faceCount -> Gaussian
  faceError : forall face : Fin faceCount,
    AffineTriangleErrorCertificate (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third)
  face_error_le_affine : forall face : Fin faceCount,
    (faceError face).totalBudget <=
      coordinateTriangleArea
          (coordinate (triangulation.faces face).first)
          (coordinate (triangulation.faces face).second)
          (coordinate (triangulation.faces face).third) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (faceCoefficient face)
  positiveFace : Fin faceCount
  unit_energy_add_error_le_affine :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve +
        (faceError positiveFace).totalBudget <=
      coordinateTriangleArea
          (coordinate (triangulation.faces positiveFace).first)
          (coordinate (triangulation.faces positiveFace).second)
          (coordinate (triangulation.faces positiveFace).third) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (faceCoefficient positiveFace)

namespace GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample

/-- Paying a face's local comparison budget proves its actual primitive
energy nonnegative. -/
theorem face_energy_nonnegative
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex)
    (face : Fin sample.faceCount) :
    0 <= triangleEnergy
      (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
      (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let coefficient := sample.faceCoefficient face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let primitiveFirst := sample.primitiveValue triangle.first
  let primitiveSecond := sample.primitiveValue triangle.second
  let primitiveThird := sample.primitiveValue triangle.third
  let error := sample.faceError face
  calc
    0 <= coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
            error.totalBudget :=
      RFAP.ConstructiveFraction.sub_nonneg_direct
        (sample.face_error_le_affine face)
    _ <= primitiveTriangleEnergy
          (energyPrimitivePoint primitiveFirst)
          (energyPrimitivePoint primitiveSecond)
          (energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = triangleEnergy
          (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces face) := rfl

/-- The selected face retains the fixed positive unit-cell contribution after
its local primitive error has been paid. -/
theorem unit_energy_le_face
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      triangleEnergy
        (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
        (sample.triangulation.faces sample.positiveFace) := by
  let triangle := sample.triangulation.faces sample.positiveFace
  let coefficient := sample.faceCoefficient sample.positiveFace
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let primitiveFirst := sample.primitiveValue triangle.first
  let primitiveSecond := sample.primitiveValue triangle.second
  let primitiveThird := sample.primitiveValue triangle.third
  let error := sample.faceError sample.positiveFace
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    sample.unit_energy_add_error_le_affine (-error.totalBudget)
  calc
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve =
        (CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve +
          error.totalBudget) + -error.totalBudget := by ring1
    _ <= coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient +
            -error.totalBudget := shifted
    _ = coordinateTriangleArea first second third *
          RFAP.ConstructiveGaussian.Gaussian.normSq coefficient -
            error.totalBudget := by ring1
    _ <= primitiveTriangleEnergy
          (energyPrimitivePoint primitiveFirst)
          (energyPrimitivePoint primitiveSecond)
          (energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = triangleEnergy
          (fun vertex => energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces sample.positiveFace) := rfl

def toUnitTriangulatedSurfaceSample
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    GenusOneUnitTriangulatedSurfaceSample data sampleIndex where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := fun vertex => energyPrimitivePoint (sample.primitiveValue vertex)
  boundary_matches := sample.boundary_matches
  face_energy_nonnegative := sample.face_energy_nonnegative
  positiveFace := sample.positiveFace
  unit_energy_le_face := sample.unit_energy_le_face

theorem unitEnergy_le_raw
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    CCL.Riemann.PreparedEnergy.genusOneRawEnergy curve <=
      CCL.Riemann.FiniteEnergy.unnormalizedEnergyForm
        CCL.Riemann.FiniteEnergy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toUnitTriangulatedSurfaceSample.unitEnergy_le_raw

end GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample

/-- A distributed triangulated unit surface at every synchronized genus-one
sample.  This is the certificate-level form of the exact two-dimensional
surface assembly. -/
structure GenusOneUnitDistributedTriangulatedSurfaceCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  sample : forall sampleIndex : Nat,
    GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex

namespace GenusOneUnitDistributedTriangulatedSurfaceCertificate

/-- Distributed local face bounds and exact incidence construct the minimal
genus-one unit-surface theorem. -/
theorem toUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      GenusOneUnitDistributedTriangulatedSurfaceCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitDistributedTriangulatedSurfaceCertificate

namespace GenusOneCanonicalFaceLowerCertificate

/-- Package the canonical two-face commutator construction at every sample. -/
def toDistributedTriangulatedSurfaceCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data) :
    GenusOneUnitDistributedTriangulatedSurfaceCertificate data where
  sample := certificate.toDistributedTriangulatedSurfaceSample

/-- Certificate-level route from the independent half-face bound through the
explicit finite commutator triangulation to the unit surface lower theorem. -/
theorem toUnitSurfaceLowerCertificate_via_commutatorTriangulation
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneCanonicalFaceLowerCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data :=
  GenusOneUnitDistributedTriangulatedSurfaceCertificate.toUnitSurfaceLowerCertificate
    certificate.toDistributedTriangulatedSurfaceCertificate

end GenusOneCanonicalFaceLowerCertificate

/-- The reduced genus-one surface input with a genuine triangulated witness
at every synchronized sample of the standard unit differential. -/
structure GenusOneUnitTriangulatedSurfaceCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  sample : forall sampleIndex : Nat,
    GenusOneUnitTriangulatedSurfaceSample data sampleIndex

namespace GenusOneUnitTriangulatedSurfaceCertificate

/-- Exact polygon incidence and local triangle energy lower bounds construct
the minimal genus-one unit-surface theorem. -/
theorem toUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitTriangulatedSurfaceCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitTriangulatedSurfaceCertificate

/-- The reduced genus-one surface input with affine local differential models
on every oriented triangle at every synchronized sample. -/
structure GenusOneUnitAffineTriangulatedSurfaceCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  sample : forall sampleIndex : Nat,
    GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex

namespace GenusOneUnitAffineTriangulatedSurfaceCertificate

/-- Affine local Jacobians and exact polygon incidence construct the complete
minimal genus-one unit-surface theorem. -/
theorem toUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : GenusOneUnitAffineTriangulatedSurfaceCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitAffineTriangulatedSurfaceCertificate

/-- Genus-one unit surface whose finite primitive vertices are compared with
local affine models through explicit rational error budgets. -/
structure GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (data : PeriodData curve) where
  sample : forall sampleIndex : Nat,
    GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data sampleIndex

namespace GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate

theorem toUnitSurfaceLowerCertificate
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate data) :
    CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate

end CCL.Riemann.PreparedEnergySurface
