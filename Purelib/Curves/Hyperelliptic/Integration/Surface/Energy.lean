module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Integration.Energy.AffineTriangle
public import Purelib.Integration.Energy.AffineTriangle.Box
import Purelib.Integration.Energy.Cell
import Purelib.Integration.Energy.Polygon
import Purelib.Integration.Path.Lifted.ConstantComparison
public import Purelib.Integration.Polynomial.ConstantComparison
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
public import Purelib.Integration.Program.Gaussian.Sampling.Readback
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Polygon.Stokes.Commutator.Triangulation
import Init.Core
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Rational

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Gaussian

open Purelib.Integration.Energy

open Purelib.Integration.Energy.Cell
open _root_.Purelib.Integration.Energy renaming Cell -> Cell

open Purelib.Integration.Path.Lifted

open Purelib.Integration.Polynomial

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Integration.Program.Gaussian.Sampling

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedClearPathModels

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.RootIsolation.SquareRoot.Preparation.Bank

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes.Commutator

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

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.Energy

open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)
open Purelib.Riemann.Periods.PeriodMatrix (PeriodData sampledMatrix sampledMatrix_apply)

namespace SurfaceCell

/-- The checked denominator lower bound supplies a horizontal clearance on the bottom side of the rational surface box.
-/
def bottomClearance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    Line.Basic.HorizontalLineClearance curve.polynomial cell.box
      cell.box.yLower where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro x lower upper
    have scalar := cell.denominator_apart (Components.Basic.point x cell.box.yLower)
      ⟨lower, upper, le_rfl, cell.box.y_valid⟩
    rw [normSq_eq_canonical] at scalar
    exact scalar

/-- The original denominator lower bound certifies polynomial clearance along the top side. -/
def topClearance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    Line.Basic.HorizontalLineClearance curve.polynomial cell.box
      cell.box.yUpper where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro x lower upper
    have scalar := cell.denominator_apart (Components.Basic.point x cell.box.yUpper)
      ⟨lower, upper, cell.box.y_valid, le_rfl⟩
    rw [normSq_eq_canonical] at scalar
    exact scalar

/-- The original denominator lower bound certifies polynomial clearance along the left side. -/
def leftClearance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    Line.Basic.VerticalLineClearance curve.polynomial cell.box
      cell.box.xLower where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro y lower upper
    have scalar := cell.denominator_apart (Components.Basic.point cell.box.xLower y)
      ⟨le_rfl, cell.box.x_valid, lower, upper⟩
    rw [normSq_eq_canonical] at scalar
    exact scalar

/-- The original denominator lower bound certifies polynomial clearance along the right side. -/
def rightClearance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    Line.Basic.VerticalLineClearance curve.polynomial cell.box
      cell.box.xUpper where
  bound := cell.denominatorLower
  positive := cell.denominatorLower_positive
  lower := by
    intro y lower upper
    have scalar := cell.denominator_apart (Components.Basic.point cell.box.xUpper y)
      ⟨cell.box.x_valid, le_rfl, lower, upper⟩
    rw [normSq_eq_canonical] at scalar
    exact scalar

/-- Counterclockwise bottom edge of the automatically clear box boundary. -/
def bottomSegment {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    ClearPath.ClearSegment curve.polynomial cell.box
      (Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerLeft cell.box)
        (Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerRight cell.box) := by
  unfold Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerLeft
    Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerRight
  exact .horizontal cell.box.xLower cell.box.xUpper cell.box.yLower
    le_rfl cell.box.x_valid cell.box.x_valid le_rfl
      (bottomClearance cell)

/-- The upward oriented right side with its retained polynomial-clearance proof. -/
def rightSegment {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    ClearPath.ClearSegment curve.polynomial cell.box
      (Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerRight cell.box)
        (Purelib.Geometry.Rational.Box.Gaussian.Corners.upperRight cell.box) := by
  unfold Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerRight
    Purelib.Geometry.Rational.Box.Gaussian.Corners.upperRight
  exact .vertical cell.box.xUpper cell.box.yLower cell.box.yUpper
    le_rfl cell.box.y_valid cell.box.y_valid le_rfl
      (rightClearance cell)

/-- The leftward oriented top side with its retained polynomial-clearance proof. -/
def topSegment {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    ClearPath.ClearSegment curve.polynomial cell.box
      (Purelib.Geometry.Rational.Box.Gaussian.Corners.upperRight cell.box)
        (Purelib.Geometry.Rational.Box.Gaussian.Corners.upperLeft cell.box) := by
  unfold Purelib.Geometry.Rational.Box.Gaussian.Corners.upperRight
    Purelib.Geometry.Rational.Box.Gaussian.Corners.upperLeft
  exact .horizontal cell.box.xUpper cell.box.xLower cell.box.yUpper
    cell.box.x_valid le_rfl le_rfl cell.box.x_valid
      (topClearance cell)

/-- The downward oriented left side with its retained polynomial-clearance proof. -/
def leftSegment {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    ClearPath.ClearSegment curve.polynomial cell.box
      (Purelib.Geometry.Rational.Box.Gaussian.Corners.upperLeft cell.box)
        (Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerLeft cell.box) := by
  unfold Purelib.Geometry.Rational.Box.Gaussian.Corners.upperLeft
    Purelib.Geometry.Rational.Box.Gaussian.Corners.lowerLeft
  exact .vertical cell.box.xLower cell.box.yUpper cell.box.yLower
    cell.box.y_valid le_rfl le_rfl cell.box.y_valid
      (leftClearance cell)

/-- Every point of the oriented bottom segment lies in the original cell box. -/
theorem bottomSegment_within {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    (bottomSegment cell).WithinAmbient :=
  ⟨le_rfl, cell.box.y_valid⟩

/-- Every point of the oriented right segment lies in the original cell box. -/
theorem rightSegment_within {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    (rightSegment cell).WithinAmbient :=
  ⟨cell.box.x_valid, le_rfl⟩

/-- Every point of the oriented top segment lies in the original cell box. -/
theorem topSegment_within {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    (topSegment cell).WithinAmbient :=
  ⟨cell.box.y_valid, le_rfl⟩

/-- Every point of the oriented left segment lies in the original cell box. -/
theorem leftSegment_within {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    (leftSegment cell).WithinAmbient :=
  ⟨le_rfl, cell.box.x_valid⟩

/-- Counterclockwise four-edge boundary path of the checked surface box. -/
def boundaryPath {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    Polynomial.Geometry.ClearPath curve.polynomial cell.box
      (Corners.lowerLeft cell.box) (Corners.lowerLeft cell.box) :=
  .cons (bottomSegment cell)
    (.cons (rightSegment cell)
      (.cons (topSegment cell)
        (.cons (leftSegment cell) (.nil (Corners.lowerLeft
          cell.box)))))

/-- Every segment of the four-edge boundary stays within the original cell box. -/
theorem boundaryPath_within {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) :
    (boundaryPath cell).WithinAmbient :=
  .cons (bottomSegment_within cell)
    (.cons (rightSegment_within cell)
      (.cons (topSegment_within cell)
        (.cons (leftSegment_within cell) (.nil
          (Corners.lowerLeft cell.box)))))

/-- Either explicitly indexed square-root owner at the lower-left corner can seed continuation around the entire clear
box boundary. -/
def boundaryOwner {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2) :
    SquareRootContinuationChain.Owner
      (curve.polynomial.eval (Corners.lowerLeft cell.box)) :=
  Owner.independent
    (bottomSegment cell).start_eval_ne_zero sheet

/-- Total prepared square-root continuation and integration geometry around the checked box. The sufficient dyadic
depths are computed internally for the requested positive root diameter. -/
def preparedBoundary {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    PreparedClearPathModels.PreparedPath (boundaryPath cell)
      ((boundaryOwner cell) sheet) :=
  Adaptive.preparePath (boundaryPath cell)
    (boundaryPath_within cell)
      ((boundaryOwner cell) sheet) rootDiameter
      rootDiameterPositive

/-- The prepared boundary immediately supplies the certified finite integration model for any standard algebraic
differential. -/
def certifiedBoundary {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (differential : Differentials.Basic.Differential genus) :
    PreparedPath.Certified curve
      differential sheet
      ((preparedBoundary cell) sheet rootDiameter
        rootDiameterPositive) :=
  PreparedPath.certify curve differential
    sheet
    ((preparedBoundary cell) sheet rootDiameter
      rootDiameterPositive)

end SurfaceCell
namespace SurfaceCell

/-- The automatically certified clear box boundary is cellwise constant, as inherited from every accepted prepared
subdivision. -/
def boundaryConstantCells {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (differential : Differentials.Basic.Differential genus) :
    PathModel.ConstantCells
      ((certifiedBoundary cell) sheet rootDiameter
        rootDiameterPositive
        differential).cells :=
  PreparedPath.certify_constantCells
    curve differential sheet
      ((preparedBoundary cell) sheet rootDiameter
        rootDiameterPositive)

/-- On the closed prepared box boundary the affine endpoint increment is zero. Hence the complete displayed boundary
sample is exactly its finite weighted coefficient-error sum relative to any rational reference. -/
theorem
  boundaryIntegralSample_eq_referenceError
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (differential : Differentials.Basic.Differential genus)
    (reference : Data.Gaussian.Basic.Canonical) :
    (PathModel.mk
      ((certifiedBoundary cell) sheet rootDiameter
        rootDiameterPositive
        differential).cells).integralSample =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (ConstantComparison.constantReferenceErrorTerms
          ((boundaryConstantCells cell) sheet rootDiameter
            rootDiameterPositive
            differential) reference) := by
  let certified := (certifiedBoundary cell) sheet
    rootDiameter
    rootDiameterPositive differential
  let constant := (boundaryConstantCells cell) sheet
    rootDiameter
    rootDiameterPositive differential
  have comparison :=
    ConstantComparison.constantFollowedPathIntegralSample_eq_affine_add_error constant
      certified.certificates.toFollowedBy reference
  simpa only [certified, constant, AffineTriangle.affinePrimitiveIncrement,
    _root_.sub_self,
    Data.Gaussian.Basic.zero_add] using comparison

/-- The computed finite reference allowance bounds the complete prepared closed-boundary residual. -/
theorem
  boundaryIntegralSample_normSq_le_referenceAllowance
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (sheet : Fin 2)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (differential : Differentials.Basic.Differential genus)
    (reference : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq
        ((PathModel.mk
          ((certifiedBoundary cell) sheet rootDiameter
            rootDiameterPositive
            differential).cells).integralSample) <=
      ConstantComparison.constantReferenceErrorAllowance
        ((boundaryConstantCells cell) sheet rootDiameter
          rootDiameterPositive
          differential) reference := by
  rw [(boundaryIntegralSample_eq_referenceError cell) sheet
    rootDiameter
    rootDiameterPositive differential reference]
  exact ConstantComparison.constantReferenceErrorSum_le
    ((boundaryConstantCells cell) sheet rootDiameter
      rootDiameterPositive
      differential) reference

end SurfaceCell

/-- A rational affine coefficient whose squared norm dominates the checked cell density turns the exact two-triangle box
identity into the required local surface-energy lower bound. -/
theorem
  SurfaceCell.contribution_le_boxAffineTriangleEnergy
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : PreparedEnergySurface.GaussianVector genus}
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients) (coefficient : Data.Gaussian.Basic.Canonical)
    (densityLower : cell.densityLower <=
      Data.Gaussian.Norm.Basic.normSq coefficient) :
    Integration.Energy.Cell.contribution cell.toEnergyCell <=
      AffineTriangle.Box.lowerBoxAffineTriangleEnergy cell.box coefficient +
        AffineTriangle.Box.upperBoxAffineTriangleEnergy cell.box coefficient := by
  rw [AffineTriangle.Box.boxAffineTriangleEnergy_add]
  unfold Cell.contribution
    SurfaceCell.toEnergyCell
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    densityLower (Content.boxContent_nonneg cell.box)

/-- First triangle of the canonical genus-one commutator polygon `0, a, a+b, b`, using the conjugate/value energy
primitive. -/
def genusOneUnitFirstTriangleEnergy
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) : Fraction.Rational :=
  let a := Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0)
  let b := Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)
  AffineTriangle.primitiveTriangleEnergy
    PrimitivePoint.zero a (a.add b)

/-- Second triangle of the same canonical handle subdivision. -/
def genusOneUnitSecondTriangleEnergy
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) : Fraction.Rational :=
  let a := Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0)
  let b := Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)
  AffineTriangle.primitiveTriangleEnergy
    PrimitivePoint.zero (a.add b) b

/-- The diagonal subdivision splits the handle energy into two equal oriented triangles. -/
theorem genusOneUnitFirstTriangleEnergy_eq_second
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex =
      genusOneUnitSecondTriangleEnergy data sampleIndex := by
  unfold genusOneUnitFirstTriangleEnergy
    genusOneUnitSecondTriangleEnergy
  rw [AffineTriangle.primitiveTriangleEnergy_zero_left_add,
    AffineTriangle.primitiveTriangleEnergy_zero_add_right]

/-- The two canonical triangle energies add to the displayed unit second-bilinear period pairing. -/
theorem genusOneUnitTriangleEnergy_add_eq_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex +
        genusOneUnitSecondTriangleEnergy data sampleIndex =
      Purelib.LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  unfold genusOneUnitFirstTriangleEnergy
    genusOneUnitSecondTriangleEnergy
  rw [AffineTriangle.primitiveTriangleEnergy_zero_left_add,
    AffineTriangle.primitiveTriangleEnergy_zero_add_right]
  unfold Polygon.energyPrimitivePoint Energy.unnormalizedEnergyForm
  rw [Energy.periodPairingEnergy_one_eq]
  simp only [Energy.periodCombination_genusOne_unit,
    Basic.sub_im,
    Basic.mul_im,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (2 : Fraction.Rational)⁻¹ = 2 * (4 : Fraction.Rational)⁻¹ by decide]
  ring1

/-- The direct A-program reading at one explicitly displayed internal refinement index. -/
def genusOneDirectASample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  ((data.aProgram 0 0).integral.model index).integralSample

/-- The direct B-program reading at one explicitly displayed internal refinement index. -/
def genusOneDirectBSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  ((data.bProgram 0 0).integral.model index).integralSample

/-- Antisymmetric genus-one pairing of two independently refined direct program readings. -/
def genusOneDirectPairing
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (aIndex bIndex : Nat) : Data.Gaussian.Basic.Canonical :=
  let a := genusOneDirectASample data aIndex
  let b := genusOneDirectBSample data bIndex
  a.conj * b - b.conj * a

/-- A synchronized named A-period sample is definitionally a direct reading of its originating finite refinement
program. -/
theorem sampledAEntry_eq_direct
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    sampledMatrix data.aMatrix sampleIndex 0 0 =
      genusOneDirectASample data
        (Readback.resampledRefinementIndex
          (data.aProgram 0 0).integral sampleIndex) := by
  rw [sampledMatrix_apply, PeriodData.aMatrix_apply]
  rfl

/-- The analogous direct-reading identity for the B-period. -/
theorem sampledBEntry_eq_direct
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    sampledMatrix data.bMatrix sampleIndex 0 0 =
      genusOneDirectBSample data
        (Readback.resampledRefinementIndex
          (data.bProgram 0 0).integral sampleIndex) := by
  rw [sampledMatrix_apply, PeriodData.bMatrix_apply]
  rfl

/-- Synchronized finite approximation to the antisymmetric genus-one period pairing `conj(A) B - conj(B) A`. The
construction retains the same sampler index in all four factors and binds each period sample once, so its geometric tail
estimate applies directly to the canonical commutator face without re-running either finite period program inside the
pointwise product. -/
def genusOnePairingApproximation
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) :
    Gaussian.Geometric.GeometricApproximation :=
  let a := GeometricApproximation.ofNamed
    (data.aMatrix 0 0).name
  let b := GeometricApproximation.ofNamed
    (data.bMatrix 0 0).name
  let base := GeometricApproximation.sub
    (GeometricApproximation.mul
      (GeometricApproximation.conj a) b)
    (GeometricApproximation.mul
      (GeometricApproximation.conj b) a)
  { sample := fun sampleIndex =>
      let aSample := a.sample sampleIndex
      let bSample := b.sample sampleIndex
      aSample.conj * bSample - bSample.conj * aSample
    errorScale := base.errorScale
    errorScale_nonneg := base.errorScale_nonneg
    later_close := by
      intro earlier later order
      change Data.Gaussian.Norm.Basic.normSq
          (base.sample later - base.sample earlier) <=
        Geometric.Basic.quarterRadius base.errorScale earlier
      exact base.later_close order
    centerBound := base.centerBound
    centerBound_nonneg := base.centerBound_nonneg
    sample_bounded := by
      intro sampleIndex
      change Data.Gaussian.Norm.Basic.normSq
          (base.sample sampleIndex) <= base.centerBound
      exact base.sample_bounded sampleIndex }

/-- Each retained pairing sample is the antisymmetrized product of the same synchronized A and B samples. -/
@[simp] theorem genusOnePairingApproximation_sample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    (genusOnePairingApproximation data).sample sampleIndex =
      Data.Gaussian.Basic.Canonical.conj
          (sampledMatrix data.aMatrix sampleIndex 0 0) *
        sampledMatrix data.bMatrix sampleIndex 0 0 -
      Data.Gaussian.Basic.Canonical.conj
          (sampledMatrix data.bMatrix sampleIndex 0 0) *
        sampledMatrix data.aMatrix sampleIndex 0 0 := by
  simp only [genusOnePairingApproximation,
    Gaussian.Geometric.GeometricApproximation.ofNamed_sample,
    sampledMatrix_apply, -eq_self, -iff_self]
  rfl

/-- The first commutator triangle is exactly one quarter of the imaginary antisymmetric period pairing at the same
finite sample index. -/
theorem
  genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    genusOneUnitFirstTriangleEnergy data sampleIndex =
      ((genusOnePairingApproximation data).sample sampleIndex).im / 4 :=
        by
  unfold genusOneUnitFirstTriangleEnergy
  rw [AffineTriangle.primitiveTriangleEnergy_zero_left_add]
  rw [genusOnePairingApproximation_sample]
  rfl

/-- A direct-program form of the canonical genus-one face bound. It is deliberately asynchronous: the productive A and B
names can answer one external request using different internal refinement indices. Proving the bound for every displayed
pair of direct readings therefore suffices for the actual synchronized named matrix. -/
structure DirectGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- Every independently indexed original A/B pair satisfies the canonical half-face energy lower bound. -/ lower :
    forall aIndex bIndex : Nat,
    Prepared.genusOneRawEnergy curve / 2 <=
      (genusOneDirectPairing data aIndex bIndex).im / 4

/-- Tail-only direct-program form of the canonical face theorem. The first external sample has already advanced each
originating refinement program to its independently computed initial accuracy index; only direct readings at or beyond
those two finite indices can occur in the named period matrix. -/
structure DirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- Every original A/B pair beyond its own initial resampling index satisfies the canonical half-face lower bound. -/
    lower : forall aIndex bIndex : Nat,
    Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0 <= aIndex ->
    Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0 <= bIndex ->
    Prepared.genusOneRawEnergy curve / 2 <=
      (genusOneDirectPairing data aIndex bIndex).im / 4

/-- Minimal local genus-one face theorem. The reference box energy is split equally across the two canonical commutator
triangles, so only one local triangle inequality is independent. -/
structure GenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- Every synchronized first canonical triangle dominates half of the unit reference energy. -/ lower : forall
    sampleIndex : Nat,
    Prepared.genusOneRawEnergy curve / 2 <=
      genusOneUnitFirstTriangleEnergy data sampleIndex

namespace DirectGenusOneCanonicalFaceLowerCertificate

/-- Transport a direct-program lower theorem through the exact finite sampler indices selected independently for the A
and B names. -/
theorem
  toCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.DirectGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    rw [Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four,
      Curves.Hyperelliptic.Integration.Surface.Energy.genusOnePairingApproximation_sample,
      Curves.Hyperelliptic.Integration.Surface.Energy.sampledAEntry_eq_direct,
        Curves.Hyperelliptic.Integration.Surface.Energy.sampledBEntry_eq_direct]
    exact certificate.lower
      (Readback.resampledRefinementIndex
        (data.aProgram 0 0).integral sampleIndex)
      (Readback.resampledRefinementIndex
        (data.bProgram 0 0).integral sampleIndex)

end DirectGenusOneCanonicalFaceLowerCertificate

namespace DirectTailGenusOneCanonicalFaceLowerCertificate

/-- Transport a tail theorem for the two direct refinement programs through the monotonically advancing internal indices
selected by named sampling. -/
theorem
  toCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.DirectTailGenusOneCanonicalFaceLowerCertificate data)
      :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    rw [Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four,
      Curves.Hyperelliptic.Integration.Surface.Energy.genusOnePairingApproximation_sample,
      Curves.Hyperelliptic.Integration.Surface.Energy.sampledAEntry_eq_direct,
        Curves.Hyperelliptic.Integration.Surface.Energy.sampledBEntry_eq_direct]
    exact certificate.lower
      (Readback.resampledRefinementIndex
        (data.aProgram 0 0).integral sampleIndex)
      (Readback.resampledRefinementIndex
        (data.bProgram 0 0).integral sampleIndex)
      (Readback.resampledRefinementIndex_zero_le
        (data.aProgram 0 0).integral sampleIndex)
      (Readback.resampledRefinementIndex_zero_le
        (data.bProgram 0 0).integral sampleIndex)

end DirectTailGenusOneCanonicalFaceLowerCertificate

/-- A uniform squared-movement allowance for the independently advancing direct A/B readings after the first public
sample. Each period program is compared with its own initial internal index, so no artificial synchronization of the two
executable refiners is required. -/
def genusOneDirectTailMovementBound
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Fraction.Rational :=
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  let aAnchor := Readback.resampledRefinementIndex aProgram 0
  let bAnchor := Readback.resampledRefinementIndex bProgram 0
  8 *
    (Geometric.Basic.quarterRadius aProgram.errorScale aAnchor *
        bProgram.centerBound +
      aProgram.centerBound *
        Geometric.Basic.quarterRadius bProgram.errorScale bAnchor)

/-- Independent later A/B readings move their antisymmetric pairing by at most the displayed finite rectangle-tail
allowance. The factor eight pays first for the two product differences and then for antisymmetrization. -/
theorem genusOneDirectPairing_sub_anchor_normSq_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (aIndex bIndex : Nat)
    (aOrder :
      Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0 <= aIndex)
    (bOrder :
      Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0 <= bIndex) :
    Data.Gaussian.Norm.Basic.normSq
        (genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data
            (Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0)
            (Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0)) <=
      genusOneDirectTailMovementBound data := by
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  let aAnchor := Readback.resampledRefinementIndex aProgram 0
  let bAnchor := Readback.resampledRefinementIndex bProgram 0
  let a := genusOneDirectASample data aIndex
  let b := genusOneDirectBSample data bIndex
  let aBase := genusOneDirectASample data aAnchor
  let bBase := genusOneDirectBSample data bAnchor
  let productDifference := a.conj * b - aBase.conj * bBase
  have aReadback : a = (aProgram.model aIndex).integralSample := rfl
  have bReadback : b = (bProgram.model bIndex).integralSample := rfl
  have aBaseReadback : aBase = (aProgram.model aAnchor).integralSample := rfl
  have bBaseReadback : bBase = (bProgram.model bAnchor).integralSample := rfl
  have conjugateReadback (value : Data.Gaussian.Basic.Canonical) :
      value.conj = Data.Gaussian.Basic.conj value := rfl
  have aMovement :
      Data.Gaussian.Norm.Basic.normSq (a - aBase) <=
        Geometric.Basic.quarterRadius aProgram.errorScale aAnchor := by
    have scalar := aProgram.later_close (earlier := aAnchor) (later := aIndex) aOrder
    rw [← aReadback, ← aBaseReadback] at scalar
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar
  have bMovement :
      Data.Gaussian.Norm.Basic.normSq (b - bBase) <=
        Geometric.Basic.quarterRadius bProgram.errorScale bAnchor := by
    have scalar := bProgram.later_close (earlier := bAnchor) (later := bIndex) bOrder
    rw [← bReadback, ← bBaseReadback] at scalar
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar
  have aBaseBound :
      Data.Gaussian.Norm.Basic.normSq aBase <=
        aProgram.centerBound :=
    by
      have scalar := aProgram.sample_bounded aAnchor
      rw [← aBaseReadback] at scalar
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact scalar
  have bBound :
      Data.Gaussian.Norm.Basic.normSq b <=
        bProgram.centerBound :=
    by
      have scalar := bProgram.sample_bounded bIndex
      rw [← bReadback] at scalar
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact scalar
  have productIdentity :
      productDifference =
        (a - aBase).conj * b + aBase.conj * (b - bBase) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [productDifference,
        Data.Gaussian.Basic.Canonical.conj,
        Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  have firstProduct :
      Data.Gaussian.Norm.Basic.normSq ((a - aBase).conj * b) <=
        Geometric.Basic.quarterRadius aProgram.errorScale aAnchor *
          bProgram.centerBound := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, conjugateReadback,
      Data.Gaussian.Norm.Basic.normSq_conj]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct aMovement bBound
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Geometric.Basic.quarterRadius_nonneg
        aProgram.errorScale_nonneg aAnchor)
  have secondProduct :
      Data.Gaussian.Norm.Basic.normSq
          (aBase.conj * (b - bBase)) <=
        aProgram.centerBound *
          Geometric.Basic.quarterRadius bProgram.errorScale bAnchor := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, conjugateReadback,
      Data.Gaussian.Norm.Basic.normSq_conj]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct aBaseBound bMovement
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      aProgram.centerBound_nonneg
  have productBound :
      Data.Gaussian.Norm.Basic.normSq productDifference <=
        2 *
          (Geometric.Basic.quarterRadius aProgram.errorScale aAnchor *
              bProgram.centerBound +
            aProgram.centerBound *
              Geometric.Basic.quarterRadius bProgram.errorScale
                bAnchor) := by
    rw [productIdentity]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstProduct secondProduct) (by decide))
  have pairingIdentity :
      genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data aAnchor bAnchor =
        productDifference - productDifference.conj := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [genusOneDirectPairing, a, b, aBase, bBase,
        productDifference,
        Data.Gaussian.Basic.Canonical.conj,
        Basic.sub_re,
        Basic.sub_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  rw [pairingIdentity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        (productDifference - productDifference.conj) <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq productDifference +
          Data.Gaussian.Norm.Basic.normSq
            productDifference.conj) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ = 4 * Data.Gaussian.Norm.Basic.normSq productDifference := by
      rw [conjugateReadback, Data.Gaussian.Norm.Basic.normSq_conj]
      ring1
    _ <= 4 *
        (2 *
          (Geometric.Basic.quarterRadius aProgram.errorScale aAnchor *
              bProgram.centerBound +
            aProgram.centerBound *
              Geometric.Basic.quarterRadius bProgram.errorScale
                bAnchor)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ = genusOneDirectTailMovementBound data := by
      unfold genusOneDirectTailMovementBound aProgram bProgram aAnchor
        bAnchor
      ring1

/-- A uniform squared-movement allowance from the zeroth internal readings of the independently advancing direct A/B
programs. Unlike `genusOneDirectTailMovementBound`, this quantity contains no executable resampling index, so an
explicit example can normalize it using only the cached program scales and center bounds. -/
def genusOneDirectZeroMovementBound
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Fraction.Rational :=
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  8 *
    (Geometric.Basic.quarterRadius aProgram.errorScale 0 *
        bProgram.centerBound +
      aProgram.centerBound *
        Geometric.Basic.quarterRadius bProgram.errorScale 0)

/-- Every pair of direct program readings is close to the pair at internal index zero. This deliberately spends the
coarser zeroth-index tail allowance in exchange for avoiding reduction of either executable resampling index. -/
theorem genusOneDirectPairing_sub_zero_normSq_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (aIndex bIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data 0 0) <=
      genusOneDirectZeroMovementBound data := by
  let aProgram := (data.aProgram 0 0).integral
  let bProgram := (data.bProgram 0 0).integral
  let a := genusOneDirectASample data aIndex
  let b := genusOneDirectBSample data bIndex
  let aBase := genusOneDirectASample data 0
  let bBase := genusOneDirectBSample data 0
  let productDifference := a.conj * b - aBase.conj * bBase
  have aReadback : a = (aProgram.model aIndex).integralSample := rfl
  have bReadback : b = (bProgram.model bIndex).integralSample := rfl
  have aBaseReadback : aBase = (aProgram.model 0).integralSample := rfl
  have bBaseReadback : bBase = (bProgram.model 0).integralSample := rfl
  have conjugateReadback (value : Data.Gaussian.Basic.Canonical) :
      value.conj = Data.Gaussian.Basic.conj value := rfl
  have aMovement :
      Data.Gaussian.Norm.Basic.normSq (a - aBase) <=
        Geometric.Basic.quarterRadius aProgram.errorScale 0 := by
    have scalar := aProgram.later_close (earlier := 0) (later := aIndex) (Nat.zero_le aIndex)
    rw [← aReadback, ← aBaseReadback] at scalar
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar
  have bMovement :
      Data.Gaussian.Norm.Basic.normSq (b - bBase) <=
        Geometric.Basic.quarterRadius bProgram.errorScale 0 := by
    have scalar := bProgram.later_close (earlier := 0) (later := bIndex) (Nat.zero_le bIndex)
    rw [← bReadback, ← bBaseReadback] at scalar
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar
  have aBaseBound :
      Data.Gaussian.Norm.Basic.normSq aBase <=
        aProgram.centerBound :=
    by
      have scalar := aProgram.sample_bounded 0
      rw [← aBaseReadback] at scalar
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact scalar
  have bBound :
      Data.Gaussian.Norm.Basic.normSq b <=
        bProgram.centerBound :=
    by
      have scalar := bProgram.sample_bounded bIndex
      rw [← bReadback] at scalar
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact scalar
  have productIdentity :
      productDifference =
        (a - aBase).conj * b + aBase.conj * (b - bBase) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [productDifference,
        Data.Gaussian.Basic.Canonical.conj,
        Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  have firstProduct :
      Data.Gaussian.Norm.Basic.normSq ((a - aBase).conj * b) <=
        Geometric.Basic.quarterRadius aProgram.errorScale 0 *
          bProgram.centerBound := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, conjugateReadback,
      Data.Gaussian.Norm.Basic.normSq_conj]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct aMovement bBound
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Geometric.Basic.quarterRadius_nonneg
        aProgram.errorScale_nonneg 0)
  have secondProduct :
      Data.Gaussian.Norm.Basic.normSq
          (aBase.conj * (b - bBase)) <=
        aProgram.centerBound *
          Geometric.Basic.quarterRadius bProgram.errorScale 0 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, conjugateReadback,
      Data.Gaussian.Norm.Basic.normSq_conj]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct aBaseBound bMovement
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      aProgram.centerBound_nonneg
  have productBound :
      Data.Gaussian.Norm.Basic.normSq productDifference <=
        2 *
          (Geometric.Basic.quarterRadius aProgram.errorScale 0 *
              bProgram.centerBound +
            aProgram.centerBound *
              Geometric.Basic.quarterRadius bProgram.errorScale 0) := by
    rw [productIdentity]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstProduct secondProduct) (by decide))
  have pairingIdentity :
      genusOneDirectPairing data aIndex bIndex -
          genusOneDirectPairing data 0 0 =
        productDifference - productDifference.conj := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [genusOneDirectPairing, a, b, aBase, bBase,
        productDifference,
        Data.Gaussian.Basic.Canonical.conj,
        Basic.sub_re,
        Basic.sub_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  rw [pairingIdentity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        (productDifference - productDifference.conj) <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq productDifference +
          Data.Gaussian.Norm.Basic.normSq
            productDifference.conj) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ = 4 * Data.Gaussian.Norm.Basic.normSq productDifference := by
      rw [conjugateReadback, Data.Gaussian.Norm.Basic.normSq_conj]
      ring1
    _ <= 4 *
        (2 *
          (Geometric.Basic.quarterRadius aProgram.errorScale 0 *
              bProgram.centerBound +
            aProgram.centerBound *
              Geometric.Basic.quarterRadius bProgram.errorScale 0)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ = genusOneDirectZeroMovementBound data := by
      unfold genusOneDirectZeroMovementBound aProgram bProgram
      ring1

/-- Finite asynchronous tail certificate for the canonical genus-one face. One exact positive margin at the pair of
first internal readings controls all later independently refined A/B readings when the rectangle-tail movement is
smaller than the squared margin. -/
structure
  AnchoredDirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- The direct pairing at the two original initial resampling indices has a strictly positive margin above four times
    the required half-energy floor. -/ tailMarginPositive :
    0 <
      (genusOneDirectPairing data
        (Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0)
        (Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0)).im -
          4 * (Prepared.genusOneRawEnergy curve / 2)
  /-- The retained direct tail movement bound is strictly below the square of the positive anchor margin. -/
    tailMovementSmall :
    genusOneDirectTailMovementBound data <
      ((genusOneDirectPairing data
        (Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0)
        (Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0)).im -
          4 * (Prepared.genusOneRawEnergy curve / 2)) ^ 2

namespace AnchoredDirectTailGenusOneCanonicalFaceLowerCertificate

/-- Promote one finite asynchronous anchor calculation to the universal direct-tail face inequality. -/
theorem
  toDirectTailGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.AnchoredDirectTailGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.DirectTailGenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro aIndex bIndex aOrder bOrder
    let target := Prepared.genusOneRawEnergy curve / 2
    let aAnchor :=
      Readback.resampledRefinementIndex (data.aProgram 0 0).integral 0
    let bAnchor :=
      Readback.resampledRefinementIndex (data.bProgram 0 0).integral 0
    let anchorValue := (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aAnchor bAnchor).im
    let sampleValue := (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex).im
    let margin := anchorValue - 4 * target
    have marginPositive : 0 < margin := certificate.tailMarginPositive
    apply (Fraction.Order.Field.le_div_iff_pos
      (by decide : (0 : Fraction.Rational) < 4)).2
    change target * 4 <= sampleValue
    by_cases enough : 4 * target <= sampleValue
    · simpa only [mul_comm target] using enough
    · have sampleBelow : sampleValue < 4 * target :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct enough
      have marginBelowDifference :
          margin < anchorValue - sampleValue :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          sampleBelow anchorValue
      have differencePositive : 0 < anchorValue - sampleValue :=
        marginPositive.trans marginBelowDifference
      have firstProduct :
          margin * margin < margin * (anchorValue - sampleValue) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          marginPositive marginBelowDifference
      have secondProduct :
          margin * (anchorValue - sampleValue) <
            (anchorValue - sampleValue) * (anchorValue - sampleValue) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          marginBelowDifference differencePositive
      have squareStrict :
          margin ^ 2 < (anchorValue - sampleValue) ^ 2 := by
        simpa only [pow_two] using firstProduct.trans secondProduct
      have imaginarySquareLe :
          (anchorValue - sampleValue) ^ 2 <=
            Data.Gaussian.Norm.Basic.normSq
              (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex -
                Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aAnchor bAnchor) := by
        change (anchorValue - sampleValue) ^ 2 <=
          ((Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex).re -
              (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aAnchor bAnchor).re) ^ 2 +
            (sampleValue - anchorValue) ^ 2
        have reflected :
            (anchorValue - sampleValue) ^ 2 =
              (sampleValue - anchorValue) ^ 2 := by ring1
        rw [reflected]
        exact le_add_of_nonneg_left
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      have movement := Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing_sub_anchor_normSq_le
        data aIndex bIndex aOrder bOrder
      have forbidden : margin ^ 2 < Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectTailMovementBound data
        :=
        squareStrict.trans_le (imaginarySquareLe.trans movement)
      have cycle := certificate.tailMovementSmall.trans forbidden
      exact (lt_irrefl _ cycle).elim

/-- Direct route from the finite asynchronous anchor to the canonical face certificate consumed by the finite Riemann
period theorem. -/
theorem
  toCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.AnchoredDirectTailGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data :=
  certificate.toDirectTailGenusOneCanonicalFaceLowerCertificate.toCanonicalFaceLowerCertificate

end AnchoredDirectTailGenusOneCanonicalFaceLowerCertificate

/-- Finite zero-anchor certificate for the canonical genus-one face. It asks for one exact positive margin at internal
index zero and compares the coarser zero-index rectangle-tail allowance with its square. In return, it controls all
direct readings and never mentions an executable resampling index. -/
structure
  AnchoredDirectZeroGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At original internal index zero, the direct pairing imaginary part exceeds four times the required half-energy
    floor. -/ zeroMarginPositive :
    0 < (genusOneDirectPairing data 0 0).im -
      4 * (Prepared.genusOneRawEnergy curve / 2)
  /-- The all-index movement bound is strictly below the square of the retained positive index-zero margin. -/
    zeroMovementSmall :
    genusOneDirectZeroMovementBound data <
      ((genusOneDirectPairing data 0 0).im -
        4 * (Prepared.genusOneRawEnergy curve / 2)) ^ 2

namespace AnchoredDirectZeroGenusOneCanonicalFaceLowerCertificate

/-- Promote the finite index-zero calculation to a lower theorem for every pair of independently refined direct
readings. -/
theorem
  toDirectGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.AnchoredDirectZeroGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.DirectGenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro aIndex bIndex
    let target := Prepared.genusOneRawEnergy curve / 2
    let anchorValue := (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data 0 0).im
    let sampleValue := (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex).im
    let margin := anchorValue - 4 * target
    have marginPositive : 0 < margin := certificate.zeroMarginPositive
    apply (Fraction.Order.Field.le_div_iff_pos
      (by decide : (0 : Fraction.Rational) < 4)).2
    change target * 4 <= sampleValue
    by_cases enough : 4 * target <= sampleValue
    · simpa only [mul_comm target] using enough
    · have sampleBelow : sampleValue < 4 * target :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct enough
      have marginBelowDifference :
          margin < anchorValue - sampleValue :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          sampleBelow anchorValue
      have differencePositive : 0 < anchorValue - sampleValue :=
        marginPositive.trans marginBelowDifference
      have firstProduct :
          margin * margin < margin * (anchorValue - sampleValue) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          marginPositive marginBelowDifference
      have secondProduct :
          margin * (anchorValue - sampleValue) <
            (anchorValue - sampleValue) * (anchorValue - sampleValue) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          marginBelowDifference differencePositive
      have squareStrict :
          margin ^ 2 < (anchorValue - sampleValue) ^ 2 := by
        simpa only [pow_two] using firstProduct.trans secondProduct
      have imaginarySquareLe :
          (anchorValue - sampleValue) ^ 2 <=
            Data.Gaussian.Norm.Basic.normSq
              (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex -
                Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data 0 0) := by
        change (anchorValue - sampleValue) ^ 2 <=
          ((Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data aIndex bIndex).re -
              (Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing data 0 0).re) ^ 2 +
            (sampleValue - anchorValue) ^ 2
        have reflected :
            (anchorValue - sampleValue) ^ 2 =
              (sampleValue - anchorValue) ^ 2 := by ring1
        rw [reflected]
        exact le_add_of_nonneg_left
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      have movement := Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectPairing_sub_zero_normSq_le
        data aIndex bIndex
      have forbidden : margin ^ 2 < Curves.Hyperelliptic.Integration.Surface.Energy.genusOneDirectZeroMovementBound data
        :=
        squareStrict.trans_le (imaginarySquareLe.trans movement)
      have cycle := certificate.zeroMovementSmall.trans forbidden
      exact (lt_irrefl _ cycle).elim

/-- Direct route from a finite index-zero calculation to the canonical face certificate consumed by the finite Riemann
period theorem. -/
theorem
  toCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.AnchoredDirectZeroGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data :=
  certificate.toDirectGenusOneCanonicalFaceLowerCertificate.toCanonicalFaceLowerCertificate

end AnchoredDirectZeroGenusOneCanonicalFaceLowerCertificate

set_option genInjectivity false in
/-- Finite form of the canonical genus-one face lower theorem. Only the samples before `anchor` are checked separately.
One positive imaginary margin at the anchor, together with a squared geometric tail bound smaller than that margin,
controls every later sample. -/
structure AnchoredGenusOneCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- The retained synchronized sample index separating the checked finite prefix from the controlled tail. -/ anchor :
    Nat
  /-- Every synchronized sample before the retained anchor satisfies the canonical half-face lower bound. -/
    prefix_lower : forall sampleIndex, sampleIndex < anchor ->
    Prepared.genusOneRawEnergy curve / 2 <=
      genusOneUnitFirstTriangleEnergy data sampleIndex
  /-- The synchronized pairing imaginary part at the retained anchor strictly exceeds four times the required
    half-energy floor. -/ tailMarginPositive :
    0 < ((genusOnePairingApproximation data).sample anchor).im -
      4 * (Prepared.genusOneRawEnergy curve / 2)
  /-- The geometric error radius at the retained anchor is strictly below its positive margin squared. -/
    tailMovementSmall :
    Geometric.Basic.quarterRadius
        (genusOnePairingApproximation data).errorScale anchor <
      (((genusOnePairingApproximation data).sample anchor).im -
        4 * (Prepared.genusOneRawEnergy curve / 2)) ^ 2

constructive_injectivity AnchoredGenusOneCanonicalFaceLowerCertificate

namespace AnchoredGenusOneCanonicalFaceLowerCertificate

/-- Promote the bounded prefix and one tail check to the universal canonical face lower theorem. The proof compares
imaginary-coordinate motion with the full Gaussian squared-motion bound; it uses no limit or completeness principle. -/
theorem
  toCanonicalFaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.AnchoredGenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data where
  lower := by
    intro sampleIndex
    by_cases before : sampleIndex < certificate.anchor
    · exact certificate.prefix_lower sampleIndex before
    · have order : certificate.anchor <= sampleIndex := Nat.le_of_not_gt before
      let approximation := Curves.Hyperelliptic.Integration.Surface.Energy.genusOnePairingApproximation data
      let target := Prepared.genusOneRawEnergy curve / 2
      let anchorValue := (approximation.sample certificate.anchor).im
      let sampleValue := (approximation.sample sampleIndex).im
      let margin := anchorValue - 4 * target
      have marginPositive : 0 < margin := certificate.tailMarginPositive
      have movement := approximation.later_close order
      have targetOriented :
          Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy data sampleIndex =
            sampleValue / 4 := by
        exact Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy_eq_pairing_im_div_four
          data sampleIndex
      rw [targetOriented]
      apply (Fraction.Order.Field.le_div_iff_pos
        (by decide : (0 : Fraction.Rational) < 4)).2
      change target * 4 <= sampleValue
      by_cases enough : 4 * target <= sampleValue
      · simpa only [mul_comm target] using enough
      · have sampleBelow : sampleValue < 4 * target :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct enough
        have marginBelowDifference :
            margin < anchorValue - sampleValue :=
          Fraction.Order.Arithmetic.sub_lt_sub_left_direct
            sampleBelow anchorValue
        have differencePositive : 0 < anchorValue - sampleValue :=
          marginPositive.trans marginBelowDifference
        have firstProduct :
            margin * margin < margin * (anchorValue - sampleValue) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            marginPositive marginBelowDifference
        have secondProduct :
            margin * (anchorValue - sampleValue) <
              (anchorValue - sampleValue) * (anchorValue - sampleValue) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            marginBelowDifference differencePositive
        have squareStrict :
            margin ^ 2 < (anchorValue - sampleValue) ^ 2 := by
          simpa only [pow_two] using firstProduct.trans secondProduct
        have imaginarySquareLe :
            (anchorValue - sampleValue) ^ 2 <=
              Data.Gaussian.Norm.Basic.normSq
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
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        have forbidden : margin ^ 2 <
            Geometric.Basic.quarterRadius approximation.errorScale
              certificate.anchor :=
          squareStrict.trans_le (imaginarySquareLe.trans movement)
        have cycle := certificate.tailMovementSmall.trans forbidden
        exact (lt_irrefl _ cycle).elim

end AnchoredGenusOneCanonicalFaceLowerCertificate

namespace GenusOneCanonicalFaceLowerCertificate

/-- Package the derived unit surface inequality at every synchronized sample. -/
theorem
  toUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    have secondLower :
        Prepared.genusOneRawEnergy curve / 2 <=
          Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitSecondTriangleEnergy data sampleIndex := by
      rw [← Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy_eq_second data sampleIndex]
      exact certificate.lower sampleIndex
    calc
      Prepared.genusOneRawEnergy curve =
          Prepared.genusOneRawEnergy curve / 2 +
            Prepared.genusOneRawEnergy curve / 2 := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        calc
          Prepared.genusOneRawEnergy curve =
              Prepared.genusOneRawEnergy curve *
                ((2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹) := by
            rw [show (2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹ = 1 by decide]
            ring1
          _ = Prepared.genusOneRawEnergy curve * 2⁻¹ +
              Prepared.genusOneRawEnergy curve * 2⁻¹ := by
            ring1
      _ <= Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy data sampleIndex +
          Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitSecondTriangleEnergy data sampleIndex :=
        add_le_add (certificate.lower sampleIndex) secondLower
      _ = Energy.unnormalizedEnergyForm
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) :=
        Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitTriangleEnergy_add_eq_raw data sampleIndex

end GenusOneCanonicalFaceLowerCertificate

set_option genInjectivity false in
/-- One completely finite cut-surface energy sample. Faces and surface cells share an index, so every checked local
lower contribution is assigned to an actual oriented triangle. -/
structure TriangulatedRawEnergySample {genus cellCount :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : PreparedEnergySurface.GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount cellCount
  /-- The retained primitive pair at each original triangulation vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- Each original cell contribution is bounded by its assigned oriented primitive triangle energy. -/
    face_energy_lower : forall face : Fin cellCount,
    Cell.contribution
        ((cells face).toEnergyCell) <=
      AffineTriangle.triangleEnergy primitive (triangulation.faces face)

constructive_injectivity TriangulatedRawEnergySample

namespace TriangulatedRawEnergySample

/-- Exact incidence cancellation identifies the sum of local triangle energies with the displayed raw A/B pairing. -/
theorem
  triangleEnergySum_eq_raw
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergySample data coefficients sampleIndex
      cells) :
    FiniteSum.Fin.sumFin (fun face =>
        Purelib.Integration.Energy.AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  let aPeriods := Energy.periodCombination coefficients
    (sampledMatrix data.aMatrix sampleIndex)
  let bPeriods := Energy.periodCombination coefficients
    (sampledMatrix data.bMatrix sampleIndex)
  calc
    FiniteSum.Fin.sumFin (fun face =>
        AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face)) =
        (Stokes.triangleWedgeSum sample.primitive
          sample.triangulation.faces).im / 4 := by
      unfold AffineTriangle.triangleEnergy Stokes.triangleWedgeSum
      rw [Energy.sumFin_im]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      exact FiniteSum.Fin.sumFin_mul_right
        (fun face =>
          (Stokes.triangleWedgeArea
            (sample.primitive (sample.triangulation.faces face).first)
            (sample.primitive (sample.triangulation.faces face).second)
            (sample.primitive
              (sample.triangulation.faces face).third)).im)
        ((4 : Fraction.Rational)⁻¹)
    _ = (Stokes.edgeListArea sample.primitive
          sample.triangulation.boundary).im / 4 := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = (Polygon.energyBoundaryArea aPeriods bPeriods).im / 4 := by
      rw [sample.boundary_matches]
    _ = Energy.periodPairingEnergy aPeriods bPeriods :=
      (Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four aPeriods bPeriods).symm
    _ = Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := rfl

/-- The global surface lower inequality is a theorem of the local face inequalities and exact finite Stokes incidence.
-/
theorem surfaceEnergy_le_raw
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergySample data coefficients sampleIndex
      cells) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  unfold Prepared.surfaceEnergy
    Cell.cellEnergy
    Prepared.energyCells
  calc
    FiniteSum.Fin.sumFin (fun face =>
        Cell.contribution
          ((cells face).toEnergyCell)) <=
        FiniteSum.Fin.sumFin (fun face =>
          AffineTriangle.triangleEnergy sample.primitive
            (sample.triangulation.faces face)) := by
      apply Order.Positivity.sumFin_mono
      exact sample.face_energy_lower
    _ = Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) :=
      sample.triangleEnergySum_eq_raw

/-- Materialize the legacy exact decomposition only after the triangulated surface calculation has proved its global
inequality. -/
def toRawBoundaryReduction
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergySample data coefficients sampleIndex
      cells) :
    Prepared.RawBoundaryReduction data coefficients
      sampleIndex cells := by
  let raw := Energy.unnormalizedEnergyForm coefficients
    (sampledMatrix data.aMatrix sampleIndex)
    (sampledMatrix data.bMatrix sampleIndex)
  let localEnergy := Prepared.surfaceEnergy cells
  exact
    { edgePairCount := 0
      edgePairValues := fun edge => Fin.elim0 edge
      remainder := raw - localEnergy
      remainder_nonnegative :=
        Fraction.Order.Arithmetic.sub_nonneg_direct sample.surfaceEnergy_le_raw
      raw_eq_decomposition := by
        rw [Prepared.pairedBoundarySum_zero]
        unfold raw localEnergy
        ring1 }

end TriangulatedRawEnergySample

set_option genInjectivity false in
/-- A stronger local-analytic presentation of a triangulated raw-energy sample. Each face carries an affine coefficient
and rational coordinate triangle. Its three global primitive values are checked against that one affine primitive, while
the triangle's coordinate area and coefficient norm dominate the assigned surface cell. The face-energy inequality is
therefore derived from the exact affine Jacobian theorem above. -/
structure AffineTriangulatedRawEnergySample {genus
  cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : PreparedEnergySurface.GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount cellCount
  /-- The retained Gaussian rational coordinate of each original triangulation vertex. -/ coordinate : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained primitive pair at each original triangulation vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- The retained constant Gaussian differential coefficient for each original face. -/ faceCoefficient : Fin cellCount
    -> Data.Gaussian.Basic.Canonical
  /-- The first primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_first :
    forall face : Fin cellCount,
    primitive (triangulation.faces face).first =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).first)
  /-- The second primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_second :
    forall face : Fin cellCount,
    primitive (triangulation.faces face).second =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).second)
  /-- The third primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_third :
    forall face : Fin cellCount,
    primitive (triangulation.faces face).third =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).third)
  /-- Each original cell area is bounded by its assigned oriented coordinate triangle area. -/ cell_area_le_triangle :
    forall face : Fin cellCount,
    Content.boxContent (cells face).box <=
      AffineTriangle.coordinateTriangleArea
        (coordinate (triangulation.faces face).first)
        (coordinate (triangulation.faces face).second)
        (coordinate (triangulation.faces face).third)
  /-- Each original cell density floor is bounded by its assigned affine coefficient squared norm. -/
    cell_density_le_coefficient : forall face : Fin cellCount,
    (cells face).densityLower <=
      Data.Gaussian.Norm.Basic.normSq (faceCoefficient face)

constructive_injectivity AffineTriangulatedRawEnergySample

namespace AffineTriangulatedRawEnergySample

/-- Exact affine local algebra derives, rather than assumes, the energy lower bound on every oriented face. -/
theorem
  face_energy_lower
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.AffineTriangulatedRawEnergySample data coefficients
      sampleIndex
      cells)
    (face : Fin cellCount) :
    Cell.contribution
        ((cells face).toEnergyCell) <=
      Purelib.Integration.Energy.AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient face
  have areaNonnegative :
      0 <= AffineTriangle.coordinateTriangleArea first second third :=
    (Content.boxContent_nonneg (cells face).box).trans
      (sample.cell_area_le_triangle face)
  calc
    Cell.contribution
        ((cells face).toEnergyCell) =
        Content.boxContent (cells face).box *
          (cells face).densityLower := rfl
    _ <= AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (sample.cell_area_le_triangle face)
        (sample.cell_density_le_coefficient face)
        (cells face).densityLower_nonnegative areaNonnegative
    _ = AffineTriangle.primitiveTriangleEnergy
          (AffineTriangle.affineEnergyPrimitive coefficient first)
          (AffineTriangle.affineEnergyPrimitive coefficient second)
          (AffineTriangle.affineEnergyPrimitive coefficient third) :=
      (AffineTriangle.affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = AffineTriangle.triangleEnergy sample.primitive
          (sample.triangulation.faces face) := by
      unfold AffineTriangle.triangleEnergy AffineTriangle.primitiveTriangleEnergy
      rw [sample.primitive_first face, sample.primitive_second face,
        sample.primitive_third face]

/-- Forget the affine sidecar only after constructing every local face lower inequality from coordinate area and
coefficient norm. -/
def
  toTriangulatedRawEnergySample
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.AffineTriangulatedRawEnergySample data coefficients
      sampleIndex
      cells) :
    Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergySample data coefficients sampleIndex cells
      where
  vertexCount := sample.vertexCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  face_energy_lower := sample.face_energy_lower

/-- Consequently the affine local model plus exact triangulation incidence proves the complete raw surface lower
theorem. -/
theorem
  surfaceEnergy_le_raw
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.AffineTriangulatedRawEnergySample data coefficients
      sampleIndex
      cells) :
    Prepared.surfaceEnergy cells <=
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toTriangulatedRawEnergySample.surfaceEnergy_le_raw

end AffineTriangulatedRawEnergySample

set_option genInjectivity false in
/-- Error-controlled affine triangulation. Global primitive vertices are arbitrary displayed Gaussian values. Each face
compares them with one local affine coefficient through an `AffineTriangleErrorCertificate`; a checked margin pays that
error before the exact incidence theorem is applied. -/
structure
  ErrorControlledAffineTriangulatedRawEnergySample
    {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : PreparedEnergySurface.GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount cellCount
  /-- The retained Gaussian rational coordinate of each original triangulation vertex. -/ coordinate : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained Gaussian primitive value at each original triangulation vertex. -/ primitiveValue : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea
        (fun vertex => Polygon.energyPrimitivePoint (primitiveValue vertex))
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination coefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination coefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- The retained constant Gaussian differential coefficient for each original face. -/ faceCoefficient : Fin cellCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained comparison certificate for the three original primitive vertices and their local affine model. -/
    faceError : forall face : Fin cellCount,
    AffineTriangle.AffineTriangleErrorCertificate (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third)
  /-- Each original cell contribution and its retained comparison budget fit within the assigned affine triangle energy.
  -/
  cell_energy_add_error_le_affine : forall face : Fin cellCount,
    Cell.contribution ((cells face).toEnergyCell) +
        (faceError face).totalBudget <=
      AffineTriangle.coordinateTriangleArea
          (coordinate (triangulation.faces face).first)
          (coordinate (triangulation.faces face).second)
          (coordinate (triangulation.faces face).third) *
        Data.Gaussian.Norm.Basic.normSq (faceCoefficient face)

constructive_injectivity ErrorControlledAffineTriangulatedRawEnergySample

namespace ErrorControlledAffineTriangulatedRawEnergySample

/-- Paying the explicit affine comparison budget derives the local face lower required by the exact triangulation layer.
-/
theorem
  face_energy_lower
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells)
    (face : Fin cellCount) :
    Cell.contribution
        ((cells face).toEnergyCell) <=
      AffineTriangle.triangleEnergy
        (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
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
  let contribution := Cell.contribution
    ((cells face).toEnergyCell)
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    (sample.cell_energy_add_error_le_affine face) (-error.totalBudget)
  calc
    Cell.contribution
        ((cells face).toEnergyCell) =
        (contribution + error.totalBudget) + -error.totalBudget := by
      unfold contribution
      ring1
    _ <= AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient +
            -error.totalBudget := shifted
    _ = AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient -
            error.totalBudget := by ring1
    _ <= AffineTriangle.primitiveTriangleEnergy
          (Polygon.energyPrimitivePoint primitiveFirst)
          (Polygon.energyPrimitivePoint primitiveSecond)
          (Polygon.energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = AffineTriangle.triangleEnergy
          (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces face) := rfl

/-- Forget error and affine sidecars only after deriving every local lower. -/
def
  toTriangulatedRawEnergySample
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells) :
    Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergySample data coefficients sampleIndex cells
      where
  vertexCount := sample.vertexCount
  triangulation := sample.triangulation
  primitive := fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex)
  boundary_matches := sample.boundary_matches
  face_energy_lower := sample.face_energy_lower

/-- Local quadrature budgets, exact incidence, and boundary matching prove the complete raw surface inequality. -/
theorem
  surfaceEnergy_le_raw
  {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : PreparedEnergySurface.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> PreparedEnergySurface.SurfaceCell curve coefficients}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.ErrorControlledAffineTriangulatedRawEnergySample data
      coefficients sampleIndex cells) :
    Prepared.surfaceEnergy cells <=
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toTriangulatedRawEnergySample.surfaceEnergy_le_raw

end ErrorControlledAffineTriangulatedRawEnergySample

set_option genInjectivity false in
/-- Genus-generic raw surface theorem assembled from locally error-controlled affine primitive triangles. -/
structure
  ErrorControlledAffineTriangulatedRawEnergyCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) where
  /-- For every coefficient vector, sample index and original cell, retain an error-controlled affine triangulation of
    that single cell. -/ sample : forall (coefficients : PreparedEnergySurface.GaussianVector genus) (sampleIndex : Nat)
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients),
    ErrorControlledAffineTriangulatedRawEnergySample data coefficients
      sampleIndex (fun _ : Fin 1 => cell)

constructive_injectivity ErrorControlledAffineTriangulatedRawEnergyCertificate

namespace ErrorControlledAffineTriangulatedRawEnergyCertificate

/-- Derive the raw surface lower bound from the retained local triangle bounds and exact finite incidence. -/
theorem
  toRawSurfaceLowerCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.ErrorControlledAffineTriangulatedRawEnergyCertificate data) :
    Prepared.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

/-- Package the derived surface lower theorem as the raw energy certificate. -/
def
  toRawCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.ErrorControlledAffineTriangulatedRawEnergyCertificate data) :
    Prepared.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end ErrorControlledAffineTriangulatedRawEnergyCertificate

set_option genInjectivity false in
/-- Genus-generic raw surface theorem whose local analytic input is given by affine coordinate triangles, not by
preassembled face-energy inequalities. -/
structure AffineTriangulatedRawEnergyCertificate {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) where
  /-- For every coefficient vector, sample index and original cell, retain its affine triangulation and exact local
    primitive comparisons. -/ sample : forall (coefficients : PreparedEnergySurface.GaussianVector genus) (sampleIndex :
    Nat)
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients),
    AffineTriangulatedRawEnergySample data coefficients sampleIndex
      (fun _ : Fin 1 => cell)

constructive_injectivity AffineTriangulatedRawEnergyCertificate

namespace AffineTriangulatedRawEnergyCertificate

/-- Derive the raw surface lower bound from the retained local triangle bounds and exact finite incidence. -/
theorem
  toRawSurfaceLowerCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.AffineTriangulatedRawEnergyCertificate data) :
    Prepared.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

/-- Package the derived surface lower theorem as the raw energy certificate. -/
def
  toRawCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.AffineTriangulatedRawEnergyCertificate data) :
    Prepared.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end AffineTriangulatedRawEnergyCertificate

set_option genInjectivity false in
/-- Genus-generic triangulated replacement for the global raw surface-lower field. The only analytic hypotheses are
local face inequalities. -/
structure TriangulatedRawEnergyCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) where
  /-- For every coefficient vector, sample index and original cell, retain a finite triangulation proving its local
    energy lower bound. -/ sample : forall (coefficients : PreparedEnergySurface.GaussianVector genus) (sampleIndex :
    Nat)
    (cell : PreparedEnergySurface.SurfaceCell curve coefficients),
    TriangulatedRawEnergySample data coefficients sampleIndex
      (fun _ : Fin 1 => cell)

constructive_injectivity TriangulatedRawEnergyCertificate

namespace TriangulatedRawEnergyCertificate

/-- Derive the raw surface lower bound from the retained local triangle bounds and exact finite incidence. -/
theorem
  toRawSurfaceLowerCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergyCertificate data) :
    Prepared.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.sample coefficients sampleIndex cell).surfaceEnergy_le_raw

/-- Package the derived surface lower theorem as the raw energy certificate. -/
def toRawCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.TriangulatedRawEnergyCertificate data) :
    Prepared.RawCertificate data :=
  certificate.toRawSurfaceLowerCertificate.toRawCertificate

end TriangulatedRawEnergyCertificate

set_option genInjectivity false in
/-- One genus-one unit-differential triangulation with its positive lower energy distributed across an arbitrary finite
bank of faces. Unlike the selected-face interface below, this records the genuinely local situation in which several
triangles jointly carry the reference-box energy. -/
structure
  GenusOneUnitDistributedTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The retained finite number of oriented triangle faces. -/ faceCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The retained primitive pair at each original triangulation vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- The retained rational energy lower bound assigned to each original oriented face. -/ faceLower : Fin faceCount ->
    Fraction.Rational
  /-- The finite sum of retained face lower bounds dominates the full unit reference energy. -/
    unit_energy_le_faceLowerSum :
    Prepared.genusOneRawEnergy curve <=
      FiniteSum.Fin.sumFin faceLower
  /-- Each retained face lower bound is bounded by the energy of that same oriented primitive triangle. -/
    face_energy_lower : forall face : Fin faceCount,
    faceLower face <= AffineTriangle.triangleEnergy primitive (triangulation.faces face)

constructive_injectivity GenusOneUnitDistributedTriangulatedSurfaceSample

namespace GenusOneUnitDistributedTriangulatedSurfaceSample

/-- Exact cancellation of internal oriented edges identifies the sum of all face energies with the displayed
unit-differential period pairing. -/
theorem
  triangleEnergySum_eq_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex)
        :
    FiniteSum.Fin.sumFin (fun face =>
        Purelib.Integration.Energy.AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  let coefficients := Energy.genusOneUnitCoefficients
  let aPeriods := Energy.periodCombination coefficients
    (sampledMatrix data.aMatrix sampleIndex)
  let bPeriods := Energy.periodCombination coefficients
    (sampledMatrix data.bMatrix sampleIndex)
  calc
    FiniteSum.Fin.sumFin (fun face =>
        AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face)) =
        (Stokes.triangleWedgeSum sample.primitive
          sample.triangulation.faces).im / 4 := by
      unfold AffineTriangle.triangleEnergy Stokes.triangleWedgeSum
      rw [Energy.sumFin_im]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      exact FiniteSum.Fin.sumFin_mul_right
        (fun face =>
          (Stokes.triangleWedgeArea
            (sample.primitive (sample.triangulation.faces face).first)
            (sample.primitive (sample.triangulation.faces face).second)
            (sample.primitive
              (sample.triangulation.faces face).third)).im)
        ((4 : Fraction.Rational)⁻¹)
    _ = (Stokes.edgeListArea sample.primitive
          sample.triangulation.boundary).im / 4 := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = (Polygon.energyBoundaryArea aPeriods bPeriods).im / 4 := by
      rw [sample.boundary_matches]
    _ = Energy.periodPairingEnergy aPeriods bPeriods :=
      (Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four aPeriods bPeriods).symm
    _ = Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := rfl

/-- The retained local face bounds and exact incidence bound the unit reference energy by the sampled raw period
pairing. -/
theorem
  unitEnergy_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex)
        :
    Prepared.genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.unit_energy_le_faceLowerSum.trans
    ((Order.Positivity.sumFin_mono sample.faceLower
      (fun face =>
        AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face))
      sample.face_energy_lower).trans_eq sample.triangleEnergySum_eq_raw)

end GenusOneUnitDistributedTriangulatedSurfaceSample

namespace GenusOneCanonicalFaceLowerCertificate

/-- The explicit commutator boundary is the unit coefficient combination of the two sampled genus-one period entries. -/
theorem
  commutatorBoundary_matches
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) :
    Stokes.edgeListArea
        (Triangulation.genusOneCommutatorPrimitive
          (Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
          (Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
        Triangulation.genusOneCommutatorTriangulation.boundary =
      Purelib.Integration.Energy.Polygon.energyBoundaryArea
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex)) := by
  rw [Triangulation.genusOneCommutatorTriangulation_boundaryArea]
  unfold Polygon.energyBoundaryArea
  rw [FiniteSum.Fin.sumFin_succ,
    Energy.periodCombination_genusOne_unit,
    Energy.periodCombination_genusOne_unit]
  change _ = _ + 0
  rw [Data.Gaussian.Basic.add_zero]

/-- Two identical half-energy lower entries sum to the full reference energy. -/
theorem
  unitEnergy_le_halfFaceLowerSum
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1} :
    Prepared.genusOneRawEnergy curve <=
      FiniteSum.Fin.sumFin (fun _ : Fin 2 =>
        Prepared.genusOneRawEnergy curve / 2) := by
  rw [FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ]
  change Prepared.genusOneRawEnergy curve <=
    Prepared.genusOneRawEnergy curve / 2 +
      (Prepared.genusOneRawEnergy curve / 2 + 0)
  rw [_root_.add_zero]
  apply le_of_eq
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  calc
    Prepared.genusOneRawEnergy curve =
        Prepared.genusOneRawEnergy curve *
          ((2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹) := by
      rw [show (2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹ = 1 by decide]
      ring1
    _ = Prepared.genusOneRawEnergy curve * 2⁻¹ +
        Prepared.genusOneRawEnergy curve * 2⁻¹ := by
      ring1

/-- The one independent canonical face bound supplies both oriented faces of the explicit commutator triangulation. -/
theorem
  halfFaceLower_le_triangleEnergy
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) (face : Fin 2) :
    Prepared.genusOneRawEnergy curve / 2 <=
      AffineTriangle.triangleEnergy
        (Triangulation.genusOneCommutatorPrimitive
          (Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
          (Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
        (Triangulation.genusOneCommutatorTriangulation.faces face) := by
  rcases face with ⟨value, bound⟩
  cases value with
  | zero =>
      change Prepared.genusOneRawEnergy curve / 2 <=
        AffineTriangle.triangleEnergy
          (Triangulation.genusOneCommutatorPrimitive
            (Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
            (Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
          (Triangulation.genusOneCommutatorTriangulation.faces (0 : Fin 2))
      rw [Triangulation.genusOneCommutatorFirstFaceEnergy]
      exact certificate.lower sampleIndex
  | succ value =>
      cases value with
      | zero =>
          change Prepared.genusOneRawEnergy curve / 2 <=
            AffineTriangle.triangleEnergy
              (Triangulation.genusOneCommutatorPrimitive
                (Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
                (Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0)))
              (Triangulation.genusOneCommutatorTriangulation.faces (1 : Fin 2))
          rw [Triangulation.genusOneCommutatorSecondFaceEnergy]
          have secondLower :
              Prepared.genusOneRawEnergy curve / 2 <=
                Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitSecondTriangleEnergy data sampleIndex := by
            rw [← Curves.Hyperelliptic.Integration.Surface.Energy.genusOneUnitFirstTriangleEnergy_eq_second data
              sampleIndex]
            exact certificate.lower sampleIndex
          exact secondLower
      | succ value =>
          exact False.elim
            (Nat.not_lt_zero value
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

/-- Realize the canonical half-face certificate on the explicit two-triangle commutator mesh. Each face receives exactly
half of the checked reference energy, so the distributed lower sum is the full unit energy. -/
def
  toDistributedTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex
      where
    vertexCount := 4
    faceCount := 2
    triangulation := Triangulation.genusOneCommutatorTriangulation
    primitive := Triangulation.genusOneCommutatorPrimitive
      (Polygon.energyPrimitivePoint (sampledMatrix data.aMatrix sampleIndex 0 0))
      (Polygon.energyPrimitivePoint (sampledMatrix data.bMatrix sampleIndex 0 0))
    boundary_matches :=
      commutatorBoundary_matches
      data sampleIndex
    faceLower := fun _ =>
      Prepared.genusOneRawEnergy curve / 2
    unit_energy_le_faceLowerSum :=
      unitEnergy_le_halfFaceLowerSum
    face_energy_lower :=
      certificate.halfFaceLower_le_triangleEnergy sampleIndex

/-- The canonical two-face mesh derives the same unit surface theorem through actual finite incidence, rather than
bypassing the triangulation algebra. -/
theorem
  unitEnergy_le_raw_via_commutatorTriangulation
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data)
    (sampleIndex : Nat) :
    Prepared.genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample.unitEnergy_le_raw
    (certificate.toDistributedTriangulatedSurfaceSample sampleIndex)

end GenusOneCanonicalFaceLowerCertificate

set_option genInjectivity false in
/-- One genus-one unit-differential triangulation. Its number of triangles is independent of the single reference box:
one selected face dominates that box's positive lower energy, while every other oriented face is nonnegative. -/
structure GenusOneUnitTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The retained finite number of oriented triangle faces. -/ faceCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The retained primitive pair at each original triangulation vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- Every original oriented primitive triangle has nonnegative energy. -/ face_energy_nonnegative : forall face : Fin
    faceCount,
    0 <= AffineTriangle.triangleEnergy primitive (triangulation.faces face)
  /-- The retained original face that carries the unit reference energy lower bound. -/ positiveFace : Fin faceCount
  /-- The selected original primitive triangle dominates the unit reference energy. -/ unit_energy_le_face :
    Prepared.genusOneRawEnergy curve <=
    AffineTriangle.triangleEnergy primitive (triangulation.faces positiveFace)

constructive_injectivity GenusOneUnitTriangulatedSurfaceSample

namespace GenusOneUnitTriangulatedSurfaceSample

/-- View the selected-face presentation as a distributed lower certificate: the selected face receives the full
reference lower and every other face receives zero. -/
def
  toDistributedTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex
      where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  faceLower := fun face =>
    if face = sample.positiveFace then
      Prepared.genusOneRawEnergy curve
    else 0
  unit_energy_le_faceLowerSum := by
    rw [FiniteSum.Fin.sumFin_ite_eq]
  face_energy_lower := by
    intro face
    by_cases equal : face = sample.positiveFace
    · rw [if_pos equal, equal]
      exact sample.unit_energy_le_face
    · rw [if_neg equal]
      exact sample.face_energy_nonnegative face

/-- Exact incidence cancellation identifies the whole oriented triangle bank with the unit-differential raw period
energy. -/
theorem
  triangleEnergySum_eq_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    FiniteSum.Fin.sumFin (fun face =>
        AffineTriangle.triangleEnergy sample.primitive (sample.triangulation.faces face)) =
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=

    GenusOneUnitDistributedTriangulatedSurfaceSample.triangleEnergySum_eq_raw
    sample.toDistributedTriangulatedSurfaceSample

/-- The retained local face bounds and exact incidence bound the unit reference energy by the sampled raw period
pairing. -/
theorem
  unitEnergy_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceSample data sampleIndex) :
    Prepared.genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceSample.unitEnergy_le_raw
    sample.toDistributedTriangulatedSurfaceSample

end GenusOneUnitTriangulatedSurfaceSample

set_option genInjectivity false in
/-- Affine local presentation of one genus-one unit surface. Every face is an explicitly oriented rational coordinate
triangle carrying one rational constant differential model. Nonnegativity and the selected positive-face lower bound are
transported to primitive energy by the exact affine Jacobian theorem. -/
structure GenusOneUnitAffineTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The retained finite number of oriented triangle faces. -/ faceCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The retained Gaussian rational coordinate of each original triangulation vertex. -/ coordinate : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained primitive pair at each original triangulation vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- The retained constant Gaussian differential coefficient for each original face. -/ faceCoefficient : Fin faceCount
    -> Data.Gaussian.Basic.Canonical
  /-- The first primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_first :
    forall face : Fin faceCount,
    primitive (triangulation.faces face).first =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).first)
  /-- The second primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_second :
    forall face : Fin faceCount,
    primitive (triangulation.faces face).second =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).second)
  /-- The third primitive vertex equals this face coefficient applied to its original coordinate. -/ primitive_third :
    forall face : Fin faceCount,
    primitive (triangulation.faces face).third =
      AffineTriangle.affineEnergyPrimitive (faceCoefficient face)
        (coordinate (triangulation.faces face).third)
  /-- Every original coordinate triangle has nonnegative oriented area. -/ face_area_nonnegative : forall face : Fin
    faceCount,
    0 <= AffineTriangle.coordinateTriangleArea
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
  /-- The retained original face that carries the unit reference energy lower bound. -/ positiveFace : Fin faceCount
  /-- The selected face coordinate area times its coefficient squared norm dominates the unit reference energy. -/
    unit_energy_le_affine_face :
    Prepared.genusOneRawEnergy curve <=
      AffineTriangle.coordinateTriangleArea
          (coordinate (triangulation.faces positiveFace).first)
          (coordinate (triangulation.faces positiveFace).second)
          (coordinate (triangulation.faces positiveFace).third) *
        Data.Gaussian.Norm.Basic.normSq
          (faceCoefficient positiveFace)

constructive_injectivity GenusOneUnitAffineTriangulatedSurfaceSample

namespace GenusOneUnitAffineTriangulatedSurfaceSample

/-- Every original oriented primitive triangle has nonnegative energy. -/
theorem
  face_energy_nonnegative
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitAffineTriangulatedSurfaceSample data
      sampleIndex)
    (face : Fin sample.faceCount) :
    0 <= Purelib.Integration.Energy.AffineTriangle.triangleEnergy sample.primitive
      (sample.triangulation.faces face) := by
  let triangle := sample.triangulation.faces face
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient face
  calc
    0 <= AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (sample.face_area_nonnegative face)
        (Data.Gaussian.Norm.Basic.normSq_nonneg coefficient)
    _ = AffineTriangle.primitiveTriangleEnergy
          (AffineTriangle.affineEnergyPrimitive coefficient first)
          (AffineTriangle.affineEnergyPrimitive coefficient second)
          (AffineTriangle.affineEnergyPrimitive coefficient third) :=
      (AffineTriangle.affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = AffineTriangle.triangleEnergy sample.primitive
          (sample.triangulation.faces face) := by
      unfold AffineTriangle.triangleEnergy AffineTriangle.primitiveTriangleEnergy
      rw [sample.primitive_first face, sample.primitive_second face,
        sample.primitive_third face]

/-- The selected original primitive triangle dominates the unit reference energy. -/
theorem
  unit_energy_le_face
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitAffineTriangulatedSurfaceSample data
      sampleIndex) :
    Prepared.genusOneRawEnergy curve <=
      Purelib.Integration.Energy.AffineTriangle.triangleEnergy sample.primitive
        (sample.triangulation.faces sample.positiveFace) := by
  let triangle := sample.triangulation.faces sample.positiveFace
  let first := sample.coordinate triangle.first
  let second := sample.coordinate triangle.second
  let third := sample.coordinate triangle.third
  let coefficient := sample.faceCoefficient sample.positiveFace
  calc
    Prepared.genusOneRawEnergy curve <=
        AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient :=
      sample.unit_energy_le_affine_face
    _ = AffineTriangle.primitiveTriangleEnergy
          (AffineTriangle.affineEnergyPrimitive coefficient first)
          (AffineTriangle.affineEnergyPrimitive coefficient second)
          (AffineTriangle.affineEnergyPrimitive coefficient third) :=
      (AffineTriangle.affinePrimitiveTriangleEnergy_eq coefficient first second third).symm
    _ = AffineTriangle.triangleEnergy sample.primitive
          (sample.triangulation.faces sample.positiveFace) := by
      unfold AffineTriangle.triangleEnergy AffineTriangle.primitiveTriangleEnergy
      rw [sample.primitive_first sample.positiveFace,
        sample.primitive_second sample.positiveFace,
        sample.primitive_third sample.positiveFace]

/-- Retain the original triangulation and primitive vertices after deriving their face bounds from the affine model. -/
def
  toUnitTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitAffineTriangulatedSurfaceSample data
      sampleIndex) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceSample data sampleIndex where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := sample.primitive
  boundary_matches := sample.boundary_matches
  face_energy_nonnegative := sample.face_energy_nonnegative
  positiveFace := sample.positiveFace
  unit_energy_le_face := sample.unit_energy_le_face

/-- The retained local face bounds and exact incidence bound the unit reference energy by the sampled raw period
pairing. -/
theorem
  unitEnergy_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitAffineTriangulatedSurfaceSample data
      sampleIndex) :
    Prepared.genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toUnitTriangulatedSurfaceSample.unitEnergy_le_raw

end GenusOneUnitAffineTriangulatedSurfaceSample

set_option genInjectivity false in
/-- Error-controlled affine presentation of one genus-one unit surface. Primitive vertices may differ from their local
affine models; each face pays the resulting three-term square budget. -/
structure
  GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (sampleIndex : Nat) where
  /-- The retained finite number of triangulation vertices. -/ vertexCount : Nat
  /-- The retained finite number of oriented triangle faces. -/ faceCount : Nat
  /-- The original finite oriented triangle incidence with its exact boundary cancellation. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The retained Gaussian rational coordinate of each original triangulation vertex. -/ coordinate : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained Gaussian primitive value at each original triangulation vertex. -/ primitiveValue : Fin vertexCount
    -> Data.Gaussian.Basic.Canonical
  /-- The original oriented boundary area is exactly the period-combination boundary area at this sample. -/
    boundary_matches :
    Stokes.edgeListArea
        (fun vertex => Polygon.energyPrimitivePoint (primitiveValue vertex))
        triangulation.boundary =
      Polygon.energyBoundaryArea
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.aMatrix sampleIndex))
        (Energy.periodCombination
          Energy.genusOneUnitCoefficients
          (sampledMatrix data.bMatrix sampleIndex))
  /-- The retained constant Gaussian differential coefficient for each original face. -/ faceCoefficient : Fin faceCount
    -> Data.Gaussian.Basic.Canonical
  /-- The retained comparison certificate for the three original primitive vertices and their local affine model. -/
    faceError : forall face : Fin faceCount,
    AffineTriangle.AffineTriangleErrorCertificate (faceCoefficient face)
      (coordinate (triangulation.faces face).first)
      (coordinate (triangulation.faces face).second)
      (coordinate (triangulation.faces face).third)
      (primitiveValue (triangulation.faces face).first)
      (primitiveValue (triangulation.faces face).second)
      (primitiveValue (triangulation.faces face).third)
  /-- Each original face affine energy pays its full retained primitive comparison budget. -/ face_error_le_affine :
    forall face : Fin faceCount,
    (faceError face).totalBudget <=
      AffineTriangle.coordinateTriangleArea
          (coordinate (triangulation.faces face).first)
          (coordinate (triangulation.faces face).second)
          (coordinate (triangulation.faces face).third) *
        Data.Gaussian.Norm.Basic.normSq (faceCoefficient face)
  /-- The retained original face that carries the unit reference energy lower bound. -/ positiveFace : Fin faceCount
  /-- The selected affine face pays both the unit reference energy and its retained primitive comparison budget. -/
    unit_energy_add_error_le_affine :
    Prepared.genusOneRawEnergy curve +
        (faceError positiveFace).totalBudget <=
      AffineTriangle.coordinateTriangleArea
          (coordinate (triangulation.faces positiveFace).first)
          (coordinate (triangulation.faces positiveFace).second)
          (coordinate (triangulation.faces positiveFace).third) *
        Data.Gaussian.Norm.Basic.normSq
          (faceCoefficient positiveFace)

constructive_injectivity GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample

namespace GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample

/-- Every original oriented primitive triangle has nonnegative energy. -/
theorem
  face_energy_nonnegative
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex)
    (face : Fin sample.faceCount) :
    0 <= AffineTriangle.triangleEnergy
      (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
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
    0 <= AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient -
            error.totalBudget :=
      Fraction.Order.Arithmetic.sub_nonneg_direct
        (sample.face_error_le_affine face)
    _ <= AffineTriangle.primitiveTriangleEnergy
          (Polygon.energyPrimitivePoint primitiveFirst)
          (Polygon.energyPrimitivePoint primitiveSecond)
          (Polygon.energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = AffineTriangle.triangleEnergy
          (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces face) := rfl

/-- The selected original primitive triangle dominates the unit reference energy. -/
theorem
  unit_energy_le_face
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    Prepared.genusOneRawEnergy curve <=
      AffineTriangle.triangleEnergy
        (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
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
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    sample.unit_energy_add_error_le_affine (-error.totalBudget)
  calc
    Prepared.genusOneRawEnergy curve =
        (Prepared.genusOneRawEnergy curve +
          error.totalBudget) + -error.totalBudget := by ring1
    _ <= AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient +
            -error.totalBudget := shifted
    _ = AffineTriangle.coordinateTriangleArea first second third *
          Data.Gaussian.Norm.Basic.normSq coefficient -
            error.totalBudget := by ring1
    _ <= AffineTriangle.primitiveTriangleEnergy
          (Polygon.energyPrimitivePoint primitiveFirst)
          (Polygon.energyPrimitivePoint primitiveSecond)
          (Polygon.energyPrimitivePoint primitiveThird) :=
      error.affineEnergy_sub_totalBudget_le
    _ = AffineTriangle.triangleEnergy
          (fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex))
          (sample.triangulation.faces sample.positiveFace) := rfl

/-- Retain the original triangulation and primitive vertices after deriving their face bounds from the affine model. -/
def
  toUnitTriangulatedSurfaceSample
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceSample data sampleIndex where
  vertexCount := sample.vertexCount
  faceCount := sample.faceCount
  triangulation := sample.triangulation
  primitive := fun vertex => Polygon.energyPrimitivePoint (sample.primitiveValue vertex)
  boundary_matches := sample.boundary_matches
  face_energy_nonnegative := sample.face_energy_nonnegative
  positiveFace := sample.positiveFace
  unit_energy_le_face := sample.unit_energy_le_face

/-- The retained local face bounds and exact incidence bound the unit reference energy by the sampled raw period
pairing. -/
theorem
  unitEnergy_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} {sampleIndex : Nat}
    (sample :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
        sampleIndex) :
    Prepared.genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) :=
  sample.toUnitTriangulatedSurfaceSample.unitEnergy_le_raw

end GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample

set_option genInjectivity false in
/-- A distributed triangulated unit surface at every synchronized genus-one sample. This is the certificate-level form
of the exact two-dimensional surface assembly. -/
structure
  GenusOneUnitDistributedTriangulatedSurfaceCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At every synchronized sample, retain the original triangulated unit surface with distributed face lower bounds. -/
    sample : forall sampleIndex : Nat,
    GenusOneUnitDistributedTriangulatedSurfaceSample data sampleIndex

constructive_injectivity GenusOneUnitDistributedTriangulatedSurfaceCertificate

namespace GenusOneUnitDistributedTriangulatedSurfaceCertificate

/-- Package the derived unit surface inequality at every synchronized sample. -/
theorem
  toUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceCertificate data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitDistributedTriangulatedSurfaceCertificate

namespace GenusOneCanonicalFaceLowerCertificate

/-- Package the canonical two-face commutator construction at every sample. -/
def
  toDistributedTriangulatedSurfaceCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data) :
    Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitDistributedTriangulatedSurfaceCertificate data where
  sample := certificate.toDistributedTriangulatedSurfaceSample

/-- Certificate-level route from the independent half-face bound through the explicit finite commutator triangulation to
the unit surface lower theorem. -/
theorem
  toUnitSurfaceLowerCertificate_via_commutatorTriangulation
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneCanonicalFaceLowerCertificate data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data :=

    GenusOneUnitDistributedTriangulatedSurfaceCertificate.toUnitSurfaceLowerCertificate
    certificate.toDistributedTriangulatedSurfaceCertificate

end GenusOneCanonicalFaceLowerCertificate

set_option genInjectivity false in
/-- The reduced genus-one surface input with a genuine triangulated witness at every synchronized sample of the standard
unit differential. -/
structure GenusOneUnitTriangulatedSurfaceCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At every synchronized sample, retain a triangulated unit surface with one selected positive face. -/ sample :
    forall sampleIndex : Nat,
    GenusOneUnitTriangulatedSurfaceSample data sampleIndex

constructive_injectivity GenusOneUnitTriangulatedSurfaceCertificate

namespace GenusOneUnitTriangulatedSurfaceCertificate

/-- Package the derived unit surface inequality at every synchronized sample. -/
theorem
  toUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitTriangulatedSurfaceCertificate data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitTriangulatedSurfaceCertificate

set_option genInjectivity false in
/-- The reduced genus-one surface input with affine local differential models on every oriented triangle at every
synchronized sample. -/
structure
  GenusOneUnitAffineTriangulatedSurfaceCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At every synchronized sample, retain the affine coordinate models and selected positive face on the original
    triangulation. -/ sample : forall sampleIndex : Nat,
    GenusOneUnitAffineTriangulatedSurfaceSample data sampleIndex

constructive_injectivity GenusOneUnitAffineTriangulatedSurfaceCertificate

namespace GenusOneUnitAffineTriangulatedSurfaceCertificate

/-- Package the derived unit surface inequality at every synchronized sample. -/
theorem
  toUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitAffineTriangulatedSurfaceCertificate
      data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitAffineTriangulatedSurfaceCertificate

set_option genInjectivity false in
/-- Genus-one unit surface whose finite primitive vertices are compared with local affine models through explicit
rational error budgets. -/
structure
  GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At every synchronized sample, retain the original affine face models and their paid primitive comparison budgets.
  -/
  sample : forall sampleIndex : Nat,
    GenusOneUnitErrorControlledAffineTriangulatedSurfaceSample data
      sampleIndex

constructive_injectivity GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate

namespace GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate

/-- Package the derived unit surface inequality at every synchronized sample. -/
theorem
  toUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate :
      Curves.Hyperelliptic.Integration.Surface.Energy.GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
        data) :
    Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.sample sampleIndex).unitEnergy_le_raw

end GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate

end Purelib.Curves.Hyperelliptic.Integration.Surface.Energy

end
