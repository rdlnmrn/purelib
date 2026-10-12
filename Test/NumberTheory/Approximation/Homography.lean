module

import Purelib.NumberTheory.Approximation.Best.Error.Homography

/-!
# Nonaffine transport of an approximation pair

The integral determinant-one matrix changes both pair coordinates and the
source. Its denominator correction is nonzero, and the transformed error
has the exact rational factor supplied by the public transport theorem.
-/

namespace Test.NumberTheory.Approximation.Homography

open Purelib.Data
open Purelib.Data.Rat.Fraction
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2
open Purelib.NumberTheory.Approximation.Best

/-- An integral nonaffine homography with determinant one. -/
private def matrix : Matrix GaussianInt := ⟨1, 2, 1, 3⟩

/-- The exact rational source away from the homographic pole. -/
private def source : Gaussian.Basic.Canonical := ⟨1, 1⟩

/-- A displayed pair with nonzero approximation error at the source. -/
private def pair : ConvergentPair where
  numerator := ⟨2, 1⟩
  denominator := ⟨1, -1⟩

/-- The integral transformation has its required exact determinant. -/
private theorem unitDeterminant : matrix.determinant = 1 := by decide

/-- The source avoids the affine pole with denominator four plus the imaginary unit. -/
private theorem sourceDenominator :
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source =
      (⟨4, 1⟩ : Gaussian.Basic.Canonical) := by decide

/-- The nonzero affine denominator supplies the original public homography certificate. -/
private theorem denominatorNonzero :
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0 := by
  rewrite [sourceDenominator]
  decide

/-- The source and pair are transported in the same nonaffine coordinate convention. -/
private theorem transportedCoordinates :
    Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source =
        (⟨13 / 17, 1 / 17⟩ : Gaussian.Basic.Canonical) ∧
      pair.transform matrix =
        ({ numerator := ⟨4, -1⟩, denominator := ⟨5, -2⟩ } : ConvergentPair) := by
  constructor
  · decide
  · apply GaussianInt.Pair.LinearCombination.pair_ext <;> decide

/-- The adjugate recovers both original integral pair coordinates. -/
private theorem exactRoundTrip : (pair.transform matrix).transform matrix.adjugate = pair :=
  ConvergentPair.transform_adjugate_of_determinant_one matrix unitDeterminant pair

/-- The public error identity gives the exact cleared rational quadrance. -/
private theorem exactErrorPayment :
    Error.errorQuadrance
        (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (pair.transform matrix) * 17 = 1 := by
  have paid := Error.errorQuadrance_transform_of_determinant_one
    matrix unitDeterminant source pair denominatorNonzero
  have denominatorNorm : Gaussian.Norm.Basic.normSq
      (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source) = 17 := by
    rewrite [sourceDenominator]
    decide
  have originalError : Error.errorQuadrance source pair = 1 := by decide
  rewrite [denominatorNorm, originalError] at paid
  exact paid

/-- The source-dependent denominator correction has both retained original coordinates. -/
private theorem nonzeroDenominatorCorrection :
    GaussianInt.toGaussian matrix.c * Error.error source pair =
      (⟨0, -1⟩ : Gaussian.Basic.Canonical) := by decide

end Test.NumberTheory.Approximation.Homography
