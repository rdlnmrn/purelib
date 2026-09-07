import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.Boxes
import mathlib.RFAP.ConstructivePolynomial
import mathlib.RFAP.ConstructiveGCD

/-!
# Finite dense-polynomial bounds over constructive Gaussian coordinates

The bounds in this module are propagated by folds over coefficient lists.  No
sparse polynomial, root set, completion, or infinite carrier is involved.
-/

namespace RFAP.PolynomialBounds

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

open RFAP.Boxes
open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

structure HornerNormBounds where
  value : Coordinate
  slope : Coordinate
deriving DecidableEq

def HornerNormBounds.step (radiusSq : Coordinate)
    (bounds : HornerNormBounds) (coefficient : Gaussian) : HornerNormBounds where
  value := 2 * (bounds.value * radiusSq + normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

def denseHornerNormBounds (p : GaussianPolynomial) (B : Box) :
    HornerNormBounds :=
  p.coeffs.foldl (HornerNormBounds.step B.normSqBound) ⟨0, 0⟩

def denseEvalNormBound (p : GaussianPolynomial) (B : Box) : Coordinate :=
  (denseHornerNormBounds p B).value

def denseEvalNormLipschitzBound (p : GaussianPolynomial) (B : Box) :
    Coordinate :=
  (denseHornerNormBounds p B).slope

def denseLipschitzBound (p : GaussianPolynomial) (B : Box) : Coordinate :=
  max 1 (denseEvalNormLipschitzBound p B)

/-- Positive finite majorant for the squared value norm. -/
def denseEvalNormMajorant (p : GaussianPolynomial) (B : Box) : Coordinate :=
  max 1 (denseEvalNormBound p B)

private theorem twice_nonneg {a : Coordinate} (ha : 0 ≤ a) : 0 ≤ 2 * a := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ a + a := add_le_add ha ha
    _ = 2 * a := by ring1

private theorem twice_le_twice {a b : Coordinate} (hab : a ≤ b) :
    2 * a ≤ 2 * b := by
  calc
    2 * a = a + a := by ring1
    _ ≤ b + b := add_le_add hab hab
    _ = 2 * b := by ring1

private theorem evalNormBoundsCoeffs_spec
    (coeffs : List Gaussian) {radiusSq : Coordinate} {x y : Gaussian}
    (hradius : 0 ≤ radiusSq)
    (hx : normSq x ≤ radiusSq) (hy : normSq y ≤ radiusSq)
    (accX accY : Gaussian) (bounds : HornerNormBounds)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (haccX : normSq accX ≤ bounds.value)
    (haccY : normSq accY ≤ bounds.value)
    (hdiff : normSq (accX - accY) ≤
      bounds.slope * normSq (x - y)) :
    let finalX := coeffs.foldl
      (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun acc coefficient => acc * y + coefficient) accY
    let finalBounds := coeffs.foldl
      (HornerNormBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      normSq finalX ≤ finalBounds.value ∧
      normSq finalY ≤ finalBounds.value ∧
      normSq (finalX - finalY) ≤
        finalBounds.slope * normSq (x - y) := by
  induction coeffs generalizing accX accY bounds with
  | nil => exact ⟨hvalue, hslope, haccX, haccY, hdiff⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct hvalue hradius)
          (normSq_nonneg coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct hslope hradius)
          hvalue
      · have hmul : normSq accX * normSq x ≤
            bounds.value * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct haccX hx
            (normSq_nonneg x) hvalue
        calc
          normSq (accX * x + coefficient) ≤
              2 * (normSq (accX * x) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accX * normSq x + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) :=
            twice_le_twice (add_le_add hmul (le_refl _))
      · have hmul : normSq accY * normSq y ≤
            bounds.value * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct haccY hy
            (normSq_nonneg y) hvalue
        calc
          normSq (accY * y + coefficient) ≤
              2 * (normSq (accY * y) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accY * normSq y + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) :=
            twice_le_twice (add_le_add hmul (le_refl _))
      · have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1
        rw [hidentity]
        have hfirst : normSq (accX - accY) * normSq x ≤
            (bounds.slope * normSq (x - y)) * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct hdiff hx
            (normSq_nonneg x)
            (RFAP.ConstructiveFraction.mul_nonneg_direct hslope
              (normSq_nonneg (x - y)))
        have hsecond : normSq accY * normSq (x - y) ≤
            bounds.value * normSq (x - y) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            haccY (normSq_nonneg (x - y))
        calc
          normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (normSq ((accX - accY) * x) +
                normSq (accY * (x - y))) := normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq x +
                normSq accY * normSq (x - y)) := by
            rw [normSq_mul, normSq_mul]
          _ ≤ 2 * ((bounds.slope * normSq (x - y)) * radiusSq +
                bounds.value * normSq (x - y)) :=
            twice_le_twice (add_le_add hfirst hsecond)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                normSq (x - y) := by ring1

theorem denseHornerNormBounds_nonneg (p : GaussianPolynomial) (B : Box) :
    0 ≤ denseEvalNormBound p B ∧
      0 ≤ denseEvalNormLipschitzBound p B := by
  have specification := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := 0) (y := 0)
    B.normSqBound_nonneg
    (by rw [normSq_zero]; exact B.normSqBound_nonneg)
    (by rw [normSq_zero]; exact B.normSqBound_nonneg)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [normSq_zero]) (by rw [normSq_zero])
    (by
      change (0 : Coordinate) ≤ 0 * normSq ((0 : Gaussian) - 0)
      have hproduct : (0 : Coordinate) * normSq ((0 : Gaussian) - 0) = 0 := by
        ring1
      rw [hproduct])
  exact ⟨specification.1, specification.2.1⟩

theorem normSq_eval_le_denseEvalNormBound
    (p : GaussianPolynomial) {B : Box} {z : Gaussian}
    (inside : B.Contains z) :
    normSq (p.eval z) ≤ denseEvalNormBound p B := by
  have specification := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := z)
    B.normSqBound_nonneg (B.normSq_le_normSqBound inside)
    (B.normSq_le_normSqBound inside)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [normSq_zero]) (by rw [normSq_zero])
    (by
      change (0 : Coordinate) ≤ 0 * normSq (z - z)
      have hproduct : (0 : Coordinate) * normSq (z - z) = 0 := by ring1
      rw [hproduct])
  simpa only [eval, evalCoeffs, denseEvalNormBound, denseHornerNormBounds]
    using specification.2.2.1

theorem normSq_eval_sub_eval_le
    (p : GaussianPolynomial) {B : Box} {z w : Gaussian}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    normSq (p.eval z - p.eval w) ≤
      denseEvalNormLipschitzBound p B * normSq (z - w) := by
  have specification := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := w)
    B.normSqBound_nonneg (B.normSq_le_normSqBound zInside)
    (B.normSq_le_normSqBound wInside)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [normSq_zero]) (by rw [normSq_zero])
    (by
      change (0 : Coordinate) ≤ 0 * normSq (z - w)
      have hproduct : (0 : Coordinate) * normSq (z - w) = 0 := by ring1
      rw [hproduct])
  simpa only [eval, evalCoeffs, denseEvalNormLipschitzBound,
    denseHornerNormBounds] using specification.2.2.2.2

theorem denseLipschitzBound_pos (p : GaussianPolynomial) (B : Box) :
    0 < denseLipschitzBound p B :=
  (by decide : (0 : Coordinate) < 1).trans_le (le_max_left _ _)

theorem denseEvalNormMajorant_pos (p : GaussianPolynomial) (B : Box) :
    0 < denseEvalNormMajorant p B :=
  (by decide : (0 : Coordinate) < 1).trans_le (le_max_left _ _)

theorem normSq_eval_le_denseEvalNormMajorant
    (p : GaussianPolynomial) {B : Box} {z : Gaussian}
    (inside : B.Contains z) :
    normSq (p.eval z) ≤ denseEvalNormMajorant p B :=
  (normSq_eval_le_denseEvalNormBound p inside).trans (le_max_right _ _)

theorem normSq_eval_sub_eval_le_denseLipschitzBound
    (p : GaussianPolynomial) {B : Box} {z w : Gaussian}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    normSq (p.eval z - p.eval w) ≤
      denseLipschitzBound p B * normSq (z - w) := by
  exact (normSq_eval_sub_eval_le p zInside wInside).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (le_max_right _ _) (normSq_nonneg (z - w)))

/-! ## Executable quadratic Taylor bounds -/

/-- Value, first-displacement, and quadratic-remainder coefficients propagated
by one finite Horner scan. -/
structure HornerTaylorNormBounds where
  value : Coordinate
  slope : Coordinate
  remainder : Coordinate
deriving DecidableEq

def HornerTaylorNormBounds.step (radiusSq : Coordinate)
    (bounds : HornerTaylorNormBounds) (coefficient : Gaussian) :
    HornerTaylorNormBounds where
  value := 2 * (bounds.value * radiusSq + normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)
  remainder := 2 * (bounds.slope + radiusSq * bounds.remainder)

def denseHornerTaylorNormBounds (p : GaussianPolynomial) (B : Box) :
    HornerTaylorNormBounds :=
  p.coeffs.foldl (HornerTaylorNormBounds.step B.normSqBound) ⟨0, 0, 0⟩

def denseEvalTaylorRemainderBound
    (p : GaussianPolynomial) (B : Box) : Coordinate :=
  (denseHornerTaylorNormBounds p B).remainder

def denseTaylorRemainderBound
    (p : GaussianPolynomial) (B : Box) : Coordinate :=
  max 1 (denseEvalTaylorRemainderBound p B)

private theorem evalTaylorNormBoundsCoeffs_spec
    (coeffs : List Gaussian) {radiusSq : Coordinate} {x y : Gaussian}
    (radiusNonnegative : 0 ≤ radiusSq)
    (xBound : normSq x ≤ radiusSq) (yBound : normSq y ≤ radiusSq)
    (accX accY derivativeY : Gaussian) (bounds : HornerTaylorNormBounds)
    (valueNonnegative : 0 ≤ bounds.value)
    (slopeNonnegative : 0 ≤ bounds.slope)
    (remainderNonnegative : 0 ≤ bounds.remainder)
    (accXBound : normSq accX ≤ bounds.value)
    (accYBound : normSq accY ≤ bounds.value)
    (differenceBound : normSq (accX - accY) ≤
      bounds.slope * normSq (x - y))
    (taylorBound : normSq
        (accX - accY - derivativeY * (x - y)) ≤
      bounds.remainder * normSq (x - y) ^ 2) :
    let finalX := coeffs.foldl
      (fun accumulator coefficient => accumulator * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun accumulator coefficient => accumulator * y + coefficient) accY
    let finalDerivativeY := coeffs.foldl
      (RFAP.ComputableDerivative.evalDerivativeStep y) (accY, derivativeY) |>.2
    let finalBounds := coeffs.foldl
      (HornerTaylorNormBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      0 ≤ finalBounds.remainder ∧
      normSq finalX ≤ finalBounds.value ∧
      normSq finalY ≤ finalBounds.value ∧
      normSq (finalX - finalY) ≤
        finalBounds.slope * normSq (x - y) ∧
      normSq (finalX - finalY - finalDerivativeY * (x - y)) ≤
        finalBounds.remainder * normSq (x - y) ^ 2 := by
  induction coeffs generalizing accX accY derivativeY bounds with
  | nil =>
      exact ⟨valueNonnegative, slopeNonnegative, remainderNonnegative,
        accXBound, accYBound, differenceBound, taylorBound⟩
  | cons coefficient coeffs inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            valueNonnegative radiusNonnegative)
          (normSq_nonneg coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            slopeNonnegative radiusNonnegative)
          valueNonnegative
      · apply twice_nonneg
        exact add_nonneg slopeNonnegative
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            radiusNonnegative remainderNonnegative)
      · have productBound : normSq accX * normSq x ≤
            bounds.value * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct accXBound xBound
            (normSq_nonneg x) valueNonnegative
        calc
          normSq (accX * x + coefficient) ≤
              2 * (normSq (accX * x) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accX * normSq x + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) :=
            twice_le_twice (add_le_add productBound (le_refl _))
      · have productBound : normSq accY * normSq y ≤
            bounds.value * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct accYBound yBound
            (normSq_nonneg y) valueNonnegative
        calc
          normSq (accY * y + coefficient) ≤
              2 * (normSq (accY * y) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accY * normSq y + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) :=
            twice_le_twice (add_le_add productBound (le_refl _))
      · have identity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1
        rw [identity]
        have firstProduct : normSq (accX - accY) * normSq x ≤
            (bounds.slope * normSq (x - y)) * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct differenceBound xBound
            (normSq_nonneg x)
            (RFAP.ConstructiveFraction.mul_nonneg_direct slopeNonnegative
              (normSq_nonneg (x - y)))
        have secondProduct : normSq accY * normSq (x - y) ≤
            bounds.value * normSq (x - y) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            accYBound (normSq_nonneg (x - y))
        calc
          normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (normSq ((accX - accY) * x) +
                normSq (accY * (x - y))) := normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq x +
                normSq accY * normSq (x - y)) := by
            rw [normSq_mul, normSq_mul]
          _ ≤ 2 * ((bounds.slope * normSq (x - y)) * radiusSq +
                bounds.value * normSq (x - y)) :=
            twice_le_twice (add_le_add firstProduct secondProduct)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                normSq (x - y) := by ring1
      · have identity :
            (accX * x + coefficient) - (accY * y + coefficient) -
                (derivativeY * y + accY) * (x - y) =
              (accX - accY) * (x - y) +
                (accX - accY - derivativeY * (x - y)) * y := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1
        rw [identity]
        have firstProduct :
            normSq (accX - accY) * normSq (x - y) ≤
              bounds.slope * normSq (x - y) ^ 2 := by
          calc
            normSq (accX - accY) * normSq (x - y) ≤
                (bounds.slope * normSq (x - y)) * normSq (x - y) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                differenceBound (normSq_nonneg (x - y))
            _ = bounds.slope * normSq (x - y) ^ 2 := by ring1
        have taylorProductNonnegative :
            0 ≤ bounds.remainder * normSq (x - y) ^ 2 :=
          RFAP.ConstructiveFraction.mul_nonneg_direct remainderNonnegative
            (RFAP.ConstructiveFraction.pow_nonneg_direct
              (normSq_nonneg (x - y)) 2)
        have secondProduct :
            normSq (accX - accY - derivativeY * (x - y)) * normSq y ≤
              (bounds.remainder * normSq (x - y) ^ 2) * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct taylorBound yBound
            (normSq_nonneg y) taylorProductNonnegative
        calc
          normSq ((accX - accY) * (x - y) +
              (accX - accY - derivativeY * (x - y)) * y) ≤
            2 * (normSq ((accX - accY) * (x - y)) +
              normSq ((accX - accY - derivativeY * (x - y)) * y)) :=
                normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq (x - y) +
              normSq (accX - accY - derivativeY * (x - y)) *
                normSq y) := by rw [normSq_mul, normSq_mul]
          _ ≤ 2 * (bounds.slope * normSq (x - y) ^ 2 +
              (bounds.remainder * normSq (x - y) ^ 2) * radiusSq) :=
            twice_le_twice (add_le_add firstProduct secondProduct)
          _ = 2 * (bounds.slope + radiusSq * bounds.remainder) *
              normSq (x - y) ^ 2 := by ring1

theorem denseHornerTaylorNormBounds_nonneg
    (p : GaussianPolynomial) (B : Box) :
    0 ≤ (denseHornerTaylorNormBounds p B).value ∧
      0 ≤ (denseHornerTaylorNormBounds p B).slope ∧
      0 ≤ denseEvalTaylorRemainderBound p B := by
  have specification := evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := 0) (y := 0)
    B.normSqBound_nonneg
    (by rw [normSq_zero]; exact B.normSqBound_nonneg)
    (by rw [normSq_zero]; exact B.normSqBound_nonneg)
    0 0 0 ⟨0, 0, 0⟩ (by decide) (by decide) (by decide)
    (by rw [normSq_zero]) (by rw [normSq_zero])
    (by
      change (0 : Coordinate) ≤ 0 * normSq ((0 : Gaussian) - 0)
      have product : (0 : Coordinate) * normSq ((0 : Gaussian) - 0) = 0 := by
        ring1
      rw [product])
    (by
      change (0 : Coordinate) ≤ 0 * normSq ((0 : Gaussian) - 0) ^ 2
      have product :
          (0 : Coordinate) * normSq ((0 : Gaussian) - 0) ^ 2 = 0 := by
        ring1
      rw [product])
  exact ⟨specification.1, specification.2.1, specification.2.2.1⟩

theorem normSq_dense_taylor_remainder_le
    (p : GaussianPolynomial) {B : Box} {z w : Gaussian}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    normSq (p.eval z - p.eval w -
        (RFAP.ConstructiveGCD.derivative p).eval w * (z - w)) ≤
      denseEvalTaylorRemainderBound p B * normSq (z - w) ^ 2 := by
  have specification := evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := w)
    B.normSqBound_nonneg (B.normSq_le_normSqBound zInside)
    (B.normSq_le_normSqBound wInside)
    0 0 0 ⟨0, 0, 0⟩ (by decide) (by decide) (by decide)
    (by rw [normSq_zero]) (by rw [normSq_zero])
    (by
      change (0 : Coordinate) ≤ 0 * normSq (z - w)
      have product : (0 : Coordinate) * normSq (z - w) = 0 := by ring1
      rw [product])
    (by
      have zeroError :
          (0 : Gaussian) - 0 - 0 * (z - w) = 0 := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, mul_re, mul_im, zero_re, zero_im] <;>
          ring1
      rw [zeroError, normSq_zero]
      change (0 : Coordinate) ≤ 0 * normSq (z - w) ^ 2
      have product : (0 : Coordinate) * normSq (z - w) ^ 2 = 0 := by ring1
      rw [product])
  have derivativeEvaluation :
      (p.coeffs.foldl (RFAP.ComputableDerivative.evalDerivativeStep w)
        (0, 0)).2 = (RFAP.ConstructiveGCD.derivative p).eval w := by
    exact (RFAP.ComputableDerivative.eval_derivative p w).symm
  rw [derivativeEvaluation] at specification
  simpa only [eval, evalCoeffs, denseEvalTaylorRemainderBound,
    denseHornerTaylorNormBounds] using specification.2.2.2.2.2.2

theorem denseTaylorRemainderBound_pos
    (p : GaussianPolynomial) (B : Box) :
    0 < denseTaylorRemainderBound p B :=
  (by decide : (0 : Coordinate) < 1).trans_le (le_max_left _ _)

theorem normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
    (p : GaussianPolynomial) {B : Box} {z w : Gaussian}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    normSq (p.eval z - p.eval w -
        (RFAP.ConstructiveGCD.derivative p).eval w * (z - w)) ≤
      denseTaylorRemainderBound p B * normSq (z - w) ^ 2 := by
  exact (normSq_dense_taylor_remainder_le p zInside wInside).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (le_max_right _ _)
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (normSq_nonneg (z - w)) 2))

end RFAP.PolynomialBounds
