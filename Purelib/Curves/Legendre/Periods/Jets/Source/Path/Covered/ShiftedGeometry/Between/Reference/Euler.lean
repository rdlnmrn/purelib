module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Tactic.Ring

/-! # Connection Euler defects on the same fixed-reference period readings

The internally derived quotient bounds pay the actual integral remainders.
The original jet source pays its connection residual at the same retained
sample index. The resulting Euler defect compares the independent matrix
step with the given source and target values, without an ODE admission.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Calculus.Linear
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale normSq_scale scale_mul_product)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector.Basic (zipWith_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ)
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Matrix.Multiplication
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}

/-- The original fixed-reference row factors determine one directional Euler factor before sampling. -/
@[expose] def referenceEulerFactor (direction : Canonical) : Rational :=
  2 * ((referenceFactor (covered := covered) 0 0 + referenceFactor (covered := covered) 0 1) *
    Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)

/-- The directional Euler factor is nonnegative for every retained original covered geometry. -/
theorem referenceEulerFactor_nonnegative (direction : Canonical) :
    0 ≤ referenceEulerFactor (covered := covered) direction :=
  mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
    ((Field.zero_add (0 : Rational)).symm.trans_le
      (add_le_add_direct
        (mul_nonneg_direct
          ((Field.zero_add (0 : Rational)).symm.trans_le
            (add_le_add_direct (referenceFactor_nonnegative (covered := covered) 0 0)
              (referenceFactor_nonnegative (covered := covered) 0 1)))
          (sq_nonneg_direct _))
        (mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2) (Norm.Basic.normSq_nonneg direction))))

/-- All-later reference quotient bounds and the same jet's source residual pay its actual local Euler defect.

The two given value vectors retain their original programme-model sample
readbacks. One original connection selection is paid at the same source
index as the quotient estimate. Scalar multiplication by the actual
nonzero increment recovers the finite integral remainder; the connection
residual then compares the symbolic slope to the independent matrix step.
-/
theorem QuotientBounds.eulerDefect_le
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {firstJet : SynchronizedPeriodJet firstFrame} {lastJet : SynchronizedPeriodJet lastFrame}
    {firstFloor lastFloor : Nat}
    (bounds : QuotientBounds covered firstJet lastJet firstFloor lastFloor)
    (width : Rational) (direction : Canonical)
    (scaled : lastOffset - firstOffset = scale width direction)
    (nonzero : lastOffset - firstOffset ≠ 0) (start firstIndex lastIndex : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame firstFrame).connectionLowerSq))
    (firstAfter : Nat.max firstFloor selection.stage ≤ firstIndex) (lastAfter : lastFloor ≤ lastIndex)
    (values outputs : Vec Canonical 2)
    (values_eq : ∀ coordinate, values coordinate =
      ((firstJet.value coordinate).integral.model firstIndex).integralSample)
    (outputs_eq : ∀ coordinate, outputs coordinate =
      ((lastJet.value coordinate).integral.model lastIndex).integralSample) :
    Norm.vector (Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs) ≤
      referenceEulerFactor (covered := covered) direction * width ^ 4 := by
  let increment := lastOffset - firstOffset
  have incrementNorm : Norm.Basic.normSq increment = width ^ 2 * Norm.Basic.normSq direction :=
    (congrArg Norm.Basic.normSq scaled).trans (normSq_scale width direction)
  have rows (row : Fin 2) :
      Norm.Basic.normSq
          (Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs row) ≤
        2 * (referenceFactor (covered := covered) 0 row * Norm.Basic.normSq direction ^ 2 +
          Norm.Basic.normSq direction) * width ^ 4 := by
    let slope := ((firstJet.first row).integral.model firstIndex).integralSample
    let error := (outputs row - values row) / increment - slope
    let remainder := outputs row - values row - increment * slope
    let acted := matrixVector (Connection.matrix (parameter + firstOffset)) values row
    have quotient := bounds 0 row firstIndex lastIndex
      ((Order.le_max_left firstFloor selection.stage).trans firstAfter) lastAfter
    change Canonical.normSq
      ((((lastJet.value row).integral.model lastIndex).integralSample -
        ((firstJet.value row).integral.model firstIndex).integralSample) / increment - slope) ≤
      referenceFactor (covered := covered) 0 row * Canonical.normSq increment at quotient
    have displayed := congrArg₂ (fun output base : Canonical =>
      Canonical.normSq ((output - base) / increment - slope)) (outputs_eq row) (values_eq row)
    have errorBound : Norm.Basic.normSq error ≤
        referenceFactor (covered := covered) 0 row * Norm.Basic.normSq increment :=
      ((Norm.Basic.normSq_eq_canonical error).trans displayed).trans_le
        (quotient.trans_eq (congrArg
          (fun quadrance : Rational => referenceFactor (covered := covered) 0 row * quadrance)
          (Norm.Basic.normSq_eq_canonical increment).symm))
    have multiplied : increment * error = remainder := by
      change increment * ((outputs row - values row) * increment⁻¹ - slope) = _
      calc
        _ = (increment * increment⁻¹) * (outputs row - values row) - increment * slope := by ring1
        _ = remainder := by
          rewrite [Canonical.mul_inv_cancel increment nonzero, Canonical.one_mul]
          rfl
    have remainderBound : Norm.Basic.normSq remainder ≤
        referenceFactor (covered := covered) 0 row * Norm.Basic.normSq direction ^ 2 * width ^ 4 :=
      (congrArg Norm.Basic.normSq multiplied).symm.trans_le
        ((Norm.Basic.normSq_mul _ _).trans_le
          ((mul_le_mul_of_nonneg_left_direct errorBound (Norm.Basic.normSq_nonneg increment)).trans_eq
            ((congrArg (fun quadrance : Rational => quadrance *
              (referenceFactor (covered := covered) 0 row * quadrance)) incrementNorm).trans (by ring1))))
    have slopeBound := Connection.sourceSlope_le firstJet width start firstIndex selection
      ((Order.le_max_right firstFloor selection.stage).trans firstAfter) values slope row values_eq rfl
    have movement : scale width (direction * acted) = increment * acted :=
      (scale_mul_product width direction acted).trans (congrArg (fun value : Canonical => value * acted) scaled.symm)
    have exactRow : Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction)
        width values outputs row = remainder + increment * (slope - acted) := by
      unfold Euler.defect
      rewrite [zipWith_apply, Euler.step_apply, Connection.alongMatrix_vector, movement]
      dsimp only [remainder]
      ring1
    have slopeContribution : Norm.Basic.normSq (increment * (slope - acted)) ≤
        Norm.Basic.normSq direction * width ^ 4 :=
      (Norm.Basic.normSq_mul _ _).trans_le
        ((mul_le_mul_of_nonneg_left_direct slopeBound (Norm.Basic.normSq_nonneg increment)).trans_eq
          ((congrArg (fun quadrance : Rational => quadrance * width ^ 2) incrementNorm).trans (by ring1)))
    exact (congrArg Norm.Basic.normSq exactRow).trans_le
      ((Norm.Bounds.normSq_add_le_two _ _).trans
        ((mul_le_mul_of_nonneg_left_direct (add_le_add_direct remainderBound slopeContribution)
          (by decide +kernel : (0 : Rational) ≤ 2)).trans_eq (by ring1)))
  have summed := add_le_add_direct (rows 0) (rows 1)
  have same : Norm.vector
      (Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs) =
      Norm.Basic.normSq
          (Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs 0) +
        Norm.Basic.normSq
          (Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs 1) := by
    unfold Norm.vector
    rewrite [sumFin_succ, sumFin_succ]
    let actual := Euler.defect (Connection.alongMatrix (parameter + firstOffset) direction) width values outputs
    change Norm.Basic.normSq (actual 0) + (Norm.Basic.normSq (actual 1) + 0) =
      Norm.Basic.normSq (actual 0) + Norm.Basic.normSq (actual 1)
    ring1
  exact same.trans_le (summed.trans_eq (by unfold referenceEulerFactor; ring1))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

end
