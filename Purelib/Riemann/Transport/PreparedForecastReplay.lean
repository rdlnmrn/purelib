module
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Power.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Exact forecast recovery from saved constant-numerator readings

For exponent zero the point-error coefficient vanishes.  Consequently the
already saved reading target and prepared root diameter determine the exact
root-error coefficient.  Numerical diagnostics can recover the canonical
forecast without reconstructing owners or querying coefficient processes.
This identity does not supply missing ownership proofs for disk artifacts.
-/

namespace Purelib.Riemann.Transport.PreparedForecastReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Topology
open Purelib.Riemann.Integration
open Purelib.Riemann.Branches

section
open Purelib.Data
/-- The exact rational carrier of the forecast and reading bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The exact Gaussian rational carrier of the segment endpoints. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Geometry.Rational (Box) in
/-- The rational box type of the retained prepared root. -/
abbrev Box := Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian.Norm in
/-- Compute the root forecast from segment displacement, root diameter and saved reading target. -/
def fromReading (start finish : Gaussian) (rootBox : Box) (readingTarget : Coordinate) : Coordinate :=
  Basic.normSq (finish - start) *
    (64 * (8 * readingTarget / rootBox.diagonalSq))

open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat in
/-- Cross multiplication recovers the forecast numerator when the root diameter is nonzero. -/
theorem fromReading_mul_diameter (start finish : Gaussian) (rootBox : Box)
    (readingTarget : Coordinate) (nonzero : rootBox.diagonalSq ≠ 0) :
    fromReading start finish rootBox readingTarget * rootBox.diagonalSq =
      Basic.normSq (finish - start) * (64 * (8 * readingTarget)) := by
  unfold fromReading
  calc
    _ = Basic.normSq (finish - start) *
        (64 * ((8 * readingTarget / rootBox.diagonalSq) * rootBox.diagonalSq)) := by ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ nonzero]

set_option genInjectivity false in
/-- A failed forecast check with its exact numerical obstruction. -/
inductive Invalidity where
  /-- The retained squared root diameter is not positive. -/ | diameter (value : Coordinate) (failed : ¬ 0 < value)
  /-- The checked cross products are unequal. -/ | identity (left right : Coordinate) (failed : left ≠ right)

constructive_injectivity Invalidity

open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat in
/-- Check a persisted forecast term by exact cross multiplication.

Success retains equality to the numerical forecast formula; invalidity identifies a nonpositive diameter or unequal
products. -/
def check (start finish : Gaussian) (rootBox : Box) (readingTarget value : Coordinate) :
    Except Invalidity { result : Coordinate // result = fromReading start finish rootBox readingTarget } :=
  if positive : 0 < rootBox.diagonalSq then
    let left := value * rootBox.diagonalSq
    let right := Basic.normSq (finish - start) * (64 * (8 * readingTarget))
    if identity : left = right then
      .ok ⟨value, Fraction.Field.mul_right_cancel_of_ne positive.ne'
        (identity.trans (fromReading_mul_diameter start finish rootBox readingTarget positive.ne').symm)⟩
    else .error (.identity left right identity)
  else .error (.diameter rootBox.diagonalSq positive)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Gaussian.Norm in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Stationary reserved transport preserves the original owner's initial root box. -/
private theorem sameTransport_box {source target : Gaussian}
    (owner : SquareRootContinuationChain.Owner source) (nonzero : target ≠ 0)
    (small : Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (reserve : Coordinate) (same : source = target) :
    (ExactQuadraticOwnerClearance.reservedTransport owner nonzero small reserve).track.initial.box =
      owner.track.initial.box := by
  subst target
  rw [ExactQuadraticOwnerClearance.reservedTransport, dif_pos rfl]

/-- The base-point query retains the original prepared owner's root box. -/
theorem baseQuery_box (edge : PreparedEdge curve differential) :
    (edge.directQueryOwner 0 edge.baseInside).track.initial.box =
      edge.cached.preparedOwner.track.initial.box := by
  unfold PreparedEdge.directQueryOwner
  apply sameTransport_box
  rw [PreparedSheetContinuation.parameterAt_zero]

open Purelib.Data.Gaussian.Power.Bounds in
open Purelib.Data.Rat in
/-- A differential of exponent zero has zero prepared point-error coefficient. -/
theorem pointCoefficient_zero (edge : PreparedEdge curve differential)
    (exponent : differential.exponent = 0) : edge.preparedPointErrorCoefficient = 0 := by
  simp only [PreparedEdge.preparedPointErrorCoefficient, exponent,
    IntegrationQuotientVariation.powerSlope, ApproximationQuotientVariation.powerSlope,
    zero_mul, mul_zero, Fraction.Field.zero_div_direct, -eq_self, -iff_self]
  try rfl

open Purelib.Data.Rat in
/-- For exponent zero, the reading target and prepared diameter determine the root-error coefficient. -/
theorem rootCoefficient_fromReading (edge : PreparedEdge curve differential)
    (exponent : differential.exponent = 0) :
    8 * edge.readingTarget / edge.preparedRootDiameter = edge.preparedRootErrorCoefficient := by
  have reading : edge.readingTarget =
      (edge.preparedRootErrorCoefficient * edge.preparedRootDiameter) / 8 := by
    rw [PreparedEdge.readingTarget, edge.modelErrorAllowance_eq_preparedLinear,
      pointCoefficient_zero edge exponent, zero_mul, zero_add]
  rw [reading, mul_comm (8 : Coordinate), Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  rw [Fraction.Field.div_eq_mul_inv_direct, mul_assoc,
    Fraction.Field.mul_inv_cancel _ edge.preparedRootDiameter_positive.ne', mul_one]

open Purelib.Riemann in
/-- The saved-reading formula equals the canonical forecast for an exponent-zero differential.

The identity uses the actual prepared edge's endpoints, query root box and reading target. -/
theorem fromReading_eq_forecast (edge : PreparedEdge curve differential)
    (exponent : differential.exponent = 0) :
    fromReading (edge.point 0) (edge.point 1)
        (edge.directQueryOwner 0 edge.baseInside).track.initial.box edge.readingTarget =
      PreparedDirectDyadicRefinements.preparedEdgeForecast differential edge := by
  rw [fromReading, baseQuery_box]
  change edge.pointMovement * (64 * (8 * edge.readingTarget / edge.preparedRootDiameter)) = _
  rw [rootCoefficient_fromReading edge exponent,
    PreparedDirectDyadicRefinements.preparedEdgeForecast,
    Integration.PreparedEdgeRecasting.recastPreparedEdge_self,
    pointCoefficient_zero edge exponent, zero_add]

end Purelib.Riemann.Transport.PreparedForecastReplay
