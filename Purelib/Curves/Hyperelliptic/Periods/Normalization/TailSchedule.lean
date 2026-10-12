module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Integration.Observation.CurveRawCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound
import Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail
import Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.CurveRawRequest
import Purelib.Riemann.Readings.NamedMatrixActionBound
public import Purelib.Riemann.Readings.TailSynchronizedEnergy
import Purelib.Riemann.Topology.PreparedObservationSurface
public import Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveNormalizedEnergy
public import Purelib.Riemann.Readings.TailEnergyRadii
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Purelib.Riemann.Integration.ScalarTailLower

open Purelib.Curves

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! Automatic controlled normalized requests on the same retained raw period
bank as the inverse-tail certificate. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.TailSchedule

open Purelib.Curves.Hyperelliptic.Periods.Normalization
open Purelib.Riemann.Readings.TailEnergyRadii

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {bank :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve} {floor : Nat}
  (request : Readings.CurveRawRequest.PairedPeriodBank.RawRequest bank floor) (action :
    Hyperelliptic.Periods.Action.LowerBound.ActionLower request)
  (geometry : Topology.PreparedObservationSurface.ObservationBoxEnergy curve.polynomial genus)
  (aBound : Readings.NamedMatrixActionBound.UniformActionBound bank.periodData.aMatrix)

/-- Equality to the original action-derived tail, used only in certificates.
The executable schedule consumes the supplied physical tail. -/
@[expose, reducible] def SuppliedTailIdentity
    (inverseTail : Periods.PeriodMatrix.ScalarTailSeparationCertificate bank.periodData.aMatrix) : Prop :=
  inverseTail = (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate

/-- Construct the comparison radius and sample index from the supplied physical inverse tail and retained normalized
energy floor. -/
@[expose] def comparisonUsingTail (inverseTail : Periods.PeriodMatrix.ScalarTailSeparationCertificate
  bank.periodData.aMatrix)
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus) (nonzero :
      LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Readings.TailSynchronizedEnergy.TailComparisonSchedule bank.periodData inverseTail
      vector nonzero target positive :=
  let energy := CurveNormalizedEnergy.normalizedFloor request geometry aBound vector
  let energyPositive := CurveNormalizedEnergy.normalizedFloor_positive request geometry aBound vector nonzero
  let radius := comparison vector energy
  let radiusPositive := Readings.TailEnergyRadii.comparison_positive vector energyPositive
  { radius := radius
    positive := radiusPositive
    sampleIndex := inverseTail.anchor +
      SynchronizedNormalization.tailSynchronizedSampleIndex bank.periodData inverseTail radius radiusPositive
    sampleIndex_eq := rfl }

/-- Retain the controlled normalized energy request on the supplied physical tail, using its exact identity with the
action-derived certificate. -/
@[expose] def requestUsingTail (inverseTail : Periods.PeriodMatrix.ScalarTailSeparationCertificate
  bank.periodData.aMatrix)
    (tailEq : SuppliedTailIdentity (request := request) (action := action) inverseTail)
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus) (nonzero :
      LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate bank.periodData inverseTail
      vector nonzero target positive := open Purelib.Data in by
  let comparison := comparisonUsingTail (request := request) (geometry := geometry) (aBound := aBound) inverseTail
    vector nonzero target positive
  have anchor_le : inverseTail.anchor ≤ comparison.sampleIndex := Nat.le_add_right _ _
  have canonicalAnchor :
      (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate.anchor ≤
        comparison.sampleIndex := by
    rw [← tailEq]
    exact anchor_le
  have raw_le : request.index ≤ comparison.sampleIndex :=
    (CurveNormalizedEnergy.ActionLower.rawIndex_le_anchor action).trans canonicalAnchor
  have scalarNonzero := CurveNormalizedEnergy.ActionLower.scalar_nonzero action comparison.sampleIndex canonicalAnchor
  let coefficients := LinearAlgebra.Gaussian.Energy.scaledNormalizedCoefficients bank.periodData comparison.sampleIndex
    vector
  let coefficientsNonzero := LinearAlgebra.Gaussian.Energy.scaledNormalizedCoefficients_nonzero_of_scalar
    bank.periodData
    comparison.sampleIndex vector nonzero scalarNonzero
  let witness := Hyperelliptic.Integration.Observation.CurveRawCells.surfaceWitness request geometry coefficients
    coefficientsNonzero
  let energy := CurveNormalizedEnergy.normalizedFloor request geometry aBound vector
  have energyPositive : 0 < energy := CurveNormalizedEnergy.normalizedFloor_positive request geometry aBound vector
    nonzero
  let radius := Readings.TailEnergyRadii.refinement vector energy target
  have radiusPositive : 0 < radius := Readings.TailEnergyRadii.refinement_positive vector energyPositive positive
  refine Readings.TailSynchronizedEnergy.TailControlledRequestCertificate.ofSchedule comparison radius radiusPositive
    (Readings.TailEnergyRadii.refinement_target vector energyPositive positive)
    (Readings.TailEnergyRadii.refinement_comparison vector energyPositive positive)
    genus witness.cells (witness.controlledReduction raw_le) (CurveNormalizedEnergy.SurfaceWitness.controlled_error_lt
      witness raw_le) ?_
  exact (Readings.TailEnergyRadii.budgets_lt_energy
    (Periods.PeriodMatrix.NormalizedPeriodData.ofScaledInverse bank.periodData inverseTail.toScaledInverseCertificate)
    vector energyPositive positive).trans_le
      (CurveNormalizedEnergy.SurfaceWitness.normalized_energy_lower (aBound := aBound) witness raw_le
        (Gaussian.Norm.Basic.normSq_pos scalarNonzero))

/-- Build a schedule on the actual retained inverse tail. Per-request
comparison construction reads its anchor and finite presentation; it does not
repeat scalarTailLower or its tail-separation construction. -/
@[expose] def tailScheduleSupplied
    (inverseTail : Periods.PeriodMatrix.ScalarTailSeparationCertificate bank.periodData.aMatrix)
    (tailEq : SuppliedTailIdentity (request := request) (action := action) inverseTail) :
    Readings.TailSynchronizedEnergy.TailControlledSchedule bank.periodData inverseTail where
  schedule := requestUsingTail (request := request) (action := action) (geometry := geometry) (aBound := aBound)
    inverseTail tailEq

/-- Build a comparison schedule on the action-derived tail for the supplied nonzero vector and positive target. -/
@[expose] def tailComparison (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus) (nonzero :
  LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Readings.TailSynchronizedEnergy.TailComparisonSchedule bank.periodData (CurveInverseTail.ActionLower.scalarTailLower
      action).toScalarTailSeparationCertificate
      vector nonzero target positive :=
  let inverseTail := (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate
  comparisonUsingTail (request := request) (geometry := geometry) (aBound := aBound) inverseTail vector nonzero target
    positive

/-- Build a controlled normalized request on the retained action-derived tail for the supplied nonzero vector and
positive target. -/
@[expose] def tailRequest (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus) (nonzero :
  LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate bank.periodData
      (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate
      vector nonzero target positive :=
  let inverseTail := (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate
  requestUsingTail (request := request) (action := action) (geometry := geometry) (aBound := aBound) inverseTail rfl
    vector nonzero target positive

/-- Retain the controlled request schedule on the original action-derived scalar tail. -/
@[expose] def tailSchedule : Readings.TailSynchronizedEnergy.TailControlledSchedule bank.periodData
    (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate :=
  let inverseTail := (CurveInverseTail.ActionLower.scalarTailLower action).toScalarTailSeparationCertificate
  tailScheduleSupplied (request := request) (action := action) (geometry := geometry) (aBound := aBound) inverseTail rfl

end Purelib.Curves.Hyperelliptic.Periods.Normalization.TailSchedule
