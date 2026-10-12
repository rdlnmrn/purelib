module
import Purelib.Tactic.Ring
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.CurveRawRequest
import Purelib.Riemann.Readings.NamedMatrixActionBound
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedObservationSurface
public import Purelib.Curves.Hyperelliptic.Integration.Observation.CurveRawCells
public import Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail
import Purelib.Curves.Hyperelliptic.Periods.Normalization.NormalizedActionLower
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Riemann.Integration.ScalarTailLower

open Purelib

open Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Curves.Hyperelliptic.Periods.Normalization

open Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

public section

/-! The raw surface witness retains a positive normalized energy floor at
every index beyond the computed inverse anchor. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveNormalizedEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Periods.PeriodMatrix (geometricMatrixOfNamed sample_geometricMatrixOfNamed canonicalScaledInverse)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (RationalVector NonzeroVector)
open Purelib.Riemann.Readings.NamedMatrixActionBound (UniformActionBound)
open Purelib.Riemann.Topology.PreparedObservationSurface (ObservationBoxEnergy)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared (surfaceEnergy ControlledBoundaryReduction)
open Purelib.LinearAlgebra.Gaussian.Energy (gaussianVectorOfRational scaledNormalizedCoefficients)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate (synchronizedScaledInverse
  synchronizedNormalizedEnergyLower)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank (RawRequest)
open Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound (ActionLower)
open Purelib.Curves.Hyperelliptic.Integration.Observation.CurveRawCells (SurfaceWitness)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_pos)

variable {genus : Nat} {curve : HyperellipticCurve genus} {bank :
  PairedPeriodBank curve} {floor : Nat}
  (request : RawRequest bank floor) (geometry :
    ObservationBoxEnergy curve.polynomial genus)
  (aBound : UniformActionBound bank.periodData.aMatrix)

/-- The retained raw surface lower coefficient times the original embedded vector norm, divided by the A-action scale.
-/
@[expose] def normalizedFloor (vector : QuadraticForm.RationalVector genus) : Fraction.Rational :=
  min geometry.lower request.lower * PreparedObservationCoercivity.coefficientNormSq (Energy.gaussianVectorOfRational
    vector) / aBound.scale

/-- The retained normalized energy floor is strictly positive for an original nonzero rational vector. -/
theorem normalizedFloor_positive (vector : QuadraticForm.RationalVector genus) (nonzero : QuadraticForm.NonzeroVector
  vector) :
    0 < normalizedFloor request geometry aBound vector
      :=
  Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (Fraction.Order.Basic.lt_min
    geometry.lower_positive request.lower_positive)
    (NormalizedActionLower.embedded_norm_positive vector nonzero)) aBound.scale_positive

namespace ActionLower

variable {request geometry aBound} (action : ActionLower request)

/-- The original raw request stage is paid at the retained inverse-tail anchor. -/
theorem rawIndex_le_anchor : request.index ≤ (ActionLower.scalarTailLower
  action).toScalarTailSeparationCertificate.anchor :=
  (ActionLower.scalarTailLower action).threshold_le_tailAnchor

/-- Every original synchronized inverse scalar is nonzero at or beyond the retained inverse anchor. -/
theorem scalar_nonzero (index : Nat)
    (later : (ActionLower.scalarTailLower action).toScalarTailSeparationCertificate.anchor ≤ index) :
    (Certificate.synchronizedScaledInverse bank.periodData index).scalar ≠ 0 := by
  have read := PivotedScaledInverse.completeApproximation_sample
    (PeriodMatrix.geometricMatrixOfNamed bank.periodData.aMatrix) index
  rw [PeriodMatrix.sample_geometricMatrixOfNamed] at read
  have scalarRead : (PeriodMatrix.canonicalScaledInverse bank.periodData.aMatrix).scalar.sample index =
      (Certificate.synchronizedScaledInverse bank.periodData index).scalar := read.1
  rw [← scalarRead]
  exact (ActionLower.scalarTailLower action).toScalarTailSeparationCertificate.sample_nonzero_of_anchor_le index later

end ActionLower

namespace SurfaceWitness

variable {request geometry aBound} {index : Nat} {vector : RationalVector
  genus}
  (witness : SurfaceWitness request geometry
    (Purelib.LinearAlgebra.Gaussian.Energy.scaledNormalizedCoefficients bank.periodData index vector))

/-- The retained controlled boundary error is strictly below the original surface energy. -/
theorem controlled_error_lt (later : request.index ≤ index) :
    (witness.controlledReduction later).boundaryError < Prepared.surfaceEnergy witness.cells :=
  witness.energy_positive

/-- The original surface witness retains the computed normalized energy floor once the synchronized inverse scalar is
positive. -/
theorem normalized_energy_lower (later : request.index ≤ index)
    (scalarPositive : 0 < Data.Gaussian.Norm.Basic.normSq (Certificate.synchronizedScaledInverse
      bank.periodData index).scalar) :
    Curves.Hyperelliptic.Periods.Normalization.CurveNormalizedEnergy.normalizedFloor request geometry aBound vector ≤
      Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate.synchronizedNormalizedEnergyLower bank.periodData
        index
        ((witness.controlledReduction later).effectiveCells
          (controlled_error_lt witness
          later)) := by
  unfold Certificate.synchronizedNormalizedEnergyLower
  rw [ControlledBoundaryReduction.cellEnergy_effectiveCells]
  change Curves.Hyperelliptic.Periods.Normalization.CurveNormalizedEnergy.normalizedFloor request geometry aBound vector
    ≤ (Prepared.surfaceEnergy witness.cells - 0) / _
  have zeroSub : Prepared.surfaceEnergy witness.cells - 0 = Prepared.surfaceEnergy witness.cells := by
    ring0
  rewrite [zeroSub]
  exact NormalizedActionLower.normalized_lower bank.periodData aBound index vector scalarPositive
    (min geometry.lower request.lower) (Fraction.Order.Basic.lt_min geometry.lower_positive request.lower_positive).le
    (Prepared.surfaceEnergy witness.cells) witness.homogeneous_lower

end SurfaceWitness
end Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveNormalizedEnergy
