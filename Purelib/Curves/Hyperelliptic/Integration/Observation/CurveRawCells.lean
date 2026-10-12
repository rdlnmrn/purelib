module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedObservationSurface
public import Purelib.Riemann.Readings.CurveRawRequest
public import Purelib.Curves.Hyperelliptic.Integration.Observation.RawCoercivityCells
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Riemann.Readings.PreparedObservationBoxes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! Separated geometric cells with both a homogeneous positive lower bound
and the raw tail upper bound. All density scaling uses the retained family's
computed energy; the boxes and denominator certificates remain unchanged. -/
namespace Purelib.Curves.Hyperelliptic.Integration.Observation.CurveRawCells

open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {bank :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve} {floor : Nat}
  (request : Readings.CurveRawRequest.PairedPeriodBank.RawRequest bank floor) (geometry :
    Topology.PreparedObservationSurface.ObservationBoxEnergy curve.polynomial genus)

set_option genInjectivity false in
/-- The energy and cells are cached; both bounds refer to that retained value.
The geometry is supplied once and may be shared across coefficient requests. -/
structure SurfaceWitness (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The actual retained original surface cells. -/ values : Data.Vector
    (Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) genus
  /-- The cached energy of those exact cells. -/ energy : Fraction.Rational
  /-- The cached energy equals the original surface-energy expression. -/ energy_eq : energy =
    Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => values index)
  /-- The cached original energy is positive. -/ positive : 0 < energy
  /-- The original coefficient norm satisfies the retained homogeneous lower bound. -/ norm_lower : min geometry.lower
    request.lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ energy
  /-- The energy is bounded by the original request's norm allowance. -/ raw_upper : energy ≤ request.lower *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The cells retain exactly the original geometric boxes. -/ boxes_eq : ∀ index, (values index).box =
    geometry.boxes.box index

constructive_injectivity SurfaceWitness

/-- Build the original separated surface cells for nonzero coefficients and retain their positive energy with the
homogeneous lower and raw upper bounds. -/
@[expose] def surfaceWitness (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (nonzero : LinearAlgebra.Gaussian.Energy.NonzeroGaussianVector coefficients) : CurveRawCells.SurfaceWitness request
      geometry coefficients := by
  let original := Topology.PreparedObservationSurface.ObservationBoxes.surfaceCells
    geometry.boxes coefficients Hyperelliptic.Integration.Energy.Prepared.canonicalSurfaceFace
  let energy := Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => original index)
  let target := request.lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  have normPositive := Readings.PreparedObservationCoercivity.coefficientNormSq_positive nonzero
  have energyPositive : 0 < energy := geometry.surfaceEnergy_positive coefficients nonzero _
  have targetPositive : 0 < target := Fraction.Order.Arithmetic.mul_pos_direct request.lower_positive normPositive
  let factor := RawCoercivityCells.capFactor energy target
  have factorPositive : 0 < factor := RawCoercivityCells.capFactor_positive energyPositive targetPositive
  have factorBound : factor ≤ 1 := RawCoercivityCells.capFactor_le_one _ _
  let values := RawCoercivityCells.scaleSurfaceCells original factor factorPositive.le factorBound
  have total : Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => values index) = min energy target
    :=
    (RawCoercivityCells.scaleSurfaceCells_energy original factor factorPositive.le factorBound).trans
      (RawCoercivityCells.capFactor_energy energyPositive target)
  refine
    { values := values
      energy := min energy target
      energy_eq := total.symm
      positive := Fraction.Order.Basic.lt_min energyPositive targetPositive
      norm_lower := ?_
      raw_upper := Fraction.Order.Basic.min_le_right _ _
      boxes_eq := ?_ }
  · apply Fraction.Order.Basic.le_min
    · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.min_le_left _ _)
        normPositive.le).trans
        (geometry.lower_mul_coefficientNorm_le_surfaceEnergy coefficients _)
    · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.min_le_right _ _)
        normPositive.le
  · intro index
    exact (RawCoercivityCells.scaleSurfaceCells_box original factor factorPositive.le factorBound index).trans
      (Topology.PreparedObservationSurface.ObservationBoxes.surfaceCells_box
        geometry.boxes coefficients Hyperelliptic.Integration.Energy.Prepared.canonicalSurfaceFace index)

namespace SurfaceWitness

variable {request geometry} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  (witness : CurveRawCells.SurfaceWitness request geometry coefficients)

/-- Read the actual retained original surface cells. -/
@[expose] def cells : Fin genus → Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
  coefficients := fun index => witness.values index

/-- The retained original cell energy is positive. -/
theorem energy_positive : 0 < Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy witness.cells := by
  change 0 < Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => witness.values index)
  rw [← witness.energy_eq]
  exact witness.positive

/-- The retained cells occupy the exact original pairwise separated boxes. -/
theorem separated {left right : Fin genus} (different : left ≠ right) :
    (witness.cells left).box.Separated (witness.cells right).box := by
  change (witness.values left).box.Separated (witness.values right).box
  rw [witness.boxes_eq, witness.boxes_eq]
  exact geometry.boxes.box_separated different

/-- The minimum of the original geometric and observation lower bounds is positive. -/
theorem lower_positive : 0 < min geometry.lower request.lower :=
  Fraction.Order.Basic.lt_min geometry.lower_positive request.lower_positive

/-- The retained energy dominates the original coefficient norm times the shared lower bound. -/
theorem homogeneous_lower : min geometry.lower request.lower * Readings.PreparedObservationCoercivity.coefficientNormSq
  coefficients ≤
    Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy witness.cells := by
  change _ ≤ Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => witness.values index)
  rw [← witness.energy_eq]
  exact witness.norm_lower

/-- Every sufficiently late original period sample bounds the retained cell energy from above. -/
theorem energy_le_raw (stage : Nat) (later : request.index ≤ stage) :
    Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy witness.cells ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients
      (Periods.PeriodMatrix.sampledMatrix bank.periodData.aMatrix stage) (Periods.PeriodMatrix.sampledMatrix
        bank.periodData.bMatrix stage) := by
  change Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => witness.values index) ≤ _
  rw [← witness.energy_eq]
  exact witness.raw_upper.trans (request.accurate stage later coefficients)

/-- Retain the actual cell energy and nonnegative raw-energy remainder with an empty edge-pair list. -/
@[expose] def rawReduction (stage : Nat) (later : request.index ≤ stage) :
    Hyperelliptic.Integration.Energy.Prepared.RawBoundaryReduction bank.periodData coefficients stage witness.cells
      where
  edgePairCount := 0
  edgePairValues := Fin.elim0
  remainder := LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients
    (Periods.PeriodMatrix.sampledMatrix bank.periodData.aMatrix stage) (Periods.PeriodMatrix.sampledMatrix
      bank.periodData.bMatrix stage) - witness.energy
  remainder_nonnegative := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct (witness.raw_upper.trans
    (request.accurate stage later coefficients))
  raw_eq_decomposition := by
    rw [Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
    change _ = Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => witness.values index) + 0 + _
    rw [← witness.energy_eq]
    ring1

/-- Use the retained surface lower bound to construct the original controlled reduction for the scaled coefficient
vector. -/
@[expose] def controlledReduction {stage : Nat} {vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus}
    (witness : CurveRawCells.SurfaceWitness request geometry (LinearAlgebra.Gaussian.Energy.scaledNormalizedCoefficients
      bank.periodData stage vector))
    (later : request.index ≤ stage) : Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction
      bank.periodData vector stage witness.cells :=
  Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction.ofSurfaceLower (witness.energy_le_raw stage
    later)

end SurfaceWitness
end Purelib.Curves.Hyperelliptic.Integration.Observation.CurveRawCells
