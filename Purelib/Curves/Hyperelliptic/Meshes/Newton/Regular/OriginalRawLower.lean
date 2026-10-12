module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.NewtonRawPeriodGeometry
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawAcquisition
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Positive homogeneous coercivity on the original displayed A/B matrices,
for every later sample of a regular even-degree retained request. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest

open Purelib

open Purelib.Riemann.Normalization
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {radius : Fraction.Rational}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {floor : Nat}

namespace RegularOriginalRawRequest

variable (request : Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest.RegularOriginalRawRequest prepared
  observations preparation radius regular floor)

/-- Acquire one shared polynomial and numerical bank at the requested later
stage; all surface and original-period comparisons consume that same bank. -/
@[expose] def acquire (stage : Nat) (first : Fin genus) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (later : request.index ≤ stage) :
    Hyperelliptic.Meshes.Newton.Regular.RawAcquisition.RegularRawAcquisition prepared observations preparation radius
      regular request.raw stage first :=
  Hyperelliptic.Meshes.Newton.Regular.RawAcquisition.RegularRawAcquisition.build prepared observations preparation
    radius regular request.raw stage first degree (request.raw_le.trans later)

/-- The comparison spends only half the strictly positive observation margin. -/
theorem lower_positive : 0 < Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 :=
  Fraction.Order.Field.div_pos_direct (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant_positive
    observations) (by decide)

/-- The acquired original raw matrices retain half the positive observation margin as a quadratic lower bound.

At a stage satisfying the retained request and the even-degree equality, the same cached triangle primitives and sheet
witnesses transfer the observation energy bound to the displayed A and B matrices. -/
theorem acquired_lower {stage : Nat} {first : Fin genus}
    (acquired : Hyperelliptic.Meshes.Newton.Regular.RawAcquisition.RegularRawAcquisition prepared observations
      preparation radius regular request.raw stage first)
    (later : request.index ≤ stage) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients
        (Periods.PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage) (Periods.PeriodMatrix.sampledMatrix
          prepared.periodData.bMatrix stage) := open Algebra in open Data in by
  let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    request.raw.grid.lifted.mesh (acquired.samples.period.triangles.get basis).values
  let energy := fun incoming => LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients
    (Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      request.raw.grid.allocated.family.single.grid.shrunk.included request.raw.grid.lifted.edges
      request.raw.grid.lifted.vertices incoming values false)
    (Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      request.raw.grid.allocated.family.single.grid.shrunk.included request.raw.grid.lifted.edges
      request.raw.grid.lifted.vertices incoming values true)
  have raw : Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ energy request.newSheet :=
    acquired.raw_lower coefficients (request.raw_le.trans later) degree
  have sheetRead := congrArg energy request.sheet_eq
  have transferred := request.comparison.energy_lower stage acquired.cache acquired.samples.period.triangles
    (request.comparison_le.trans later) coefficients
  have coefficientSumEq :
      (FiniteSum.Fin.sumFin fun basis => Gaussian.Norm.Basic.normSq (coefficients basis)) =
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold Readings.PreparedObservationCoercivity.coefficientNormSq
    apply FiniteSum.Fin.sumFin_congr
    intro basis
    exact Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis)
  rw [coefficientSumEq] at transferred
  have half : Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 * 2 =
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations :=
    Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  calc
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients =
        Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients -
          Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
            Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
      calc
        _ = (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 * 2) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients -
            Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
              Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by ring1
        _ = _ := by rw [half]
    _ ≤ energy (Periods.NewtonCanonicalPeriodReadback.canonicalPeriodSheet (lifted := lifted) (sheet := sheet)
      (Periods.NewtonRawPeriodGeometry.periodGeometry request.raw.grid)) -
        Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
      Fraction.Order.Arithmetic.sub_le_sub_right_direct (raw.trans_eq sheetRead) _
    _ ≤ _ := transferred

/-- The later-stage raw bound needs no caller surface sample or analytic
certificate: the retained request constructs all of its finite samples. -/
theorem lower (stage : Nat) (first : Fin genus) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (later : request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients
        (Periods.PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage) (Periods.PeriodMatrix.sampledMatrix
          prepared.periodData.bMatrix stage) :=
  request.acquired_lower (request.acquire stage first degree later) later degree coefficients

end RegularOriginalRawRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest
