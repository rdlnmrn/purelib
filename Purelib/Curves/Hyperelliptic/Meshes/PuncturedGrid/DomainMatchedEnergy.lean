module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.EnergyRibbonCombination
import Purelib.Riemann.Integration.RectangularWholeSideMagnitude
import Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
public import Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

open Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! Coefficient-independent numerical budgets on matched traces in one
retained face domain. Cached basis ribbons supply the combined energy;
the complete trace count and open endpoint correction remain explicit. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {preflight :
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain}
  {leftBox rightBox : Rational.Box} {left : Meshes.RectangularObservationMesh.ObservationMesh
    domain.cuts leftBox} {right : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts rightBox}
  {depth stage : Nat} {localTarget target : Fraction.Rational}

/-- The fixed trace-magnitude ceiling from the original slope and retained boundary-segment count. -/
@[expose] def matchedMagnitude (slope : Fraction.Rational) (segments : Nat) : Fraction.Rational :=
  2 * (slope + (segments : Fraction.Rational) ^ 2 * (2 * (4 + slope)))

/-- The original matched-trace magnitude is nonnegative when its slope is nonnegative. -/
theorem matchedMagnitude_nonnegative {slope : Fraction.Rational} (nonnegative : 0 ≤ slope) (segments : Nat) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude slope segments :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide) nonnegative))))

/-- Increasing the retained slope increases the matched-trace magnitude ceiling. -/
private theorem magnitude_mono {first last : Fraction.Rational} (bound : first ≤ last) (segments : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude first segments ≤
      Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude last segments :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct bound
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct le_rfl bound) (by decide))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))) (by decide)

set_option genInjectivity false in
/-- A fixed trace geometry determines the numerical stage independently of
the eventual coefficient vector. Both the allowance and model requests are
retained, so a later shared numerical bank can discharge the same request. -/
structure MatchedEnergyRequest (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    (slope : Fraction.Rational) (segments count : Nat) (target : Fraction.Rational) where
  /-- The original trace-count budget with its retained common magnitude and positive reading cap. -/ budget :
    Path.EnergyRibbonCombination.CombinationBudget count
    (Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude slope segments) target
  /-- The basis model request at that exact retained trace budget cap. -/ models :
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request preflight budget.cap

constructive_injectivity MatchedEnergyRequest

namespace MatchedEnergyRequest

/-- Allocate the matched-trace budget from its original geometry and request the basis models at the same positive cap.
-/
@[expose] def build (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain) (slope :
  Fraction.Rational) (segments count : Nat) (target : Fraction.Rational)
    (nonnegative : 0 ≤ slope) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.MatchedEnergyRequest preflight slope segments count target
      :=
  let budget := Path.EnergyRibbonCombination.CombinationBudget.build count
    (Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude slope segments) target
    (Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.matchedMagnitude_nonnegative nonnegative segments) positive
  ⟨budget, Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request.build preflight budget.cap
    budget.positive⟩

variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Fraction.Rational} {horizontal :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
    height}
  {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {coordinate : Fraction.Rational} {vertical :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
    coordinate}

/-- The actual retained horizontal basis ribbons satisfy the homogeneous combined energy bound at a sufficient common
model stage. -/
theorem horizontal_combination_bound (tolerance :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance preflight left
  localTarget)
    (trace : horizontal.Trace depth)
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.MatchedEnergyRequest preflight tolerance.slope
      left.boundaryColumns trace.vertices.rest.length target)
    (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (ribbons : Data.Vector (Path.BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ row, ribbons row =
      MatchedHorizontalSide.Trace.energyRibbon
      trace (cached row).anchors (cached row).offsets)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (Path.EnergyRibbonCombination.combine (fun row => coefficients row) (fun row =>
      ribbons row)).difference ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        target := open Purelib.Algebra in by
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  unfold Readings.PreparedObservationCoercivity.coefficientNormSq
  rw [← coefficientNorm]
  apply request.budget.combine_bound
  · intro row vertex
    rw [readback row]
    let accuracy := request.models.rowAtStage stage later row
    let ribbon :=
      MatchedHorizontalSide.Trace.energyRibbon
      trace (cached row).anchors (cached row).offsets
    rw [ribbon.errors_eq]
    change Data.Gaussian.Norm.Basic.normSq ((trace.leftReadings (cached row).anchors (cached row).offsets).values
      vertex -
      (trace.rightReadings (cached row).anchors (cached row).offsets).values vertex) ≤ _
    rw [trace.leftReadings_value, trace.rightReadings_value]
    have scalar := Data.Rat.Fraction.Order.Basic.le_trans _ _ _ (accuracy.overlap_bound (cached row).anchors (cached
      row).offsets domain.patch.cell_refines
      (trace.leftOwner (trace.vertices.indexed vertex)).column (trace.rightOwner (trace.vertices.indexed vertex)).column
      (trace.leftOwner (trace.vertices.indexed vertex)).row (trace.rightOwner (trace.vertices.indexed vertex)).row
      (trace.leftOwner (trace.vertices.indexed vertex)).contains (trace.rightOwner (trace.vertices.indexed
        vertex)).contains)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accuracy.accurate.le (by decide))
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    simp only [Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.leftOwner,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.rightOwner] at scalar
    exact scalar
  · intro row vertex
    rw [readback row]
    let accuracy := request.models.rowAtStage stage later row
    have estimate := Integration.RectangularWholeSideMagnitude.matched_readings_magnitude accuracy (cached row).anchors
      (cached row).offsets domain.patch.cell_refines
      (accuracy.accurate.le.trans request.budget.le_one) trace vertex
    change Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings (cached row).anchors (cached row).offsets).values vertex -
        (trace.rightReadings (cached row).anchors (cached row).offsets).values 0) ≤ _
    have scalar := Data.Rat.Fraction.Order.Basic.le_trans _ _ _ estimate
      (Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.magnitude_mono (tolerance.row_le row)
        left.boundaryColumns)
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar

/-- The actual retained vertical basis ribbons satisfy the homogeneous combined energy bound at a sufficient common
model stage. -/
theorem vertical_combination_bound (tolerance :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance preflight left
  localTarget)
    (trace : vertical.Trace depth)
    (request : Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.MatchedEnergyRequest preflight tolerance.slope
      left.boundaryRows trace.vertices.rest.length target)
    (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (ribbons : Data.Vector (Path.BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ row, ribbons row =
      MatchedVerticalSide.Trace.energyRibbon
      trace (cached row).anchors (cached row).offsets)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (Path.EnergyRibbonCombination.combine (fun row => coefficients row) (fun row =>
      ribbons row)).difference ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        target := open Purelib.Algebra in by
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  unfold Readings.PreparedObservationCoercivity.coefficientNormSq
  rw [← coefficientNorm]
  apply request.budget.combine_bound
  · intro row vertex
    rw [readback row]
    let accuracy := request.models.rowAtStage stage later row
    let ribbon :=
      MatchedVerticalSide.Trace.energyRibbon
      trace (cached row).anchors (cached row).offsets
    rw [ribbon.errors_eq]
    change Data.Gaussian.Norm.Basic.normSq ((trace.leftReadings (cached row).anchors (cached row).offsets).values
      vertex -
      (trace.rightReadings (cached row).anchors (cached row).offsets).values vertex) ≤ _
    rw [trace.leftReadings_value, trace.rightReadings_value]
    have scalar := Data.Rat.Fraction.Order.Basic.le_trans _ _ _ (accuracy.overlap_bound (cached row).anchors (cached
      row).offsets domain.patch.cell_refines
      (trace.leftOwner (trace.vertices.indexed vertex)).column (trace.rightOwner (trace.vertices.indexed vertex)).column
      (trace.leftOwner (trace.vertices.indexed vertex)).row (trace.rightOwner (trace.vertices.indexed vertex)).row
      (trace.leftOwner (trace.vertices.indexed vertex)).contains (trace.rightOwner (trace.vertices.indexed
        vertex)).contains)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accuracy.accurate.le (by decide))
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    simp only [Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.leftOwner,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.rightOwner] at scalar
    exact scalar
  · intro row vertex
    rw [readback row]
    let accuracy := request.models.rowAtStage stage later row
    have estimate := Integration.RectangularWholeVerticalSideMagnitude.matched_vertical_readings_magnitude accuracy
      (cached row).anchors (cached row).offsets domain.patch.cell_refines
      (accuracy.accurate.le.trans request.budget.le_one) trace vertex
    change Data.Gaussian.Norm.Basic.normSq
      ((trace.rightReadings (cached row).anchors (cached row).offsets).values vertex -
        (trace.rightReadings (cached row).anchors (cached row).offsets).values 0) ≤ _
    have scalar := Data.Rat.Fraction.Order.Basic.le_trans _ _ _ estimate
      (Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy.magnitude_mono (tolerance.row_le row) left.boundaryRows)
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar

end MatchedEnergyRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy
