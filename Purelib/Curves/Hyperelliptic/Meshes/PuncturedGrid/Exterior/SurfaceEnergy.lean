module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergyData
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Signed energy comparison for the actual shared exterior surface

All retained surface occurrences use one polynomial-bound cache and one fan
mesh. The aggregate compares directly with the physical boundary formula.
Its remaining signed endpoint correction includes the polygon of block totals;
it is displayed explicitly for the original cross-occurrence join proof.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Normalization.InverseRootPolynomial.Coordinate} {floor index depth readingIndex :
    Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

namespace Request.ChartRequest.Plan

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor} {charts :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest request
    chartTarget}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan
    charts sample}

set_option genInjectivity false in
/-- The cached shared-depth energy comparison on the exact original exterior occurrence list.

The original signed endpoint terms, coarse polygon, local discrepancies and physical surface comparison remain explicit.
-/
structure SharedEnergy (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan.Evaluation
  plan shared depth readingIndex) (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat)
  where
  /-- The shared local energy allowance for the original occurrence count. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The allowance is the supplied energy target divided by the original count plus one. -/ allowance_eq : allowance =
    energyTarget / ((request.count : Normalization.InverseRootPolynomial.Coordinate) + 1)
  /-- The retained local energy allowance is positive. -/ allowance_positive : 0 < allowance
  /-- The original occurrence count times the allowance is strictly below the energy target. -/ allowance_paid :
    (request.count : Normalization.InverseRootPolynomial.Coordinate) * allowance < energyTarget
  /-- The single retained reciprocal polynomial bound on the original radial domain. -/ bounds :
    Charts.Reciprocal.Cap.EnergyBounds sample RootContinuation.RootRadialGeometry.domain
  /-- The actual energy preparations for the exact original chart entries. -/ preparations :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyPreparations allowance energyFloor
    evaluated.samples.values
  /-- The common sufficient radial refinement depth. -/ depth : Nat
  /-- The depth is the maximum required by the original retained preparations. -/ depth_eq : depth =
    preparations.maximum evaluated.samples.values
  /-- The shared radial mesh parameters at the retained depth. -/ parameters : Path.Dyadic.RadialTriangles.Parameters
    depth
  /-- The actual evaluated energy data on the exact original occurrence list. -/ data :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData allowance energyFloor depth
    evaluated.samples.values
  /-- The cached sum of the original occurrence energy readings. -/ energy :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached energy is exactly the sum of the retained data values. -/ energy_eq : energy =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (data.values evaluated.samples.values)
  /-- The actual energy exceeds the negative supplied energy target. -/ lower : -energyTarget < energy.im / 4
  /-- The original signed endpoint terms in occurrence order. -/ endpointTerms : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The endpoint list is exactly the boundary readback of the retained energy data. -/ endpointTerms_eq :
    endpointTerms = data.boundaries evaluated.samples.values
  /-- The cached polygon summary of the original chart-block totals. -/ coarse : Path.IncrementArea.Summary
    (evaluated.samples.values.map (fun value => value.chart.summary.total))
  /-- The cached signed boundary correction including the coarse polygon. -/ boundary :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The boundary correction is the original endpoint-term sum plus the coarse polygon area. -/ boundary_eq : boundary
    = Data.Gaussian.Norm.Sum.Basic.gaussianSum endpointTerms + coarse.area
  /-- The original occurrence-by-occurrence comparison errors. -/ errors : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained errors are exactly the energy-data discrepancy list. -/ errors_eq : errors = data.errors
    evaluated.samples.values
  /-- The error list has the original requested occurrence count. -/ count_eq : errors.length = request.count
  /-- The full signed energy discrepancy is exactly the sum of the original retained local errors. -/ discrepancy :
    energy - (-evaluated.summary.area + boundary) = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- The actual energy and signed chart boundary satisfy the paid original chart and local target bound. -/
    boundary_close : Data.Gaussian.Norm.Basic.normSq (energy - (-evaluated.summary.area + boundary)) < 256 * (4 *
    chartTarget + target)
  /-- The actual energy and original physical surface satisfy the combined bound with the signed endpoint correction
    retained. -/ surface_close : Data.Gaussian.Norm.Basic.normSq (energy - (-(evaluated.original.surface.area +
    evaluated.original.internalArea) + boundary)) <
    2 * (256 * (4 * chartTarget + target) + 2 * (areaTarget + chartTarget))

constructive_injectivity SharedEnergy

/-- The surface preparation supplies every orientation from its original
program. Fan generation consumes the actual chart data at the shared depth. -/
@[expose] def Evaluation.energy (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.ChartRequest.Plan.Evaluation
  plan shared depth readingIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :

      SharedEnergy
      evaluated energyTarget energyFloor := open Purelib.Approximation in open Purelib in by
  have countNonnegative : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ request.count :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : (0 : Normalization.InverseRootPolynomial.Coordinate) < request.count + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct countNonnegative (by decide)
  let allowance := energyTarget / ((request.count : Normalization.InverseRootPolynomial.Coordinate) + 1)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have allowancePaid : (request.count : Normalization.InverseRootPolynomial.Coordinate) * allowance < energyTarget := by
    have countLt : (request.count : Normalization.InverseRootPolynomial.Coordinate) < (request.count :
      Normalization.InverseRootPolynomial.Coordinate) + 1 :=
      (show (request.count : Normalization.InverseRootPolynomial.Coordinate) = (request.count :
        Normalization.InverseRootPolynomial.Coordinate) + 0 by ring1).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1) _)
    exact (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct countLt allowancePositive).trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  let bounds := Charts.Reciprocal.Cap.EnergyBounds.build sample
    RootContinuation.RootRadialGeometry.domain
  let preparations := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.prepareEnergy bounds
    allowance allowancePositive energyFloor evaluated.samples.values
  let energyDepth := preparations.maximum evaluated.samples.values
  let parameters := Path.Dyadic.RadialTriangles.Parameters.build energyDepth
  have oriented : ∀ entry ∈ evaluated.samples.values, ∀ parent ∈ entry.entry.occurrence.compared.entered.cache.parents,
      0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) := by
    intro entry member parent parentMember
    have entryMember : entry.entry ∈ request.entries :=
      evaluated.samples.entries_eq ▸ Data.List.Map.mem_map.mpr ⟨entry, member, rfl⟩
    have occurrenceMember : entry.entry.occurrence ∈ prepared.occurrences :=
      request.occurrences_eq ▸ Data.List.Map.mem_map.mpr ⟨entry.entry, entryMember, rfl⟩
    exact prepared.parents_oriented entry.entry.occurrence occurrenceMember parent parentMember
  let data := preparations.evaluate branch parameters evaluated.samples.values oriented le_rfl
  let energy := Data.Gaussian.Norm.Sum.Basic.gaussianSum (data.values evaluated.samples.values)
  have countEq : evaluated.samples.values.length = request.count := evaluated.samples.count_eq.trans
    request.count_entries
  have lower : -energyTarget < energy.im / 4 := by
    have bound := data.lower allowancePositive evaluated.samples.values
    rw [countEq] at bound
    exact (Fraction.Order.Arithmetic.neg_lt_neg_direct allowancePaid).trans_le bound
  let endpointTerms := data.boundaries evaluated.samples.values
  let coarse := Path.IncrementArea.Summary.build (evaluated.samples.values.map (fun value => value.chart.summary.total))
  let boundary := Data.Gaussian.Norm.Sum.Basic.gaussianSum endpointTerms + coarse.area
  let errors := data.errors evaluated.samples.values
  have errorCount : errors.length = request.count := (data.errors_count evaluated.samples.values).trans countEq
  have areaEq : evaluated.summary.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.samples.values.map (fun
    value => value.chart.summary.area)) + coarse.area := by
    rw [evaluated.summary.area_eq, ← (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary
      evaluated.samples.values).area_eq,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.summary_area, coarse.area_eq]
  have discrepancy : energy - (-evaluated.summary.area + boundary) = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors :=
    by
    rw [data.errors_sum evaluated.samples.values, areaEq]
    dsimp only [energy, boundary, endpointTerms]
    ring1
  have localPositive : 0 < charts.localChart := charts.localChart_eq ▸ Rational.Budget.Aggregate.perTerm_positive
    charts.positive _
  have boundaryClose : Data.Gaussian.Norm.Basic.normSq (energy - (-evaluated.summary.area + boundary)) < 256 * (4 *
    chartTarget + target) := by
    rw [discrepancy]
    have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le errors
      (256 * (4 * charts.localChart + request.localTarget))
      (fun error member => by
        have scalar := data.errors_bounded branch localPositive evaluated.samples.values error member
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar)
    rw [errorCount] at estimate
    have chartPaid : (request.count : Normalization.InverseRootPolynomial.Coordinate) * ((request.count :
      Normalization.InverseRootPolynomial.Coordinate) * charts.localChart) < chartTarget := by
      rw [charts.localChart_eq]
      exact Rational.Budget.Aggregate.count_mul_perTerm_lt charts.positive request.count
    have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 256)
      (Fraction.Order.Arithmetic.add_lt_add_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4) chartPaid) request.total_paid)
    exact estimate.trans_lt ((by ring1 :
      (request.count : Normalization.InverseRootPolynomial.Coordinate) * ((request.count :
        Normalization.InverseRootPolynomial.Coordinate) * (256 * (4 * charts.localChart + request.localTarget))) =
        256 * (4 * ((request.count : Normalization.InverseRootPolynomial.Coordinate) * ((request.count :
          Normalization.InverseRootPolynomial.Coordinate) * charts.localChart)) +
          (request.count : Normalization.InverseRootPolynomial.Coordinate) * ((request.count :
            Normalization.InverseRootPolynomial.Coordinate) * request.localTarget))).trans_lt paid)
  have surfaceClose : Data.Gaussian.Norm.Basic.normSq (energy - (-(evaluated.original.surface.area +
    evaluated.original.internalArea) + boundary)) <
      2 * (256 * (4 * chartTarget + target) + 2 * (areaTarget + chartTarget)) := by
    have retainedSurface := evaluated.surface_area_close
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at retainedSurface
    have second : Data.Gaussian.Norm.Basic.normSq ((-evaluated.summary.area + boundary) -
        (-(evaluated.original.surface.area + evaluated.original.internalArea) + boundary)) < 2 * (areaTarget +
          chartTarget) :=
      (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt retainedSurface
    exact (Gaussian.Norm.Bounds.normSq_sub_le_via energy (-evaluated.summary.area + boundary)
      (-(evaluated.original.surface.area + evaluated.original.internalArea) + boundary)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct boundaryClose second))
  exact ⟨allowance, rfl, allowancePositive, allowancePaid, bounds, preparations, energyDepth, rfl, parameters, data,
    energy, rfl, lower, endpointTerms, rfl, coarse, boundary, rfl, errors, rfl, errorCount, discrepancy, boundaryClose,
      surfaceClose⟩

end Request.ChartRequest.Plan
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
