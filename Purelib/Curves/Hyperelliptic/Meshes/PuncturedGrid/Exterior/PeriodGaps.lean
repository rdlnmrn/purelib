module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyGaps
import Purelib.Riemann.Periods.SegmentGapPeriods
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest

open Purelib.Data.Rat

open Purelib.Riemann.Periods

public section

/-! The original reciprocal endpoint requests bound the total period of
the actual exterior source readings. Every count is an original surface
segment count; later subdivision counts do not enter this closing bound. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodGaps

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
  (RootEnergyAcquisition)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index
    depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

/-- The retained chart summary total is exactly the Gaussian sum of its original entry summary totals. -/
private theorem chart_totals
    (values : List (ChartSamples.ChartedEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea chartTarget floor)) :
    (ChartedEntry.summary values).total = Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun entry =>
      entry.chart.summary.total)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (head.chart.summary.total + ·) ih

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodGaps

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
namespace RootEnergyAcquisition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
  (RootEnergyAcquisition)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index
    depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}
  {request : Request
    prepared target areaTarget floor} {charts :
    SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
    request chartTarget}
  {component :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential} {joining energyTarget :
    Coordinate}
  {depthFloor energyFloor : Nat}

/-- The cached chart total is controlled by the actual closing root requests. This uses the original odd-degree exterior
component, not a substituted loop. -/
theorem period_total_bound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget
  depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq acquired.evaluated.summary.total ≤
      (request.count : InverseRootPolynomial.Coordinate) * ((request.count : InverseRootPolynomial.Coordinate) *
        acquired.roots.allowance) := by
  have gaps := RootEnergyAcquisition.segment_gaps (curve := curve) acquired branch
  have bounded := SegmentGapPeriods.closed_total_bound _ gaps
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
  have totals := acquired.energy.data.segments_totals branch acquired.evaluated.samples.values
    acquired.energy.occurrences_nonempty
  have count : (acquired.energy.data.segments branch acquired.evaluated.samples.values).length = request.count :=
    (acquired.energy.data.segments_length branch acquired.evaluated.samples.values).trans
      (acquired.evaluated.samples.count_eq.trans request.count_entries)
  have totalEq := acquired.evaluated.summary.total_eq.trans
    (ChartedEntry.summary acquired.evaluated.samples.values).total_eq.symm
  have equal := totalEq.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodGaps.chart_totals
    acquired.evaluated.samples.values)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_le
    ((congrArg (fun values => Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      values)) totals).symm.trans_le
      (bounded.trans_eq (congrArg (fun size : Nat =>
        (size : InverseRootPolynomial.Coordinate) * ((size : InverseRootPolynomial.Coordinate) *
          acquired.roots.allowance)) count)))

/-- The same surface source integral used by the reciprocal comparison is small with a computed bound from its local
request and closing allowance. -/
theorem source_period_bound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget
  depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq acquired.evaluated.original.integral <
      2 * (target + (request.count : InverseRootPolynomial.Coordinate) * ((request.count :
        InverseRootPolynomial.Coordinate) * acquired.roots.allowance)) := by
  have total := acquired.period_total_bound branch
  have integralClose := acquired.evaluated.integral_close
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at integralClose
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (acquired.evaluated.original.integral - acquired.evaluated.summary.total) acquired.evaluated.summary.total).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      ((add_le_add le_rfl total).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_right_direct integralClose _)))
  have same : acquired.evaluated.original.integral - acquired.evaluated.summary.total + acquired.evaluated.summary.total
    =
      acquired.evaluated.original.integral := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq same).symm.trans_lt bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest.RootEnergyAcquisition
