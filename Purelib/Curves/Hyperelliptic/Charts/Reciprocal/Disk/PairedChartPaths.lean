module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
public import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Data.Vector.Dependent
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! Finite paired chart paths preserve their original samples and endpoint
terms. The comparison pays the actual edge count and does not assert that
the source path itself has small area. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary.HandleAreaBounds
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings (PairedChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest (Evaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
variable {genus count otherCount index : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch otherParent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : ParameterEdge}
  {cell : Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {model : RootModel cell} {otherModel :
    RootModel otherCell}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}

namespace PairedChartRequest
variable {parameter otherParameter target : Coordinate} {floor stage
  : Nat}
  {leftPoint : Point cap model parameter} {rightPoint :
    Point cap otherModel otherParameter}
  {joined : Join leftPoint rightPoint} {request :
    PairedChartRequest joined sample otherSample
    target floor}

/-- Pair the actual first differential reading with the second reading on its separate original owner. -/
@[expose] def Evaluation.originalPoint (readings : PairedChartRequest.Evaluation request stage) : PrimitivePoint :=
  ⟨readings.first.value, readings.originalOther.value⟩

/-- Pair the two retained chart primitive values on their common original coordinate. -/
@[expose] def Evaluation.chartPoint (readings : PairedChartRequest.Evaluation request stage) : PrimitivePoint :=
  ⟨readings.firstChart.value, readings.otherChart.value⟩

/-- Sum the retained center bounds of the two original endpoint approximation streams. -/
@[expose] def pointBound (request : PairedChartReadings.PairedChartRequest joined sample otherSample target floor) :
  Coordinate :=
  request.first.approximation.centerBound + request.originalOther.approximation.centerBound

/-- The two original approximation center bounds give a nonnegative paired-point ceiling. -/
theorem pointBound_nonnegative (request : PairedChartReadings.PairedChartRequest joined sample otherSample target floor)
  : 0 ≤ request.pointBound :=
  add_nonneg request.first.approximation.centerBound_nonneg request.originalOther.approximation.centerBound_nonneg

/-- Both components of the retained original paired point satisfy its cached stream ceiling. -/
theorem Evaluation.original_bounded (readings : PairedChartRequest.Evaluation request stage) :
    PrimitivePoint.Bounded readings.originalPoint request.pointBound := by
  constructor
  · change Data.Gaussian.Basic.Canonical.normSq readings.first.value ≤ _
    rw [readings.first.sample_eq]
    have scalar := request.first.approximation.sample_bounded stage
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      (le_add_of_nonneg_right request.originalOther.approximation.centerBound_nonneg)
  · change Data.Gaussian.Basic.Canonical.normSq readings.originalOther.value ≤ _
    rw [readings.originalOther.sample_eq]
    have scalar := request.originalOther.approximation.sample_bounded stage
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      (le_add_of_nonneg_left request.first.approximation.centerBound_nonneg)

/-- The actual original paired point and shared-coordinate chart point differ componentwise by at most four targets. -/
theorem Evaluation.point_error (readings : PairedChartRequest.Evaluation request stage) :
    PrimitivePoint.Bounded
      (readings.originalPoint.sub readings.chartPoint) (4 * target) := by
  constructor
  · have scalar := readings.firstChart.accurate.le
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      ((by ring1 : target = 1 * target).trans_le
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) request.firstChart.positive.le))
  · change Data.Gaussian.Basic.Canonical.normSq (readings.originalOther.value - readings.otherChart.value) ≤ _
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    have expanded : readings.originalOther.value - readings.otherChart.value =
        (readings.originalOther.value - readings.other.value) + (readings.other.value - readings.otherChart.value) := by
          ring1
    rw [expanded]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct readings.transported.le readings.otherChart.accurate.le) (by
          decide)).trans_eq (by ring1))

/-- Change only the comparison requests; keep all three endpoint coefficients and their prepared root-coordinate
programs. -/
@[expose] def withTarget (request : PairedChartReadings.PairedChartRequest joined sample otherSample target floor)
    (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) : PairedChartReadings.PairedChartRequest
      joined sample otherSample requested floor := by
  let firstChart := ChartRequest.build request.first requested positive floor
  let otherChart := ChartRequest.build request.other requested positive floor
  have agrees : Gaussian.Equivalence.Equivalent request.originalOther.approximation request.other.approximation :=
    request.originalOther.sampled_agreement.symm.trans
      (Equivalent.trans (joined.primitiveEquivalent otherSample).symm request.other.sampled_agreement)
  let transport := agrees.compare floor floor requested positive
  exact ⟨request.first, request.other, request.originalOther, firstChart, otherChart, transport,
    max firstChart.stage (max otherChart.stage (max transport.leftIndex transport.rightIndex)), rfl⟩

end PairedChartRequest

/-- The componentwise difference of two paired points with a common squared-norm ceiling is bounded by four times that
ceiling. -/
theorem sub_bound {a b : Stokes.PrimitivePoint} {bound : InverseRootPolynomial.Coordinate}
    (first : PrimitivePoint.Bounded a bound)
    (last : PrimitivePoint.Bounded b bound) :
    PrimitivePoint.Bounded (a.sub b) (4 * bound) := by
  constructor
  · have scalar := Data.Gaussian.Norm.Bounds.normSq_sub_le_two a.left b.left
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at scalar
    exact scalar.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first.1
        last.1) (by decide)).trans_eq (by ring1))
  · have scalar := Data.Gaussian.Norm.Bounds.normSq_sub_le_two a.right b.right
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at scalar
    exact scalar.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first.2
        last.2) (by decide)).trans_eq (by ring1))
section Paths
variable {edges : Nat} {parameters otherParameters : Fin (edges + 1) →
  Coordinate}
  {leftPoints : (i : Fin (edges + 1)) → Point cap model
    (parameters i)}
  {rightPoints : (i : Fin (edges + 1)) → Point cap
    otherModel (otherParameters i)}
  (joins : (i : Fin (edges + 1)) → Join (leftPoints i)
    (rightPoints i))
  {target : Coordinate} {floor : Nat}

/-- The paired chart request at one exact original joined path vertex. -/
@[expose] def ChartPathRequestAt (i : Fin (edges + 1)) := PairedChartReadings.PairedChartRequest (joins i) sample
  otherSample target floor

/-- Read the original paired vertex request's required common reading stage. -/
@[expose] def chartPathStageWeight (i : Fin (edges + 1)) (request :
  ChartPathRequestAt (sample := sample) (otherSample :=
  otherSample) joins (target := target) (floor := floor) i) : Nat := request.stage

set_option genInjectivity false in
/-- Paired chart requests retained at every original path vertex with one common reading stage.

The dependent vector keeps each original coordinate join and both differential samples. -/
structure ChartPathRequest where
  /-- The retained dependent vector of original paired vertex requests. -/ entries : Data.Vector.DependentVector
    (ChartPathRequestAt (sample := sample) (otherSample
    := otherSample) joins (target := target) (floor := floor))
  /-- The cached common stage for all original path vertex readings. -/ stage : Nat
  /-- The cached stage is exactly the maximum original vertex request stage. -/ stage_eq : stage = entries.maximum
    (chartPathStageWeight joins)

constructive_injectivity ChartPathRequest

namespace ChartPathRequest

/-- Prepare the original paired coordinate joins at every retained path vertex and cache their common reading stage. -/
@[expose] def build (sample : Primitives.Sample cap differential index box)
    (otherSample : Primitives.Sample cap other index otherBox)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
      otherSample) joins (target := target) (floor := floor) :=
  let entries := DependentVector.ofFn (fun i => PairedChartRequest.build (joins i) sample otherSample target positive
    floor)
  ⟨entries, entries.maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.chartPathStageWeight
    joins), rfl⟩

variable {joins}

/-- The retained common path reading stage respects the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample :=
  sample) (otherSample := otherSample) joins (target := target) (floor := floor)) :
    floor ≤ request.stage := by
  let entry := request.entries.get 0
  have localFloor : floor ≤ entry.stage :=
    entry.firstChart.floor_le.trans (entry.stage_eq.symm ▸ Data.Nat.Order.le_max_left _ _)
  exact localFloor.trans ((DependentVector.get_le_maximum
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.chartPathStageWeight joins) request.entries
      0).trans_eq request.stage_eq.symm)

/-- The original paired vertex evaluation at this retained path request's common stage. -/
@[expose] def ReadingAt (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor))
    (i : Fin (edges + 1)) := PairedChartRequest.Evaluation (request.entries.get i) request.stage

/-- The dependent vector of actual paired readings indexed by the original path requests. -/
@[expose] def Readings (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor)) :=
  Data.Vector.DependentVector (request.ReadingAt)

/-- Read each original paired endpoint request once at the retained common path stage. -/
@[expose] def acquire (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor)) : request.Readings :=
  DependentVector.ofFn (fun i => (request.entries.get i).evaluate request.stage
    ((DependentVector.get_le_maximum
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.chartPathStageWeight joins) request.entries
      i).trans_eq request.stage_eq.symm))

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample :=
  sample) (otherSample := otherSample) joins (target := target) (floor := floor)}

/-- Read the original paired primitive point at this exact retained path vertex. -/
@[expose] def originalValues (readings : request.Readings) (i : Fin (edges + 1)) : PrimitivePoint := (readings.get
  i).originalPoint
/-- Read the shared-coordinate chart primitive point at this exact retained path vertex. -/
@[expose] def chartValues (readings : request.Readings) (i : Fin (edges + 1)) : PrimitivePoint := (readings.get
  i).chartPoint
/-- The finite centered path sample of the original paired primitive readings. -/
@[expose] def OriginalSample (readings : request.Readings) := CenteredBilinearPath.Sample
  (originalValues readings)
/-- The finite centered path sample of the retained paired chart readings. -/
@[expose] def ChartSample (readings : request.Readings) := CenteredBilinearPath.Sample
  (chartValues readings)

/-- The cached finite sum of the original paired vertex stream ceilings. -/
@[expose] def magnitude (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor)) : Coordinate :=
  FiniteSum.Fin.sumFin (fun i => (request.entries.get i).pointBound)

/-- The original finite vertex stream ceilings have a nonnegative total magnitude. -/
theorem magnitude_nonnegative (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
  otherSample) joins (target := target) (floor := floor)) :
    0 ≤ request.magnitude := FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun i => (request.entries.get
      i).pointBound_nonnegative)

/-- Retarget the original paired request vector while preserving every endpoint coefficient and root-coordinate program.
-/
@[expose] def withTarget (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor))
    (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
      otherSample) joins (target := requested) (floor := floor) :=
  let entries := DependentVector.ofFn (fun i => (request.entries.get i).withTarget requested positive)
  ⟨entries, entries.maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.chartPathStageWeight
    joins), rfl⟩

/-- Changing only the comparison target preserves the exact original path magnitude. -/
theorem withTarget_magnitude (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor))
    (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) : (request.withTarget requested
      positive).magnitude = request.magnitude := by
  apply FiniteSum.Fin.sumFin_congr
  intro i
  change ((DependentVector.ofFn (fun i => (request.entries.get i).withTarget requested positive)).get i).pointBound = _
  rw [DependentVector.ofFn_get]
  rfl

/-- Each original paired path reading satisfies the finite magnitude ceiling retained by the request. -/
theorem original_bound (readings : request.Readings) (i : Fin (edges + 1)) :
    PrimitivePoint.Bounded
      (originalValues readings i)
        request.magnitude := by
  have bounded := (readings.get i).original_bounded
  have larger := FiniteSum.Fin.Rational.entry_le_sum (fun i => (request.entries.get i).pointBound)
    (fun i => (request.entries.get i).pointBound_nonnegative) i
  exact ⟨bounded.1.trans larger, bounded.2.trans larger⟩

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
/-- The original paired path area comparison with both retained open endpoint corrections explicit. -/
@[expose] def AreaEstimate {readings : request.Readings} (original :
  OriginalSample readings) (chart :
  ChartSample readings)
    (magnitude : InverseRootPolynomial.Coordinate) : Prop :=
  Data.Gaussian.Norm.Basic.normSq ((chart.originalArea - original.originalArea) - (chart.endpoint -
    original.endpoint)) ≤
    (edges : InverseRootPolynomial.Coordinate)^2 * (32 * (4 * magnitude + 1) * (16 * target))

/-- The complete original paired path area discrepancy bounded by its actual edge count and retained magnitude. -/
@[expose] def FullAreaEstimate {readings : request.Readings} (original :
  OriginalSample readings) (chart :
  ChartSample readings)
    (magnitude : InverseRootPolynomial.Coordinate) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (chart.originalArea - original.originalArea) ≤
    (edges : InverseRootPolynomial.Coordinate)^2 * (32 * (4 * magnitude + 1) * (16 * target))

end

/-- Reversing an original Gaussian difference preserves its squared norm. -/
theorem reverse_norm (first last : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Norm.Basic.normSq (first -
  last) = Data.Gaussian.Norm.Basic.normSq (last - first) :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1 : first - last = -(last - first))).trans
    (Data.Gaussian.Norm.Basic.normSq_neg _)

/-- Compare every original edge directly. Thus endpoint contributions are controlled as part of the full path, without
assuming either path closes. -/
theorem compare_full (readings : request.Readings) (original :
  OriginalSample readings) (chart :
  ChartSample readings)
    (small : 16 * target ≤ 1) :
      FullAreaEstimate original chart
      request.magnitude := by
  have positive : 0 < target := (request.entries.get 0).firstChart.positive
  have magnitudeLe : request.magnitude ≤ 4 * request.magnitude :=
    (by ring1 : request.magnitude = 1 * request.magnitude).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) request.magnitude_nonnegative)
  have errorLe : 4 * target ≤ 16 * target :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) positive.le
  have bounded (i : Fin (edges + 1)) :
      PrimitivePoint.Bounded
        (originalValues readings i) (4
          * request.magnitude) :=
    ⟨(original_bound readings
      i).1.trans magnitudeLe,
      (original_bound readings
      i).2.trans magnitudeLe⟩
  have accurate (i : Fin (edges + 1)) :
      PrimitivePoint.Bounded
        ((chartValues readings i).sub
          (originalValues readings i))
          (16 * target) :=
    by
      constructor
      · have scalar := reverse_norm
          (chartValues readings i).left
          (originalValues readings
          i).left
        simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at scalar
        exact (scalar.trans_le (readings.get i).point_error.1).trans errorLe
      · have scalar := reverse_norm
          (chartValues readings i).right
          (originalValues readings
          i).right
        simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at scalar
        exact (scalar.trans_le (readings.get i).point_error.2).trans errorLe
  change Data.Gaussian.Norm.Basic.normSq (chart.originalArea - original.originalArea) ≤ _
  rw [chart.originalArea_eq, original.originalArea_eq]
  unfold CenteredBilinearPath.area
  rw [← FiniteSum.Fin.sumFin_sub]
  exact Indexed.normSq_sumFin_le _ _ (fun edge =>
    PrimitivePoint.area_difference_bound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.magnitude_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small
      (bounded edge.castSucc) (bounded edge.succ) (accurate edge.castSucc) (accurate edge.succ))

/-- The centered chart and original paired paths satisfy the retained finite bound including both original endpoint
corrections. -/
theorem compare (readings : request.Readings) (original :
  OriginalSample readings) (chart :
  ChartSample readings)
    (small : 16 * target ≤ 1) :
      AreaEstimate original chart
      request.magnitude := by
  have positive : 0 < target := (request.entries.get 0).firstChart.positive
  apply chart.comparison original
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.magnitude_nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small
  · intro i
    rw [original.centered_eq]
    exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.sub_bound
      (original_bound readings i)
      (original_bound readings 0)
  · intro i
    have bounded := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.sub_bound (readings.get
      0).point_error (readings.get i).point_error
    have equal : (chart.centered i).sub (original.centered i) =
        ((originalValues readings
          0).sub (chartValues readings
          0)).sub
          ((originalValues readings
            i).sub (chartValues
            readings i)) := by
      rw [chart.centered_eq, original.centered_eq]
      apply congrArg₂ PrimitivePoint.mk <;> simp only [PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1
    have scalar : 4 * (4 * target) = 16 * target := by ring1
    rw [equal, ← scalar]
    exact bounded

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
set_option genInjectivity false in
/-- Cached original and chart path samples with both full-area and endpoint-corrected finite comparison certificates. -/
structure AreaEvaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor)) where
  /-- The cached actual paired readings at the original request's shared stage. -/ readings : request.Readings
  /-- The cached centered path sample of the original paired readings. -/ original :
    OriginalSample readings
  /-- The cached centered path sample of the shared-coordinate chart readings. -/ chart :
    ChartSample readings
  /-- The cached finite sum of the original paired vertex stream ceilings. -/ magnitude :
    InverseRootPolynomial.Coordinate
  /-- The cached magnitude is exactly that of the original retained path request. -/ magnitude_eq : magnitude =
    request.magnitude
  /-- The retained area comparison with both original endpoint corrections explicit. -/ estimate :
    AreaEstimate original chart
    magnitude
  /-- The retained comparison of the complete original and chart path areas. -/ full_estimate :
    FullAreaEstimate original chart
    magnitude

constructive_injectivity AreaEvaluation

/-- Read the retained original vertex bank once and cache both finite path samples and their area comparison bounds. -/
@[expose] def acquireArea (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor))
    (small : 16 * target ≤ 1) :
      AreaEvaluation request :=
  let readings := request.acquire
  let original := CenteredBilinearPath.Sample.build
    (originalValues readings)
  let chart := CenteredBilinearPath.Sample.build
    (chartValues readings)
  ⟨readings, original, chart, request.magnitude, rfl,
    compare readings original chart
    small,
    compare_full readings original
      chart small⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
/-- The exact finite edge-count and retained-magnitude cost of the paired path area comparison. -/
@[expose] def areaRate (edges : Nat) (magnitude : InverseRootPolynomial.Coordinate) : Coordinate :=
  (edges : InverseRootPolynomial.Coordinate)^2 * (32 * (4 * magnitude + 1) * 16)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
set_option genInjectivity false in
/-- A positive vertex tolerance paying the requested original paired path area discrepancy.

The tolerance also satisfies the finite comparison's smallness condition and permits a zero-edge path. -/
structure AreaBudget (edges : Nat) (magnitude requested : InverseRootPolynomial.Coordinate) where
  /-- The cached positive comparison tolerance at each original vertex. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The tolerance is capped by one sixteenth and the original weighted area allowance. -/ tolerance_eq : tolerance =
    min (1 / 16) (Weighted.allowance (requested / 2)
    (areaRate edges magnitude))
  /-- The retained per-vertex tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- Sixteen times the retained comparison tolerance is at most one. -/ small : 16 * tolerance ≤ 1
  /-- The retained tolerance pays the exact original edge-count and magnitude area cost. -/ paid : (edges :
    InverseRootPolynomial.Coordinate)^2 * (32 * (4 * magnitude + 1) * (16 * tolerance)) < requested

constructive_injectivity AreaBudget

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
/-- Choose a positive small vertex tolerance paying the original path's exact finite area rate. -/
@[expose] def AreaBudget.build (edges : Nat) (magnitude requested : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤
  magnitude)
    (positive : 0 < requested) :
      AreaBudget edges magnitude
      requested := by
  have rateNonnegative : 0 ≤ areaRate
    edges magnitude :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) (by decide)))
      (by decide +kernel))
  have halfPositive : 0 < requested / 2 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let tolerance := min (1 / 16) (Weighted.allowance (requested / 2)
    (areaRate edges magnitude))
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide) (Weighted.allowance_positive
    halfPositive rateNonnegative)
  have small : 16 * tolerance ≤ 1 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left ..) (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 16)).trans_eq (by decide +kernel)
  have halfEq : requested / 2 + requested / 2 = requested :=
    (by ring1 : requested / 2 + requested / 2 = (requested / 2) * 2).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have halfLess : requested / 2 < requested := (Fraction.Field.zero_add _ ▸
    Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive _).trans_eq halfEq
  have paid := ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right (1 / 16)
    _) rateNonnegative).trans
    (Weighted.mul_allowance_le halfPositive.le rateNonnegative)).trans_lt halfLess
  exact ⟨tolerance, rfl, tolerancePositive, small,
    (by dsimp [areaRate]; ring1 :
      (edges : InverseRootPolynomial.Coordinate)^2 * (32 * (4 * magnitude + 1) * (16 * tolerance)) =
      areaRate edges magnitude *
      tolerance).trans_lt paid⟩

/-- The chosen reading tolerance is bounded by half the requested area error even for a zero-edge path. No positive
edge-count premise is needed. -/
theorem AreaBudget.tolerance_le {edges : Nat} {magnitude requested : InverseRootPolynomial.Coordinate}
    (budget : AreaBudget edges
      magnitude requested) (nonnegative : 0 ≤ magnitude) (positive : 0 < requested) :
    budget.tolerance ≤ requested / 2 := by
  have rateNonnegative : 0 ≤ areaRate
    edges magnitude :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) (by decide)))
      (by decide +kernel))
  have denominatorPositive : 0 <
    areaRate edges magnitude + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct rateNonnegative (by decide)
  have allowanceNonnegative := (Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : InverseRootPolynomial.Coordinate) < 2))
      rateNonnegative).le
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (le_add_of_nonneg_left rateNonnegative : (1 : InverseRootPolynomial.Coordinate) ≤
      areaRate edges magnitude + 1)
      allowanceNonnegative
  rw [Fraction.Field.one_mul, Weighted.allowance, Fraction.Field.mul_comm,
    Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'] at bound
  rw [budget.tolerance_eq]
  exact (Fraction.Order.Basic.min_le_right _ _).trans bound

end

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
/-- The refined paired path request is exactly the original request retargeted at the retained paid tolerance. -/
@[expose] def RetargetReadback (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
  otherSample) joins (target := target) (floor := floor))
    {magnitude requested : InverseRootPolynomial.Coordinate} (budget :
      AreaBudget edges magnitude
      requested)
    (refined : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample)
      (otherSample := otherSample) joins (target := budget.tolerance) (floor := floor)) : Prop :=
  refined = request.withTarget budget.tolerance budget.positive

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
set_option genInjectivity false in
/-- The original paired path request with its paid tolerance, exact retargeting and cached area evaluation.

Both complete and endpoint-corrected area discrepancies are bounded by the same original requested target. -/
structure RequestedArea (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest
  (sample := sample) (otherSample := otherSample) joins (target := target) (floor := floor))
    (requested : InverseRootPolynomial.Coordinate) where
  /-- The cached finite sum of the original paired vertex stream ceilings. -/ magnitude :
    InverseRootPolynomial.Coordinate
  /-- The cached magnitude is exactly that of the original retained path request. -/ magnitude_eq : magnitude =
    request.magnitude
  /-- The cached original finite area budget for the retained magnitude and requested target. -/ budget :
    AreaBudget edges magnitude
    requested
  /-- The original paired path request at the retained paid vertex tolerance. -/ refined :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
    otherSample) joins (target := budget.tolerance) (floor := floor)
  /-- The retained refined request is exactly the original request's target-only update. -/ refined_eq :
    RetargetReadback request budget
    refined
  /-- The cached actual area evaluation of this exact retargeted original request. -/ evaluated :
    AreaEvaluation refined
  /-- The complete retained chart and original path areas differ by less than the requested target. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (evaluated.chart.originalArea - evaluated.original.originalArea) <
    requested
  /-- The retained endpoint-corrected area discrepancy is less than the original requested target. -/ corrected_bounded
    : Data.Gaussian.Norm.Basic.normSq ((evaluated.chart.originalArea - evaluated.original.originalArea) -
    (evaluated.chart.endpoint - evaluated.original.endpoint)) < requested

constructive_injectivity RequestedArea

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest in
/-- Retarget only the original comparison requests, preserve their endpoint programs and cache both paid paired-path
area estimates. -/
@[expose] def acquireRequestedArea (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest (sample := sample) (otherSample :=
  otherSample) joins (target := target) (floor := floor))
    (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      RequestedArea request requested
      := by
  let magnitude := request.magnitude
  let budget := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.AreaBudget.build edges
    magnitude requested request.magnitude_nonnegative positive
  let refined := request.withTarget budget.tolerance budget.positive
  let evaluated := refined.acquireArea budget.small
  have magnitudeEq : evaluated.magnitude = magnitude :=
    evaluated.magnitude_eq.trans (request.withTarget_magnitude budget.tolerance budget.positive)
  have scalar := congrArg (fun value => (edges : InverseRootPolynomial.Coordinate)^2 * (32 * (4 * value + 1) * (16 *
    budget.tolerance))) magnitudeEq
  exact ⟨magnitude, rfl, budget, refined, rfl, evaluated,
    evaluated.full_estimate.trans_lt (scalar.trans_lt budget.paid),
    evaluated.estimate.trans_lt (scalar.trans_lt budget.paid)⟩

end ChartPathRequest
end Paths
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
