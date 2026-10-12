module
import Purelib.Data.List.Zip
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

public section

/-! Compare the actual conjugate source polygon with the retained cap totals.
The same paired entries and per-occurrence budgets supply the Hermitian bound. -/
section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
  (Request SampledEntry Samples sourceMaximum_nonnegative)
open Purelib.Riemann.Normalization

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    ExteriorProgram.AllSurfacePreparation
    regular domains differential} {target areaTarget : Fraction.Rational} {floor : Nat}
  {requested : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

/-- Bound each original source increment and cached cap total by twice a common source slope plus one. -/
private theorem bounds (values :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples requested.entries sample
  shared depth readingIndex)
    (value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex requested.localTarget requested.budget.areaTarget floor)
    (member : value ∈ values.values) {slope : Fraction.Rational} (nonnegative : 0 ≤ slope) (slopeLe : requested.slope ≤
      slope) :
    Data.Gaussian.Norm.Basic.normSq value.increment ≤ 2 * (slope + 1) ∧ Data.Gaussian.Norm.Basic.normSq
      value.evaluated.right.total ≤ 2 * (slope + 1) := by
  have sourceLe := (requested.entry_bound value.entry (values.entries_eq ▸ Data.List.Map.mem_map_of_mem member)).trans
    slopeLe
  have small := requested.local_le.trans requested.budget.total_le_one
  have capBound := (value.pair_bounds nonnegative sourceLe small).2.2.2
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum value.evaluated.capPath) ≤ _
    at capBound
  exact ⟨value.increment_bound sourceLe small, (congrArg Data.Gaussian.Norm.Basic.normSq
    value.evaluated.right.total_eq).trans_le capBound⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

variable {other : Hyperelliptic.Differentials.Basic.Differential genus} {next :
  ExteriorProgram.AllSurfacePreparation
  regular domains other}
  {otherTarget otherArea : Fraction.Rational} {otherFloor otherDepth otherReadingIndex : Nat}
  {otherRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request next
    otherTarget otherArea otherFloor}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index box}
  {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains}

variable (left : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
  requested.entries sample shared depth readingIndex)
  (right : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
    otherRequest.entries otherSample otherShared otherDepth otherReadingIndex)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

open Purelib.Integration.Path.ConjugateIncrementComparison in
/-- Automatic per-occurrence bounds use the original request slopes. No
caller numerical bound or fresh primitive evaluation is needed. -/
theorem conjugate_paired_area_error :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((left.pairedValues right).map (fun pair =>
      conjugateFirst pair.1)) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map (fun pair => conjugateFirst pair.2))) ≤
      16 * (requested.count : Fraction.Rational)^4 * max requested.localTarget otherRequest.localTarget *
        (2 * (max requested.slope otherRequest.slope + 1)) := by
  let slope := max requested.slope otherRequest.slope
  have nonnegative : 0 ≤ slope :=
    (requested.slope_eq ▸
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum_nonnegative
      prepared.occurrences).trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _)
  have pointBounds : ∀ pair ∈ left.pairedValues right,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (pair.1.sub pair.2) (max requested.localTarget
        otherRequest.localTarget) ∧
        Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 (2 * (slope + 1)) ∧
          Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 (2 * (slope + 1)) := by
    intro pair member
    obtain ⟨entries, retained, equal⟩ := Data.List.Map.mem_map.mp member
    cases equal
    have members := Zip.of_mem_zip retained
    have lb := left.bounds entries.1 members.1 nonnegative (Data.Rat.Fraction.Order.Basic.le_max_left _ _)
    have rb := right.bounds entries.2 members.2 nonnegative (Data.Rat.Fraction.Order.Basic.le_max_right _ _)
    exact ⟨⟨by
        change Fraction.Order.Basic.LessEqual
          (Gaussian.Basic.Canonical.normSq (entries.1.increment - entries.1.evaluated.right.total))
          (max requested.localTarget otherRequest.localTarget)
        have h := entries.1.integral_close.le.trans (Data.Rat.Fraction.Order.Basic.le_max_left requested.localTarget
          otherRequest.localTarget)
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h,
      by
        change Fraction.Order.Basic.LessEqual _ _
        have h := entries.2.integral_close.le.trans (Data.Rat.Fraction.Order.Basic.le_max_right requested.localTarget
          otherRequest.localTarget)
        change Fraction.Order.Basic.LessEqual _ _ at h
        simpa only [Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using h⟩,
      ⟨by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using lb.1,
        by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using rb.1⟩,
      ⟨by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using lb.2,
        by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using rb.2⟩⟩
  have estimate := Path.ConjugateIncrementComparison.conjugate_area_difference_bound (left.pairedValues right)
    (requested.positive.le.trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative (by decide)))
    (fun pair member => (pointBounds pair member).1)
    (fun pair member => (pointBounds pair member).2.1)
    (fun pair member => (pointBounds pair member).2.2)
  rw [left.paired_count right] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

open Purelib.Integration.Path.ConjugateIncrementComparison in
/-- Compare the actual shared triangle polygon with paired cap totals.
Each total belongs to a complete retained cap path; their internal paired
areas still need a separate comparison and are not set to zero here. -/
theorem conjugate_triangle_cap_area_error (firstReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (prepared.sources.map (fun source =>
        (conjugateFirst ⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map (fun pair => conjugateFirst pair.2))) ≤
      16 * (requested.count : Fraction.Rational)^4 * max requested.localTarget otherRequest.localTarget *
        (2 * (max requested.slope otherRequest.slope + 1)) := by
  have values := congrArg (List.map conjugateFirst)
    (left.paired_triangle_values right firstReadings lastReadings)
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at values
  exact (congrArg (fun values => Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area values -
    Path.PairedIncrementArea.area ((left.pairedValues right).map (fun pair => conjugateFirst pair.2))))
      values).symm.trans_le (left.conjugate_paired_area_error right)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
  (Request Samples sourceMaximum_nonnegative)
open Purelib.Riemann.Normalization

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

section PairedCapRequest
open Purelib.Data.Rat.Fraction.Compatibility

/-- The per-occurrence allowance of a positive target does not exceed that target. -/
private theorem perOccurrence_le_target {target : Fraction.Rational} (positive : 0 < target) (count : Nat) :
    Purelib.Approximation.Rational.Budget.Aggregate.perTerm target count ≤ target := open Purelib.Approximation in by
  have countNonnegative : (0 : Fraction.Rational) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have squareNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct (count : Fraction.Rational)
  have extra : 0 ≤ 2 * (count : Fraction.Rational)^2 + 4 * count + 1 :=
    add_nonneg (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) squareNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative)) (by decide)
  have denominatorLe : (1 : Fraction.Rational) ≤ 2 * ((count : Fraction.Rational) + 1)^2 :=
    (le_add_of_nonneg_right extra).trans_eq (by ring1)
  have denominatorPositive : 0 < (2 : Fraction.Rational) * ((count : Fraction.Rational) + 1)^2 :=
    lt_of_lt_of_le (by decide) denominatorLe
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorLe positive.le
  rw [mul_one] at scaled
  rw [Rational.Budget.Aggregate.perTerm, Rational.Budget.Aggregate.countCoordinate_eq]
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr scaled

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- The original cap request's local allowance is bounded by its positive complete target. -/
private theorem localAllowance_le_target {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches
    :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
    {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
    {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
      Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
    {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {target areaTarget : Fraction.Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
      areaTarget floor) (positive : 0 < target) : request.localTarget ≤ target := by
  rw [request.localTarget_eq]
  exact ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _)).trans
    (perOccurrence_le_target positive request.count)

variable {first :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {last :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains other} {target : Fraction.Rational} {floor : Nat}

section

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {other : Hyperelliptic.Differentials.Basic.Differential genus}
  {first :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  {last :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains other} {target : Fraction.Rational} {floor : Nat}
  {stage depth otherDepth readingIndex otherReadingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
  Purelib.Integration.Path.ConjugateIncrementComparison in
/-- The requested bound holds on any common later bank. The supplied samples
retain both original cap paths, including unequal internal subdivisions. -/
theorem conjugate_accurate (allocated : PairedCapRequest
  first last target floor)
    (left : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
      allocated.left.entries sample shared depth readingIndex)
    (right : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
      allocated.right.entries otherSample otherShared otherDepth otherReadingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (first.sources.map (fun source =>
        (conjugateFirst ⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map (fun pair => conjugateFirst pair.2))) < target := by
  have estimate := left.conjugate_triangle_cap_area_error right firstReadings lastReadings
  have count : allocated.left.count = allocated.count := allocated.left.count_eq.trans allocated.count_eq.symm
  have slope : max allocated.left.slope allocated.right.slope = allocated.slope :=
    (congrArg₂ max allocated.left.slope_eq allocated.right.slope_eq).trans allocated.slope_eq.symm
  have errors : max allocated.left.localTarget allocated.right.localTarget ≤ allocated.allowance :=
    Fraction.Order.Basic.max_le
      (localAllowance_le_target allocated.left
      allocated.positive) (localAllowance_le_target
      allocated.right allocated.positive)
  have coefficient : 16 * (allocated.left.count : Fraction.Rational)^4 *
      (2 * (max allocated.left.slope allocated.right.slope + 1)) = allocated.coefficient := by
    rw [count, slope]
    exact allocated.coefficient_eq.symm
  have payment := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errors allocated.coefficient_nonnegative
  have rearrange : 16 * (allocated.left.count : Fraction.Rational)^4 *
      max allocated.left.localTarget allocated.right.localTarget *
        (2 * (max allocated.left.slope allocated.right.slope + 1)) =
      allocated.coefficient * max allocated.left.localTarget allocated.right.localTarget := by
    rw [← coefficient]
    ring1
  exact estimate.trans_lt ((rearrange.trans_le payment).trans_lt allocated.paid)

namespace Evaluation

/-- The retained paired evaluation satisfies its requested conjugate shared-triangle versus cap-total area bound. -/
theorem conjugate_accurate {allocated :
  PairedCapRequest first last target floor}
    (evaluated : Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (first.sources.map (fun source =>
        (conjugateFirst ⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
        conjugateFirst pair.2))) < target :=
  allocated.conjugate_accurate evaluated.left.samples evaluated.right.samples firstReadings lastReadings

end Evaluation

end
end PairedCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
