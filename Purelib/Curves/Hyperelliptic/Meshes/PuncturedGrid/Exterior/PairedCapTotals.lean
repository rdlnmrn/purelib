module
import Purelib.Data.List.Zip
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Integration.Path.PairedIncrementComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

public section

/-! Pair actual cap evaluations by their certified original source lists.
The polygon comparison retains both differential totals for every occurrence;
it does not assert that the internal cap paths have matching subdivisions. -/
universe u v w
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

/-- The ordered triangle-source list read from the original sampled cap entries. -/
@[expose] def sources (values :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples requested.entries sample
  shared depth readingIndex) : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
  lifted.mesh.triangles.length) :=
  values.values.map (fun value => value.entry.occurrence.placement.location.sourceEdge)

/-- The sampled entries retain exactly the original preparation's ordered source list. -/
theorem sources_eq (values : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
  requested.entries sample shared depth readingIndex) : values.sources = prepared.sources := by
  have first := congrArg (List.map (fun entry => entry.occurrence.placement.location.sourceEdge)) values.entries_eq
  have last := congrArg (List.map (fun occurrence => occurrence.placement.location.sourceEdge)) requested.occurrences_eq
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at first last
  exact first.trans last

/-- Bound both an original sampled source increment and its cached cap total by twice a common slope plus one. -/
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

/-- Both source projections equal the literal ordered physical exterior. -/
theorem same_sources : left.sources = right.sources :=
  left.sources_eq.trans ((prepared.differential_sources_eq next).trans right.sources_eq.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples in
/-- Two original cap sample banks for the same physical exterior have equal lengths. -/
theorem same_length : left.values.length = right.values.length := by
  have same := congrArg List.length (left.same_sources right)
  simpa only [sources, Map.length_map, -eq_self, -iff_self] using same

/-- The zip retains both full lists; differing cap subdivision depths do not
truncate the original exterior occurrence list. -/
theorem paired_entries_complete :
    (left.values.zip right.values).map Prod.fst = left.values ∧
      (left.values.zip right.values).map Prod.snd = right.values :=
  ⟨Zip.map_fst_zip (left.same_length right).le, Zip.map_snd_zip (left.same_length right).symm.le⟩

/-- Pair the two original source increments with their two cached cap-path totals in retained occurrence order. -/
@[expose] def pairedValues : List (Topology.Polygon.Stokes.PrimitivePoint × Topology.Polygon.Stokes.PrimitivePoint) :=
  (left.values.zip right.values).map (fun pair =>
    (⟨pair.1.increment, pair.2.increment⟩,
     ⟨pair.1.evaluated.right.total, pair.2.evaluated.right.total⟩))

/-- The complete paired reading list has the original request's retained occurrence count. -/
theorem paired_count : (left.pairedValues right).length = requested.count := by
  have complete := congrArg List.length (left.paired_entries_complete right).1
  rw [Map.length_map] at complete
  have retained := congrArg List.length left.entries_eq
  rw [Map.length_map, requested.count_entries] at retained
  exact (Map.length_map ..).trans (complete.trans retained)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples in
/-- The source side of every paired cap reading equals the shared triangle-source increment pair.

Exact ordered source identities align the two differentials while preserving every original occurrence and both cached
cap totals. -/
theorem paired_triangle_values (firstReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    (left.pairedValues right).map Prod.fst = prepared.sources.map (fun source =>
      (⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)) := by
  have matched := Zip.keys_eq_of_mem_zip
    (fun value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular
      := regular) sample shared depth readingIndex requested.localTarget requested.budget.areaTarget floor =>
      value.entry.occurrence.placement.location.sourceEdge)
    (fun value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular
      := regular) otherSample otherShared otherDepth otherReadingIndex otherRequest.localTarget
      otherRequest.budget.areaTarget otherFloor =>
      value.entry.occurrence.placement.location.sourceEdge)
    left.values right.values (left.same_sources right)
  have entries : (left.pairedValues right).map Prod.fst =
      (left.values.zip right.values).map (fun pair =>
        (⟨pair.1.entry.occurrence.placement.location.sourceEdge.increment firstReadings.values,
          pair.1.entry.occurrence.placement.location.sourceEdge.increment lastReadings.values⟩ :
            Topology.Polygon.Stokes.PrimitivePoint)) := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples.pairedValues,
      Map.map_map]
    apply Data.List.Map.map_congr_left
    intro pair member
    have first := pair.1.increment_eq.trans (firstReadings.route_increment _).symm
    have last := pair.2.increment_eq.trans (lastReadings.route_increment _).symm
    have same := matched pair member
    exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk first (last.trans (congrArg (fun source =>
      source.increment lastReadings.values) same).symm)
  have projected := congrArg (List.map (fun value =>
    (⟨value.entry.occurrence.placement.location.sourceEdge.increment firstReadings.values,
      value.entry.occurrence.placement.location.sourceEdge.increment lastReadings.values⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (left.paired_entries_complete right).1
  have sources := congrArg (List.map (fun source =>
    (⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))) left.sources_eq
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at projected
  simp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples.sources,
    Map.map_map, Function.comp_def, -eq_self, -iff_self] at sources
  exact entries.trans (projected.trans sources)

/-- Automatic per-occurrence bounds use the original request slopes. No
caller numerical bound or fresh primitive evaluation is needed. -/
theorem paired_area_error :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((left.pairedValues right).map Prod.fst) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map Prod.snd)) ≤
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
    have leftClose := entries.1.integral_close
    have rightClose := entries.2.integral_close
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at leftClose rightClose
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at lb rb
    exact ⟨⟨leftClose.le.trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _), rightClose.le.trans
      (Data.Rat.Fraction.Order.Basic.le_max_right _ _)⟩,
      ⟨lb.1, rb.1⟩, ⟨lb.2, rb.2⟩⟩
  have estimate := Path.PairedIncrementComparison.area_difference_bound (left.pairedValues right)
    (requested.positive.le.trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative (by decide)))
    (fun pair member => (pointBounds pair member).1)
    (fun pair member => (pointBounds pair member).2.1)
    (fun pair member => (pointBounds pair member).2.2)
  rw [left.paired_count right] at estimate
  exact estimate

/-- Compare the actual shared triangle polygon with paired cap totals.
Each total belongs to a complete retained cap path; their internal paired
areas still need a separate comparison and are not set to zero here. -/
theorem triangle_cap_area_error (firstReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (prepared.sources.map (fun source =>
        (⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map Prod.snd)) ≤
      16 * (requested.count : Fraction.Rational)^4 * max requested.localTarget otherRequest.localTarget *
        (2 * (max requested.slope otherRequest.slope + 1)) :=
  (congrArg (fun values => Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area values -
    Path.PairedIncrementArea.area ((left.pairedValues right).map Prod.snd)))
      (left.paired_triangle_values right firstReadings lastReadings)).symm.trans_le (left.paired_area_error right)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples

end
